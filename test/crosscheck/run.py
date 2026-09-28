#!/usr/bin/env python3
"""Cross-library CMS harness: the one-flaw corpus through every CMS verifier on this machine.

    python test/crosscheck/run.py [--out DIR]

Builds the corpus (corpus.py, which needs `cryptography`), runs each verifier on every message, and writes
a table of who accepts what to test/crosscheck/RESULTS.md and the raw verdicts to results.json. Every
message except the controls has exactly one flaw and a correct RSA signature, so "accepts" means the
verifier accepted that flaw. Only the signature is judged: no verifier is asked to trust the certificate.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
BREW = "/opt/homebrew/opt"


def sh(cmd, **kw):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, **kw)
    except FileNotFoundError:
        return subprocess.CompletedProcess(cmd, 127, "", f"{cmd[0]} not found")


def per_case(fn):
    def run(d, cases):
        out = {}
        for c in cases:
            try:
                ok, err = fn(d, c)
            except Exception as e:  # noqa: BLE001
                ok, err = False, f"driver error: {e}"
            out[c["id"]] = {"ok": ok, "err": err}
        return out
    return run


def path(d, c, key):
    return os.path.join(d, c[key]) if key in c else None


def lean_driver():
    exe = os.path.join(ROOT, ".lake", "build", "bin", "cms")

    @per_case
    def run(d, c):
        args = [exe, "verify", path(d, c, "msg")]
        if "content" in c:
            args += ["--content", path(d, c, "content")]
        r = json.loads(sh(args).stdout)
        return r["valid"], r.get("reason", "")
    return run


def openssl_driver(binary):
    @per_case
    def run(d, c):
        args = [binary, "cms", "-verify", "-noverify", "-binary", "-inform", "DER", "-in", path(d, c, "msg"),
                "-out", "/dev/null"]
        if "content" in c:
            args += ["-content", path(d, c, "content")]
        r = sh(args)
        return r.returncode == 0, r.stderr.strip().splitlines()[-1] if r.returncode else ""
    return run


def gnutls_driver():
    @per_case
    def run(d, c):
        args = [f"/opt/homebrew/bin/gnutls-certtool", "--p7-verify", "--inder", "--infile", path(d, c, "msg"),
                "--load-ca-certificate", os.path.join(d, "root.pem")]
        if "content" in c:
            args += ["--load-data", path(d, c, "content")]
        r = sh(args)
        err = [l.strip() for l in (r.stdout + r.stderr).splitlines() if "status" in l.lower() or "error" in l.lower()]
        return r.returncode == 0, "; ".join(err)[:200] if r.returncode else ""
    return run


def json_driver(cmd, env=None):
    def run(d, cases):
        r = sh(cmd + [d], env=env)
        out = {}
        for line in r.stdout.splitlines():
            if line.startswith("{"):
                o = json.loads(line)
                out[o["id"]] = {"ok": o["ok"], "err": o.get("err", "")}
        for c in cases:
            out.setdefault(c["id"], {"ok": False, "err": "driver gave no answer: " + r.stderr[-200:]})
        return out
    return run


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=os.path.join(ROOT, "out", "crosscheck"))
    ap.add_argument("--only", help="comma-separated verifiers to run, e.g. Lean,OpenSSL; RESULTS.md is kept")
    a = ap.parse_args()
    d = a.out
    os.makedirs(d, exist_ok=True)
    r = sh([sys.executable, os.path.join(HERE, "corpus.py"), d])
    if r.returncode:
        sys.exit(r.stderr)
    cases = json.load(open(os.path.join(d, "manifest.json")))["cases"]
    with open(os.path.join(d, "manifest.tsv"), "w") as f:
        for c in cases:
            f.write(f"{c['id']}\t{c['msg']}\t{c.get('content', '')}\n")
    openssl3 = f"{BREW}/openssl@3/bin/openssl"
    if not os.path.exists(openssl3):
        openssl3 = shutil.which("openssl")
    for n in ("root", "signer"):
        sh([openssl3, "x509", "-inform", "DER", "-in", os.path.join(d, n + ".der"), "-out", os.path.join(d, n + ".pem")])

    only = set(a.only.split(",")) if a.only else None
    java = f"{BREW}/openjdk/bin/java"
    dotnet_env = dict(os.environ, DOTNET_ROOT=os.path.expanduser("~/.dotnet"), DOTNET_CLI_TELEMETRY_OPTOUT="1")
    dotnet_proj = os.path.join(HERE, "dotnet")
    apple = os.path.join(d, "crosscheck-apple")
    if not only or ".NET" in only:
        sh([os.path.expanduser("~/.dotnet/dotnet"), "build", "-c", "Release", "-o", os.path.join(d, "dotnet-bin"),
            dotnet_proj], env=dotnet_env)
    if not only or "Apple" in only:
        sh(["swiftc", "-O", os.path.join(HERE, "swift", "main.swift"), "-o", apple])

    drivers = [
        ("Lean", lean_driver(), "this project (lean-pkcs7cms)"),
        ("OpenSSL", openssl_driver(openssl3), sh([openssl3, "version"]).stdout.split(" (")[0].strip()),
        ("LibreSSL", openssl_driver("/usr/bin/openssl"), sh(["/usr/bin/openssl", "version"]).stdout.strip() + " (macOS)"),
        ("GnuTLS", gnutls_driver(), "GnuTLS " + (sh(["/opt/homebrew/bin/gnutls-certtool", "--version"]).stdout.split() + ["?", "?"])[1]
         + " (certtool --p7-verify)"),
        ("Java", json_driver([java, "--add-exports", "java.base/sun.security.pkcs=ALL-UNNAMED",
                              os.path.join(HERE, "java", "Main.java")]),
         "OpenJDK " + (sh([java, "-version"]).stderr.split('"') + ["?", "?"])[1] + " (sun.security.pkcs.PKCS7, as jarsigner)"),
        (".NET", json_driver([os.path.expanduser("~/.dotnet/dotnet"), os.path.join(d, "dotnet-bin", "crosscheck.dll")],
                             env=dotnet_env),
         ".NET 10, System.Security.Cryptography.Pkcs 10.0.12 (SignedCms.CheckSignature)"),
        ("Apple", json_driver([apple]), "macOS Security framework (CMSDecoder)"),
    ]
    if only:
        drivers = [x for x in drivers if x[0] in only]
    results = {}
    for name, drv, version in drivers:
        results[name] = {"version": version, "verdicts": drv(d, cases)}

    names = [n for n, _, _ in drivers]
    lines = ["# Cross-library results", "",
             "Each message has exactly one flaw and a correct RSA signature over what it signs, so **accepts** "
             "means the verifier accepted that flaw. Controls are marked. Generated by `test/crosscheck/run.py`.", ""]
    lines.append("| Case | Lean expects | " + " | ".join(names) + " |")
    lines.append("|---|---|" + "---|" * len(names))
    for c in cases:
        row = []
        for n in names:
            v = results[n]["verdicts"][c["id"]]["ok"]
            row.append("accepts" if v else "refuses")
        exp = "accepts" if c["lean_expected"] else "refuses"
        what = c["what"]
        lines.append(f"| {what} | {exp} | " + " | ".join(
            (f"**{x}**" if x != exp and not c["lean_expected"] else x) for x in row) + " |")
    lines += ["", "Versions:", ""] + [f"- {n}: {results[n]['version']}" for n in names]
    if not only:
        open(os.path.join(HERE, "RESULTS.md"), "w").write("\n".join(lines) + "\n")
        json.dump({"cases": cases, "results": results}, open(os.path.join(HERE, "results.json"), "w"), indent=1)
    wrong = [c["id"] for c in cases if results["Lean"]["verdicts"][c["id"]]["ok"] != c["lean_expected"]]
    print("\n".join(lines))
    if wrong:
        sys.exit(f"Lean disagrees with the expected verdict on: {wrong}")


if __name__ == "__main__":
    main()
