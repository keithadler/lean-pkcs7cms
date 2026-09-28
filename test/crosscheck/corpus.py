"""The one-flaw corpus: CMS SignedData messages built byte by byte, each with exactly one thing wrong and a
correct RSA signature, so that a verifier accepting it has accepted that flaw.

    python test/crosscheck/corpus.py OUT_DIR

Writes OUT_DIR/<id>.der (and <id>.content for detached cases), the signer's and root's certificates, and
OUT_DIR/manifest.json. A new throwaway PKI is made on every run; no private key is ever written to disk.
"""
import datetime
import hashlib
import json
import os
import sys

from cryptography import x509
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import padding, rsa
from cryptography.x509.oid import NameOID

# --- DER -----------------------------------------------------------------------------------------------


def length(n):
    if n < 128:
        return bytes([n])
    b = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([0x80 | len(b)]) + b


def tlv(tag, content):
    return bytes([tag]) + length(len(content)) + content


def seq(*xs):
    return tlv(0x30, b"".join(xs))


def der_set(*xs):
    """A DER SET OF: the elements in DER order (X.690 §11.6)."""
    return tlv(0x31, b"".join(sorted(xs, key=lambda e: e + b"\0" * (max(map(len, xs)) - len(e)))))


def raw_set(*xs):
    return tlv(0x31, b"".join(xs))


def oid(dotted):
    parts = [int(p) for p in dotted.split(".")]
    out = bytearray([parts[0] * 40 + parts[1]])
    for p in parts[2:]:
        chunk = [p & 0x7F]
        p >>= 7
        while p:
            chunk.append(0x80 | (p & 0x7F))
            p >>= 7
        out += bytes(reversed(chunk))
    return tlv(0x06, bytes(out))


def integer(n):
    b = n.to_bytes(max(1, (n.bit_length() + 8) // 8), "big", signed=True)
    return tlv(0x02, b)


def octets(b):
    return tlv(0x04, b)


def utctime(s):
    return tlv(0x17, s.encode())


NULL = b"\x05\x00"
DATA = "1.2.840.113549.1.7.1"
SIGNED_DATA = "1.2.840.113549.1.7.2"
TST_INFO = "1.2.840.113549.1.9.16.1.4"
CONTENT_TYPE = "1.2.840.113549.1.9.3"
MESSAGE_DIGEST = "1.2.840.113549.1.9.4"
SIGNING_TIME = "1.2.840.113549.1.9.5"
COUNTERSIGNATURE = "1.2.840.113549.1.9.6"
SHA256 = "2.16.840.1.101.3.4.2.1"
SHA1 = "1.3.14.3.2.26"
RSA = "1.2.840.113549.1.1.1"
SHA256_RSA = "1.2.840.113549.1.1.11"

# --- A throwaway PKI -----------------------------------------------------------------------------------


def make_pki():
    now = datetime.datetime(2026, 9, 1, tzinfo=datetime.timezone.utc)
    root_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    signer_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    root_name = x509.Name([x509.NameAttribute(NameOID.COUNTRY_NAME, "US"),
                           x509.NameAttribute(NameOID.ORGANIZATION_NAME, "lean-pkcs7cms crosscheck"),
                           x509.NameAttribute(NameOID.COMMON_NAME, "Crosscheck Root")])
    signer_name = x509.Name([x509.NameAttribute(NameOID.COUNTRY_NAME, "US"),
                             x509.NameAttribute(NameOID.ORGANIZATION_NAME, "lean-pkcs7cms crosscheck"),
                             x509.NameAttribute(NameOID.COMMON_NAME, "Crosscheck Signer")])
    root = (x509.CertificateBuilder().subject_name(root_name).issuer_name(root_name)
            .public_key(root_key.public_key()).serial_number(x509.random_serial_number())
            .not_valid_before(now).not_valid_after(now + datetime.timedelta(days=3650))
            .add_extension(x509.BasicConstraints(ca=True, path_length=None), critical=True)
            .add_extension(x509.KeyUsage(False, False, False, False, False, True, True, False, False), critical=True)
            .add_extension(x509.SubjectKeyIdentifier.from_public_key(root_key.public_key()), critical=False)
            .sign(root_key, hashes.SHA256()))
    signer = (x509.CertificateBuilder().subject_name(signer_name).issuer_name(root_name)
              .public_key(signer_key.public_key()).serial_number(x509.random_serial_number())
              .not_valid_before(now).not_valid_after(now + datetime.timedelta(days=3650))
              .add_extension(x509.BasicConstraints(ca=False, path_length=None), critical=True)
              .add_extension(x509.KeyUsage(True, False, False, False, False, False, False, False, False), critical=True)
              .add_extension(x509.SubjectKeyIdentifier.from_public_key(signer_key.public_key()), critical=False)
              .sign(root_key, hashes.SHA256()))
    return root, signer, signer_key


# --- Messages ------------------------------------------------------------------------------------------

CONTENT = b"Hello from Lean's kernel.\n"
OTHER = b"Pay Mallory $10,000.\n"


def attr(type_oid, *values, raw_values=False):
    vals = raw_set(*values) if raw_values else der_set(*values)
    return seq(oid(type_oid), vals)


def build(pki, content=CONTENT, *, attrs="default", order="der", sign_over="as_written",
          e_content_type=DATA, detached=False, sd_version=None, si_version=None, sid="issuerSerial",
          digest_alg=None, sig_alg=None, strip_leading_zero=False, outer_ber=False, trailing=b"",
          certs=None, signers=1):
    root, signer, key = pki
    digest = hashlib.sha256(content).digest()
    if attrs == "default":
        attrs = [attr(CONTENT_TYPE, oid(e_content_type)),
                 attr(SIGNING_TIME, utctime("260915120000Z")),
                 attr(MESSAGE_DIGEST, octets(digest))]
    elif callable(attrs):
        attrs = attrs(digest)

    if attrs is None:
        signed_attrs_field = b""
        to_sign = content
    else:
        written = attrs if order == "as_given" else sorted(attrs, key=lambda e: e + b"\0" * 512)
        if order == "reversed":
            written = list(reversed(sorted(attrs, key=lambda e: e + b"\0" * 512)))
        signed_attrs_field = tlv(0xA0, b"".join(written))
        if sign_over == "as_written":
            to_sign = tlv(0x31, b"".join(written))
        elif sign_over == "sorted":
            to_sign = der_set(*attrs)
        elif sign_over == "a0":
            to_sign = signed_attrs_field
        elif sign_over == "content":
            to_sign = content
        else:
            raise ValueError(sign_over)

    sig = key.sign(to_sign, padding.PKCS1v15(), hashes.SHA256())
    if strip_leading_zero:
        sig = sig.lstrip(b"\0")

    signer_der = signer.public_bytes(serialization.Encoding.DER)
    root_der = root.public_bytes(serialization.Encoding.DER)
    if sid == "issuerSerial":
        issuer = signer.issuer.public_bytes()
        sid_der = seq(issuer, integer(signer.serial_number))
        default_si_version = 1
    else:
        ski = signer.extensions.get_extension_for_class(x509.SubjectKeyIdentifier).value.digest
        sid_der = tlv(0x80, ski)
        default_si_version = 3

    d_alg = digest_alg if digest_alg is not None else seq(oid(SHA256))
    s_alg = sig_alg if sig_alg is not None else seq(oid(RSA), NULL)
    si = seq(integer(si_version if si_version is not None else default_si_version), sid_der, d_alg,
             signed_attrs_field, s_alg, octets(sig))
    encap = seq(oid(e_content_type)) if detached else seq(oid(e_content_type), tlv(0xA0, octets(content)))
    cert_list = [signer_der, root_der] if certs is None else certs(signer_der, root_der)
    certs_field = tlv(0xA0, b"".join(sorted(cert_list))) if cert_list else b""
    default_sd_version = 1 if (e_content_type == DATA and (si_version or default_si_version) == 1) else 3
    sd = seq(integer(sd_version if sd_version is not None else default_sd_version),
             der_set(seq(oid(SHA256))), encap, certs_field, raw_set(*([si] * signers)))
    if outer_ber:
        # BER's indefinite length on the outermost ContentInfo: legal CMS, not DER.
        msg = b"\x30\x80" + oid(SIGNED_DATA) + b"\xa0\x80" + sd + b"\x00\x00" + b"\x00\x00"
    else:
        msg = seq(oid(SIGNED_DATA), tlv(0xA0, sd))
    return msg + trailing


def sign_until_leading_zero(pki):
    """A message whose RSA signature starts with a zero byte, found by varying the signing time."""
    for i in range(20000):
        t = f"2609151{i // 3600 % 10}{i // 60 % 60:02d}{i % 60:02d}Z"
        m = build(pki, attrs=lambda d, t=t: [attr(CONTENT_TYPE, oid(DATA)), attr(SIGNING_TIME, utctime(t)),
                                               attr(MESSAGE_DIGEST, octets(d))])
        if b"\x04\x82\x01\x00\x00" in m:
            return t
    raise RuntimeError("no signature with a leading zero byte")


def cases(pki):
    d = hashlib.sha256(CONTENT).digest()
    ct = attr(CONTENT_TYPE, oid(DATA))
    st = attr(SIGNING_TIME, utctime("260915120000Z"))
    md = attr(MESSAGE_DIGEST, octets(d))
    bad_md = attr(MESSAGE_DIGEST, octets(hashlib.sha256(b"something else").digest()))
    # wrong digests that sort before and after the right one, since DER fixes the order of the attributes
    lo = next(h for i in range(10000) if (h := hashlib.sha256(b"lo%d" % i).digest()) < d)
    hi = next(h for i in range(10000) if (h := hashlib.sha256(b"hi%d" % i).digest()) > d)
    md_lo, md_hi = attr(MESSAGE_DIGEST, octets(lo)), attr(MESSAGE_DIGEST, octets(hi))
    zero_t = sign_until_leading_zero(pki)
    zt = lambda dg: [ct, attr(SIGNING_TIME, utctime(zero_t)), attr(MESSAGE_DIGEST, octets(dg))]  # noqa: E731
    return [
        # id, what, expected Lean verdict, message, detached content
        ("valid-attached", "control: signed attributes, content inside", True, build(pki), None),
        ("valid-detached", "control: detached signature, content given separately", True, build(pki, detached=True), CONTENT),
        ("valid-noattrs", "control: no signed attributes, signature over the content", True, build(pki, attrs=None), None),
        ("valid-ski", "control: signer named by subject key identifier (SignerInfo v3, SignedData v3)", True, build(pki, sid="ski"), None),
        ("valid-sha256rsa", "control: signatureAlgorithm sha256WithRSAEncryption", True, build(pki, sig_alg=seq(oid(SHA256_RSA), NULL)), None),
        ("valid-digest-null", "control: digestAlgorithm SHA-256 with NULL parameters (RFC 5754 asks verifiers to accept)", True, build(pki, digest_alg=seq(oid(SHA256), NULL)), None),
        ("attrs-unsorted-signed-as-written", "signed attributes not in DER order, signature over the bytes as written", False,
         build(pki, attrs=lambda _: [md, st, ct], order="as_given", sign_over="as_written"), None),
        ("attrs-unsorted-signed-sorted", "signed attributes not in DER order, signature over their DER (sorted) encoding", False,
         build(pki, attrs=lambda _: [md, st, ct], order="as_given", sign_over="sorted"), None),
        ("sig-over-a0", "signature over the attributes with the [0] tag 0xA0, not the SET OF tag 0x31", False,
         build(pki, sign_over="a0"), None),
        ("sig-over-content-with-attrs", "signed attributes present, but the signature is over the content", False,
         build(pki, sign_over="content"), None),
        ("md-twice-first-right", "two message-digest attributes, the first one right", False,
         build(pki, attrs=lambda _: [ct, st, md, md_hi]), None),
        ("md-twice-second-right", "two message-digest attributes, the second one right", False,
         build(pki, attrs=lambda _: [ct, st, md_lo, md]), None),
        ("md-two-values", "one message-digest attribute with two values", False,
         build(pki, attrs=lambda dg: [ct, st, attr(MESSAGE_DIGEST, octets(dg), octets(hashlib.sha256(b"x").digest()))]), None),
        ("md-missing", "no message-digest attribute", False, build(pki, attrs=lambda _: [ct, st]), None),
        ("md-wrong", "message-digest of other content", False, build(pki, attrs=lambda _: [ct, st, bad_md]), None),
        ("ct-missing", "no content-type attribute", False, build(pki, attrs=lambda _: [st, md]), None),
        ("ct-twice", "two content-type attributes", False,
         build(pki, attrs=lambda _: [ct, ct, st, md]), None),
        ("md-two-documents", "detached: message-digests of two different documents, checked against the second", False,
         build(pki, detached=True, attrs=lambda _: [ct, st, attr(MESSAGE_DIGEST, octets(hashlib.sha256(OTHER).digest())), md]),
         CONTENT),
        ("noattrs-not-data", "no signed attributes, and the content type is not id-data", False,
         build(pki, attrs=None, e_content_type=TST_INFO), None),
        ("time-twice", "two signing-time attributes", False,
         build(pki, attrs=lambda _: [ct, st, attr(SIGNING_TIME, utctime("260916120000Z")), md]), None),
        ("time-invalid", "signing-time 2026-02-30", False,
         build(pki, attrs=lambda _: [ct, attr(SIGNING_TIME, utctime("260230120000Z")), md]), None),
        ("countersig-signed", "a countersignature among the signed attributes", False,
         build(pki, attrs=lambda _: [ct, st, md, attr(COUNTERSIGNATURE, seq(integer(1)))]), None),
        ("si-version-3-issuer", "SignerInfo version 3 with issuerAndSerialNumber (must be 1)", False,
         build(pki, si_version=3, sd_version=3), None),
        ("sd-version-3", "SignedData version 3 for plain data and v1 signers (must be 1)", False,
         build(pki, sd_version=3), None),
        ("sig-short", "RSA signature one byte shorter than the modulus (its leading zero dropped)", False,
         build(pki, attrs=zt, strip_leading_zero=True), None),
        ("sig-full-length", "control: the same signature with its leading zero kept", True,
         build(pki, attrs=zt), None),
        ("trailing-byte", "a zero byte after the message", False, build(pki, trailing=b"\0"), None),
        ("ber-indefinite", "BER indefinite lengths on the outer ContentInfo (legal CMS, not DER)", False,
         build(pki, outer_ber=True), None),
        ("no-signers", "SignedData with no SignerInfo at all", False, build(pki, signers=0), None),
        ("no-cert", "the signer's certificate is not in the message", False,
         build(pki, certs=lambda s, r: [r]), None),
    ]


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    pki = make_pki()
    root, signer, _ = pki
    open(os.path.join(out, "signer.der"), "wb").write(signer.public_bytes(serialization.Encoding.DER))
    open(os.path.join(out, "root.der"), "wb").write(root.public_bytes(serialization.Encoding.DER))
    manifest = []
    for cid, what, expect, msg, content in cases(pki):
        open(os.path.join(out, cid + ".der"), "wb").write(msg)
        entry = {"id": cid, "what": what, "lean_expected": expect, "msg": cid + ".der"}
        if content is not None:
            open(os.path.join(out, cid + ".content"), "wb").write(content)
            entry["content"] = cid + ".content"
        manifest.append(entry)
    json.dump({"cases": manifest}, open(os.path.join(out, "manifest.json"), "w"), indent=1)
    print(f"wrote {len(manifest)} cases to {out}")


if __name__ == "__main__":
    main()
