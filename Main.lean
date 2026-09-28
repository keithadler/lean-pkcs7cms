import CMS
import Lean.Data.Json

/-!
`cms`: the same code the proofs are about, compiled, for the tests in `test/`.

    cms verify MSG.der [--content FILE] [--cert CERT.der ...]
        prints one JSON line: {"valid":true,"signers":[subject, ...]} or {"valid":false,"reason":...}
-/

open CMS X509 Lean

def readBytes (path : String) : IO (List Nat) := do
  pure ((← IO.FS.readBinFile path).toList.map (·.toNat))

def str (bs : List Nat) : String := String.ofList (bs.map Char.ofNat)

def cn (n : X509.Name) : String :=
  match n.flatten.find? (·.1 == X509.Oid.commonName) with
  | some (_, _, v) => str v
  | none => "(no CN)"

/-- The first rule a signer breaks against a certificate, for the report. The verdict itself comes from
`verify`; this only says why. -/
def whyNot (ty : X509.Oid) (content : List Nat) (si : SignerInfo) (c : Cert) : String :=
  if si.version != (match si.sid with | .issuerSerial .. => 1 | .keyId _ => 3) then "signer version"
  else if !identifies si.sid c then "certificate does not match the signer identifier"
  else if si.digestAlg != CMS.Oid.sha256 then "digest algorithm is not SHA-256"
  else if !(si.sigAlg == X509.Oid.rsaEncryption || si.sigAlg == X509.Oid.sha256WithRSA) then "signature algorithm"
  else
    let attrs := match si.signedAttrs with
      | none => if ty == CMS.Oid.data then none else some "no signed attributes, but the content is not id-data"
      | some as =>
        if !decide ((as.map Attribute.der).Pairwise (fun a b => derLe a b = true)) then some "signed attributes not in DER order"
        else if valuesOf as CMS.Oid.contentType != [[encode (.prim 0x06 ty)]] then some "content-type attribute"
        else if valuesOf as CMS.Oid.messageDigest != [[encode (.prim 0x04 (Sha256.hash content))]] then some "message-digest attribute"
        else if !signingTimeOk as then some "signing-time attribute"
        else if valuesOf as CMS.Oid.countersignature != [] then some "countersignature among signed attributes"
        else none
    match attrs with
    | some w => w
    | none =>
      match c.key with
      | .other _ => "not an RSA key"
      | .rsa k =>
        if si.signature.length != Rsa.byteLen k.n then "signature length is not the modulus length"
        else "signature does not verify"

def verifyCmd (args : List String) : IO UInt32 := do
  let rec opts : List String → Option String → List String → Option String × List String
    | "--content" :: f :: rest, _, cs => opts rest (some f) cs
    | "--cert" :: f :: rest, c, cs => opts rest c (cs ++ [f])
    | _ :: rest, c, cs => opts rest c cs
    | [], c, cs => (c, cs)
  match args with
  | msgPath :: rest =>
    let (contentPath, certPaths) := opts rest none []
    let bs ← readBytes msgPath
    let detached ← match contentPath with
      | some p => pure (some (← readBytes p))
      | none => pure none
    let mut extra : List Cert := []
    for p in certPaths do
      if let some c := decodeCert (← readBytes p) then extra := extra ++ [c]
    let out := match verify bs detached extra with
      | some cs => Json.mkObj [("valid", true), ("signers", toJson (cs.map fun (c : Cert) => cn c.subject))]
      | none =>
        let reason := match decode bs with
          | none => "not a DER SignedData message this reader accepts"
          | some sd =>
            match contentOf sd detached with
            | none => "no content, or content both attached and given"
            | some content =>
              if sd.signers.isEmpty then "no signers"
              else if sd.version != expectedVersion sd then s!"SignedData version {sd.version}, expected {expectedVersion sd}"
              else
                let certs := certsOf sd extra
                match sd.signers.find? (fun si => (findSigner sd.eContentType content certs si).isNone) with
                | none => "invalid"
                | some si =>
                  match certs.find? (fun c => identifies si.sid c) with
                  | none => "no certificate matches the signer identifier"
                  | some c => whyNot sd.eContentType content si c
        Json.mkObj [("valid", false), ("reason", toJson reason)]
    IO.println out.compress
    pure 0
  | [] => IO.eprintln "usage: cms verify MSG.der [--content FILE] [--cert CERT.der ...]"; pure 2

def main (args : List String) : IO UInt32 :=
  match args with
  | "verify" :: rest => verifyCmd rest
  | _ => do IO.eprintln "usage: cms verify MSG.der [--content FILE] [--cert CERT.der ...]"; pure 2
