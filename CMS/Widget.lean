import CMS.Real
import X509.Widget
import Lean.Widget.UserWidget

/-!
# The widget

A picture of one verification, the timestamp token DigiCert issued for the sealed findings
(`CMS.Real.findings_stamped`). Everything the widget shows is computed here, by Lean, from the definitions
the theorems are about: the DER tree `parse` returns, the fields `decode` reads, each rule of
`SignerValid`, the block `sᵉ mod n` that RSA reveals, and the `TSTInfo` that was signed. The JavaScript only
lays it out.

Open this file in Lean Studio (or VS Code), put the cursor on the `#widget` line at the end, and look at the
Infoview.
-/

namespace CMS.Widget

open Lean X509 CMS

def hex (bs : List Nat) : String := String.join (bs.map X509.Widget.hexByte)

/-- `n` as exactly `k` big-endian bytes. -/
def bytesK (k n : Nat) : List Nat := X509.Data.bytesOf n k []

def check (ok : Bool) (rule source thm : String) : Json :=
  Json.mkObj [("ok", toJson ok), ("rule", toJson rule), ("source", toJson source), ("thm", toJson thm)]

def theorems : List (String × String) := [
  ("signerOk_iff", "The checker accepts a signer exactly when the specification SignerValid holds."),
  ("signed_attrs_slice", "The signed bytes are the message's own bytes, with the tag 0xA0 changed to 0x31."),
  ("reencode_same", "Sorting the signed attributes changes nothing, so no two verifiers can disagree."),
  ("digest_signed", "The content's SHA-256 is inside the signed bytes."),
  ("verify_iff", "RSA accepts exactly when sᵉ mod n is the one correctly padded block (lean-x509)."),
  ("decode_der", "The message is DER: one encoding, nothing before or after it."),
  ("verifyStamp_sound", "What the token says is the TSTInfo that was signed."),
  ("findings_stamped", "This token verifies, and dates the findings' SHA-256 to 2026-09-28 22:03:34 UTC.")]

def widgetProps : Json := Id.run do
  let bs := Data.findings
  let some sd := decode bs | return Json.null
  let some si := sd.signers.head? | return Json.null
  let content := sd.eContent.getD []
  let certs := certsOf sd []
  let some c := findSigner sd.eContentType content certs si | return Json.null
  let some (stamp, _) := verifyStamp bs [] | return Json.null
  let .rsa k := c.key | return Json.null
  let kb := Rsa.byteLen k.n
  let signed := signedBytes si content
  let s := ofBE si.signature
  let block := Rsa.powMod k.n (Nat.log2 k.e + 1) s k.e
  let expected := Rsa.expected kb signed
  let as := si.signedAttrs.getD []
  let attrs := as.map fun a =>
    Json.mkObj [("oid", toJson (hex a.type)), ("values", toJson (a.values.map fun v => hex (encode v)))]
  let written := encode (.cons 0xA0 (as.map Attribute.node))
  let ok := attrsOkB as sd.eContentType content
  let checks := [
    check true "The message is DER, with nothing before or after it" "X.690" "decode_der",
    check (sd.version == expectedVersion sd) s!"SignedData version {sd.version}" "RFC 5652 §5.1" "verify_sound",
    check (si.version == (match si.sid with | .issuerSerial .. => 1 | .keyId _ => 3)) s!"SignerInfo version {si.version}, named by issuer and serial" "§5.3" "signerOk_iff",
    check (identifies si.sid c) "The certificate is the one the signer names" "§5.3" "signerOk_iff",
    check (si.digestAlg == CMS.Oid.sha256) "Digest SHA-256" "RFC 5754" "signerOk_iff",
    check (si.sigAlg == X509.Oid.rsaEncryption || si.sigAlg == X509.Oid.sha256WithRSA) "RSA PKCS #1 v1.5" "RFC 3370, 4055" "signerOk_iff",
    check (decide ((as.map Attribute.der).Pairwise (fun a b => derLe a b = true))) "Signed attributes in DER order" "§5.3, X.690 §11.6" "reencode_same",
    check (valuesOf as CMS.Oid.contentType == [[encode (.prim 0x06 sd.eContentType)]]) "One content-type, equal to the content's type" "§11.1" "signerOk_iff",
    check (valuesOf as CMS.Oid.messageDigest == [[encode (.prim 0x04 (Sha256.hash content))]]) "One message-digest, equal to SHA-256 of the content" "§11.2" "digest_signed",
    check (signingTimeOk as) "At most one signing-time, a valid time" "§11.3" "signerOk_iff",
    check (valuesOf as CMS.Oid.countersignature == []) "No countersignature among signed attributes" "§11.4" "signerOk_iff",
    check (si.signature.length == kb) s!"Signature exactly {kb} bytes, as the modulus" "RFC 8017 §8.2.2" "verify_iff",
    check (Rsa.verify k signed s) "sᵉ mod n is the one correctly padded block" "RFC 8017 §8.2.2" "verify_iff"]
  return Json.mkObj [
    ("title", toJson "DigiCert's timestamp on the sealed findings"),
    ("size", toJson bs.length),
    ("tree", match parse bs with | some t => X509.Widget.nodeJson t | none => Json.null),
    ("valid", toJson ((verify bs none []).isSome && ok)),
    ("signer", toJson (X509.Widget.cn c.subject)),
    ("issuer", toJson (X509.Widget.cn c.issuer)),
    ("bits", toJson (Nat.log2 k.n + 1)), ("e", toJson k.e),
    ("certs", toJson (certs.map fun (x : Cert) => X509.Widget.cn x.subject)),
    ("eContentType", toJson (hex sd.eContentType)),
    ("contentLen", toJson content.length),
    ("contentHash", toJson (hex (Sha256.hash content))),
    ("attrs", Json.arr attrs.toArray),
    ("written", toJson (hex (written.take 8))),
    ("signed", toJson (hex (signed.take 8))),
    ("signedLen", toJson signed.length),
    ("block", toJson (hex (bytesK kb block))),
    ("expected", toJson (hex (bytesK kb expected))),
    ("stampHash", toJson (hex stamp.hashed)),
    ("stampTime", toJson stamp.time),
    ("checks", Json.arr checks.toArray),
    ("theorems", Json.arr (theorems.map fun (a, b) => Json.arr #[toJson a, toJson b]).toArray)]

@[widget_module]
def CMSWidget : Widget.Module where
  javascript := include_str ".." / "widget" / "CMS.js"

end CMS.Widget

open CMS.Widget in
#widget CMSWidget with widgetProps
