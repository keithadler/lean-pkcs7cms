import CMS.Timestamp
import CMS.Data

/-!
# Real messages, checked by Lean's kernel

Every theorem here is proved by `decide +kernel`: Lean's kernel parses the DER, hashes the content and the
signed attributes with SHA-256, and raises each RSA signature to the public exponent, with no compiled code
involved.
-/

namespace CMS.Real

open CMS X509

/-- The attached message verifies, and its one signer is the test signer. -/
theorem attached_valid :
    (verify Data.attached none []).map (·.map fun (c : Cert) => commonName c.subject) =
      some [some (Sha256.ascii "Test Signer")] := by decide +kernel

/-- The detached signature verifies over the content it is given. -/
theorem detached_valid : (verify Data.detached (some Data.msg) []).isSome = true := by decide +kernel

/-- A signature with no signed attributes verifies over the content itself. -/
theorem noattr_valid : (verify Data.noattr none []).isSome = true := by decide +kernel

/-- Change the last byte of the content (the newline becomes `!`) and the detached signature fails. -/
theorem detached_tampered :
    (verify Data.detached (some (Data.msg.dropLast ++ [0x21])) []).isNone = true := by decide +kernel

/-- A detached signature with no content to check is not valid. -/
theorem detached_needs_content : (verify Data.detached none []).isNone = true := by decide +kernel

/-- DigiCert's timestamp token verifies (RSA-4096, SHA-256), signed by DigiCert's timestamp responder, and
says that the SHA-256 of `msg` existed at 2026-09-28 21:43:25 UTC. -/
theorem digicert_stamps_msg :
    (verifyStamp Data.digicert []).map (fun (s, cs) => (s.hashed, s.time, cs.map fun (c : Cert) => commonName c.subject)) =
      some (Sha256.hash Data.msg, 20260928214325,
        [some (Sha256.ascii "DigiCert SHA256 RSA4096 Timestamp Responder 2026 1")]) := by decide +kernel

/-- DigiCert's timestamp token for the sealed findings file of 2026-09-28
(keithadler/lean-pkcs7cms-disclosure, `commitment/findings-2026-09-28.txt`) verifies, and says its SHA-256 existed
at 2026-09-28 22:03:34 UTC. -/
theorem findings_stamped :
    (verifyStamp Data.findings []).map (fun (s, cs) => (s.hashed, s.time, cs.map fun (c : Cert) => commonName c.subject)) =
      some (X509.Data.bytesOf 0x06cce00a1e2d4c2b8cc88708c038ccf5502ec230f49171b6878e0711ae35916f 32 [], 20260928220334,
        [some (Sha256.ascii "DigiCert SHA256 RSA4096 Timestamp Responder 2026 1")]) := by decide +kernel

end CMS.Real
