import CMS.Signed

/-!
# Timestamp tokens (RFC 3161)

A timestamp token is a CMS `SignedData` whose content is a `TSTInfo`: the authority's statement that a
given hash existed at a given time.

    TSTInfo ::= SEQUENCE {
      version INTEGER { v1(1) },
      policy TSAPolicyId,
      messageImprint MessageImprint,
      serialNumber INTEGER,
      genTime GeneralizedTime,
      accuracy Accuracy OPTIONAL,
      ordering BOOLEAN DEFAULT FALSE,
      nonce INTEGER OPTIONAL,
      tsa [0] GeneralName OPTIONAL,
      extensions [1] IMPLICIT Extensions OPTIONAL }

    MessageImprint ::= SEQUENCE { hashAlgorithm AlgorithmIdentifier, hashedMessage OCTET STRING }
-/

namespace CMS

open X509

namespace Oid
/-- id-ct-TSTInfo, 1.2.840.113549.1.9.16.1.4 -/
def tstInfo : X509.Oid := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x10, 0x01, 0x04]
end Oid

/-- What a timestamp says: the hash it stamps, and when, as `YYYYMMDDHHMMSS` in UTC. -/
structure Stamp where
  hashAlg : X509.Oid
  hashed : List Nat
  time : Nat
  deriving Repr, DecidableEq

/-- RFC 3161's GeneralizedTime: `YYYYMMDDhhmmss`, then optionally a dot and fractional digits with no
trailing zero, then `Z` (§2.4.2). The fraction is checked and dropped. -/
def decodeGenTime (c : List Nat) : Option Nat :=
  if c.length < 15 || c.getLast? != some 90 then none
  else
    let frac := (c.drop 14).dropLast
    let fracOk := frac == [] ||
      (frac.head? == some 46 && frac.length ≥ 2 && (digits (frac.drop 1)).isSome && frac.getLast? != some 48)
    if !fracOk then none
    else do
      let y ← digits (c.take 4)
      let rest ← digits ((c.drop 4).take 10)
      stamp y rest

def decodeTstInfo (bs : List Nat) : Option Stamp :=
  match parse bs with
  | some (.cons 0x30 (.prim 0x02 [1] :: .prim 0x06 policy :: .cons 0x30 [alg, .prim 0x04 h] ::
      .prim 0x02 _ :: .prim 0x18 gt :: _)) =>
    if !oidOk policy then none
    else match algOid alg, decodeGenTime gt with
      | some a, some t => some ⟨a, h, t⟩
      | _, _ => none
  | _ => none

/-- Verifies a timestamp token and reads what it says: the token must verify as CMS, hold a `TSTInfo`, and
stamp a SHA-256 hash. -/
def verifyStamp (token : List Nat) (extra : List Cert) : Option (Stamp × List Cert) :=
  match verify token none extra, decode token with
  | some signers, some sd =>
    if sd.eContentType = Oid.tstInfo then
      match sd.eContent with
      | some c => (decodeTstInfo c).bind fun s => if s.hashAlg = Oid.sha256 then some (s, signers) else none
      | none => none
    else none
  | _, _ => none

/-- A token `verifyStamp` accepts is a valid CMS message whose signed content is the `TSTInfo` it read. -/
theorem verifyStamp_sound {token extra s signers} (h : verifyStamp token extra = some (s, signers)) :
    (∃ sd content, MessageValid token none extra sd content signers ∧ sd.eContentType = Oid.tstInfo ∧
      decodeTstInfo content = some s) ∧ s.hashAlg = Oid.sha256 := by
  unfold verifyStamp at h
  split at h
  · rename_i signers' sd hv hd
    split at h
    · rename_i hty
      split at h
      · rename_i c hc
        cases hs : decodeTstInfo c with
        | none => simp [hs] at h
        | some s' =>
          simp only [hs, Option.bind_some] at h
          split at h
          · rename_i halg
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨sd', content, hmv⟩ := verify_sound hv
            have hsd : sd' = sd := by
              have := hmv.decodes; rw [hd] at this; exact (Option.some.inj this).symm
            subst hsd
            have hcontent : content = c := by
              have := hmv.has_content; simp [contentOf, hc] at this; exact this.symm
            subst hcontent
            exact ⟨⟨sd', content, hmv, hty, hs⟩, halg⟩
          · simp at h
      · simp at h
    · simp at h
  · simp at h

end CMS
