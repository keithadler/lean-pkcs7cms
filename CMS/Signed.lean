import X509

/-!
# CMS SignedData (RFC 5652), with SHA-256 and RSA

    ContentInfo ::= SEQUENCE { contentType OBJECT IDENTIFIER, content [0] EXPLICIT ANY }

    SignedData ::= SEQUENCE {
      version CMSVersion,
      digestAlgorithms SET OF DigestAlgorithmIdentifier,
      encapContentInfo EncapsulatedContentInfo,
      certificates [0] IMPLICIT CertificateSet OPTIONAL,
      crls [1] IMPLICIT RevocationInfoChoices OPTIONAL,
      signerInfos SET OF SignerInfo }

    SignerInfo ::= SEQUENCE {
      version CMSVersion,
      sid SignerIdentifier,
      digestAlgorithm DigestAlgorithmIdentifier,
      signedAttrs [0] IMPLICIT SignedAttributes OPTIONAL,
      signatureAlgorithm SignatureAlgorithmIdentifier,
      signature SignatureValue,
      unsignedAttrs [1] IMPLICIT UnsignedAttributes OPTIONAL }

A signer signs one of two things. With no signed attributes, it signs the content itself, and the content
must then be plain data. With signed attributes, it signs the attributes, and two of them tie the signature
to the content: `content-type` names what was signed and `message-digest` holds its hash. The attributes are
signed as a DER `SET OF`, tag `0x31`, although they are written with the tag `[0] IMPLICIT`, `0xA0`
(§5.4). That swap, and the rule that the set is in DER order, are where verifiers go wrong.

The whole message is read with lean-x509's DER parser, so an accepted message has exactly one encoding.
RFC 5652 allows BER outside the signed attributes; this project does not read BER yet.
-/

namespace CMS

open X509

/-! ## Object identifiers -/

namespace Oid
/-- id-data, 1.2.840.113549.1.7.1 -/
def data : X509.Oid := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x07, 0x01]
/-- id-signedData, 1.2.840.113549.1.7.2 -/
def signedData : X509.Oid := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x07, 0x02]
/-- id-contentType, 1.2.840.113549.1.9.3 -/
def contentType : X509.Oid := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x03]
/-- id-messageDigest, 1.2.840.113549.1.9.4 -/
def messageDigest : X509.Oid := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x04]
/-- id-signingTime, 1.2.840.113549.1.9.5 -/
def signingTime : X509.Oid := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x05]
/-- id-countersignature, 1.2.840.113549.1.9.6 -/
def countersignature : X509.Oid := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x06]
/-- id-sha256, 2.16.840.1.101.3.4.2.1 -/
def sha256 : X509.Oid := [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01]
/-- subjectKeyIdentifier, 2.5.29.14 -/
def subjectKeyId : X509.Oid := [0x55, 0x1d, 0x0e]
end Oid

/-! ## The structures -/

/-- One attribute: its type and its values, kept as DER trees. -/
structure Attribute where
  type : X509.Oid
  values : List Node

/-- The tree an attribute was read from. -/
def Attribute.node (a : Attribute) : Node := .cons 0x30 [.prim 0x06 a.type, .cons 0x31 a.values]

/-- The attribute's DER bytes, which is what the DER order of a `SET OF` compares. -/
def Attribute.der (a : Attribute) : List Nat := encode a.node

/-- How a signer names its certificate. -/
inductive Sid where
  | issuerSerial (issuer : X509.Name) (serial : List Nat)
  | keyId (id : List Nat)

structure SignerInfo where
  version : Nat
  sid : Sid
  digestAlg : X509.Oid
  signedAttrs : Option (List Attribute)
  sigAlg : X509.Oid
  /-- The signature's octets. -/
  signature : List Nat

structure SignedData where
  version : Nat
  eContentType : X509.Oid
  /-- The content, when it is carried in the message; `none` for a detached signature. -/
  eContent : Option (List Nat)
  /-- The certificates the message carries, as DER trees. -/
  certs : List Node
  signers : List SignerInfo

/-! ## The DER order of a `SET OF` (X.690 §11.6)

The encodings are compared as octet strings, the shorter one padded at its end with zero octets. -/

def derLe : List Nat → List Nat → Bool
  | [], _ => true
  | a :: as, [] => a == 0 && derLe as []
  | a :: as, b :: bs => a < b || (a == b && derLe as bs)

/-! ## Reading -/

/-- An AlgorithmIdentifier whose parameters are absent or NULL, the two forms RFC 5754 and RFC 4055 ask
verifiers to accept for SHA-256 and RSA. -/
def algOid : Node → Option X509.Oid
  | .cons 0x30 [.prim 0x06 o] => if oidOk o then some o else none
  | .cons 0x30 [.prim 0x06 o, .prim 0x05 []] => if oidOk o then some o else none
  | _ => none

def Attribute.ofNode : Node → Option Attribute
  | .cons 0x30 [.prim 0x06 t, .cons 0x31 vs] => if oidOk t then some ⟨t, vs⟩ else none
  | _ => none

def decodeSid : Node → Option Sid
  | .cons 0x30 [iss, .prim 0x02 sn] =>
    match decodeName iss with
    | some n => if minimalInt sn then some (.issuerSerial n sn) else none
    | none => none
  | .prim 0x80 id => some (.keyId id)
  | _ => none

/-- The algorithm, signature and unsigned attributes that end a SignerInfo. -/
def decodeSignerTail : List Node → Option (X509.Oid × List Nat)
  | [alg, .prim 0x04 sig] => (algOid alg).map (·, sig)
  | [alg, .prim 0x04 sig, .cons 0xA1 _] => (algOid alg).map (·, sig)
  | _ => none

def decodeSignerInfo : Node → Option SignerInfo
  | .cons 0x30 (.prim 0x02 [v] :: sid :: dAlg :: .cons 0xA0 as :: tail) =>
    match decodeSid sid, algOid dAlg, as.mapM Attribute.ofNode, decodeSignerTail tail with
    | some s, some d, some attrs, some (a, sig) => some ⟨v, s, d, some attrs, a, sig⟩
    | _, _, _, _ => none
  | .cons 0x30 (.prim 0x02 [v] :: sid :: dAlg :: tail) =>
    match decodeSid sid, algOid dAlg, decodeSignerTail tail with
    | some s, some d, some (a, sig) => some ⟨v, s, d, none, a, sig⟩
    | _, _, _ => none
  | _ => none

/-- EncapsulatedContentInfo: the content type, and the content unless the signature is detached. -/
def decodeEncap : Node → Option (X509.Oid × Option (List Nat))
  | .cons 0x30 [.prim 0x06 t] => if oidOk t then some (t, none) else none
  | .cons 0x30 [.prim 0x06 t, .cons 0xA0 [.prim 0x04 c]] => if oidOk t then some (t, some c) else none
  | _ => none

/-- What follows the encapsulated content: optional certificates, optional revocation information (not
read), and the signers. Only plain certificates (a `SEQUENCE`) are accepted, and only plain CRLs. -/
def decodeSets : List Node → Option (List Node × List Node)
  | [.cons 0xA0 cs, .cons 0xA1 rs, .cons 0x31 sis] =>
    if cs.all (·.tag == 0x30) && rs.all (·.tag == 0x30) then some (cs, sis) else none
  | [.cons 0xA0 cs, .cons 0x31 sis] => if cs.all (·.tag == 0x30) then some (cs, sis) else none
  | [.cons 0xA1 rs, .cons 0x31 sis] => if rs.all (·.tag == 0x30) then some ([], sis) else none
  | [.cons 0x31 sis] => some ([], sis)
  | _ => none

def decodeSignedData : Node → Option SignedData
  | .cons 0x30 (.prim 0x02 [v] :: .cons 0x31 algs :: encap :: rest) =>
    match algs.mapM algOid, decodeEncap encap, decodeSets rest with
    | some _, some (t, c), some (certs, sis) =>
      match sis.mapM decodeSignerInfo with
      | some signers => some ⟨v, t, c, certs, signers⟩
      | none => none
    | _, _, _ => none
  | _ => none

/-- Reads a whole message: a DER `ContentInfo` holding `SignedData`, with nothing after it. -/
def decode (bs : List Nat) : Option SignedData :=
  match parse bs with
  | some (.cons 0x30 [.prim 0x06 t, .cons 0xA0 [sd]]) => if t = Oid.signedData then decodeSignedData sd else none
  | _ => none

/-! ## What a signer signs -/

/-- The bytes the signature covers: the content itself, or the signed attributes re-tagged as a DER
`SET OF` (§5.4). -/
def signedBytes (si : SignerInfo) (content : List Nat) : List Nat :=
  match si.signedAttrs with
  | none => content
  | some as => encode (.cons 0x31 (as.map Attribute.node))

/-- The values of every attribute of type `t`, one list per attribute, each value as its DER bytes. -/
def valuesOf (as : List Attribute) (t : X509.Oid) : List (List (List Nat)) :=
  (as.filter (·.type == t)).map (·.values.map encode)

/-- `signing-time`, if present, appears once, with one value, a time RFC 5280 would accept (§11.3). -/
def signingTimeOk (as : List Attribute) : Bool :=
  match ((as.filter (·.type == Oid.signingTime)).map (·.values) : List (List Node)) with
  | [] => true
  | [[.prim t c]] => (decodeTime t c).isSome
  | _ => false

/-- The signer's certificate is the one it names: by issuer and serial number, or by subject key
identifier. -/
def identifies (sid : Sid) (c : Cert) : Bool :=
  match sid with
  | .issuerSerial iss sn => c.issuer == iss && c.serial == sn
  | .keyId id =>
    match c.exts.find? (·.oid == Oid.subjectKeyId) with
    | some e => match parse e.value with
      | some (.prim 0x04 kid) => kid == id
      | _ => false
    | none => false

/-! ## The specification -/

/-- What RFC 5652 requires of the signed attributes of content `content` of type `ty`. -/
structure AttrsOk (as : List Attribute) (ty : X509.Oid) (content : List Nat) : Prop where
  /-- In DER order, so the bytes written are the bytes signed (§5.3, X.690 §11.6). -/
  der_order : (as.map Attribute.der).Pairwise (fun a b => derLe a b = true)
  /-- One `content-type`, with one value, the content's type (§11.1). -/
  content_type : valuesOf as Oid.contentType = [[encode (.prim 0x06 ty)]]
  /-- One `message-digest`, with one value, the SHA-256 of the content (§11.2). -/
  message_digest : valuesOf as Oid.messageDigest = [[encode (.prim 0x04 (Sha256.hash content))]]
  /-- At most one `signing-time`, with one value, a valid time (§11.3). -/
  signing_time : signingTimeOk as = true
  /-- A countersignature is never a signed attribute (§11.4). -/
  no_countersignature : valuesOf as Oid.countersignature = []

/-- `si` validly signs `content`, of type `ty`, with the key in certificate `c`. -/
structure SignerValid (ty : X509.Oid) (content : List Nat) (si : SignerInfo) (c : Cert) : Prop where
  /-- Version 1 names the certificate by issuer and serial, version 3 by key identifier (§5.3). -/
  version : si.version = (match si.sid with | .issuerSerial .. => 1 | .keyId _ => 3)
  identifies : identifies si.sid c = true
  /-- SHA-256, and RSA PKCS #1 v1.5 named either way RFC 3370 and RFC 4055 allow. -/
  digest : si.digestAlg = Oid.sha256
  sig_alg : si.sigAlg = X509.Oid.rsaEncryption ∨ si.sigAlg = X509.Oid.sha256WithRSA
  /-- Without signed attributes the content must be plain data (§5.3); with them, the rules above. -/
  attrs : match si.signedAttrs with
    | none => ty = Oid.data
    | some as => AttrsOk as ty content
  /-- An RSA key, a signature exactly as long as the modulus (RFC 8017 §8.2.2), and the signature
  verifies over the signed bytes. -/
  signature : ∃ k, c.key = .rsa k ∧ si.signature.length = Rsa.byteLen k.n ∧
    Rsa.verify k (signedBytes si content) (ofBE si.signature) = true

/-! ## The checker -/

def attrsOkB (as : List Attribute) (ty : X509.Oid) (content : List Nat) : Bool :=
  decide ((as.map Attribute.der).Pairwise (fun a b => derLe a b = true)) &&
  valuesOf as Oid.contentType == [[encode (.prim 0x06 ty)]] &&
  valuesOf as Oid.messageDigest == [[encode (.prim 0x04 (Sha256.hash content))]] &&
  signingTimeOk as &&
  valuesOf as Oid.countersignature == []

def signerOk (ty : X509.Oid) (content : List Nat) (si : SignerInfo) (c : Cert) : Bool :=
  si.version == (match si.sid with | .issuerSerial .. => 1 | .keyId _ => 3) &&
  identifies si.sid c &&
  si.digestAlg == Oid.sha256 &&
  (si.sigAlg == X509.Oid.rsaEncryption || si.sigAlg == X509.Oid.sha256WithRSA) &&
  (match si.signedAttrs with
    | none => ty == Oid.data
    | some as => attrsOkB as ty content) &&
  (match c.key with
    | .rsa k => si.signature.length == Rsa.byteLen k.n && Rsa.verify k (signedBytes si content) (ofBE si.signature)
    | .other _ => false)

theorem attrsOkB_iff (as : List Attribute) (ty : X509.Oid) (content : List Nat) :
    attrsOkB as ty content = true ↔ AttrsOk as ty content := by
  simp only [attrsOkB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

/-- The checker is the specification, no more and no less. -/
theorem signerOk_iff (ty : X509.Oid) (content : List Nat) (si : SignerInfo) (c : Cert) :
    signerOk ty content si c = true ↔ SignerValid ty content si c := by
  simp only [signerOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨hv, hid⟩, hd⟩, hs⟩, ha⟩, hk⟩
    refine ⟨hv, hid, hd, hs, ?_, ?_⟩
    · cases h : si.signedAttrs with
      | none => simpa [h] using ha
      | some as => simp only [h] at ha; exact (attrsOkB_iff _ _ _).1 ha
    · cases hc : c.key with
      | rsa k =>
        simp only [hc, Bool.and_eq_true, beq_iff_eq] at hk
        exact ⟨k, rfl, hk.1, hk.2⟩
      | other _ => simp [hc] at hk
  · rintro ⟨hv, hid, hd, hs, ha, k, hk, hl, hsig⟩
    refine ⟨⟨⟨⟨⟨hv, hid⟩, hd⟩, hs⟩, ?_⟩, ?_⟩
    · cases h : si.signedAttrs with
      | none => simp only [h] at ha; simp [ha]
      | some as => simp only [h] at ha; exact (attrsOkB_iff _ _ _).2 ha
    · simp [hk, hl, hsig]

/-- The first common name in a distinguished name, for reporting who signed. -/
def commonName (n : X509.Name) : Option (List Nat) :=
  (n.flatten.find? (·.1 == X509.Oid.commonName)).map fun (_, _, v) => v

/-! ## Messages -/

/-- The certificates a verifier can use: the ones the message carries that lean-x509 reads, then any
the caller supplies. -/
def certsOf (sd : SignedData) (extra : List Cert) : List Cert :=
  sd.certs.filterMap (fun n => decodeCert (encode n)) ++ extra

/-- The first usable certificate that makes the signer valid. -/
def findSigner (ty : X509.Oid) (content : List Nat) (certs : List Cert) (si : SignerInfo) : Option Cert :=
  certs.find? (signerOk ty content si)

/-- The content a verifier checks: the one in the message, or the detached one it is given. A message
that carries content and is also given detached content is refused, so there is never a question of
which was signed. -/
def contentOf (sd : SignedData) (detached : Option (List Nat)) : Option (List Nat) :=
  match sd.eContent, detached with
  | some c, none => some c
  | none, some c => some c
  | _, _ => none

/-- SignedData's own version (§5.1), for messages holding only plain certificates and CRLs: 3 when the
content is not plain data or any signer is version 3, otherwise 1. -/
def expectedVersion (sd : SignedData) : Nat :=
  if sd.eContentType = Oid.data && sd.signers.all (·.version == 1) then 1 else 3

/-- Verifies a whole message: every signer must be valid, and there must be at least one. On success,
the certificate of each signer, in order. -/
def verify (bs : List Nat) (detached : Option (List Nat)) (extra : List Cert) : Option (List Cert) :=
  match decode bs with
  | none => none
  | some sd =>
    match contentOf sd detached with
    | none => none
    | some content =>
      if sd.version = expectedVersion sd && !sd.signers.isEmpty then
        sd.signers.mapM (findSigner sd.eContentType content (certsOf sd extra))
      else none

/-- What a verified message guarantees: it decodes, its version is right, and each signer is valid with a
certificate the message carries or the caller supplied. -/
structure MessageValid (bs : List Nat) (detached : Option (List Nat)) (extra : List Cert) (sd : SignedData)
    (content : List Nat) (signers : List Cert) : Prop where
  decodes : decode bs = some sd
  has_content : contentOf sd detached = some content
  version : sd.version = expectedVersion sd
  nonempty : sd.signers ≠ []
  lengths : signers.length = sd.signers.length
  each : ∀ i (h₁ : i < sd.signers.length) (h₂ : i < signers.length),
    signers[i] ∈ certsOf sd extra ∧ SignerValid sd.eContentType content sd.signers[i] signers[i]

theorem findSigner_spec {ty content certs si c} (h : findSigner ty content certs si = some c) :
    c ∈ certs ∧ SignerValid ty content si c := by
  unfold findSigner at h
  exact ⟨List.mem_of_find?_eq_some h, (signerOk_iff _ _ _ _).1 (List.find?_some h)⟩

theorem mapM_findSigner {ty content certs} :
    ∀ (sis : List SignerInfo) (cs : List Cert), sis.mapM (findSigner ty content certs) = some cs →
      cs.length = sis.length ∧ ∀ i (h₁ : i < sis.length) (h₂ : i < cs.length),
        cs[i] ∈ certs ∧ SignerValid ty content sis[i] cs[i]
  | [], cs, h => by simp at h; subst h; simp
  | si :: sis, cs, h => by
    rw [List.mapM_cons] at h
    cases hc : findSigner ty content certs si with
    | none => simp [hc] at h
    | some c =>
    cases hcs' : sis.mapM (findSigner ty content certs) with
    | none => simp [hc, hcs'] at h
    | some cs' =>
    have h' : c :: cs' = cs := by simpa [hc, hcs'] using h
    subst h'
    obtain ⟨hlen, hall⟩ := mapM_findSigner sis cs' hcs'
    refine ⟨by simp [hlen], fun i h₁ h₂ => ?_⟩
    cases i with
    | zero => exact findSigner_spec hc
    | succ i => exact hall i (by simpa using h₁) (by simpa using h₂)

/-- A message `verify` accepts meets `MessageValid`. -/
theorem verify_sound {bs detached extra signers} (h : verify bs detached extra = some signers) :
    ∃ sd content, MessageValid bs detached extra sd content signers := by
  unfold verify at h
  split at h
  · simp at h
  · rename_i sd hsd
    split at h
    · simp at h
    · rename_i content hc
      split at h
      · rename_i hv
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hv
        obtain ⟨hlen, hall⟩ := mapM_findSigner _ _ h
        exact ⟨sd, content, hsd, hc, hv.1, hv.2, hlen, hall⟩
      · simp at h

/-! ## What the checks rule out -/

/-- The signed attributes are in DER order, so a verifier that re-encodes them (sorting the set, as a DER
encoder must) signs over the same bytes as one that uses them as written. The two kinds of verifier cannot
disagree about an accepted message. -/
theorem reencode_same {as : List Attribute} {ty content} (h : AttrsOk as ty content) :
    (as.map Attribute.der).mergeSort derLe = as.map Attribute.der :=
  List.mergeSort_of_pairwise h.der_order

/-- With signed attributes, the content's SHA-256 is among the signed bytes: the signature covers the
content through the `message-digest` attribute. -/
theorem digest_signed {ty content si c as} (hv : SignerValid ty content si c) (ha : si.signedAttrs = some as) :
    ∃ a ∈ as, a.type = Oid.messageDigest ∧
      a.values.map encode = [encode (.prim 0x04 (Sha256.hash content))] := by
  have hattrs := hv.attrs
  simp only [ha] at hattrs
  have hmd := hattrs.message_digest
  unfold valuesOf at hmd
  cases hf : as.filter (·.type == Oid.messageDigest) with
  | nil => simp [hf] at hmd
  | cons a rest =>
    cases rest with
    | cons _ _ => simp [hf] at hmd
    | nil =>
      simp only [hf, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmd
      have hmem : a ∈ as.filter (·.type == Oid.messageDigest) := by rw [hf]; simp
      simp only [List.mem_filter, beq_iff_eq] at hmem
      exact ⟨a, hmem.1, hmem.2, hmd⟩

/-- Without signed attributes the content is plain data, and the signature is over the content itself. -/
theorem no_attrs_data {ty content si c} (hv : SignerValid ty content si c) (ha : si.signedAttrs = none) :
    ty = Oid.data ∧ signedBytes si content = content := by
  have hattrs := hv.attrs
  simp only [ha] at hattrs
  exact ⟨hattrs, by simp [signedBytes, ha]⟩

/-- An accepted message is DER: it is exactly the encoding of the tree it was read as, with nothing before
or after it, so no second byte string reads as the same message (lean-x509's `der_unique`). -/
theorem decode_der {bs : List Nat} {sd : SignedData} (h : decode bs = some sd) :
    ∃ x, parse bs = some x ∧ bs = encode x := by
  unfold decode at h
  split at h
  · rename_i t n hp
    exact ⟨_, hp, encode_parse hp⟩
  · simp at h

end CMS
