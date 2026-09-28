import CMS.Signed

/-!
# The signed bytes are in the message

With signed attributes, the signature covers the attributes encoded as a `SET OF` (tag `0x31`), while the
message carries them under the tag `[0] IMPLICIT` (`0xA0`) (RFC 5652 §5.4). `signed_attrs_slice` proves the
checker verifies exactly the bytes in the message with that one tag byte changed: not a re-encoding, not a
reordering, nothing added or dropped.
-/

namespace CMS

open X509

/-- A child's encoding is a contiguous part of its parent's. -/
theorem encode_infix_encodeSeq : ∀ {n : Node} {cs : List Node}, n ∈ cs → encode n <:+: encodeSeq cs
  | _, [], h => by simp at h
  | n, c :: cs, h => by
    simp only [encodeSeq]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.prefix_append _ _ |>.isInfix
    · exact (encode_infix_encodeSeq h).trans (List.suffix_append _ _).isInfix

theorem encode_infix_child {n : Node} {t : Nat} {cs : List Node} (h : n ∈ cs) :
    encode n <:+: encode (.cons t cs) := by
  simp only [encode]
  exact (encode_infix_encodeSeq h).trans (List.suffix_append _ _).isInfix

/-- What `mapM` returns comes from what it was given. -/
theorem mem_of_mapM {α β} {f : α → Option β} :
    ∀ {l : List α} {l' : List β} {y : β}, l.mapM f = some l' → y ∈ l' → ∃ x ∈ l, f x = some y
  | [], l', y, h, hy => by simp at h; subst h; simp at hy
  | x :: xs, l', y, h, hy => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
    cases hxs : xs.mapM f with
    | none => simp [hx, hxs] at h
    | some bs =>
    have h' : b :: bs = l' := by simpa [hx, hxs] using h
    subst h'
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, List.mem_cons_self .., hx⟩
    · obtain ⟨z, hz, hfz⟩ := mem_of_mapM hxs hy
      exact ⟨z, List.mem_cons_of_mem _ hz, hfz⟩

theorem Attribute.ofNode_node {n : Node} {a : Attribute} (h : Attribute.ofNode n = some a) : a.node = n := by
  unfold Attribute.ofNode at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h
  · simp at h

theorem mapM_ofNode_node : ∀ {ns : List Node} {as : List Attribute},
    ns.mapM Attribute.ofNode = some as → as.map Attribute.node = ns
  | [], as, h => by simp at h; subst h; rfl
  | n :: ns, as, h => by
    rw [List.mapM_cons] at h
    cases hn : Attribute.ofNode n with
    | none => simp [hn] at h
    | some a =>
    cases hns : ns.mapM Attribute.ofNode with
    | none => simp [hn, hns] at h
    | some as' =>
    have h' : a :: as' = as := by simpa [hn, hns] using h
    subst h'
    simp [Attribute.ofNode_node hn, mapM_ofNode_node hns]

/-- A signer with signed attributes was read from a SignerInfo that carries them under `[0]`. -/
theorem signerInfo_attrs {n : Node} {si : SignerInfo} {as : List Attribute}
    (h : decodeSignerInfo n = some si) (ha : si.signedAttrs = some as) :
    encode (.cons 0xA0 (as.map Attribute.node)) <:+: encode n := by
  unfold decodeSignerInfo at h
  split at h
  · rename_i v sid dAlg ans tail
    split at h
    · rename_i s d attrs a sig _ _ hattrs _
      simp only [Option.some.injEq] at h; subst h
      simp only [Option.some.injEq] at ha; subst ha
      rw [mapM_ofNode_node hattrs]
      exact encode_infix_child (by simp)
    · simp at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; simp at ha
    · simp at h
  · simp at h

/-- The signers were read from the `SET OF SignerInfo` that `decodeSets` found among the children. -/
theorem decodeSets_mem {rest : List Node} {certs sis : List Node} (h : decodeSets rest = some (certs, sis)) :
    Node.cons 0x31 sis ∈ rest := by
  unfold decodeSets at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp
    · simp at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp
    · simp at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp
    · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp
  · simp at h

/-- **The signed bytes are a slice of the message.** For every signer with signed attributes, the message
contains the bytes the signature is checked over, except that their first byte, the `SET OF` tag `0x31`,
is written `0xA0`. -/
theorem signed_attrs_slice {bs : List Nat} {sd : SignedData} {si : SignerInfo} {as : List Attribute}
    (content : List Nat) (hd : decode bs = some sd) (hsi : si ∈ sd.signers) (ha : si.signedAttrs = some as) :
    ∃ pre suf, bs = pre ++ 0xA0 :: (signedBytes si content).tail ++ suf := by
  unfold decode at hd
  split at hd
  · rename_i t sdNode hp
    split at hd
    · unfold decodeSignedData at hd
      split at hd
      · rename_i v algs encap rest
        split at hd
        · rename_i _ _ _ _ tc certsSis _ _ hsets
          split at hd
          · rename_i signers hsigners
            simp only [Option.some.injEq] at hd; subst hd
            obtain ⟨siNode, hmem, hdec⟩ := mem_of_mapM hsigners hsi
            have h1 := signerInfo_attrs hdec ha
            have h2 : encode siNode <:+: encode (.cons 0x31 certsSis) := encode_infix_child hmem
            have h3 : encode (.cons 0x31 certsSis) <:+:
                encode (.cons 0x30 (.prim 0x02 [v] :: .cons 0x31 algs :: encap :: rest)) :=
              encode_infix_child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (decodeSets_mem hsets))))
            have h4 : encode (.cons 0x30 (.prim 0x02 [v] :: .cons 0x31 algs :: encap :: rest)) <:+:
                encode (.cons 0x30 [.prim 0x06 t,
                  .cons 0xA0 [.cons 0x30 (.prim 0x02 [v] :: .cons 0x31 algs :: encap :: rest)]]) :=
              (encode_infix_child (t := 0xA0) (List.mem_singleton_self _)).trans
                (encode_infix_child (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
            obtain ⟨pre, suf, hps⟩ := h1.trans (h2.trans (h3.trans h4))
            refine ⟨pre, suf, ?_⟩
            rw [encode_parse hp, ← hps]
            simp [signedBytes, ha, encode]
          · simp at hd
        · simp at hd
      · simp at hd
    · simp at hd
  · simp at hd

end CMS
