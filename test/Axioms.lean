import CMS
/-! Every theorem of the project, with the axioms it rests on. Run: `lake env lean test/Axioms.lean`. -/
open CMS
#print axioms signerOk_iff
#print axioms attrsOkB_iff
#print axioms verify_sound
#print axioms reencode_same
#print axioms digest_signed
#print axioms no_attrs_data
#print axioms decode_der
#print axioms signed_attrs_slice
#print axioms verifyStamp_sound
#print axioms CMS.Real.attached_valid
#print axioms CMS.Real.detached_valid
#print axioms CMS.Real.noattr_valid
#print axioms CMS.Real.detached_tampered
#print axioms CMS.Real.detached_needs_content
#print axioms CMS.Real.digicert_stamps_msg
#print axioms CMS.Real.findings_stamped
