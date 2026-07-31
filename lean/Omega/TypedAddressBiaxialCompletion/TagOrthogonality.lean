import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete failure tags for the typed-address biaxial-completion chapter. -/
inductive TagWitness
  | out
  | cech
  | hard
  deriving DecidableEq

/-- Paper: `prop:typed-address-biaxial-completion-tag-orthogonality`. -/
theorem paper_typed_address_biaxial_completion_tag_orthogonality
    (witness : TagWitness)
    (outTag cechTag hardTag : Prop)
    (outTag_iff : outTag ↔ witness = .out)
    (cechTag_iff : cechTag ↔ witness = .cech)
    (hardTag_iff : hardTag ↔ witness = .hard) :
    (outTag -> ¬ cechTag ∧ ¬ hardTag) ∧
      (cechTag -> ¬ outTag ∧ ¬ hardTag) ∧
      (hardTag -> ¬ outTag ∧ ¬ cechTag) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hout
    refine ⟨?_, ?_⟩
    · intro hcech
      cases (outTag_iff.mp hout).symm.trans (cechTag_iff.mp hcech)
    · intro hhard
      cases (outTag_iff.mp hout).symm.trans (hardTag_iff.mp hhard)
  · intro hcech
    refine ⟨?_, ?_⟩
    · intro hout
      cases (cechTag_iff.mp hcech).symm.trans (outTag_iff.mp hout)
    · intro hhard
      cases (cechTag_iff.mp hcech).symm.trans (hardTag_iff.mp hhard)
  · intro hhard
    refine ⟨?_, ?_⟩
    · intro hout
      cases (hardTag_iff.mp hhard).symm.trans (outTag_iff.mp hout)
    · intro hcech
      cases (hardTag_iff.mp hhard).symm.trans (cechTag_iff.mp hcech)

end Omega.TypedAddressBiaxialCompletion
