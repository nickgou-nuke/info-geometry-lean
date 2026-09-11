import InfoGeometry.Topology.D4StarQuotientCompactOpen
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! The two quotient classes are clopen, via the two Boolean labels. -/

theorem centreClass_eq_preimage :
    centreClass = quotientToBool ⁻¹' ({true} : Set Bool) := by
  ext q
  induction q using Quotient.inductionOn with
  | _ v =>
      cases v with
      | inl c =>
          change (starQuotientMap (outerVertex c) =
              starQuotientMap centralVertex) ↔ (false = true)
          constructor
          · intro h
            exact False.elim ((centre_not_outer_class c) h.symm)
          · intro h
            cases h
      | inr u =>
          cases u
          change (starQuotientMap centralVertex =
              starQuotientMap centralVertex) ↔ (true = true)
          constructor <;> intro _ <;> rfl

theorem outerClass_eq_preimage :
    outerClass = quotientToBool ⁻¹' ({false} : Set Bool) := by
  ext q
  induction q using Quotient.inductionOn with
  | _ v =>
      cases v with
      | inl c =>
          change (starQuotientMap (outerVertex c) =
              starQuotientMap (outerVertex ColorChannel.red)) ↔
            (false = false)
          constructor
          · intro _
            rfl
          · intro _
            exact outer_vertices_same_class c ColorChannel.red
      | inr u =>
          cases u
          change (starQuotientMap centralVertex =
              starQuotientMap (outerVertex ColorChannel.red)) ↔
            (true = false)
          constructor
          · intro h
            exact False.elim ((centre_not_outer_class ColorChannel.red) h)
          · intro h
            cases h

theorem isOpen_centreClass : IsOpen centreClass := by
  rw [centreClass_eq_preimage]
  exact IsOpen.preimage continuous_quotientToBool (isOpen_discrete _)

theorem isClosed_centreClass : IsClosed centreClass := by
  rw [centreClass_eq_preimage]
  exact IsClosed.preimage continuous_quotientToBool (isClosed_discrete _)

theorem isOpen_outerClass : IsOpen outerClass := by
  rw [outerClass_eq_preimage]
  exact IsOpen.preimage continuous_quotientToBool (isOpen_discrete _)

theorem isClosed_outerClass : IsClosed outerClass := by
  rw [outerClass_eq_preimage]
  exact IsClosed.preimage continuous_quotientToBool (isClosed_discrete _)

theorem centreClass_isClopen : IsClopen centreClass :=
  ⟨isClosed_centreClass, isOpen_centreClass⟩

theorem outerClass_isClopen : IsClopen outerClass :=
  ⟨isClosed_outerClass, isOpen_outerClass⟩

end InfoGeometry.Topology.PauliJungD4Star
