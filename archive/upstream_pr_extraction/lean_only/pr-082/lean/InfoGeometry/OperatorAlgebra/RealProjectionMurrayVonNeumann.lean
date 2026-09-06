import Mathlib

/-!
# Murray--von Neumann equivalence for real self-adjoint idempotents

The relation is stated on elements, while its equivalence laws explicitly
carry the projection hypotheses needed for the partial-isometry composition.
No C*-completion or `K₀` construction is asserted here.
-/

namespace InfoGeometry.OperatorAlgebra

variable {A : Type*} [Ring A] [StarRing A]

def MurrayVonNeumannEquivalent (p q : A) : Prop :=
  ∃ v : A, star v * v = p ∧ v * star v = q

theorem mvn_refl {p : A} (hp : IsIdempotentElem p ∧ star p = p) :
    MurrayVonNeumannEquivalent p p := by
  refine ⟨p, ?_, ?_⟩
  · simpa [hp.2] using hp.1
  · simpa [hp.2] using hp.1

theorem mvn_symm {p q : A}
    (h : MurrayVonNeumannEquivalent p q) :
    MurrayVonNeumannEquivalent q p := by
  rcases h with ⟨v, hvp, hvq⟩
  refine ⟨star v, ?_, ?_⟩
  · simpa [star_mul, star_star] using hvq
  · simpa [star_mul, star_star] using hvp

theorem mvn_trans {p q r : A}
    (hp : IsIdempotentElem p ∧ star p = p)
    (hr : IsIdempotentElem r ∧ star r = r)
    (h₁ : MurrayVonNeumannEquivalent p q)
    (h₂ : MurrayVonNeumannEquivalent q r) :
    MurrayVonNeumannEquivalent p r := by
  rcases h₁ with ⟨v, hvp, hvq⟩
  rcases h₂ with ⟨w, hwq, hwr⟩
  refine ⟨w * v, ?_, ?_⟩
  · calc
      star (w * v) * (w * v) = star v * (star w * w) * v := by
        simp [star_mul, mul_assoc]
      _ = star v * q * v := by rw [hwq]
      _ = star v * (v * star v) * v := by rw [← hvq]
      _ = (star v * v) * (star v * v) := by simp [mul_assoc]
      _ = p * p := by rw [hvp]
      _ = p := hp.1
  · calc
      (w * v) * star (w * v) = w * (v * star v) * star w := by
        simp [star_mul, mul_assoc]
      _ = w * q * star w := by rw [hvq]
      _ = w * (star w * w) * star w := by rw [hwq]
      _ = (w * star w) * (w * star w) := by simp [mul_assoc]
      _ = r * r := by rw [hwr]
      _ = r := hr.1

end InfoGeometry.OperatorAlgebra
