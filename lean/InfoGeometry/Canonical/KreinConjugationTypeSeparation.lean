import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Scalar-type obstruction to identifying a fundamental symmetry with conjugation

This is not a Tomita--Takesaki theorem or a claim about a real internal-phase
presentation. It distinguishes linear and semilinear maps over the same ℂ.
-/

namespace InfoGeometry.Canonical.KreinConjugationTypeSeparation

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

theorem linear_eq_conjugateLinear_forces_zero
    (L : H →ₗ[ℂ] H) (J : H →ₛₗ[starRingEnd ℂ] H)
    (h : ∀ x, L x = J x) : L = 0 := by
  ext x
  have hi : Complex.I • L x = (-Complex.I) • L x := by
    calc
      Complex.I • L x = L (Complex.I • x) := (L.map_smul _ _).symm
      _ = J (Complex.I • x) := h _
      _ = (-Complex.I) • L x := by
        rw [map_smulₛₗ, ← h x]
        simp
  have hz : (Complex.I + Complex.I) • L x = 0 := by
    calc
      (Complex.I + Complex.I) • L x = Complex.I • L x + Complex.I • L x :=
        add_smul _ _ _
      _ = (-Complex.I) • L x + Complex.I • L x :=
        congrArg (fun y => y + Complex.I • L x) hi
      _ = 0 := by rw [neg_smul]; exact neg_add_cancel _
  have hn : Complex.I + Complex.I ≠ (0 : ℂ) := by
    intro he
    have him := congrArg Complex.im he
    norm_num at him
  exact (smul_eq_zero.mp hz).resolve_left hn

theorem linearEquiv_not_conjugateLinear [Nontrivial H]
    (L : H ≃ₗ[ℂ] H) (J : H →ₛₗ[starRingEnd ℂ] H) :
    ¬ ∀ x, L x = J x := by
  intro h
  have hz := linear_eq_conjugateLinear_forces_zero L.toLinearMap J h
  obtain ⟨x,hx⟩ := exists_ne (0 : H)
  apply hx
  apply L.injective
  have he := congrArg (fun T : H →ₗ[ℂ] H => T x) hz
  simpa using he

end InfoGeometry.Canonical.KreinConjugationTypeSeparation
