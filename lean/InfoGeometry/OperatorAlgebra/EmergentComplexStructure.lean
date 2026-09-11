import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic scalar extension from a central square root of `-1`

This owner records only the algebraic statement: a central element squaring to
`-1` gives a compatible `ℂ`-algebra structure on a real associative algebra.
No topological or analytic structure is part of the theorem.
-/

namespace InfoGeometry.OperatorAlgebra.EmergentComplexStructure

variable {A : Type*} [Ring A] [Algebra ℝ A]

class IsEmergentImaginary (J : A) : Prop where
  sq_eq_neg_one : J * J = -1
  commutes : ∀ x : A, J * x = x * J

noncomputable def emergentComplexHom (J : A)
    [hJ : IsEmergentImaginary J] : ℂ →ₐ[ℝ] A :=
  Complex.lift ⟨J, hJ.sq_eq_neg_one⟩

noncomputable def emergentComplexAlgebra (J : A)
    [hJ : IsEmergentImaginary J] : Algebra ℂ A where
  algebraMap := (emergentComplexHom J).toRingHom
  smul z x := (emergentComplexHom J z) * x
  commutes' z x := by
    change (emergentComplexHom J z) * x = x * (emergentComplexHom J z)
    have h_eval : (emergentComplexHom J z) =
        (algebraMap ℝ A z.re) + (z.im : ℝ) • J := by
      change Complex.liftAux J hJ.sq_eq_neg_one z = _
      exact Complex.liftAux_apply J hJ.sq_eq_neg_one z
    rw [h_eval, add_mul, mul_add]
    have h₁ : ((algebraMap ℝ A z.re) : A) * x =
        x * ((algebraMap ℝ A z.re) : A) :=
      Algebra.commutes (z.re : ℝ) x
    have h₂ : ((z.im : ℝ) • J) * x =
        x * ((z.im : ℝ) • J) := by
      rw [smul_mul_assoc, mul_smul_comm]
      congr 1
      exact hJ.commutes x
    rw [h₁, h₂]
  smul_def' z x := rfl

end InfoGeometry.OperatorAlgebra.EmergentComplexStructure
