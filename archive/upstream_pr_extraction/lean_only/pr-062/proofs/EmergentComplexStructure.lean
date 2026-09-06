import Mathlib
import proofs.ChiralParitySuperalgebra

/-!
# Complex scalar extension from a central square root of `-1`

This file gives the algebraic scalar-extension theorem. It does not construct
an analytic structure, a topology, or a spacetime model.

If a real algebra contains a central element `J` with `J * J = -1`, Mathlib's
`Complex.lift` supplies a compatible `Algebra ℂ A` structure.
-/

namespace InfoGeometry.EmergentComplexStructure

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The geometric condition for an emergent imaginary unit:
    An operator J that is central and squares to -1. -/
class IsEmergentImaginary (J : A) : Prop where
  sq_eq_neg_one : J * J = -1
  commutes : ∀ x : A, J * x = x * J

/-- The structural algebraic homomorphism from ℂ into the real operator algebra A. -/
noncomputable def emergentComplexHom (J : A) [hJ : IsEmergentImaginary J] : ℂ →ₐ[ℝ] A :=
  Complex.lift ⟨J, hJ.sq_eq_neg_one⟩

/-- The central square root of `-1` supplies the complex scalar action. -/
noncomputable def emergentComplexAlgebra (J : A) [hJ : IsEmergentImaginary J] : Algebra ℂ A where
  algebraMap := (emergentComplexHom J).toRingHom
  smul z x := (emergentComplexHom J z) * x
  commutes' z x := by
    change (emergentComplexHom J z) * x = x * (emergentComplexHom J z)
    have h_eval : (emergentComplexHom J z) = (algebraMap ℝ A z.re) + (z.im : ℝ) • J := by
      change Complex.liftAux J hJ.sq_eq_neg_one z = _
      exact Complex.liftAux_apply J hJ.sq_eq_neg_one z
    rw [h_eval, add_mul, mul_add]
    have h1 : ((algebraMap ℝ A z.re) : A) * x = x * ((algebraMap ℝ A z.re) : A) := by
      exact Algebra.commutes (z.re : ℝ) x
    have h2 : ((z.im : ℝ) • J) * x = x * ((z.im : ℝ) • J) := by
      rw [smul_mul_assoc, mul_smul_comm]
      congr 1
      exact hJ.commutes x
    rw [h1, h2]
  smul_def' z x := rfl

end InfoGeometry.EmergentComplexStructure
