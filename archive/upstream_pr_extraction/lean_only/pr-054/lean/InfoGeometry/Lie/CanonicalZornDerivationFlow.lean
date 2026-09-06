import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelDerivative

/-!
# Exponential flows of represented canonical Zorn derivations

The canonical Zorn carrier is currently an algebraic carrier and does not
carry a native normed topology. Consequently an exponential flow is stated
here only after supplying a representation into a complete normed real
algebra. No topology or automorphism structure is invented for the Zorn
carrier by this file.
-/

namespace InfoGeometry.Lie.CanonicalZornDerivation

variable {A : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

noncomputable def representedDerivationFlow
    (ρ : canonicalZornDerivations →ₗ[ℝ] A)
    (D : canonicalZornDerivations) (t : ℝ) : A :=
  NormedSpace.exp (t • ρ D)

@[simp]
theorem representedDerivationFlow_zero
    (ρ : canonicalZornDerivations →ₗ[ℝ] A)
    (D : canonicalZornDerivations) :
    representedDerivationFlow ρ D 0 = 1 := by
  simp [representedDerivationFlow]

theorem representedDerivationFlow_add
    (ρ : canonicalZornDerivations →ₗ[ℝ] A)
    (D : canonicalZornDerivations) (s t : ℝ) :
    representedDerivationFlow ρ D (s + t) =
      representedDerivationFlow ρ D s *
        representedDerivationFlow ρ D t := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hComm : Commute (s • ρ D) (t • ρ D) := by
    exact (Commute.refl (ρ D)).smul_left s |>.smul_right t
  unfold representedDerivationFlow
  rw [add_smul, NormedSpace.exp_add_of_commute hComm]

theorem representedDerivationFlow_neg_mul
    (ρ : canonicalZornDerivations →ₗ[ℝ] A)
    (D : canonicalZornDerivations) (t : ℝ) :
    representedDerivationFlow ρ D (-t) *
        representedDerivationFlow ρ D t = 1 := by
  rw [← representedDerivationFlow_add, neg_add_cancel,
    representedDerivationFlow_zero]

theorem representedDerivationFlow_mul_neg
    (ρ : canonicalZornDerivations →ₗ[ℝ] A)
    (D : canonicalZornDerivations) (t : ℝ) :
    representedDerivationFlow ρ D t *
        representedDerivationFlow ρ D (-t) = 1 := by
  rw [← representedDerivationFlow_add, add_neg_cancel,
    representedDerivationFlow_zero]

theorem hasDerivAt_representedDerivationFlow
    (ρ : canonicalZornDerivations →ₗ[ℝ] A)
    (D : canonicalZornDerivations) (t : ℝ) :
    HasDerivAt (representedDerivationFlow ρ D)
      (representedDerivationFlow ρ D t * ρ D) t := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  simpa [representedDerivationFlow] using
    (hasDerivAt_exp_smul_const (x := ρ D) (t := t))

theorem deriv_representedDerivationFlow_zero
    (ρ : canonicalZornDerivations →ₗ[ℝ] A)
    (D : canonicalZornDerivations) :
    deriv (representedDerivationFlow ρ D) 0 = ρ D := by
  simpa using (hasDerivAt_representedDerivationFlow ρ D 0).deriv

end InfoGeometry.Lie.CanonicalZornDerivation
