import InfoGeometry.Lie.ContinuousDerivationExponential
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Noncommutative Maurer--Cartan adjoint multiplier bridge

For an associative real Banach algebra, left and right multiplication are
bounded endomorphisms and commute solely by associativity.  Their difference
is the inner derivation

`ad_a(x) = a*x - x*a`.

This owner formalizes that algebraic engine and factors the exponential of the
adjoint derivation into commuting left/right multiplier exponentials.  It is a
coordinate-free Maurer--Cartan predecessor for the Duhamel calculus.

The file deliberately does not identify the Fréchet derivative of `exp` with a
Duhamel integral.  That identification still requires the analytic continuity
edge isolated by `NoncommutativeDuhamelContinuityReduction`.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge

variable {A : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

abbrev EndA := A →L[ℝ] A

noncomputable local instance : NormedAlgebra ℚ EndA :=
  NormedAlgebra.restrictScalars ℚ ℝ EndA

/-- Continuous left multiplication `x ↦ a*x`. -/
def leftMulCLM (a : A) : EndA :=
  (ContinuousLinearMap.mul ℝ A) a

/-- Continuous right multiplication `x ↦ x*a`. -/
def rightMulCLM (a : A) : EndA :=
  (ContinuousLinearMap.mul ℝ A).flip a

@[simp] theorem leftMulCLM_apply (a x : A) :
    leftMulCLM a x = a * x :=
  rfl

@[simp] theorem rightMulCLM_apply (a x : A) :
    rightMulCLM a x = x * a :=
  rfl

/-- Left and right multiplication commute for arbitrary multipliers. -/
theorem leftMul_rightMul_commute (a b : A) :
    Commute (leftMulCLM a) (rightMulCLM b) := by
  show leftMulCLM a * rightMulCLM b =
    rightMulCLM b * leftMulCLM a
  ext x
  simp [ContinuousLinearMap.mul_apply, mul_assoc]

/-- Inner adjoint derivation `ad_a = L_a - R_a`. -/
def adCLM (a : A) : EndA :=
  leftMulCLM a - rightMulCLM a

@[simp] theorem adCLM_apply (a x : A) :
    adCLM a x = a * x - x * a := by
  rfl

/-- The inner adjoint operator obeys the Leibniz rule. -/
theorem adCLM_leibniz (a x y : A) :
    adCLM a (x * y) =
      adCLM a x * y + x * adCLM a y := by
  simp [adCLM_apply]
  noncomm_ring

/-- The inner adjoint operator is a derivation for the native continuous
bilinear multiplication. -/
theorem adCLM_isDerivation (a : A) :
    InfoGeometry.Lie.ContinuousDerivationExponential.IsDerivation
      (ContinuousLinearMap.mul ℝ A) (adCLM a) := by
  intro x y
  exact adCLM_leibniz a x y

/-- Scaled left and right multipliers remain commuting endomorphisms. -/
theorem scaled_leftMul_rightMul_commute
    (a : A) (s t : ℝ) :
    Commute (s • leftMulCLM a) (t • rightMulCLM a) :=
  ((leftMul_rightMul_commute a a).smul_left s).smul_right t

/-- Exponential of the adjoint derivation factors into its commuting left and
right multiplier flows, with no BCH correction. -/
theorem exp_smul_adCLM_factor
    (a : A) (s : ℝ) :
    NormedSpace.exp (s • adCLM a) =
      NormedSpace.exp (s • leftMulCLM a) *
        NormedSpace.exp ((-s) • rightMulCLM a) := by
  have hcomm :
      Commute (s • leftMulCLM a) ((-s) • rightMulCLM a) :=
    scaled_leftMul_rightMul_commute a s (-s)
  have hsum :
      s • adCLM a =
        s • leftMulCLM a + (-s) • rightMulCLM a := by
    unfold adCLM
    module
  rw [hsum]
  exact NormedSpace.exp_add_of_commute hcomm

/-- The repository's derivation-flow owner applies directly to every inner
adjoint derivation. -/
theorem adCLM_flow_is_multiplicative
    (a : A) (t : ℝ) (x y : A) :
    InfoGeometry.Lie.ContinuousDerivationExponential.flow (adCLM a) t (x * y) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow (adCLM a) t x *
        InfoGeometry.Lie.ContinuousDerivationExponential.flow (adCLM a) t y := by
  exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_map_mul
    (ContinuousLinearMap.mul ℝ A) (adCLM a)
    (adCLM_isDerivation a) t x y

end InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge
