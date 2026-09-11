import InfoGeometry.Lie.ContinuousDerivationExponential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Noncommutative Maurer--Cartan adjoint multiplier bridge

The associative Banach-algebra part of the Maurer--Cartan construction.  The
carrier is deliberately associative; this owner is not a claim about raw
split-octonion multiplication.
-/

noncomputable section
namespace InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def leftMulCLM (a : A) : A →L[ℝ] A :=
  (ContinuousLinearMap.mul ℝ A) a

def rightMulCLM (a : A) : A →L[ℝ] A :=
  (ContinuousLinearMap.mul ℝ A).flip a

@[simp] theorem leftMulCLM_apply (a x : A) :
    leftMulCLM a x = a * x := rfl

@[simp] theorem rightMulCLM_apply (a x : A) :
    rightMulCLM a x = x * a := rfl

theorem leftMul_rightMul_commute (a b : A) :
    Commute (leftMulCLM a) (rightMulCLM b) := by
  show leftMulCLM a * rightMulCLM b = rightMulCLM b * leftMulCLM a
  ext x
  simp [ContinuousLinearMap.mul_apply, mul_assoc]

def adCLM (a : A) : A →L[ℝ] A := leftMulCLM a - rightMulCLM a

@[simp] theorem adCLM_apply (a x : A) :
    adCLM a x = a * x - x * a := rfl

theorem adCLM_leibniz (a x y : A) :
    adCLM a (x * y) = adCLM a x * y + x * adCLM a y := by
  simp [adCLM_apply]
  noncomm_ring

theorem adCLM_isDerivation (a : A) :
    InfoGeometry.Lie.ContinuousDerivationExponential.IsDerivation
      (ContinuousLinearMap.mul ℝ A) (adCLM a) := by
  intro x y
  exact adCLM_leibniz a x y

theorem adCLM_commutator (a b x : A) :
    adCLM a (adCLM b x) - adCLM b (adCLM a x) =
      adCLM (a * b - b * a) x := by
  simp [adCLM_apply]
  noncomm_ring

theorem adCLM_commutator_operator (a b : A) :
    (adCLM a).comp (adCLM b) - (adCLM b).comp (adCLM a) =
      adCLM (a * b - b * a) := by
  ext x
  exact adCLM_commutator a b x

/-! The same closure statement in Mathlib's associative Lie-bracket
notation.  This is the native `ad` readback used by the derivation-form
complex; it keeps the coefficient algebra associative and does not identify
it with the split-octonion commutator. -/

theorem adCLM_lieBracket (a b : A) :
    ⁅adCLM a, adCLM b⁆ = adCLM (a * b - b * a) := by
  rw [LieRing.of_associative_ring_bracket]
  exact adCLM_commutator_operator a b

theorem adCLM_flow_is_multiplicative (a : A) (t : ℝ) (x y : A) :
    InfoGeometry.Lie.ContinuousDerivationExponential.flow (adCLM a) t (x * y) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow (adCLM a) t x *
        InfoGeometry.Lie.ContinuousDerivationExponential.flow (adCLM a) t y := by
  exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_map_mul
    (ContinuousLinearMap.mul ℝ A) (adCLM a) (adCLM_isDerivation a) t x y

end InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge
