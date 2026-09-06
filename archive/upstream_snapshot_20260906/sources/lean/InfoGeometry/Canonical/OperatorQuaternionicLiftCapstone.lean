import InfoGeometry.Canonical.OperatorChiralDeterminantDefect
import InfoGeometry.Canonical.QuaternionicTwistorSphereOperator
import InfoGeometry.Canonical.OperatorHermitianLieJordanSplit
import InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition

/-!
# InfoGeometry.Canonical.OperatorQuaternionicLiftCapstone

Canonical owner for the parts of the quaternion/Pauli/chiral operator lift
that are already theorem-supported in the repository.

The capstone deliberately separates four algebraic facts from stronger
geometric interpretations:

1. the classical chiral adjugate identity acquires explicit commutator defects
   over noncommuting operator coefficients;
2. quaternionic `I,J,K` extend to the full normalized two-sphere
   `a I + b J + c K` of pointwise complex structures;
3. products of Hermitian finite operators split into Hermitian Jordan and
   skew-Hermitian Lie channels;
4. the repository-owned tripotent construction reconstructs every element from
   its five grouped Peirce components.

No Berry connection, DeWitt supermetric, unbounded Dirac operator, or
Lichnerowicz curvature theorem is inferred merely from these algebraic facts.
Those require their own differential/topological/analytic hypotheses.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorQuaternionicLiftCapstone

open Matrix
open InfoGeometry.Clifford.DiracPauliGamma
open InfoGeometry.Canonical.OperatorChiralDeterminantDefect
open InfoGeometry.Canonical.QuaternionicTwistorSphereOperator
open InfoGeometry.Canonical.QuaternionicOperatorComplexStructure
open InfoGeometry.Canonical.OperatorHermitianLieJordanSplit
open InfoGeometry.Physics.Algebra

/-- The complete algebraic operator-lift packet on the finite Pauli/Dirac
carriers. -/
theorem finite_operator_lift_packet
    {A : Type*} [Ring A]
    (p m r l : A)
    {a b c : ℝ} (hsphere : OnTwistorSphere a b c)
    {H K : DiracMatrix}
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    chiralBlock p m r l * chiralAdjugate p m r l =
        !![leftQuadraticReadout p m r l,
            operatorCommutator r p;
           operatorCommutator l m,
            rightQuadraticReadout p m r l] ∧
      (pauliTwistorComplexStructure a b c).comp
          (pauliTwistorComplexStructure a b c) =
        -(LinearMap.id : PauliSpinorOperator) ∧
      H * K =
        operatorJordanProduct H K +
          (2 : ℂ)⁻¹ • operatorLieBracket H K ∧
      (operatorJordanProduct H K).IsHermitian ∧
      Matrix.conjTranspose (operatorLieBracket H K) =
        -operatorLieBracket H K := by
  exact ⟨chiralBlock_mul_adjugate p m r l,
    pauliTwistorComplexStructure_sq hsphere,
    operator_product_eq_jordan_add_half_lie H K,
    operatorJordanProduct_isHermitian hH hK,
    operatorLieBracket_conjTranspose hH hK⟩

/-- The existing five-grade owner is the correct Peirce reconstruction layer;
this alias exposes it from the operator-lift capstone without introducing a
second projector family. -/
theorem fiveGrade_operator_reconstruction
    {R : Type*} [Ring R] [Algebra ℝ R]
    (e x : R) :
    fiveGradeRecomposeLinear e (fiveGradeDecomposeLinear e x) = x :=
  fiveGrade_recompose_decompose e x

/-- Under the commutativity assumptions that kill the operator defects, the
chiral block collapses back to the ordinary scalar adjugate channel. -/
theorem classical_chiral_limit
    {A : Type*} [Ring A]
    (p m r l : A)
    (hpm : Commute p m)
    (hrl : Commute r l)
    (hrp : Commute r p)
    (hlm : Commute l m) :
    chiralBlock p m r l * chiralAdjugate p m r l =
      scalarChiralBlock (leftQuadraticReadout p m r l) :=
  chiralBlock_mul_adjugate_eq_scalar_of_commute
    p m r l hpm hrl hrp hlm

end InfoGeometry.Canonical.OperatorQuaternionicLiftCapstone
