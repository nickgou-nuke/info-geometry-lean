import InfoGeometry.Canonical.OperatorChiralDeterminantDefect
import InfoGeometry.Algebra.CircularChiralOperatorEightBridge
import InfoGeometry.Canonical.ChiralZornNCZornBridge
import InfoGeometry.Canonical.QuaternionicTwistorSphereOperator
import InfoGeometry.Canonical.OperatorHermitianLieJordanSplit
import InfoGeometry.Canonical.OperatorZornSpinCasimirLift
import InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge
import InfoGeometry.Canonical.QuaternionicOperatorLiftCurvature
import InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition

/-!
# InfoGeometry.Canonical.OperatorQuaternionicLiftCapstone

Canonical owner for the parts of the quaternion/Pauli/chiral operator lift
that are already theorem-supported in the repository.

The capstone deliberately separates seven algebraic layers from stronger
geometric interpretations:

1. the classical chiral adjugate identity acquires explicit commutator defects
   over noncommuting operator coefficients;
2. quaternionic `I,J,K` extend to the full normalized two-sphere
   `a I + b J + c K` of pointwise complex structures;
3. products of Hermitian finite operators split into Hermitian Jordan and
   skew-Hermitian Lie channels;
4. spin-half projections and the quadratic spin Casimir transport exactly to
   the associative operator-Zorn/chiral coordinates;
5. concrete vector/axial Dirac matrices are `γ5`-odd and their square is
   `γ5`-even, with scalar plus explicit mixed bivector residue;
6. the genuinely operator-valued causal soldering owner records the ordered
   Pauli factorization defect and connection curvature as commutator residues;
7. the repository-owned tripotent construction reconstructs every element from
   its five grouped Peirce components.
8. the existing eight-element circular chiral frame and its matrix-coefficient
   noncommutative Zorn transport are exposed without carrier identification.

Exterior Clifford degree and the tripotent/TKK five-grading remain separate
structures.  No Berry connection, DeWitt supermetric, unbounded Dirac operator,
or Lichnerowicz theorem is inferred merely from these finite algebraic facts.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorQuaternionicLiftCapstone

open Matrix
open InfoGeometry.Clifford.DiracPauliGamma
open InfoGeometry.Canonical.OperatorChiralDeterminantDefect
open InfoGeometry.Canonical.QuaternionicTwistorSphereOperator
open InfoGeometry.Canonical.QuaternionicOperatorComplexStructure
open InfoGeometry.Canonical.OperatorHermitianLieJordanSplit
open InfoGeometry.Canonical.OperatorZornSpinCasimirLift
open InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge
open InfoGeometry.Physics.Algebra
open InfoGeometry.Algebra.CircularChiralCausalConeBasis
open InfoGeometry.Algebra.CircularChiralOperatorEightBridge
open InfoGeometry.Canonical.ChiralZornNCZornBridge
open InfoGeometry.Physics.NCG
open InfoGeometry.Physics.Octonion

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
            OperatorChiralDeterminantDefect.operatorCommutator r p;
           OperatorChiralDeterminantDefect.operatorCommutator l m,
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

/-- Spin-half data in the chiral operator-Zorn carrier: helicity remains an
involution, the two spin projectors remain complementary idempotents, and the
quadratic Casimir remains the scalar `3/4` channel. -/
theorem finite_operator_spin_casimir_packet :
    zornHelicity * zornHelicity = 1 ∧
      zornSpinPlusProjector * zornSpinPlusProjector = zornSpinPlusProjector ∧
      zornSpinMinusProjector * zornSpinMinusProjector = zornSpinMinusProjector ∧
      zornSpinPlusProjector * zornSpinMinusProjector = 0 ∧
      InfoGeometry.Physics.OperatorZornMatrix.toMatrix zornSpinHalfCasimir =
        (3 / 4 : ℂ) • (1 : Mat2C) :=
  operatorZorn_spin_half_packet

/-- Exterior-Clifford parity packet for the finite vector plus axial-vector
operator.  This is the theorem-honest replacement for identifying the
tripotent five-grading with exterior degrees `0,...,4`. -/
theorem finite_clifford_odd_even_square_packet
    (A B : OperatorCliffordOddEvenSquareBridge.ComplexFourVector) :
    IsCliffordOdd (oddPotential A B) ∧
      IsCliffordEven (oddPotential A B * oddPotential A B) ∧
      oddPotential A B * oddPotential A B =
        (minkowskiQuadratic A - minkowskiQuadratic B) •
            (1 : DiracMatrix) +
          mixedBivectorResidue A B := by
  exact ⟨oddPotential_isCliffordOdd A B,
    oddPotential_sq_isCliffordEven A B,
    oddPotential_sq_decomposition A B⟩

/-- Pure-vector Dirac linearization packet. -/
theorem finite_vector_square_root_packet
    (A : OperatorCliffordOddEvenSquareBridge.ComplexFourVector) :
    IsCliffordOdd (slash A) ∧
      slash A * slash A = minkowskiQuadratic A • (1 : DiracMatrix) := by
  exact ⟨slash_isCliffordOdd A, slash_sq A⟩

/-- Commuting with two quaternionic spatial bivectors protects the entire
three-dimensional quaternionic bivector span. -/
theorem quaternionic_bivector_commutant_packet
    (N : DiracMatrix)
    (hi : Commute N InfoGeometry.Canonical.QuaternionEmbedding.quat_i)
    (hj : Commute N InfoGeometry.Canonical.QuaternionEmbedding.quat_j)
    (a b c : ℂ) :
    Commute N (quaternionicBivectorCombination a b c) :=
  commute_quaternionicBivectorCombination_of_first_two N hi hj a b c

/-! ## Circular chiral operator frame and noncommutative Zorn transport -/

/-- The existing circular chiral frame supplies eight distinct native
operator readouts.  This theorem packages the cardinality and injectivity
owners without identifying this readout carrier with the finite Dirac or
tensor-colimit carriers. -/
theorem circular_chiral_eight_operator_packet :
    Fintype.card ChiralBasis = 8 ∧
      Function.Injective operatorFrame := by
  exact ⟨chiral_basis_card, operatorFrame_injective⟩

/-- Matrix-valued chiral coordinates are transported through the existing
noncommutative Zorn presentation.  The product is preserved as an explicit
coordinate law, not promoted to an unjustified associative octonion ring. -/
theorem matrix_coefficient_chiral_zorn_packet
    (X Y : ChiralZornMatrix MatrixTwoOperator) :
    toNC (X * Y) =
      NCZornElement.mul (toNC X) (toNC Y) :=
  toNC_matrixTwo_mul X Y

/-! ## Genuine operator-valued causal tier -/

section OperatorCurvature

open InfoGeometry.Canonical.QuaternionicOperatorLiftCurvature
open InfoGeometry.Optics.OperatorCausalSoldering

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The actual operator-valued Pauli determinant proxy separates into a
symmetric quadratic channel and explicit noncommutative commutators. -/
theorem operator_pauli_factorization_packet
    (v : OperatorFourVector W) :
    orderedPauliFactor v =
        symmetricPauliQuadratic v -
          QuaternionicOperatorLiftCurvature.operatorCommutator (v 0) (v 3) -
          Complex.I •
            QuaternionicOperatorLiftCurvature.operatorCommutator (v 1) (v 2) ∧
      pauliFactorizationCurvature v =
        (-2 : ℂ) •
          (QuaternionicOperatorLiftCurvature.operatorCommutator (v 0) (v 3) +
            Complex.I •
              QuaternionicOperatorLiftCurvature.operatorCommutator (v 1) (v 2)) := by
  exact ⟨orderedPauliFactor_eq_symmetric_sub_commutators v,
    pauliFactorizationCurvature_eq_commutator_residue v⟩

section Connection

variable {Point Tangent : Type*}

/-- The repository's genuine connection owner supplies the differential term
plus the operator commutator.  This is the first layer at which `curvature` is
used literally rather than as an analogy. -/
theorem operator_connection_curvature_packet
    (C : CausalOperatorConnection W Point Tangent)
    (p : Point) (X Y : Tangent) :
    matrixAction (curvature (matrixConnection C) p X Y) =
      matrixAction (reconstruct_causal (C.derivative p X Y)) +
        QuaternionicOperatorLiftCurvature.operatorCommutator
          (matrixAction (reconstruct_causal (C.form p X)))
          (matrixAction (reconstruct_causal (C.form p Y))) :=
  matrixConnection_curvature_eq_derivative_add_commutator C p X Y

end Connection
end OperatorCurvature

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
