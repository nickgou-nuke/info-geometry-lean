import InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge
import InfoGeometry.Canonical.OperatorWeylChiralCurvatureResidue
import InfoGeometry.Canonical.WeylChiralHodgeCurvatureSplit
import InfoGeometry.Canonical.QuaternionicOperatorLiftCurvature

/-!
# InfoGeometry.Canonical.OperatorCliffordWeylCurvatureCapstone

Theorem-honest capstone for the operator-potential / Clifford-parity / Weyl
curvature chain.

The capstone keeps three layers distinct:

1. finite scalar-coordinate Dirac/Weyl Clifford identities;
2. genuine operator-valued chiral curvature residues;
3. Lorentzian Hodge splitting of the two Weyl diagonal blocks.

It also exposes the already-proved quaternionic commutant protection on the
spatial bivector span.  No theorem here identifies that span with one Weyl
Hodge eigenspace; that final comparison still requires an explicit
Dirac-Pauli ↔ Weyl basis-change intertwiner.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorCliffordWeylCurvatureCapstone

open InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge
open InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks
open InfoGeometry.Canonical.OperatorWeylChiralCurvatureResidue
open InfoGeometry.Canonical.WeylChiralHodgeCurvatureSplit
open InfoGeometry.Canonical.QuaternionicOperatorLiftCurvature
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Canonical.QuaternionEmbedding

/-- Scalar-coordinate Clifford/Weyl square-root packet. -/
theorem scalar_clifford_weyl_packet (A : ComplexFourVector) :
    slash A * slash A = minkowskiQuadratic A •
        (1 : InfoGeometry.Clifford.DiracPauliGamma.DiracMatrix) ∧
      weylSlash A * weylSlash A =
        minkowskiQuadratic A • (1 : Mat4C) := by
  exact ⟨slash_sq A, weylSlash_sq_scalar A⟩

/-- Weyl parity and Hodge decomposition packet. -/
theorem weyl_parity_hodge_packet (A : ComplexFourVector) :
    weylGamma5 * weylSlash A + weylSlash A * weylGamma5 = 0 ∧
      weylSlash A * weylSlash A =
        leftChiralBlock (sigmaSolder A * coSolder A) +
          rightChiralBlock (coSolder A * sigmaSolder A) ∧
      weylHodgeStar
          (leftChiralBlock (sigmaSolder A * coSolder A)) =
        (-Complex.I) • leftChiralBlock (sigmaSolder A * coSolder A) ∧
      weylHodgeStar
          (rightChiralBlock (coSolder A * sigmaSolder A)) =
        Complex.I • rightChiralBlock (coSolder A * sigmaSolder A) := by
  exact ⟨weylGamma5_anticomm_weylSlash A,
    weylSlash_sq_hodge_split A,
    leftChiralBlock_hodge_eigen _,
    rightChiralBlock_hodge_eigen _⟩

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Genuine operator-valued Weyl curvature packet: both chiral blocks are a
common quadratic channel plus explicit coefficient commutators. -/
theorem operator_weyl_curvature_packet (v : OperatorFourVector W) :
    leftCurvatureBlock v =
      !![operatorMinkowskiQuadratic v - opComm (v 0) (v 3) -
            Complex.I • opComm (v 1) (v 2),
          -opComm (v 0) (v 1) + opComm (v 1) (v 3) +
            Complex.I • (opComm (v 0) (v 2) + opComm (v 3) (v 2));
         -opComm (v 0) (v 1) - opComm (v 1) (v 3) -
            Complex.I • opComm (v 0) (v 2) +
            Complex.I • opComm (v 3) (v 2),
          operatorMinkowskiQuadratic v + opComm (v 0) (v 3) +
            Complex.I • opComm (v 1) (v 2)] ∧
      rightCurvatureBlock v =
      !![operatorMinkowskiQuadratic v + opComm (v 0) (v 3) -
            Complex.I • opComm (v 1) (v 2),
          opComm (v 0) (v 1) + opComm (v 1) (v 3) -
            Complex.I • opComm (v 0) (v 2) +
            Complex.I • opComm (v 3) (v 2);
         opComm (v 0) (v 1) - opComm (v 1) (v 3) +
            Complex.I • opComm (v 0) (v 2) +
            Complex.I • opComm (v 3) (v 2),
          operatorMinkowskiQuadratic v - opComm (v 0) (v 3) +
            Complex.I • opComm (v 1) (v 2)] :=
  chiral_curvature_residue_packet v

/-- Commuting with two quaternionic spatial bivectors protects their full
three-dimensional complex span. -/
theorem quaternionic_bivector_span_protected
    (N : InfoGeometry.Clifford.DiracPauliGamma.DiracMatrix)
    (hi : Commute N quat_i)
    (hj : Commute N quat_j)
    (a b c : ℂ) :
    Commute N (quaternionicBivectorCombination a b c) :=
  commute_quaternionicBivectorCombination_of_first_two N hi hj a b c

end InfoGeometry.Canonical.OperatorCliffordWeylCurvatureCapstone
