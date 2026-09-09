import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks

/-!
# InfoGeometry.Canonical.OperatorWeylChiralCurvatureResidue

Explicit commutator coordinates of the two ordered Weyl curvature blocks.

The parent owner proves that an operator-valued Weyl odd square has diagonal
blocks `σ(A) \barσ(A)` and `\barσ(A) σ(A)`.  This file expands those blocks
without assigning a geometric self-duality label.  Every departure from the
scalar Minkowski quadratic channel is written as an actual commutator of
operator coefficients.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorWeylChiralCurvatureResidue

open Matrix
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

abbrev EndW := Module.End ℂ W
abbrev OperatorMat2 := Matrix (Fin 2) (Fin 2) EndW

/-- Ring commutator of operator coefficients. -/
def opComm (x y : EndW) : EndW := x * y - y * x

/-- Symmetric Minkowski quadratic channel of an operator-valued four-vector. -/
def operatorMinkowskiQuadratic (v : OperatorFourVector W) : EndW :=
  v 0 * v 0 - v 1 * v 1 - v 2 * v 2 - v 3 * v 3

/-- Exact left Weyl block: scalar quadratic channel plus commutator residue. -/
theorem leftCurvatureBlock_explicit (v : OperatorFourVector W) :
    leftCurvatureBlock v =
      !![operatorMinkowskiQuadratic v - opComm (v 0) (v 3) -
            Complex.I • opComm (v 1) (v 2),
          -opComm (v 0) (v 1) + opComm (v 1) (v 3) +
            Complex.I • (opComm (v 0) (v 2) + opComm (v 3) (v 2));
         -opComm (v 0) (v 1) - opComm (v 1) (v 3) -
            Complex.I • opComm (v 0) (v 2) +
            Complex.I • opComm (v 3) (v 2),
          operatorMinkowskiQuadratic v + opComm (v 0) (v 3) +
            Complex.I • opComm (v 1) (v 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftCurvatureBlock, operatorSoldering_apply, operatorCoSoldering,
      operatorMinkowskiQuadratic, opComm, Matrix.mul_apply,
      Fin.sum_univ_two, Algebra.smul_def]
    <;> noncomm_ring

/-- Exact right Weyl block, with the reversed operator ordering retained. -/
theorem rightCurvatureBlock_explicit (v : OperatorFourVector W) :
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
            Complex.I • opComm (v 1) (v 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rightCurvatureBlock, operatorSoldering_apply, operatorCoSoldering,
      operatorMinkowskiQuadratic, opComm, Matrix.mul_apply,
      Fin.sum_univ_two, Algebra.smul_def]
    <;> noncomm_ring

/-- Scalar `2×2` operator block. -/
def scalarOperatorBlock (q : EndW) : OperatorMat2 :=
  !![q, 0; 0, q]

/-- If all six independent coefficient commutators vanish, the left Weyl
curvature block collapses to the scalar quadratic channel. -/
theorem leftCurvatureBlock_eq_scalar_of_pairwise_commute
    (v : OperatorFourVector W)
    (h01 : opComm (v 0) (v 1) = 0)
    (h02 : opComm (v 0) (v 2) = 0)
    (h03 : opComm (v 0) (v 3) = 0)
    (h12 : opComm (v 1) (v 2) = 0)
    (h13 : opComm (v 1) (v 3) = 0)
    (h23 : opComm (v 2) (v 3) = 0) :
    leftCurvatureBlock v =
      scalarOperatorBlock (operatorMinkowskiQuadratic v) := by
  rw [leftCurvatureBlock_explicit]
  have h32 : opComm (v 3) (v 2) = 0 := by
    simp [opComm]
    exact sub_eq_zero.mpr (sub_eq_zero.mp h23).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarOperatorBlock, h01, h02, h03, h12, h13, h23, h32]

/-- The same commuting limit collapses the right block to the identical scalar
quadratic channel. -/
theorem rightCurvatureBlock_eq_scalar_of_pairwise_commute
    (v : OperatorFourVector W)
    (h01 : opComm (v 0) (v 1) = 0)
    (h02 : opComm (v 0) (v 2) = 0)
    (h03 : opComm (v 0) (v 3) = 0)
    (h12 : opComm (v 1) (v 2) = 0)
    (h13 : opComm (v 1) (v 3) = 0)
    (h23 : opComm (v 2) (v 3) = 0) :
    rightCurvatureBlock v =
      scalarOperatorBlock (operatorMinkowskiQuadratic v) := by
  rw [rightCurvatureBlock_explicit]
  have h32 : opComm (v 3) (v 2) = 0 := by
    simp [opComm]
    exact sub_eq_zero.mpr (sub_eq_zero.mp h23).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarOperatorBlock, h01, h02, h03, h12, h13, h23, h32]

/-- The operator-valued Weyl square separates cleanly into a common scalar
quadratic part and two order-sensitive commutator residues. -/
theorem chiral_curvature_residue_packet (v : OperatorFourVector W) :
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
            Complex.I • opComm (v 1) (v 2)] := by
  exact ⟨leftCurvatureBlock_explicit v, rightCurvatureBlock_explicit v⟩

end InfoGeometry.Canonical.OperatorWeylChiralCurvatureResidue
