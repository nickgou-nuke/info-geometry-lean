import Mathlib
import InfoGeometry.Physics.NuclearSolovievStateProjection

noncomputable section
namespace InfoGeometry.Physics.Cl55TwoStatePeirceCompressionBridge

open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Physics.NuclearSolovievStateProjection
open InfoGeometry.Physics.NuclearSolovievStateProjection.TwoSpinorChannel

abbrev SpinorOperator := FullHamiltonian

def rankOneProjector (ψ : InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ) : SpinorOperator :=
  Matrix.vecMulVec
    (m := InfoGeometry.Clifford.TowerMatrix.Idx 5)
    (n := InfoGeometry.Clifford.TowerMatrix.Idx 5)
    ψ ψ
def peirceBlock (P Q H : SpinorOperator) : SpinorOperator := P * H * Q

namespace TwoSpinorChannel
variable (C : TwoSpinorChannel)

def bareProjector : SpinorOperator := rankOneProjector C.bare
def dressedProjector : SpinorOperator := rankOneProjector C.dressed

theorem bareProjector_mulVec_bare :
    bareProjector C *ᵥ C.bare = C.bare := by
  simp [bareProjector, rankOneProjector, Matrix.vecMulVec_mulVec, C.bare_norm]

theorem dressedProjector_mulVec_dressed :
    dressedProjector C *ᵥ C.dressed = C.dressed := by
  simp [dressedProjector, rankOneProjector, Matrix.vecMulVec_mulVec, C.dressed_norm]

theorem bareProjector_mulVec_dressed :
    bareProjector C *ᵥ C.dressed = 0 := by
  simp [bareProjector, rankOneProjector, Matrix.vecMulVec_mulVec,
    C.bare_dressed_orthogonal]

theorem dressedProjector_mulVec_bare :
    dressedProjector C *ᵥ C.bare = 0 := by
  have h : C.dressed ⬝ᵥ C.bare = 0 := by
    simpa [dotProduct_comm] using C.bare_dressed_orthogonal
  simp [dressedProjector, rankOneProjector, Matrix.vecMulVec_mulVec, h]

theorem bareProjector_sq :
    bareProjector C * bareProjector C = bareProjector C := by
  simp [bareProjector, rankOneProjector, Matrix.vecMulVec_mul_vecMulVec,
    C.bare_norm]

theorem dressedProjector_sq :
    dressedProjector C * dressedProjector C = dressedProjector C := by
  simp [dressedProjector, rankOneProjector, Matrix.vecMulVec_mul_vecMulVec,
    C.dressed_norm]

theorem bareProjector_mul_dressedProjector :
    bareProjector C * dressedProjector C = 0 := by
  simp [bareProjector, dressedProjector, rankOneProjector,
    Matrix.vecMulVec_mul_vecMulVec, C.bare_dressed_orthogonal]

theorem dressedProjector_mul_bareProjector :
    dressedProjector C * bareProjector C = 0 := by
  have h : C.dressed ⬝ᵥ C.bare = 0 := by
    simpa [dotProduct_comm] using C.bare_dressed_orthogonal
  simp [bareProjector, dressedProjector, rankOneProjector,
    Matrix.vecMulVec_mul_vecMulVec, h]

def bareBareBlock (H : SpinorOperator) : SpinorOperator :=
  peirceBlock (bareProjector C) (bareProjector C) H
def bareDressedBlock (H : SpinorOperator) : SpinorOperator :=
  peirceBlock (bareProjector C) (dressedProjector C) H
def dressedBareBlock (H : SpinorOperator) : SpinorOperator :=
  peirceBlock (dressedProjector C) (bareProjector C) H
def dressedDressedBlock (H : SpinorOperator) : SpinorOperator :=
  peirceBlock (dressedProjector C) (dressedProjector C) H

theorem rankOne_mul_matrix_mulVec
    (u v w : InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)
    (M : SpinorOperator) :
    (Matrix.vecMulVec u v * M) *ᵥ w =
      (v ⬝ᵥ (M *ᵥ w)) • u := by
  rw [← Matrix.mulVec_mulVec]
  simpa using Matrix.vecMulVec_mulVec u v (M *ᵥ w)

theorem bareDressedBlock_action (H : SpinorOperator) :
    bareDressedBlock C H *ᵥ C.dressed =
      C.matrixElement C.bare C.dressed H • C.bare := by
  rw [bareDressedBlock, peirceBlock]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dressedProjector_mulVec_dressed C]
  simpa [bareProjector, rankOneProjector, matrixElement] using
    rankOne_mul_matrix_mulVec C.bare C.bare C.dressed H

theorem dressedBareBlock_action (H : SpinorOperator) :
    dressedBareBlock C H *ᵥ C.bare =
      C.matrixElement C.dressed C.bare H • C.dressed := by
  rw [dressedBareBlock, peirceBlock]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    bareProjector_mulVec_bare C]
  simpa [dressedProjector, rankOneProjector, matrixElement] using
    rankOne_mul_matrix_mulVec C.dressed C.dressed C.bare H

end TwoSpinorChannel
end InfoGeometry.Physics.Cl55TwoStatePeirceCompressionBridge
