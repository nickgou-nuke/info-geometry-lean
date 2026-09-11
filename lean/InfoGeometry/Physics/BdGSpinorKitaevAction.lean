import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

namespace InfoGeometry.Physics

variable {A : Type*} [CommRing A] [StarRing A]

abbrev BdGSpinor (A : Type*) := Fin 2 → A

def applyBdGBlock (M : BdGBlock A) (v : BdGSpinor A) : BdGSpinor A :=
  fun i => M i 0 * v 0 + M i 1 * v 1

/-- Canonical matrix-to-linear-map action on the BdG spinor carrier. -/
def bdgSpinorAction : BdGBlock A →ₐ[A] BdGSpinor A →ₗ[A] BdGSpinor A :=
  Matrix.toLinAlgEquiv (Pi.basisFun A (Fin 2))

@[simp] theorem bdgSpinorAction_apply (M : BdGBlock A) (v : BdGSpinor A) :
    bdgSpinorAction (A := A) M v = applyBdGBlock M v := by
  ext i
  fin_cases i <;>
    simp [bdgSpinorAction, applyBdGBlock, Matrix.toLinAlgEquiv_apply,
      Matrix.mulVec, Fin.sum_univ_two]

def kitaevMajoranaE1 : BdGBlock A :=
  !![0, 1; 1, 0]

def kitaevMajoranaE2 : BdGBlock A :=
  !![0, 1; -1, 0]

@[simp] theorem kitaevMajoranaE1_sq :
    kitaevMajoranaE1 * kitaevMajoranaE1 = (1 : BdGBlock A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kitaevMajoranaE1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem kitaevMajoranaE2_sq :
    kitaevMajoranaE2 * kitaevMajoranaE2 = (-1 : BdGBlock A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kitaevMajoranaE2, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem kitaevMajorana_anticommutes :
    kitaevMajoranaE1 * kitaevMajoranaE2 +
        kitaevMajoranaE2 * kitaevMajoranaE1 = (0 : BdGBlock A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kitaevMajoranaE1, kitaevMajoranaE2, Matrix.mul_apply,
      Fin.sum_univ_two]

@[simp] theorem kitaevMajorana_product_eq_neg_chiralGrading :
    kitaevMajoranaE1 * kitaevMajoranaE2 =
      -(chiralGrading : BdGBlock A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kitaevMajoranaE1, kitaevMajoranaE2, chiralGrading,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem apply_chiralGrading (v : BdGSpinor A) :
    applyBdGBlock chiralGrading v 0 = v 0 ∧
      applyBdGBlock chiralGrading v 1 = -v 1 := by
  constructor <;> simp [applyBdGBlock, chiralGrading]

end InfoGeometry.Physics
