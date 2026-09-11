import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Omega.Zeta.XiChainInteriorIncidenceAlgebraMobiusInversion
import InfoGeometry.Neurosymbolic.BornNMFEngine

namespace InfoGeometry.Unified.UnifiedInversionMatrix

open Matrix
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

def conformalInversionMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; 1, 0]

theorem conformalInversionMatrix_sq :
    conformalInversionMatrix * conformalInversionMatrix =
      -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conformalInversionMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem conformalInversionMatrix_mul_neg :
    conformalInversionMatrix * (-conformalInversionMatrix) = 1 := by
  rw [mul_neg, conformalInversionMatrix_sq]
  simp

theorem neg_conformalInversionMatrix_mul :
    (-conformalInversionMatrix) * conformalInversionMatrix = 1 := by
  rw [neg_mul, conformalInversionMatrix_sq]
  simp

def conformalInversionUnit : (Matrix (Fin 2) (Fin 2) ℝ)ˣ where
  val := conformalInversionMatrix
  inv := -conformalInversionMatrix
  val_inv := conformalInversionMatrix_mul_neg
  inv_val := neg_conformalInversionMatrix_mul

theorem arithmeticInversion_identity :
    (μ * (zeta : ArithmeticFunction ℤ)) = 1 :=
  moebius_mul_coe_zeta

theorem arithmeticInversion_identity_right :
    ((zeta : ArithmeticFunction ℤ) * μ) = 1 :=
  coe_zeta_mul_coe_moebius

noncomputable def arithmeticMobiusUnit : (ArithmeticFunction ℤ)ˣ where
  val := μ
  inv := zeta
  val_inv := arithmeticInversion_identity
  inv_val := arithmeticInversion_identity_right

abbrev BooleanIndex (m : ℕ) := Finset (Fin m)

def booleanZetaMatrix (m : ℕ) : Matrix (BooleanIndex m) (BooleanIndex m) ℤ :=
  fun T S => if S ⊆ T then 1 else 0

def booleanMobiusMatrix (m : ℕ) : Matrix (BooleanIndex m) (BooleanIndex m) ℤ :=
  fun T S => Omega.Zeta.booleanIntervalSign S T

theorem booleanMobiusMatrix_mul_booleanZetaMatrix (m : ℕ) :
    booleanMobiusMatrix m * booleanZetaMatrix m = 1 := by
  classical
  ext T S
  rw [Matrix.mul_apply, Matrix.one_apply]
  let f : BooleanIndex m → ℤ := fun U => if U = S then 1 else 0
  let g : BooleanIndex m → ℤ := fun U => if S ⊆ U then 1 else 0
  have hfg : ∀ U, g U = Finset.sum U.powerset f := by
    intro U
    by_cases hSU : S ⊆ U
    · have hmem : S ∈ U.powerset := Finset.mem_powerset.mpr hSU
      simp [f, g, hSU, hmem]
    · have hnotmem : S ∉ U.powerset := by simpa using hSU
      simp [f, g, hSU, hnotmem]
  have hinv :=
    Omega.Zeta.paper_xi_chain_interior_incidence_algebra_mobius_inversion (m + 1)
  have hT :
      f T = Finset.sum T.powerset
        (fun U => Omega.Zeta.booleanIntervalSign U T * g U) := by
    simpa using hinv f g hfg T
  have hsum :
      (∑ U : BooleanIndex m, Omega.Zeta.booleanIntervalSign U T * g U) =
        Finset.sum T.powerset
          (fun U => Omega.Zeta.booleanIntervalSign U T * g U) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro U _ hU
    have hnot : ¬ U ⊆ T := by
      simpa [Finset.mem_powerset] using hU
    simp [Omega.Zeta.booleanIntervalSign, hnot]
  change
    (∑ U : BooleanIndex m,
      Omega.Zeta.booleanIntervalSign U T * (if S ⊆ U then 1 else 0)) = _
  calc
    (∑ U : BooleanIndex m,
        Omega.Zeta.booleanIntervalSign U T * (if S ⊆ U then 1 else 0)) =
        ∑ U : BooleanIndex m, Omega.Zeta.booleanIntervalSign U T * g U := by
          rfl
    _ = Finset.sum T.powerset
          (fun U => Omega.Zeta.booleanIntervalSign U T * g U) := hsum
    _ = f T := hT.symm
    _ = if T = S then 1 else 0 := by rfl

theorem booleanZetaMatrix_mul_booleanMobiusMatrix (m : ℕ) :
    booleanZetaMatrix m * booleanMobiusMatrix m = 1 :=
  mul_eq_one_comm.mp (booleanMobiusMatrix_mul_booleanZetaMatrix m)

noncomputable def booleanIncidenceUnit (m : ℕ) :
    (Matrix (BooleanIndex m) (BooleanIndex m) ℤ)ˣ where
  val := booleanMobiusMatrix m
  inv := booleanZetaMatrix m
  val_inv := booleanMobiusMatrix_mul_booleanZetaMatrix m
  inv_val := booleanZetaMatrix_mul_booleanMobiusMatrix m

/-- 
THE POSET-ARROW BRIDGE:
Proves that the Zeta matrix ζ(x,y) of any finite poset P is a strictly 
non-negative matrix (MatrixNonneg), rendering it an admissible 
transition operator W for the Born-NMF Neurosymbolic Engine.
-/
theorem poset_zeta_is_matrix_nonneg {α : Type*} [Fintype α] [DecidableEq α] [Preorder α]
    [DecidableRel (· ≤ · : α → α → Prop)] :
    InfoGeometry.Neurosymbolic.BornNMFEngine.MatrixNonneg (fun (x y : α) => if x ≤ y then (1 : ℝ) else 0) := by
  intro i j
  dsimp [InfoGeometry.Neurosymbolic.BornNMFEngine.MatrixNonneg]
  split_ifs
  · exact zero_le_one
  · exact le_refl 0

end InfoGeometry.Unified.UnifiedInversionMatrix
