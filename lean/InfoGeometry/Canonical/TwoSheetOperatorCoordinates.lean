import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetOperatorCoordinates

abbrev M3C := InfoGeometry.Algebra.FiniteSpin.Mat3C
abbrev M6C := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ

abbrev OperatorBlocks := M3C × M3C × M3C × M3C

def blockLinearMap : M6C →ₗ[ℂ] OperatorBlocks where
  toFun A :=
    ( (fun i j => A (0, i) (0, j)),
      (fun i j => A (0, i) (1, j)),
      (fun i j => A (1, i) (0, j)),
      (fun i j => A (1, i) (1, j)) )
  map_add' A B := by
    ext s <;> simp [Matrix.add_apply]
  map_smul' c A := by
    ext s <;> simp [Matrix.smul_apply]

def blockLinearMapInv : OperatorBlocks →ₗ[ℂ] M6C where
  toFun b := fun s t =>
    match s.1, t.1 with
    | 0, 0 => b.1 s.2 t.2
    | 0, 1 => b.2.1 s.2 t.2
    | 1, 0 => b.2.2.1 s.2 t.2
    | 1, 1 => b.2.2.2 s.2 t.2
  map_add' A B := by
    ext s t
    rcases s with ⟨s, i⟩
    rcases t with ⟨t, j⟩
    fin_cases s <;> fin_cases t <;> simp [Matrix.add_apply]
  map_smul' c A := by
    ext s t
    rcases s with ⟨s, i⟩
    rcases t with ⟨t, j⟩
    fin_cases s <;> fin_cases t <;> simp [Matrix.smul_apply]

@[simp] theorem blockLinearMapInv_apply (b : OperatorBlocks) (s t : Fin 2 × Fin 3) :
    blockLinearMapInv b s t =
      match s.1, t.1 with
      | 0, 0 => b.1 s.2 t.2
      | 0, 1 => b.2.1 s.2 t.2
      | 1, 0 => b.2.2.1 s.2 t.2
      | 1, 1 => b.2.2.2 s.2 t.2 := rfl

theorem blockLinearMapInv_blockLinearMap (A : M6C) :
    blockLinearMapInv (blockLinearMap A) = A := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  fin_cases s <;> fin_cases t <;> rfl

theorem blockLinearMap_blockLinearMapInv (b : OperatorBlocks) :
    blockLinearMap (blockLinearMapInv b) = b := by
  rcases b with ⟨A, B, C, D⟩
  apply Prod.ext
  · ext i j
    rfl
  · apply Prod.ext
    · ext i j
      rfl
    · apply Prod.ext
      · ext i j
        rfl
      · ext i j
        rfl

def blockLinearEquiv : M6C ≃ₗ[ℂ] OperatorBlocks where
  toLinearMap := blockLinearMap
  invFun := blockLinearMapInv
  left_inv := blockLinearMapInv_blockLinearMap
  right_inv := blockLinearMap_blockLinearMapInv

@[simp] theorem blockLinearEquiv_apply (A : M6C) :
    blockLinearEquiv A = blockLinearMap A := rfl

@[simp] theorem blockLinearEquiv_symm_apply (b : OperatorBlocks) :
    blockLinearEquiv.symm b = blockLinearMapInv b := rfl

end InfoGeometry.Canonical.TwoSheetOperatorCoordinates
