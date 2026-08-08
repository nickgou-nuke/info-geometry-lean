import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import InfoGeometry.Canonical.TwoSheetStokesCoordinates

noncomputable section

namespace InfoGeometry.Canonical.ChiralStokesPauliBasis

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetStokesCoordinates

abbrev SheetMatrix := Matrix (Fin 2) (Fin 2) ℂ

def sheetIdentity : SheetMatrix := !![(1 : ℂ), 0; 0, 1]

def sheetParity : SheetMatrix := !![(1 : ℂ), 0; 0, -1]

def sheetFlip : SheetMatrix := !![(0 : ℂ), 1; 1, 0]

def sheetPhase : SheetMatrix :=
  !![(0 : ℂ), -Complex.I; Complex.I, 0]

def sheetTensor (P : SheetMatrix) (A : M3C) : M6C :=
  fun (s, i) (t, j) => P s t * A i j

def assembleStokes (q : StokesQuad) : M6C :=
  blockLinearMapInv (stokesToBlocks q)

def pauliExpansion (q : StokesQuad) : M6C :=
  sheetTensor sheetIdentity q.1 +
    sheetTensor sheetParity q.2.2.2 +
    sheetTensor sheetFlip q.2.1 +
    sheetTensor sheetPhase q.2.2.1

def pauliEven (q : StokesQuad) : M6C :=
  sheetTensor sheetIdentity q.1 +
    sheetTensor sheetParity q.2.2.2

def pauliOdd (q : StokesQuad) : M6C :=
  sheetTensor sheetFlip q.2.1 +
    sheetTensor sheetPhase q.2.2.1

def sheetGradeSign : Fin 2 → ℂ
  | 0 => 1
  | 1 => -1

def gradeConjugate (A : M6C) : M6C :=
  fun (s, i) (t, j) => sheetGradeSign s * sheetGradeSign t * A (s, i) (t, j)

theorem gradeConjugate_involutive (A : M6C) :
    gradeConjugate (gradeConjugate A) = A := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  fin_cases s <;> fin_cases t <;>
    simp [gradeConjugate, sheetGradeSign]

theorem gradeConjugate_mul (A B : M6C) :
    gradeConjugate (A * B) = gradeConjugate A * gradeConjugate B := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  simp only [gradeConjugate, Matrix.mul_apply]
  calc
    _ = ∑ x : Fin 2 × Fin 3,
        (sheetGradeSign s * sheetGradeSign t) *
          (A (s, i) x * B x (t, j)) := by
      exact (Finset.mul_sum Finset.univ
        (fun x : Fin 2 × Fin 3 => A (s, i) x * B x (t, j))
        (sheetGradeSign s * sheetGradeSign t))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases x with ⟨xs, xi⟩
      fin_cases xs <;> simp [sheetGradeSign] <;> ring

theorem gradeConjugate_add (A B : M6C) :
    gradeConjugate (A + B) = gradeConjugate A + gradeConjugate B := by
  ext s t
  simp [gradeConjugate, Matrix.add_apply, mul_add]

theorem gradeConjugate_smul (c : ℂ) (A : M6C) :
    gradeConjugate (c • A) = c • gradeConjugate A := by
  ext s t
  simp [gradeConjugate, Matrix.smul_apply, smul_eq_mul]
  ring

theorem gradeConjugate_one :
    gradeConjugate (1 : M6C) = 1 := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  fin_cases s <;> fin_cases t <;>
    simp [gradeConjugate, sheetGradeSign, Matrix.one_apply]

noncomputable def gradeConjugateAlgEquiv : M6C ≃ₐ[ℂ] M6C where
  toFun := gradeConjugate
  invFun := gradeConjugate
  left_inv := gradeConjugate_involutive
  right_inv := gradeConjugate_involutive
  map_add' := gradeConjugate_add
  map_mul' := gradeConjugate_mul
  commutes' := by
    intro c
    ext s t
    rcases s with ⟨s, i⟩
    rcases t with ⟨t, j⟩
    fin_cases s <;> fin_cases t <;>
      simp [gradeConjugate, sheetGradeSign, Algebra.smul_def,
        Matrix.algebraMap_matrix_apply, Matrix.one_apply]

theorem assembleStokes_eq_block_reconstruction (q : StokesQuad) :
    assembleStokes q = blockLinearMapInv (stokesToBlocks q) := rfl

theorem assembleStokes_eq_pauli_expansion (q : StokesQuad) :
    assembleStokes q = pauliExpansion q := by
  rcases q with ⟨a0, a1, a2, a3⟩
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  fin_cases s <;> fin_cases t <;>
    simp [assembleStokes, pauliExpansion, sheetTensor, sheetIdentity,
      sheetParity, sheetFlip, sheetPhase, stokesToBlocks,
      blockLinearMapInv, Matrix.add_apply] <;>
    ring

theorem pauliExpansion_eq_even_add_odd (q : StokesQuad) :
    pauliExpansion q = pauliEven q + pauliOdd q := by
  rcases q with ⟨a0, a1, a2, a3⟩
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  fin_cases s <;> fin_cases t <;>
    simp [pauliExpansion, pauliEven, pauliOdd, sheetTensor,
      sheetIdentity, sheetParity, sheetFlip, sheetPhase,
      Matrix.add_apply] <;> ring

theorem gradeConjugate_pauliEven (q : StokesQuad) :
    gradeConjugate (pauliEven q) = pauliEven q := by
  rcases q with ⟨a0, a1, a2, a3⟩
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  fin_cases s <;> fin_cases t <;>
    simp [gradeConjugate, pauliEven, sheetTensor, sheetIdentity,
      sheetParity, sheetGradeSign, Matrix.add_apply] <;>
    ring

theorem gradeConjugate_pauliOdd (q : StokesQuad) :
    gradeConjugate (pauliOdd q) = -(pauliOdd q) := by
  rcases q with ⟨a0, a1, a2, a3⟩
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  fin_cases s <;> fin_cases t <;>
    simp [gradeConjugate, pauliOdd, sheetTensor, sheetFlip, sheetPhase,
      sheetGradeSign, Matrix.add_apply] <;>
    ring

theorem gradeConjugate_pauliExpansion (q : StokesQuad) :
    gradeConjugate (pauliExpansion q) =
      pauliEven q - pauliOdd q := by
  rw [show pauliExpansion q = pauliEven q + pauliOdd q by
    exact (pauliExpansion_eq_even_add_odd q)]
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  fin_cases s <;> fin_cases t <;>
    simp [gradeConjugate, pauliEven, pauliOdd, sheetTensor, sheetIdentity,
      sheetParity, sheetFlip, sheetPhase, sheetGradeSign, Matrix.add_apply] <;>
    ring

end InfoGeometry.Canonical.ChiralStokesPauliBasis
