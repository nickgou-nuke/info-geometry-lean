import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace SarsRoadblock

abbrev RootA4 := {p : Fin 5 × Fin 5 // p.1 ≠ p.2}

def hAdjointCharge : Fin 5 → ℤ
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => -3
  | 4 => -3

def rootCentralizedByAdjointHiggs (r : RootA4) : Bool :=
  hAdjointCharge r.val.1 == hAdjointCharge r.val.2

def rootBrokenByAdjointHiggs (r : RootA4) : Bool :=
  hAdjointCharge r.val.1 != hAdjointCharge r.val.2

def A4RootCount : Nat := Fintype.card RootA4

def SMRootCount : Nat :=
  Finset.univ.filter (fun r => rootCentralizedByAdjointHiggs r = true) |>.card

def BrokenRootCount : Nat :=
  Finset.univ.filter (fun r => rootBrokenByAdjointHiggs r = true) |>.card

def SU5Rank : Nat := 4

def SU5AdjointDimension : Nat := SU5Rank + A4RootCount

def SMRank : Nat := 4

def SMAdjointDimension : Nat := SMRank + SMRootCount

def BrokenDimension : Nat := BrokenRootCount

def SarsFundamentalScalarDimension : Nat := 5 * 5

def ExteriorC5Dimension : Nat :=
  Finset.univ.sum (fun k : Fin 6 => Nat.choose 5 k)

def SO10AdjointDimension : Nat := 10 * (10 - 1) / 2

def Cl55Dimension : Nat := 2 ^ 10

def M32Dimension : Nat := 32 * 32

inductive Z2Parity where
  | even | odd
  deriving DecidableEq, Repr

def superBracketTarget : Z2Parity → Z2Parity → Z2Parity
  | Z2Parity.odd, Z2Parity.odd => Z2Parity.even
  | Z2Parity.even, Z2Parity.even => Z2Parity.even
  | _, _ => Z2Parity.odd

abbrev M16R := InfoGeometry.Algebra.FiniteSpin.Mat16R
abbrev M32SplitR := InfoGeometry.Algebra.FiniteSpin.Mat32SplitR

def Gamma32 : M32SplitR := !![(1 : M16R), 0; 0, -(1 : M16R)]

def blockTrace32 (A : M32SplitR) : ℝ := Matrix.trace (A 0 0) + Matrix.trace (A 1 1)

def superTrace32 (A : M32SplitR) : ℝ := blockTrace32 (Gamma32 * A)

@[simp] theorem Gamma32_sq : Gamma32 * Gamma32 = (1 : M32SplitR) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gamma32, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem blockTrace32_one : blockTrace32 (1 : M32SplitR) = 32 := by
  norm_num [blockTrace32, Matrix.trace]

@[simp] theorem blockTrace32_Gamma32 : blockTrace32 Gamma32 = 0 := by
  norm_num [blockTrace32, Gamma32, Matrix.trace]

@[simp] theorem superTrace32_one : superTrace32 (1 : M32SplitR) = 0 := by
  simp [superTrace32]

private def diagonalRootEquiv : {p : Fin 5 × Fin 5 // p.1 = p.2} ≃ Fin 5 where
  toFun p := p.val.1
  invFun i := ⟨(i, i), rfl⟩
  left_inv p := by
    rcases p with ⟨⟨i, j⟩, h⟩
    cases h
    rfl
  right_inv i := rfl

theorem a4_root_count_eq_20 : A4RootCount = 20 := by
  rw [A4RootCount, Fintype.card_subtype_compl (fun p : Fin 5 × Fin 5 => p.1 = p.2)]
  have hdiag : Fintype.card {p : Fin 5 × Fin 5 // p.1 = p.2} = 5 := by
    exact Fintype.card_congr diagonalRootEquiv
  rw [hdiag]
  norm_num

private lemma centralizedRoots_eq :
    (Finset.univ.filter (fun r : RootA4 => rootCentralizedByAdjointHiggs r = true)) =
      {⟨(((0 : Fin 5), (1 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((0 : Fin 5), (2 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((1 : Fin 5), (0 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((1 : Fin 5), (2 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((2 : Fin 5), (0 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((2 : Fin 5), (1 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((3 : Fin 5), (4 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((4 : Fin 5), (3 : Fin 5)) : Fin 5 × Fin 5), by simp⟩} := by
  ext r
  rcases r with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j <;> simp [rootCentralizedByAdjointHiggs, hAdjointCharge] at hij ⊢

private lemma brokenRoots_eq :
    (Finset.univ.filter (fun r : RootA4 => rootBrokenByAdjointHiggs r = true)) =
      {⟨(((0 : Fin 5), (3 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((0 : Fin 5), (4 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((1 : Fin 5), (3 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((1 : Fin 5), (4 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((2 : Fin 5), (3 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((2 : Fin 5), (4 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((3 : Fin 5), (0 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((3 : Fin 5), (1 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((3 : Fin 5), (2 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((4 : Fin 5), (0 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((4 : Fin 5), (1 : Fin 5)) : Fin 5 × Fin 5), by simp⟩,
       ⟨(((4 : Fin 5), (2 : Fin 5)) : Fin 5 × Fin 5), by simp⟩} := by
  ext r
  rcases r with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j <;> simp [rootBrokenByAdjointHiggs, hAdjointCharge] at hij ⊢

theorem sm_root_count_eq_8 : SMRootCount = 8 := by
  rw [SMRootCount, centralizedRoots_eq]
  simp

theorem broken_root_count_eq_12 : BrokenRootCount = 12 := by
  rw [BrokenRootCount, brokenRoots_eq]
  simp

theorem su5_adjoint_dimension_eq_24 : SU5AdjointDimension = 24 := by
  norm_num [SU5AdjointDimension, SU5Rank, a4_root_count_eq_20]

theorem sm_adjoint_dimension_eq_12 : SMAdjointDimension = 12 := by
  norm_num [SMAdjointDimension, SMRank, sm_root_count_eq_8]

theorem broken_dimension_eq_12 : BrokenDimension = 12 := by
  norm_num [BrokenDimension, broken_root_count_eq_12]

theorem sars_fundamental_scalar_dimension_eq_25 : SarsFundamentalScalarDimension = 25 := by
  norm_num [SarsFundamentalScalarDimension]

theorem sars_fundamental_scalar_not_adjoint :
    SarsFundamentalScalarDimension ≠ SU5AdjointDimension := by
  norm_num [SarsFundamentalScalarDimension, SU5AdjointDimension, SU5Rank, a4_root_count_eq_20]

theorem sars_dimension_gap_eq_1 :
    SarsFundamentalScalarDimension - SU5AdjointDimension = 1 := by
  norm_num [SarsFundamentalScalarDimension, SU5AdjointDimension, SU5Rank, a4_root_count_eq_20]

theorem exterior_c5_dimension_eq_32 : ExteriorC5Dimension = 32 := by
  rw [ExteriorC5Dimension]
  repeat rw [Fin.sum_univ_succ]
  norm_num [Nat.choose]

theorem so10_adjoint_dimension_eq_45 : SO10AdjointDimension = 45 := by
  norm_num [SO10AdjointDimension]

theorem cl55_matches_m32_dimension : Cl55Dimension = M32Dimension ∧ M32Dimension = 1024 := by
  norm_num [Cl55Dimension, M32Dimension]

theorem odd_odd_superbracket_target_even :
    superBracketTarget Z2Parity.odd Z2Parity.odd = Z2Parity.even := by
  rfl

end SarsRoadblock

end noncomputable section
