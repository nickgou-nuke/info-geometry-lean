/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel

/-!
# Sector projectors and charge selection

These are occupation/charge sectors, not angular momentum tensor ranks.
Physical spatial parity can use the same theorem only after its actual
operator and intertwining law have been supplied.
-/

noncomputable section
namespace InfoGeometry.Physics.NuclearSectorSelection
open Matrix
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Orthogonal coordinate projector onto one value of a diagonal charge. -/
def sectorProjector (charge : ι → ℝ) (a : ℝ) : Matrix ι ι ℝ :=
  diagonal (fun i => if charge i = a then 1 else 0)

theorem sectorProjector_idempotent (charge : ι → ℝ) (a : ℝ) :
    sectorProjector charge a * sectorProjector charge a = sectorProjector charge a := by
  simp only [sectorProjector, diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

omit [Fintype ι] in
theorem sectorProjector_transpose (charge : ι → ℝ) (a : ℝ) :
    (sectorProjector charge a)ᵀ = sectorProjector charge a := by
  simp [sectorProjector]

theorem sectorProjector_disjoint (charge : ι → ℝ) (a b : ℝ) (hab : a ≠ b) :
    sectorProjector charge a * sectorProjector charge b = 0 := by
  simp only [sectorProjector, diagonal_mul_diagonal]
  have hz : (fun i => (if charge i = a then (1 : ℝ) else 0) *
      (if charge i = b then (1 : ℝ) else 0)) = 0 := by
    funext i
    by_cases ha : charge i = a
    · rw [if_pos ha, if_neg (fun hb => hab (ha.symm.trans hb))]
      norm_num
    · rw [if_neg ha]
      simp
  rw [hz]
  simp

/-- A forbidden charge difference kills the entire transition block. -/
theorem sector_selection (charge : ι → ℝ) (O : Matrix ι ι ℝ) (a b k : ℝ)
    (hO : diagonal charge * O - O * diagonal charge = k • O)
    (hforbid : a - b ≠ k) :
    sectorProjector charge a * O * sectorProjector charge b = 0 := by
  ext i j
  by_cases ha : charge i = a <;> by_cases hb : charge j = b
  · have hij := congrArg (fun M : Matrix ι ι ℝ => M i j) hO
    simp [diagonal_mul, mul_diagonal, ha, hb] at hij
    have hz : (a - b - k) * O i j = 0 := by nlinarith [hij]
    have hne : a - b - k ≠ 0 := sub_ne_zero.mpr hforbid
    have ho := (mul_eq_zero.mp hz).resolve_left hne
    simp [sectorProjector, diagonal_mul, mul_diagonal, ha, hb, ho]
  all_goals simp [sectorProjector, diagonal_mul, mul_diagonal, ha, hb]

/-- The existing CAR grading has three state sectors and five operator differences. -/
def occupationCharge : Fin 4 → ℝ := ![-1, 0, 0, 1]

theorem grading_eq_charge : gradingOperator = diagonal occupationCharge := by
  rw [gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [occupationCharge, diagonal]

theorem occupation_sectors_complete :
    sectorProjector occupationCharge (-1) + sectorProjector occupationCharge 0 +
      sectorProjector occupationCharge 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sectorProjector, occupationCharge, diagonal]

theorem five_grade_sector_selection (O : M4R) (k : ℤ) (hO : HasGrade k O)
    (a b : ℝ) (hforbid : a - b ≠ (k : ℝ)) :
    sectorProjector occupationCharge a * O * sectorProjector occupationCharge b = 0 := by
  apply sector_selection occupationCharge O a b (k : ℝ) _ hforbid
  simpa [HasGrade, NuclearTwoModeFiveGradeLieModel.comm, grading_eq_charge] using hO

/-- The whole two-mode matrix algebra, not just its named generators, has no
nonzero homogeneous operator outside the five supported integer grades. -/
theorem five_grade_support (O : M4R) (k : ℤ) (hO : HasGrade k O)
    (houtside : k < -2 ∨ 2 < k) : O = 0 := by
  have hk : (k : ℝ) < -2 ∨ 2 < (k : ℝ) := by exact_mod_cast houtside
  have hb (i : Fin 4) : -1 ≤ occupationCharge i ∧ occupationCharge i ≤ 1 := by
    fin_cases i <;> norm_num [occupationCharge]
  ext i j
  have hi := hb i
  have hj := hb j
  have hforbid : occupationCharge i - occupationCharge j ≠ (k : ℝ) := by
    rcases hk with hk | hk <;> linarith
  have hz := congrArg (fun M : M4R => M i j)
    (five_grade_sector_selection O k hO (occupationCharge i) (occupationCharge j) hforbid)
  simpa [sectorProjector, diagonal_mul, mul_diagonal] using hz

/-- Necessary conditions for parity-even physical multipoles in doubled-spin notation.
This predicate does not manufacture a spherical tensor operator. -/
def parityEvenMultipoleAllowed (rank twoJi twoJf : ℕ) (sameParity : Bool) : Prop :=
  twoJi ≤ twoJf + 2 * rank ∧ twoJf ≤ twoJi + 2 * rank ∧
    2 * rank ≤ twoJi + twoJf ∧ twoJi % 2 = twoJf % 2 ∧ sameParity = true

/-- Both E2 and M1 preserve spatial parity; their angular ranks differ.
The 7/2 → 3/2 example is E2-compatible and M1-forbidden. -/
theorem sulfur37_rank_boundary :
    parityEvenMultipoleAllowed 2 7 3 true ∧ ¬ parityEvenMultipoleAllowed 1 7 3 true := by
  norm_num [parityEvenMultipoleAllowed]

end InfoGeometry.Physics.NuclearSectorSelection
