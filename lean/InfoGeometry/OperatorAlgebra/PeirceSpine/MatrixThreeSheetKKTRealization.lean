/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTitsFiveGradedClosurePoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Three-sheet matrix realization of the five Peirce-KKT grades

The matrix unit `E₁₂` and its adjoint `E₂₁` generate two supported sheets
inside `Matrix (Fin 3) (Fin 3) B`. The third matrix coordinate is the genuine
transverse corner, so this model realizes all five Peirce grades over an
arbitrary, possibly noncommutative coefficient ring.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization

open OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset (P Q)

variable {B : Type*} [Ring B] [StarRing B]

/-- A rank-one matrix cut used to realize the Peirce archetypes inside the
three-sheet operator algebra. -/
def archetypeCut3 : Matrix (Fin 3) (Fin 3) B :=
  !![1, 0, 0; 0, 0, 0; 0, 0, 0]

omit [StarRing B] in
theorem archetypeCut3_idempotent :
    archetypeCut3 (B := B) * archetypeCut3 = archetypeCut3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [archetypeCut3, Matrix.mul_apply, Fin.sum_univ_succ]

omit [StarRing B] in
/-- Matrix coordinates of the four Peirce corners for an arbitrary operator.
The entries remain in their original order; this is a genuine matrix-operator
decomposition, not a commutative coefficient calculation. -/
theorem archetype_fourfold_matrix_coordinates
    (X : Matrix (Fin 3) (Fin 3) B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (archetypeCut3 (B := B)) X =
      !![X 0 0, 0, 0; 0, 0, 0; 0, 0, 0] ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 (archetypeCut3 (B := B)) X =
      !![0, 0, 0; 0, X 1 1, X 1 2; 0, X 2 1, X 2 2] ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (archetypeCut3 (B := B)) X =
      !![0, X 0 1, X 0 2; 0, 0, 0; 0, 0, 0] ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (archetypeCut3 (B := B)) X =
      !![0, 0, 0; X 1 0, 0, 0; X 2 0, 0, 0] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11,
        InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00,
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
        archetypeCut3, Matrix.mul_apply, Matrix.one_apply,
        Matrix.sub_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

omit [StarRing B] in
/-- The four matrix corners reconstruct every operator without exchanging
the order of any coefficient products. -/
theorem archetype_fourfold_partition (X : Matrix (Fin 3) (Fin 3) B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (archetypeCut3 (B := B)) X +
      InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 (archetypeCut3 (B := B)) X +
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (archetypeCut3 (B := B)) X +
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (archetypeCut3 (B := B)) X = X := by
  rcases archetype_fourfold_matrix_coordinates (B := B) X with ⟨h11, h00, h10, h01⟩
  rw [h11, h00, h10, h01]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [StarRing B] in
/-- The matrix Peirce grading separates the two diagonal corners from the two
off-diagonal transport corners. -/
theorem archetype_even_odd_matrix_partition
    (X : Matrix (Fin 3) (Fin 3) B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
        (archetypeCut3 (B := B)) X +
      InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade
        (archetypeCut3 (B := B)) X = X := by
  have h := archetype_fourfold_partition (B := B) X
  calc
    _ = InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11
          (archetypeCut3 (B := B)) X +
        InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00
          (archetypeCut3 (B := B)) X +
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus
          (archetypeCut3 (B := B)) X +
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus
          (archetypeCut3 (B := B)) X := by
      dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade,
        InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade,
        InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11,
        InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00,
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus]
      noncomm_ring
    _ = X := h

/-- The positive nilpotent matrix unit `E₁₂`. -/
def Nplus3 : Matrix (Fin 3) (Fin 3) B := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

/-- The negative nilpotent matrix unit `E₂₁`. -/
def Nminus3 : Matrix (Fin 3) (Fin 3) B := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

/-- The diagonal change-of-frame unit determined by three coefficient-ring
units. -/
def diagonalFrameUnit (u : Fin 3 → Bˣ) : Units (Matrix (Fin 3) (Fin 3) B) where
  val := Matrix.diagonal fun i => (u i : B)
  inv := Matrix.diagonal fun i => (((u i)⁻¹ : Bˣ) : B)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i
    simp

/-- The matrix entry formula for a true inner change of frame by a diagonal
operator unit. The left and right coefficient order is retained. -/
theorem diagonalFrameUnit_conjugate_apply
    (u : Fin 3 → Bˣ) (X : Matrix (Fin 3) (Fin 3) B) (i j : Fin 3) :
    let U : Units (Matrix (Fin 3) (Fin 3) B) := diagonalFrameUnit u
    ((U : Matrix (Fin 3) (Fin 3) B) * X * (↑(U⁻¹) : Matrix (Fin 3) (Fin 3) B)) i j =
      (u i : B) * X i j * (((u j)⁻¹ : Bˣ) : B) := by
  simp [diagonalFrameUnit, Matrix.mul_apply, Matrix.diagonal_apply]

theorem Nplus3_star : star (Nplus3 (B := B)) = Nminus3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Nplus3, Nminus3]

omit [StarRing B] in
/-- The two matrix-unit channels do not commute: their products occupy the
distinct first and second diagonal corners. -/
theorem Nplus3_mul_Nminus3_ne [Nontrivial B] :
    Nplus3 (B := B) * Nminus3 ≠ Nminus3 * Nplus3 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) B => M 0 0) h
  simp [Nplus3, Nminus3, Matrix.mul_apply, Fin.sum_univ_succ] at h00

omit [StarRing B] in
theorem Nplus3_sq_zero : Nplus3 (B := B) * Nplus3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nplus3, Matrix.mul_apply, Fin.sum_univ_succ]

theorem Nplus3_regular :
    Nplus3 (B := B) * star Nplus3 * Nplus3 = Nplus3 := by
  rw [Nplus3_star]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nplus3, Nminus3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- In this model the two sheet supports are `E₁₁` and `E₂₂`. -/
theorem Nplus3_sheets :
    P (Nplus3 (B := B)) = !![1, 0, 0; 0, 0, 0; 0, 0, 0] ∧
    Q (Nplus3 (B := B)) = !![0, 0, 0; 0, 1, 0; 0, 0, 0] := by
  constructor
  · change Nplus3 (B := B) * star Nplus3 = _
    rw [Nplus3_star]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Nplus3, Nminus3, Matrix.mul_apply, Fin.sum_univ_succ]
  · change star Nplus3 * Nplus3 (B := B) = _
    rw [Nplus3_star]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Nplus3, Nminus3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The anomaly square is the rank-two support `E₁₁ + E₂₂`. -/
theorem Nplus3_gap :
    Gap (Nplus3 (B := B)) = !![1, 0, 0; 0, 1, 0; 0, 0, 0] := by
  rw [← Phi_sq_eq_Gap (Nplus3 (B := B)) Nplus3_sq_zero Nplus3_regular]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Phi, Nplus3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_succ]

/-- The residual Peirce support is the nonzero transverse sheet `E₃₃`. -/
theorem Nplus3_peirceR :
    peirceR (Nplus3 (B := B)) = !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
  rw [peirceR, Nplus3_gap]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply]

/-- The five Peirce grade projections have the expected matrix-coordinate
locations: `E₁₂`; `E₁₃ + E₃₂`; the three diagonal entries; `E₃₁ + E₂₃`; `E₂₁`.
Every coefficient remains in its original order, so no commutativity of `B`
is used. -/
theorem five_grade_matrix_coordinates (X : Matrix (Fin 3) (Fin 3) B) :
    peirceGradePlus2 (Nplus3 (B := B)) X = !![0, X 0 1, 0; 0, 0, 0; 0, 0, 0] ∧
    peirceGradePlus1 (Nplus3 (B := B)) X = !![0, 0, X 0 2; 0, 0, 0; 0, X 2 1, 0] ∧
    peirceGradeZero (Nplus3 (B := B)) X =
      !![X 0 0, 0, 0; 0, X 1 1, 0; 0, 0, X 2 2] ∧
    peirceGradeMinus1 (Nplus3 (B := B)) X = !![0, 0, 0; 0, 0, X 1 2; X 2 0, 0, 0] ∧
    peirceGradeMinus2 (Nplus3 (B := B)) X = !![0, 0, 0; X 1 0, 0, 0; 0, 0, 0] := by
  have hSheets := Nplus3_sheets (B := B)
  have hR := Nplus3_peirceR (B := B)
  constructor
  · rw [peirceGradePlus2, peircePQ, hSheets.1, hSheets.2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  constructor
  · rw [peirceGradePlus1, peircePR, peirceRQ, hSheets.1, hSheets.2, hR]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  constructor
  · rw [peirceGradeZero, peircePP, peirceQQ, peirceRR,
      hSheets.1, hSheets.2, hR]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  constructor
  · rw [peirceGradeMinus1, peirceRP, peirceQR, hSheets.1, hSheets.2, hR]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  · rw [peirceGradeMinus2, peirceQP, hSheets.1, hSheets.2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

/-- The five matrix-coordinate sectors reconstruct every operator.  This is
the explicit 3-sheet matrix form of the abstract Peirce five-grade
decomposition; no coefficient factors are commuted or reordered. -/
theorem five_grade_matrix_reconstruction (X : Matrix (Fin 3) (Fin 3) B) :
    peirceGradePlus2 (Nplus3 (B := B)) X +
      peirceGradePlus1 (Nplus3 (B := B)) X +
      peirceGradeZero (Nplus3 (B := B)) X +
      peirceGradeMinus1 (Nplus3 (B := B)) X +
      peirceGradeMinus2 (Nplus3 (B := B)) X = X := by
  rcases five_grade_matrix_coordinates (B := B) X with
    ⟨h₂, h₁, h₀, hm1, hm2⟩
  rw [h₂, h₁, h₀, hm1, hm2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The grade `+1` commutator closes in grade `+2`.  In coordinates, its
coefficient is the ordered difference `X₀₂ Y₂₁ - Y₀₂ X₂₁`; no commutativity
of the coefficient ring is assumed. -/
theorem plus1_bracket_matrix_coordinates (X Y : Matrix (Fin 3) (Fin 3) B) :
    comm (peirceGradePlus1 (Nplus3 (B := B)) X)
      (peirceGradePlus1 (Nplus3 (B := B)) Y) =
      !![0, X 0 2 * Y 2 1 - Y 0 2 * X 2 1, 0;
        0, 0, 0;
        0, 0, 0] := by
  have hX := five_grade_matrix_coordinates (B := B) X
  have hY := five_grade_matrix_coordinates (B := B) Y
  rw [hX.2.1, hY.2.1]
  dsimp [comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The grade `-1` commutator closes in grade `-2`, with the coefficient
order retained as `X₁₂ Y₂₀ - Y₁₂ X₂₀`. -/
theorem minus1_bracket_matrix_coordinates (X Y : Matrix (Fin 3) (Fin 3) B) :
    comm (peirceGradeMinus1 (Nplus3 (B := B)) X)
      (peirceGradeMinus1 (Nplus3 (B := B)) Y) =
      !![0, 0, 0;
        X 1 2 * Y 2 0 - Y 1 2 * X 2 0, 0, 0;
        0, 0, 0] := by
  have hX := five_grade_matrix_coordinates (B := B) X
  have hY := five_grade_matrix_coordinates (B := B) Y
  rw [hX.2.2.2.1, hY.2.2.2.1]
  dsimp [comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The neutral diagonal acts on the two coordinates of grade `+1` by
ordered left-minus-right multiplication, preserving coefficient order over
an arbitrary ring. -/
theorem zero_plus1_bracket_matrix_coordinates
    (X Y : Matrix (Fin 3) (Fin 3) B) :
    comm (peirceGradeZero (Nplus3 (B := B)) X)
      (peirceGradePlus1 (Nplus3 (B := B)) Y) =
      !![0, 0, X 0 0 * Y 0 2 - Y 0 2 * X 2 2;
        0, 0, 0;
        0, X 2 2 * Y 2 1 - Y 2 1 * X 1 1, 0] := by
  have hX := five_grade_matrix_coordinates (B := B) X
  have hY := five_grade_matrix_coordinates (B := B) Y
  rw [hX.2.2.1, hY.2.1]
  dsimp [comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The neutral diagonal acts on the two coordinates of grade `-1` by the
same ordered left-minus-right rule on their incident sheets. -/
theorem zero_minus1_bracket_matrix_coordinates
    (X Y : Matrix (Fin 3) (Fin 3) B) :
    comm (peirceGradeZero (Nplus3 (B := B)) X)
      (peirceGradeMinus1 (Nplus3 (B := B)) Y) =
      !![0, 0, 0;
        0, 0, X 1 1 * Y 1 2 - Y 1 2 * X 2 2;
        X 2 2 * Y 2 0 - Y 2 0 * X 0 0, 0, 0] := by
  have hX := five_grade_matrix_coordinates (B := B) X
  have hY := five_grade_matrix_coordinates (B := B) Y
  rw [hX.2.2.1, hY.2.2.2.1]
  dsimp [comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The mixed `(+1,-1)` bracket is a neutral diagonal operator. Its three
entries retain the noncommutative product order, giving the concrete
three-sheet readback of the abstract degree-zero KKT interaction. -/
theorem plus1_minus1_bracket_matrix_coordinates
    (X Y : Matrix (Fin 3) (Fin 3) B) :
    comm (peirceGradePlus1 (Nplus3 (B := B)) X)
      (peirceGradeMinus1 (Nplus3 (B := B)) Y) =
      !![X 0 2 * Y 2 0, 0, 0;
        0, -(Y 1 2 * X 2 1), 0;
        0, 0, X 2 1 * Y 1 2 - Y 2 0 * X 0 2] := by
  have hX := five_grade_matrix_coordinates (B := B) X
  have hY := five_grade_matrix_coordinates (B := B) Y
  rw [hX.2.1, hY.2.2.2.1]
  dsimp [comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The zero-grade Peirce projection fixes every diagonal operator in the
three-sheet matrix model. -/
theorem peirceGradeZero_diagonal_matrix (a b c : B) :
    peirceGradeZero (Nplus3 (B := B))
      (!![a, 0, 0; 0, b, 0; 0, 0, c]) =
      !![a, 0, 0; 0, b, 0; 0, 0, c] := by
  have h := five_grade_matrix_coordinates (B := B)
    (!![a, 0, 0; 0, b, 0; 0, 0, c])
  rw [h.2.2.1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The mixed `(+1,-1)` bracket is fixed by the zero-grade Peirce projection,
so the explicit coordinate interaction is genuinely closed in the neutral
sector, not merely diagonal-looking. -/
theorem plus1_minus1_bracket_eq_gradeZero
    (X Y : Matrix (Fin 3) (Fin 3) B) :
    peirceGradeZero (Nplus3 (B := B))
      (comm (peirceGradePlus1 (Nplus3 (B := B)) X)
        (peirceGradeMinus1 (Nplus3 (B := B)) Y)) =
      comm (peirceGradePlus1 (Nplus3 (B := B)) X)
        (peirceGradeMinus1 (Nplus3 (B := B)) Y) := by
  simp only [plus1_minus1_bracket_matrix_coordinates]
  exact peirceGradeZero_diagonal_matrix
    (X 0 2 * Y 2 0) (-(Y 1 2 * X 2 1))
    (X 2 1 * Y 1 2 - Y 2 0 * X 0 2)

/-- The neutral diagonal acts on the positive extremal coordinate by the
ordered left-minus-right coefficient action. This is the concrete
`[G₀,G₊₂] → G₊₂` interaction, retaining noncommutative multiplication order. -/
theorem zero_plus2_bracket_matrix_coordinates
    (X Y : Matrix (Fin 3) (Fin 3) B) :
    comm (peirceGradeZero (Nplus3 (B := B)) X)
      (peirceGradePlus2 (Nplus3 (B := B)) Y) =
      !![0, X 0 0 * Y 0 1 - Y 0 1 * X 1 1, 0;
        0, 0, 0;
        0, 0, 0] := by
  have hX := five_grade_matrix_coordinates (B := B) X
  have hY := five_grade_matrix_coordinates (B := B) Y
  rw [hX.2.2.1, hY.1]
  dsimp [comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The neutral diagonal acts on the negative extremal coordinate by the
ordered left-minus-right coefficient action. This is the concrete
`[G₀,G₋₂] → G₋₂` interaction, retaining noncommutative multiplication order. -/
theorem zero_minus2_bracket_matrix_coordinates
    (X Y : Matrix (Fin 3) (Fin 3) B) :
    comm (peirceGradeZero (Nplus3 (B := B)) X)
      (peirceGradeMinus2 (Nplus3 (B := B)) Y) =
      !![0, 0, 0;
        X 1 1 * Y 1 0 - Y 1 0 * X 0 0, 0, 0;
        0, 0, 0] := by
  have hX := five_grade_matrix_coordinates (B := B) X
  have hY := five_grade_matrix_coordinates (B := B) Y
  rw [hX.2.2.1, hY.2.2.2.2]
  dsimp [comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [StarRing B] in
/-- The left-minus-right action of neutral diagonal operators on the extremal
`(0,1)` block is a Lie representation. The two diagonal entries act on
opposite sides, and the displayed order is valid over a noncommutative
coefficient ring. -/
theorem zero_plus2_block_action_lie_law (x₀ x₁ y₀ y₁ r : B) :
    (x₀ * (y₀ * r - r * y₁) - (y₀ * r - r * y₁) * x₁) -
        (y₀ * (x₀ * r - r * x₁) - (x₀ * r - r * x₁) * y₁) =
      (x₀ * y₀ - y₀ * x₀) * r - r * (x₁ * y₁ - y₁ * x₁) := by
  noncomm_ring

/-- Opposite extremal grades bracket to a diagonal operator with the two
ordered corner products on its diagonal. -/
theorem plus2_minus2_bracket_matrix_coordinates
    (X Y : Matrix (Fin 3) (Fin 3) B) :
    comm (peirceGradePlus2 (Nplus3 (B := B)) X)
      (peirceGradeMinus2 (Nplus3 (B := B)) Y) =
      !![X 0 1 * Y 1 0, 0, 0;
        0, -(Y 1 0 * X 0 1), 0;
        0, 0, 0] := by
  have hX := five_grade_matrix_coordinates (B := B) X
  have hY := five_grade_matrix_coordinates (B := B) Y
  rw [hX.1, hY.2.2.2.2]
  dsimp [comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The concrete extremal bracket is fixed by the zero-grade Peirce
projection, realizing the abstract `(+2,-2) → 0` closure in three-sheet
coordinates over an arbitrary coefficient ring. -/
theorem plus2_minus2_bracket_eq_gradeZero
    (X Y : Matrix (Fin 3) (Fin 3) B) :
    peirceGradeZero (Nplus3 (B := B))
      (comm (peirceGradePlus2 (Nplus3 (B := B)) X)
        (peirceGradeMinus2 (Nplus3 (B := B)) Y)) =
      comm (peirceGradePlus2 (Nplus3 (B := B)) X)
        (peirceGradeMinus2 (Nplus3 (B := B)) Y) := by
  simp only [plus2_minus2_bracket_matrix_coordinates]
  exact peirceGradeZero_diagonal_matrix
    (X 0 1 * Y 1 0) (-(Y 1 0 * X 0 1)) 0

/-- The `(+2,+1)` bracket vanishes: the three-sheet matrix model has no
coordinate support in degree `+3`. -/
theorem plus2_plus1_bracket_eq_zero (X Y : Matrix (Fin 3) (Fin 3) B) :
    comm (peirceGradePlus2 (Nplus3 (B := B)) X)
      (peirceGradePlus1 (Nplus3 (B := B)) Y) = 0 := by
  have hX := five_grade_matrix_coordinates (B := B) X
  have hY := five_grade_matrix_coordinates (B := B) Y
  rw [hX.1, hY.2.1]
  dsimp [comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The `(-2,-1)` bracket vanishes: the three-sheet matrix model has no
coordinate support in degree `-3`. -/
theorem minus2_minus1_bracket_eq_zero (X Y : Matrix (Fin 3) (Fin 3) B) :
    comm (peirceGradeMinus2 (Nplus3 (B := B)) X)
      (peirceGradeMinus1 (Nplus3 (B := B)) Y) = 0 := by
  have hX := five_grade_matrix_coordinates (B := B) X
  have hY := five_grade_matrix_coordinates (B := B) Y
  rw [hX.2.2.2.2, hY.2.2.2.1]
  dsimp [comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The coefficient `E₀₁` in `M₂(ℤ)`. -/
def noncommCoeffE01 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- The coefficient `E₁₀` in `M₂(ℤ)`. -/
def noncommCoeffE10 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- Two grade-`+1` elements in `M₃(M₂(ℤ))` with matrix-unit coefficients in
both grade-one corners. -/
def nestedPlus1X : Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) ℤ) :=
  !![0, 0, noncommCoeffE01; 0, 0, 0; 0, noncommCoeffE01, 0]

/-- The second nested-matrix grade-`+1` element, with the opposite
coefficient matrix unit. -/
def nestedPlus1Y : Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) ℤ) :=
  !![0, 0, noncommCoeffE10; 0, 0, 0; 0, noncommCoeffE10, 0]

/-- In the genuinely noncommutative operator algebra `M₃(M₂(ℤ))`, the
grade-`+1` bracket is nonzero. Its `(0,1)` coefficient is
`E₀₁E₁₀ - E₁₀E₀₁ = E₀₀ - E₁₁`, witnessing the order sensitivity of the
general coordinate formula. -/
theorem nested_matrix_plus1_bracket_ne_zero :
    comm (peirceGradePlus1 (Nplus3 (B := Matrix (Fin 2) (Fin 2) ℤ)) nestedPlus1X)
      (peirceGradePlus1 (Nplus3 (B := Matrix (Fin 2) (Fin 2) ℤ)) nestedPlus1Y) ≠ 0 := by
  have h := plus1_bracket_matrix_coordinates (B := Matrix (Fin 2) (Fin 2) ℤ) nestedPlus1X nestedPlus1Y
  rw [h]
  intro h₁
  have hEntry := congrArg
    (fun M : Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) ℤ) => M 0 1) h₁
  have hCoeff := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hEntry
  have hone : (1 : ℤ) = 0 := by
    simpa [nestedPlus1X, nestedPlus1Y, noncommCoeffE01, noncommCoeffE10,
      Matrix.mul_apply, Fin.sum_univ_succ] using hCoeff
  exact Int.one_ne_zero hone

/-- The coefficient matrix units are genuinely noncommuting in `M₂(ℤ)`. -/
theorem noncomm_coeff_matrix_units :
    noncommCoeffE01 * noncommCoeffE10 ≠ noncommCoeffE10 * noncommCoeffE01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  norm_num [noncommCoeffE01, noncommCoeffE10, Matrix.mul_apply,
    Fin.sum_univ_two] at h00

/-- The nested operator witness also distinguishes the two ordered associative
products in `M₃(M₂(ℤ))`; the previously proved nonzero Peirce bracket gives
the contradiction directly. -/
theorem nested_matrix_products_ne :
    nestedPlus1X * nestedPlus1Y ≠ nestedPlus1Y * nestedPlus1X := by
  intro h
  have h01 := congrArg
    (fun M : Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) ℤ) => M 0 1) h
  have hCoeff : noncommCoeffE01 * noncommCoeffE10 =
      noncommCoeffE10 * noncommCoeffE01 := by
    simpa [nestedPlus1X, nestedPlus1Y, Matrix.mul_apply,
      Fin.sum_univ_succ] using h01
  exact noncomm_coeff_matrix_units hCoeff

omit [StarRing B] in
private theorem matrix_nat_smul_apply (n : ℕ) (X : Matrix (Fin 3) (Fin 3) B)
    (i j : Fin 3) : (n • X) i j = n • X i j := by
  simpa using
    (map_nsmul ((AddMonoidHom.eval j).comp (AddMonoidHom.eval i)) n X)

/-! **KKT Euler Five-Grading on the Three-Sheet Matrix Model.**
The grade matrix `grade3Matrix = !![0, 2, 1; -2, 0, -1; -1, 1, 0]` assigns
eigen-values $(0, ±1, ±2)$ to the five Peirce grades realized in this matrix model:
- Grade $+2$: position $(0,1)$, eigen-value $+2$
- Grade $+1$: positions $(0,2), (2,1)$, eigen-value $+1$
- Grade $0$: diagonal $(0,0), (1,1), (2,2)$, eigen-value $0$
- Grade $-1$: positions $(1,2), (2,0)$, eigen-value $-1$
- Grade $-2$: position $(1,0)$, eigen-value $-2$

This is the explicit $3×3$ matrix form of the Euler 5-grading from
`AlbertCayleyDickson.opEulerFiveGrading`, with eigen-values matching the
KKT degrees $(\mathcal{G}_{-2}, \mathcal{G}_{-1}, \mathcal{G}_0, \mathcal{G}_{+1}, \mathcal{G}_{+2})$.
The degree-5 minimal polynomial $\mathcal{E}^5 - 5\mathcal{E}^3 + 4\mathcal{E} = 0$
holds because each eigen-value $g \in \{0, ±1, ±2\}$ satisfies $g(g²-1)(g²-4) = 0$. -/

def grade3Matrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 2, 1; -2, 0, -1; -1, 1, 0]

def eulerFiveGrading3 (X : Matrix (Fin 3) (Fin 3) B) : Matrix (Fin 3) (Fin 3) B :=
  fun i j => (grade3Matrix i j : B) * X i j

/-- Inner conjugation by a diagonal operator unit is equivariant for the
intrinsic Euler five-grading. Hence it transports each of the five graded
operator sectors to itself. -/
theorem eulerFiveGrading3_diagonalConjugation
    (u : Fin 3 → Bˣ) (X : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 (((diagonalFrameUnit u : Matrix (Fin 3) (Fin 3) B) * X) *
      (↑((diagonalFrameUnit u)⁻¹) : Matrix (Fin 3) (Fin 3) B)) =
    ((diagonalFrameUnit u : Matrix (Fin 3) (Fin 3) B) * eulerFiveGrading3 X) *
      (↑((diagonalFrameUnit u)⁻¹) : Matrix (Fin 3) (Fin 3) B) := by
  ext i j
  change (grade3Matrix i j : B) *
      (((diagonalFrameUnit u : Matrix (Fin 3) (Fin 3) B) * X) *
        (↑((diagonalFrameUnit u)⁻¹) : Matrix (Fin 3) (Fin 3) B)) i j =
    (((diagonalFrameUnit u : Matrix (Fin 3) (Fin 3) B) * eulerFiveGrading3 X) *
      (↑((diagonalFrameUnit u)⁻¹) : Matrix (Fin 3) (Fin 3) B)) i j
  rw [diagonalFrameUnit_conjugate_apply u (eulerFiveGrading3 X) i j,
    diagonalFrameUnit_conjugate_apply u X i j]
  fin_cases i <;> fin_cases j <;>
    simp [eulerFiveGrading3, grade3Matrix] <;> noncomm_ring

/-- In the three-sheet matrix model, the Euler grading is exactly the
adjoint action of the anomaly `Σ = [N₊, N₊*]`. This identifies the entrywise
degree table with the intrinsic commutator grading, including for
noncommutative coefficient rings. -/
theorem eulerFiveGrading3_eq_ad_sigma (X : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 X = comm (Sigma (Nplus3 (B := B))) X := by
  have hSigma : Sigma (Nplus3 (B := B)) =
      !![(1 : B), 0, 0; 0, -1, 0; 0, 0, 0] := by
    change Nplus3 * star Nplus3 - star Nplus3 * Nplus3 = _
    rw [Nplus3_star]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Nplus3, Nminus3, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hSigma]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerFiveGrading3, grade3Matrix, comm,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Nplus3, Nminus3] <;> norm_num <;> noncomm_ring

/-- The matrix Euler grading is a derivation of the associative matrix
product. This follows from its `ad(Σ)` realization and holds on all matrices,
not only the positive or negative nilradicals. -/
theorem eulerFiveGrading3_mul_leibniz (X Y : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 (X * Y) =
      eulerFiveGrading3 X * Y + X * eulerFiveGrading3 Y := by
  rw [eulerFiveGrading3_eq_ad_sigma (X * Y),
    eulerFiveGrading3_eq_ad_sigma X, eulerFiveGrading3_eq_ad_sigma Y]
  dsimp [comm]
  noncomm_ring

theorem eulerFiveGrading3_gradePlus2 (X : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 (peirceGradePlus2 (Nplus3 (B := B)) X) =
      (2 : ℤ) • peirceGradePlus2 (Nplus3 (B := B)) X := by
  have h := five_grade_matrix_coordinates (B := B) X
  rw [h.1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerFiveGrading3, grade3Matrix,
      Fin.val_zero, Fin.val_one, Fin.val_two, smul_smul, mul_comm,
      one_mul, mul_one, zero_mul, mul_zero]
    <;> norm_num
    <;> abel

theorem eulerFiveGrading3_gradePlus1 (X : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 (peirceGradePlus1 (Nplus3 (B := B)) X) =
      (1 : ℤ) • peirceGradePlus1 (Nplus3 (B := B)) X := by
  have h := five_grade_matrix_coordinates (B := B) X
  rw [h.2.1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerFiveGrading3, grade3Matrix,
      Fin.val_zero, Fin.val_one, Fin.val_two, smul_smul, mul_comm,
      one_mul, mul_one, zero_mul, mul_zero]
    <;> norm_num
    <;> abel

theorem eulerFiveGrading3_gradeZero (X : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 (peirceGradeZero (Nplus3 (B := B)) X) = 0 := by
  have h := five_grade_matrix_coordinates (B := B) X
  rw [h.2.2.1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerFiveGrading3, grade3Matrix,
      Fin.val_zero, Fin.val_one, Fin.val_two, smul_smul, mul_comm,
      one_mul, mul_one, zero_mul, mul_zero]
    <;> norm_num
    <;> abel

theorem eulerFiveGrading3_gradeMinus1 (X : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 (peirceGradeMinus1 (Nplus3 (B := B)) X) =
      (-1 : ℤ) • peirceGradeMinus1 (Nplus3 (B := B)) X := by
  have h := five_grade_matrix_coordinates (B := B) X
  rw [h.2.2.2.1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerFiveGrading3, grade3Matrix,
      Fin.val_zero, Fin.val_one, Fin.val_two, smul_smul, mul_comm,
      one_mul, mul_one, zero_mul, mul_zero]
    <;> norm_num
    <;> abel

theorem eulerFiveGrading3_kkt_polynomial (X : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 (eulerFiveGrading3 (eulerFiveGrading3 (eulerFiveGrading3 (eulerFiveGrading3 X)))) -
      (5 : ℕ) • eulerFiveGrading3 (eulerFiveGrading3 (eulerFiveGrading3 X)) +
      (4 : ℕ) • eulerFiveGrading3 X = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply]
    rw [matrix_nat_smul_apply, matrix_nat_smul_apply]
    simp [eulerFiveGrading3, grade3Matrix, nsmul_eq_mul] <;> noncomm_ring

theorem eulerFiveGrading3_gradeMinus2 (X : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 (peirceGradeMinus2 (Nplus3 (B := B)) X) =
      (-2 : ℤ) • peirceGradeMinus2 (Nplus3 (B := B)) X := by
  have h := five_grade_matrix_coordinates (B := B) X
  rw [h.2.2.2.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerFiveGrading3, grade3Matrix,
      Fin.val_zero, Fin.val_one, Fin.val_two, smul_smul, mul_comm,
      one_mul, mul_one, zero_mul, mul_zero]
    <;> norm_num
    <;> abel

/-- The generic Jordan-associator KKT generator from
`KantorKoecherTitsFiveGradedClosurePoset` lands in the concrete grade `+2`
eigenspace of the three-sheet Euler action. This connects the abstract
associator construction to the matrix grading through the shared anomaly
commutator, without identifying their definitions by name alone. -/
theorem eulerFiveGrading3_K_plus2 (X : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 (K_plus2 (Nplus3 (B := B)) X) =
      (2 : ℕ) • K_plus2 (Nplus3 (B := B)) X := by
  rw [eulerFiveGrading3_eq_ad_sigma]
  have h := comm_Sigma_K_plus2 (Nplus3 (B := B)) X
    Nplus3_sq_zero Nplus3_regular
  simpa only [two_nsmul] using h

/-- The dual abstract KKT generator lands in the concrete grade `-2`
eigenspace of the three-sheet Euler action. -/
theorem eulerFiveGrading3_K_minus2 (X : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 (K_minus2 (Nplus3 (B := B)) X) =
      -((2 : ℕ) • K_minus2 (Nplus3 (B := B)) X) := by
  rw [eulerFiveGrading3_eq_ad_sigma]
  have h := comm_Sigma_K_minus2 (Nplus3 (B := B)) X
    Nplus3_sq_zero Nplus3_regular
  simpa only [two_nsmul] using h

end InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization
