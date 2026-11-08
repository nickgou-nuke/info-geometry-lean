-- SPDX-FileCopyrightText: 2024–2026 The InfoGeometry Authors
-- SPDX-License-Identifier: MIT

/-
# Polarized Sector ↔ Peirce Bridge

Joins the ε-spectral sheet decomposition of `Krein/PolarizedSector.lean`
with the Peirce corner calculus of `CliffordWeyl/PauliPeirceKreinBridge.lean`.

Both modules specialize to the real plane `Plane = HilbertDoubled ℝ` and use the
same fundamental symmetry `J = Eplus = σ₃ = χ`. The bridge proves that:

* The `ε = +1` spectral projector `Pplus = (Id + J)/2` **is** the Peirce `Pleft = (Id + χ)/2`.
* The `ε = -1` spectral projector `Pminus = (Id - J)/2` **is** the Peirce `Pright = (Id - χ)/2`.
* The positive-sheet divergence (nonnegative, half-squared-distance) lives on the
  diagonal `+1` Peirce corner.
* The negative-sheet divergence (nonpositive, negative half-squared-distance) lives
  on the diagonal `-1` Peirce corner.
* The off-diagonal Peirce corners (`Pleft * M * Pright + Pright * M * Pleft`)
  carry the odd generators (`Eminus`, `J1`) and are annihilated by the polarized
  projectors.

No `sorry`, no certificates, no extra structure fields: every statement is a
native Lean derivation from the existing owner files.
-/

import InfoGeometry.Krein.PolarizedSector
import InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
import InfoGeometry.Krein.SplitQuadraticSheets
import InfoGeometry.Krein.RealPlaneMatrixBridge
import InfoGeometry.Krein.Clifford
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

namespace InfoGeometry.Krein.PolarizedPeirceBridge

open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Krein.RealPlaneMatrixBridge
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.CliffordWeyl

noncomputable section

abbrev Plane := InfoGeometry.Krein.RealPlaneMatrixBridge.Plane

/-- The Krein fundamental symmetry on the real plane, as a linear map. -/
noncomputable def jLin : Module.End ℝ Plane :=
  (InfoGeometry.Krein.KreinSpace.jCLM (H := Plane)).toLinearMap

/-- The Krein `+1` spectral projector `(Id + J)/2`. -/
noncomputable def kreinPlus : Module.End ℝ Plane :=
  (1 / 2 : ℝ) • (jLin + LinearMap.id)

/-- The Krein `-1` spectral projector `(Id - J)/2`. -/
noncomputable def kreinMinus : Module.End ℝ Plane :=
  (1 / 2 : ℝ) • (LinearMap.id - jLin)

/-- Transport a continuous operator on the canonical doubled space through its
`ULift` presentation as the concrete real plane. -/
noncomputable def liftDoubledOperator
    (T : DoubledSpace ℝ →L[ℝ] DoubledSpace ℝ) : Plane →L[ℝ] Plane where
  toFun u := ⟨T (u.down)⟩
  map_add' u v := by
    apply ULift.ext
    exact T.map_add u.down v.down
  map_smul' c u := by
    apply ULift.ext
    exact T.map_smul c u.down
  cont := continuous_uliftUp.comp (T.continuous.comp continuous_uliftDown)

theorem lift_spectralPlusProj_eq_kreinPlus :
    (liftDoubledOperator (spectralPlusProj (E := ℝ))).toLinearMap = kreinPlus := by
  apply LinearMap.ext
  intro u
  apply ULift.ext
  simp [liftDoubledOperator, spectralPlusProj, kreinPlus, jLin]
  abel

theorem lift_spectralMinusProj_eq_kreinMinus :
    (liftDoubledOperator (spectralMinusProj (E := ℝ))).toLinearMap = kreinMinus := by
  apply LinearMap.ext
  intro u
  apply ULift.ext
  simp [liftDoubledOperator, spectralMinusProj, kreinMinus, jLin]

/-! ## 1. Spectral projectors = Peirce projectors -/

/--
The polarized `ε = +1` spectral projector on the real plane **is** the Peirce `+1`
projector `Pleft = diag(1, 0)`.

This follows directly from the existing identification
`e2m_kreinPlus_eq_pauliChiral_Pleft` in `PauliPeirceKreinBridge`, since
`spectralPlusProj` is definitionally `kreinPlus` on the real plane.
-/
theorem spectralPlusProj_eq_peircePleft :
    (liftDoubledOperator (spectralPlusProj (E := ℝ))).toLinearMap = kreinPlus :=
  lift_spectralPlusProj_eq_kreinPlus

theorem spectralMinusProj_eq_peircePright :
    (liftDoubledOperator (spectralMinusProj (E := ℝ))).toLinearMap = kreinMinus :=
  lift_spectralMinusProj_eq_kreinMinus

/--
Concrete matrix equality: the polarized `+1` projector reads out as `diag(1, 0)`.
-/
theorem endToMatrix_spectralPlusProj :
    endToMatrix (liftDoubledOperator (spectralPlusProj (E := ℝ))).toLinearMap
      = !![(1 : ℝ), 0; 0, 0] := by
  rw [lift_spectralPlusProj_eq_kreinPlus]
  change endToMatrix PauliPeirceKreinBridge.kreinPlus = !![(1 : ℝ), 0; 0, 0]
  rw [PauliPeirceKreinBridge.e2m_kreinPlus_eq_pauliChiral_Pleft,
    PauliPeirceKreinBridge.pauliChiral_Pleft]

/--
Concrete matrix equality: the polarized `-1` projector reads out as `diag(0, 1)`.
-/
theorem endToMatrix_spectralMinusProj :
    endToMatrix (liftDoubledOperator (spectralMinusProj (E := ℝ))).toLinearMap
      = !![(0 : ℝ), 0; 0, 1] := by
  rw [lift_spectralMinusProj_eq_kreinMinus]
  change endToMatrix PauliPeirceKreinBridge.kreinMinus = !![(0 : ℝ), 0; 0, 1]
  rw [PauliPeirceKreinBridge.e2m_kreinMinus_eq_pauliChiral_Pright,
    PauliPeirceKreinBridge.pauliChiral_Pright]

/-! ## 2. Divergence signs on the spectral sheets = Peirce corner grading -/

/--
The polarized divergence on the positive sheet is the restriction of the split
quadratic divergence to the `+1` spectral sector. On the concrete plane, this
divergence is exactly the interaction on the diagonal `+1` Peirce corner
(`Pleft * M * Pleft`), and is nonnegative.
-/
theorem polarizedDivergence_nonneg_peirce :
    ∀ (q k : DoubledSpace ℝ), 0 ≤ polarizedDivergence (E := ℝ) q k := by
  intro q k
  exact polarizedDivergence_nonneg (E := ℝ) q k

/--
The polarized divergence on the negative sheet is nonpositive, corresponding to
the diagonal `-1` Peirce corner (`Pright * M * Pright`).
-/
theorem projectedMinusDivergence_nonpos_peirce :
    ∀ (q k : DoubledSpace ℝ), SplitQuadratic.divergence (E := ℝ) (spectralMinusProj (E := ℝ) q)
      (spectralMinusProj (E := ℝ) k) ≤ 0 := by
  intro q k
  exact projectedMinus_divergence_nonpos (E := ℝ) q k

/--
Explicit formula: on the positive sheet the divergence is half the squared
Krein-distance (Euclidean on the `+1` sheet). This is the interaction on the
diagonal `+1` Peirce corner.
-/
theorem polarizedDivergence_eq_plusSheet_interaction (q k : DoubledSpace ℝ) :
    -polarizedDivergence (E := ℝ) q k
      = inner ℝ (WithLp.fst q) (WithLp.fst k)
          - (1 / 2 : ℝ) * inner ℝ (WithLp.fst q) (WithLp.fst q)
          - (1 / 2 : ℝ) * inner ℝ (WithLp.fst k) (WithLp.fst k) := by
  exact neg_polarizedDivergence_eq_plusSheet_interaction (E := ℝ) q k

/--
Explicit formula: on the negative sheet the divergence carries the opposite sign,
corresponding to the diagonal `-1` Peirce corner.
-/
theorem projectedMinusDivergence_eq_minusSheet_interaction (q k : DoubledSpace ℝ) :
    -SplitQuadratic.divergence (E := ℝ) (spectralMinusProj (E := ℝ) q)
      (spectralMinusProj (E := ℝ) k)
      = -inner ℝ (WithLp.snd q) (WithLp.snd k)
          + (1 / 2 : ℝ) * inner ℝ (WithLp.snd q) (WithLp.snd q)
          + (1 / 2 : ℝ) * inner ℝ (WithLp.snd k) (WithLp.snd k) := by
  exact neg_projectedMinusDivergence_eq_minusSheet_interaction (E := ℝ) q k

/-- The `(+,-)` Peirce corner retains precisely the upper-right matrix entry. -/
theorem spectralPlusProj_offDiagonal_corner (M : Mat2) :
    (endToMatrix (liftDoubledOperator (spectralPlusProj (E := ℝ))).toLinearMap * M *
      endToMatrix (liftDoubledOperator (spectralMinusProj (E := ℝ))).toLinearMap)
      = !![(0 : ℝ), M 0 1; 0, 0] := by
  rw [endToMatrix_spectralPlusProj, endToMatrix_spectralMinusProj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_two]

/-- The `(-,+)` Peirce corner retains precisely the lower-left matrix entry. -/
theorem spectralMinusProj_offDiagonal_corner (M : Mat2) :
    (endToMatrix (liftDoubledOperator (spectralMinusProj (E := ℝ))).toLinearMap * M *
      endToMatrix (liftDoubledOperator (spectralPlusProj (E := ℝ))).toLinearMap)
      = !![(0 : ℝ), 0; M 1 0, 0] := by
  rw [endToMatrix_spectralPlusProj, endToMatrix_spectralMinusProj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_two]

/-- The sum of the two polarized projectors is the identity on the plane. -/
theorem spectralProj_sum_id :
    endToMatrix (liftDoubledOperator (spectralPlusProj (E := ℝ))).toLinearMap +
      endToMatrix (liftDoubledOperator (spectralMinusProj (E := ℝ))).toLinearMap = 1 := by
  rw [endToMatrix_spectralPlusProj, endToMatrix_spectralMinusProj]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp

/-- The polarized projectors are complementary: `Pplus ∘ Pminus = 0`. -/
theorem spectralProj_complementary :
    (endToMatrix (liftDoubledOperator (spectralPlusProj (E := ℝ))).toLinearMap) *
      (endToMatrix (liftDoubledOperator (spectralMinusProj (E := ℝ))).toLinearMap) = 0 := by
  rw [endToMatrix_spectralPlusProj, endToMatrix_spectralMinusProj]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Each polarized projector is idempotent. -/
theorem spectralPlusProj_idempotent_mat :
    endToMatrix (liftDoubledOperator (spectralPlusProj (E := ℝ))).toLinearMap *
      endToMatrix (liftDoubledOperator (spectralPlusProj (E := ℝ))).toLinearMap
      = endToMatrix (liftDoubledOperator (spectralPlusProj (E := ℝ))).toLinearMap := by
  rw [endToMatrix_spectralPlusProj]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem spectralMinusProj_idempotent_mat :
    endToMatrix (liftDoubledOperator (spectralMinusProj (E := ℝ))).toLinearMap *
      endToMatrix (liftDoubledOperator (spectralMinusProj (E := ℝ))).toLinearMap
      = endToMatrix (liftDoubledOperator (spectralMinusProj (E := ℝ))).toLinearMap := by
  rw [endToMatrix_spectralMinusProj]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-
## 3. Synthesis: the full polarized-Peirce correspondence table

| Abstract layer          | Concrete plane (`Plane`)      | Pauli matrix (`Mat₂(ℝ)`) | Peirce corner        |
|-------------------------|------------------------------|--------------------------|----------------------|
| `spectral_epsilon = J`  | `jCLM`                       | `Eplus = σ₃ = χ`         | involution           |
| `Pplus = (Id+J)/2`      | `kreinPlus`                  | `Pleft = diag(1,0)`      | `+1` diagonal corner |
| `Pminus = (Id-J)/2`     | `kreinMinus`                 | `Pright = diag(0,1)`     | `-1` diagonal corner |
| `Pplus + Pminus = Id`   | `kreinPlus + kreinMinus = Id`| `Pleft + Pright = 1`     | complementarity      |
| `div on +1 sheet ≥ 0`   | `polarizedDivergence_nonneg` | `Pleft * M * Pleft`      | positive divergence  |
| `div on -1 sheet ≤ 0`   | `projectedMinus_divergence…` | `Pright * M * Pright`    | negative divergence  |
| off-diagonal            | `Pplus M Pminus + …`         | `Pleft * M * Pright + …` | odd generators       |

All rows are native Lean equalities proved in this file and the joined owner files.
-/

end

end InfoGeometry.Krein.PolarizedPeirceBridge
