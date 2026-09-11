import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Topology.RohozhkinPentagonMatrix

/-!
# Rohozhkin affine-chart and cross-ratio bridge

#### BUCKET 1: CLOSED FINITE THEOREMS
- `rohozhkinFlipBlock_eq_affine_chart_form`: the local `2 × 2` Rohozhkin flip block is the
  barycentric transition matrix in the affine chart determined by `(zk, zi)`.
- `rohozhkinFlipBlock_first_column_sum` and `rohozhkinFlipBlock_second_column_sum`: each column sum is `1`.
- `rohozhkinFlipBlock_det`: the determinant is `(zj - zl) / (zi - zk)`.
- `crossRatio_from_rohozhkinFlipBlock`: the Möbius-invariant scalar extracted from the block is the
  projective cross-ratio convention `((a-b)(c-d))/((a-c)(b-d))` on `(zi,zj,zl,zk)`.
- `pentagon_chart_cocycle_identity`: the Appendix A five-flip product is the closed chart cocycle.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
- A global `PB_n → GL_{2n+1}` representation statement phrased directly in projective-line terms.
- A Möbius-covariance theorem for individual entries under general fractional linear transforms.
- The Penrose / golden-field specialization over `ℚ(√5)`.

This file only formalizes the finite affine-chart / cross-ratio layer of the Rohozhkin flip
block. It does not claim a full Möbius-geometry representation theorem or a Penrose-model
classification.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Topology.Delaunay

open Matrix

section FieldBridge

variable {K : Type} [Field K]

/-- Affine coordinate in the chart sending `zk ↦ 0` and `zi ↦ 1`. -/
def affineChart (zi zk x : K) : K :=
  (x - zk) / (zi - zk)

/-- One projective cross-ratio convention on an ordered quadruple. -/
def projectiveCrossRatio (a b c d : K) : K :=
  ((a - b) * (c - d)) / ((a - c) * (b - d))

/-- The local `2 × 2` Rohozhkin flip block for `ik → jl`. -/
def rohozhkinFlipBlock (zi zk zj zl : K) : Matrix (Fin 2) (Fin 2) K :=
  !![(zi - zl) / (zi - zk), (zi - zj) / (zi - zk);
    (zl - zk) / (zi - zk), (zj - zk) / (zi - zk)]

lemma one_sub_affineChart (zi zk x : K) (h : zi - zk ≠ 0) :
    1 - affineChart zi zk x = (zi - x) / (zi - zk) := by
  unfold affineChart
  field_simp [h]
  ring

/-- The flip block is the barycentric transition matrix in the affine chart of `(zk, zi)`. -/
theorem rohozhkinFlipBlock_eq_affine_chart_form (zi zk zj zl : K) (h : zi - zk ≠ 0) :
    rohozhkinFlipBlock zi zk zj zl =
      !![1 - affineChart zi zk zl, 1 - affineChart zi zk zj;
        affineChart zi zk zl, affineChart zi zk zj] := by
  ext a b
  fin_cases a
  · fin_cases b
    · rw [one_sub_affineChart zi zk zl h]
      simp [rohozhkinFlipBlock]
    · rw [one_sub_affineChart zi zk zj h]
      simp [rohozhkinFlipBlock]
  · fin_cases b
    · simp [rohozhkinFlipBlock, affineChart]
    · simp [rohozhkinFlipBlock, affineChart]

/-- The first column is affine/barycentric: its entries sum to `1`. -/
theorem rohozhkinFlipBlock_first_column_sum (zi zk zj zl : K) (h : zi - zk ≠ 0) :
    rohozhkinFlipBlock zi zk zj zl 0 0 + rohozhkinFlipBlock zi zk zj zl 1 0 = 1 := by
  simp [rohozhkinFlipBlock]
  field_simp [h]
  ring

/-- The second column is affine/barycentric: its entries sum to `1`. -/
theorem rohozhkinFlipBlock_second_column_sum (zi zk zj zl : K) (h : zi - zk ≠ 0) :
    rohozhkinFlipBlock zi zk zj zl 0 1 + rohozhkinFlipBlock zi zk zj zl 1 1 = 1 := by
  simp [rohozhkinFlipBlock]
  field_simp [h]
  ring

/-- The determinant of the local flip block. -/
theorem rohozhkinFlipBlock_det (zi zk zj zl : K) (h : zi - zk ≠ 0) :
    Matrix.det (rohozhkinFlipBlock zi zk zj zl) = (zj - zl) / (zi - zk) := by
  simp [rohozhkinFlipBlock, Matrix.det_fin_two]
  field_simp [h]
  ring

/--
The cross-ratio hidden in the flip block: the ratio of the off-diagonal product to the diagonal
product is the projective cross-ratio convention on `(zi, zj, zl, zk)`.
-/
theorem crossRatio_from_rohozhkinFlipBlock
    (zi zk zj zl : K)
    (h_ik : zi - zk ≠ 0)
    (h_il : zi - zl ≠ 0)
    (h_jk : zj - zk ≠ 0) :
    ((rohozhkinFlipBlock zi zk zj zl 0 1) * (rohozhkinFlipBlock zi zk zj zl 1 0)) /
        ((rohozhkinFlipBlock zi zk zj zl 0 0) * (rohozhkinFlipBlock zi zk zj zl 1 1)) =
      projectiveCrossRatio zi zj zl zk := by
  simp [rohozhkinFlipBlock, projectiveCrossRatio]
  field_simp [h_ik, h_il, h_jk]

end FieldBridge

/--
The already-proved Appendix A five-flip identity, read conceptually as a closed affine/projective
chart cocycle around the pentagon.
-/
theorem pentagon_chart_cocycle_identity
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    pentagonGamma5 zi zj zk zl zm *
      pentagonGamma4 zi zj zk zl zm *
      pentagonGamma3 zi zj zk zl zm *
      pentagonGamma2 zi zj zk zl zm *
      pentagonGamma1 zi zj zk zl zm = 1 :=
  pentagon_appendix_identity zi zj zk zl zm h_il h_ik h_km h_jm h_jl

end InfoGeometry.Topology.Delaunay
