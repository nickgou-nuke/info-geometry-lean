import InfoGeometry.Algebra.PauliQuaternionSplitComparison

/-!
# Biquaternion and split-biquaternion sign checks

This file records the finite algebraic sign facts needed to keep the
"biquaternion versus split-biquaternion" comparison precise.

Two distinctions matter:

* In the usual complex biquaternion matrix model, multiplying a compact
  quaternion unit `K` by the scalar complex unit makes a square-`+1` boost
  generator.  Therefore its exponential has the `cosh/sinh` shape, not a
  `cosh/sin` mixed shape.
* If the hyperbolic scalar algebra `𝔻 ≃ ℝ × ℝ` is tensored with the already
  split-quaternion matrix algebra `H_split ≃ M₂(ℝ)`, then the result is
  represented by `M₂(ℝ) × M₂(ℝ)`, and `l ⊗ k_split` still squares to `+1`.
  By contrast, `l ⊗ K` for a compact quaternion unit `K² = -1` squares to
  `-1` in the product model `𝔻 ⊗ H`.

These are only finite matrix/product identities; no global Lorentz-group
classification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Algebra.BiquaternionSplitBiquaternionSignatures

open Matrix
open scoped Matrix
open InfoGeometry.Algebra.PauliQuaternionSplitComparison

/-- The usual complex-biquaternion boost generator `i K`. -/
def complexScalarTimesQuatK : InfoGeometry.Algebra.PauliQuaternionSplitComparison.M2C :=
  Complex.I • quatK

/-- Since `K²=-1` and `i²=-1`, the biquaternion boost generator squares to `+1`. -/
theorem complexScalarTimesQuatK_sq :
    complexScalarTimesQuatK * complexScalarTimesQuatK =
      (1 : InfoGeometry.Algebra.PauliQuaternionSplitComparison.M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [complexScalarTimesQuatK, quatK, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.I_mul_I]

/-- The algebraically correct closed boost shape for a square-`+1` generator. -/
def complexBiquaternionBoostShape (φ : ℂ) :
    InfoGeometry.Algebra.PauliQuaternionSplitComparison.M2C :=
  Complex.cosh φ • (1 : InfoGeometry.Algebra.PauliQuaternionSplitComparison.M2C) +
    Complex.sinh φ • complexScalarTimesQuatK

/-- The compact quaternion rotation generator itself squares to `-1`. -/
theorem quatK_rotation_generator_sq :
    quatK * quatK = -(1 : InfoGeometry.Algebra.PauliQuaternionSplitComparison.M2C) :=
  quatK_sq

/-! ## Hyperbolic scalars as a product algebra -/

/-- The hyperbolic scalar algebra `𝔻` in product coordinates. -/
abbrev HyperbolicScalar := ℝ × ℝ

/-- The scalar unit. -/
def hOne : HyperbolicScalar := (1, 1)

/-- The hyperbolic unit `l`, represented by the idempotent splitting. -/
def hL : HyperbolicScalar := (1, -1)

/-- Componentwise product on hyperbolic scalars. -/
def hMul (x y : HyperbolicScalar) : HyperbolicScalar :=
  (x.1 * y.1, x.2 * y.2)

/-- The hyperbolic unit squares to `+1`. -/
theorem hL_sq : hMul hL hL = hOne := by
  norm_num [hMul, hL, hOne]

/-! ## `𝔻 ⊗ H_split` as `M₂(ℝ) × M₂(ℝ)` -/

/-- Product model for hyperbolic-scalar extension of the real split-quaternion matrix owner. -/
abbrev SplitBiquatProduct := InfoGeometryCore.M2R × InfoGeometryCore.M2R

/-- Componentwise multiplication in the product model. -/
def splitProductMul (X Y : SplitBiquatProduct) : SplitBiquatProduct :=
  (X.1 * Y.1, X.2 * Y.2)

/-- Product unit. -/
def splitProductOne : SplitBiquatProduct :=
  ((1 : InfoGeometryCore.M2R), (1 : InfoGeometryCore.M2R))

/-- The element `l ⊗ k_split` in `𝔻 ⊗ H_split ≃ M₂(ℝ) × M₂(ℝ)`. -/
def hyperbolicTensorSplitK : SplitBiquatProduct :=
  (SplitQuaternionMatrices.sqK, -SplitQuaternionMatrices.sqK)

/-- In `𝔻 ⊗ H_split`, `l ⊗ k_split` squares to `+1`, because `l²=1` and `k_split²=1`. -/
theorem hyperbolicTensorSplitK_sq :
    splitProductMul hyperbolicTensorSplitK hyperbolicTensorSplitK = splitProductOne := by
  simp [splitProductMul, hyperbolicTensorSplitK, splitProductOne]

/-! ## `𝔻 ⊗ H` has the opposite sign for a compact quaternion unit -/

/-- Product model for hyperbolic-scalar extension of the compact quaternion matrix packet. -/
abbrev CompactBiquatProduct :=
  InfoGeometry.Algebra.PauliQuaternionSplitComparison.M2C ×
    InfoGeometry.Algebra.PauliQuaternionSplitComparison.M2C

/-- Componentwise multiplication in the compact product model. -/
def compactProductMul (X Y : CompactBiquatProduct) : CompactBiquatProduct :=
  (X.1 * Y.1, X.2 * Y.2)

/-- Product unit in the compact product model. -/
def compactProductOne : CompactBiquatProduct :=
  ((1 : InfoGeometry.Algebra.PauliQuaternionSplitComparison.M2C),
    (1 : InfoGeometry.Algebra.PauliQuaternionSplitComparison.M2C))

/-- Product negation written explicitly. -/
def compactProductNeg (X : CompactBiquatProduct) : CompactBiquatProduct :=
  (-X.1, -X.2)

/-- The element `l ⊗ K` for a compact quaternion unit `K²=-1`. -/
def hyperbolicTensorCompactK : CompactBiquatProduct := (quatK, -quatK)

/-- In `𝔻 ⊗ H`, `l ⊗ K` squares to `-1`, because `l²=1` but `K²=-1`. -/
theorem hyperbolicTensorCompactK_sq :
    compactProductMul hyperbolicTensorCompactK hyperbolicTensorCompactK =
      compactProductNeg compactProductOne := by
  simp [compactProductMul, hyperbolicTensorCompactK, compactProductNeg,
    compactProductOne]

/-- Consolidated sign packet separating the two possible meanings of
"split-biquaternion". -/
theorem biquaternion_split_biquaternion_sign_packet :
    complexScalarTimesQuatK * complexScalarTimesQuatK =
        (1 : InfoGeometry.Algebra.PauliQuaternionSplitComparison.M2C) ∧
    hMul hL hL = hOne ∧
    splitProductMul hyperbolicTensorSplitK hyperbolicTensorSplitK = splitProductOne ∧
    compactProductMul hyperbolicTensorCompactK hyperbolicTensorCompactK =
      compactProductNeg compactProductOne := by
  exact ⟨complexScalarTimesQuatK_sq, hL_sq,
    hyperbolicTensorSplitK_sq, hyperbolicTensorCompactK_sq⟩

end InfoGeometry.Algebra.BiquaternionSplitBiquaternionSignatures

end
