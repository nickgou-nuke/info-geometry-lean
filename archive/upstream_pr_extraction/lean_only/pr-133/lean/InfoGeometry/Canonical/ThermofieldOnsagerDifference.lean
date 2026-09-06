import Mathlib
import InfoGeometry.SuperMetriplectic.Flow

noncomputable section

namespace InfoGeometry.Canonical.ThermofieldOnsagerDifference

open Matrix
open InfoGeometry.SuperMetriplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Finite forward/backward connection pair.  No dissipativity is built into the carrier. -/
structure DoubledConnection where
  gammaPlus : Matrix n n ℝ
  gammaMinus : Matrix n n ℝ

namespace DoubledConnection

/-- Average/classical branch connection. -/
def gammaSum (Γ : DoubledConnection (n := n)) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (Γ.gammaPlus + Γ.gammaMinus)

/-- Forward-minus-backward connection difference. -/
def gammaDiff (Γ : DoubledConnection (n := n)) : Matrix n n ℝ :=
  Γ.gammaPlus - Γ.gammaMinus

/-- Symmetric part of the connection difference. -/
def onsagerTensor (Γ : DoubledConnection (n := n)) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (Γ.gammaDiff + Γ.gammaDiff.transpose)

/-- Skew/Casimir part of the connection difference. -/
def gyroscopicTensor (Γ : DoubledConnection (n := n)) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (Γ.gammaDiff - Γ.gammaDiff.transpose)

@[simp] theorem onsagerTensor_transpose (Γ : DoubledConnection (n := n)) :
    Γ.onsagerTensor.transpose = Γ.onsagerTensor := by
  ext i j
  simp [onsagerTensor, gammaDiff, Matrix.transpose_apply]
  ring

@[simp] theorem gyroscopicTensor_transpose (Γ : DoubledConnection (n := n)) :
    Γ.gyroscopicTensor.transpose = -Γ.gyroscopicTensor := by
  ext i j
  simp [gyroscopicTensor, gammaDiff, Matrix.transpose_apply]
  ring

/-- Exact symmetric/skew decomposition of the branch difference. -/
theorem gammaDiff_eq_onsager_add_gyroscopic
    (Γ : DoubledConnection (n := n)) :
    Γ.gammaDiff = Γ.onsagerTensor + Γ.gyroscopicTensor := by
  ext i j
  simp [onsagerTensor, gyroscopicTensor, gammaDiff, Matrix.transpose_apply]
  ring

end DoubledConnection

/-- Quadratic production readout associated with the full connection difference. -/
def entropyProduction
    (Γ : DoubledConnection (n := n)) (X : n → ℝ) : ℝ :=
  dotProduct X (Γ.gammaDiff.mulVec X)

/-- A real skew matrix contributes no diagonal quadratic form. -/
theorem skew_quadratic_form_zero
    (W : Matrix n n ℝ) (hW : W.transpose = -W) (X : n → ℝ) :
    dotProduct X (W.mulVec X) = 0 := by
  have hneg : dotProduct X (W.mulVec X) = -dotProduct X (W.mulVec X) := by
    calc
      dotProduct X (W.mulVec X) = Matrix.vecMul X W ⬝ᵥ X :=
        Matrix.dotProduct_mulVec X W X
      _ = dotProduct (W.transpose.mulVec X) X := by
        rw [Matrix.mulVec_transpose]
      _ = dotProduct ((-W).mulVec X) X := by rw [hW]
      _ = -dotProduct (W.mulVec X) X := by simp
      _ = -dotProduct X (W.mulVec X) := by rw [dotProduct_comm]
  linarith

/-- The skew/Casimir sector drops out of the production quadratic form. -/
theorem entropyProduction_eq_onsager_quad
    (Γ : DoubledConnection (n := n)) (X : n → ℝ) :
    entropyProduction Γ X = dotProduct X (Γ.onsagerTensor.mulVec X) := by
  rw [entropyProduction, Γ.gammaDiff_eq_onsager_add_gyroscopic,
    Matrix.add_mulVec, dotProduct_add]
  rw [skew_quadratic_form_zero Γ.gyroscopicTensor Γ.gyroscopicTensor_transpose X]
  simp

/-- Minimal second-law hypothesis: the symmetric response tensor is PSD. -/
def IsOnsagerDissipative (Γ : DoubledConnection (n := n)) : Prop :=
  ∀ X : n → ℝ, 0 ≤ dotProduct X (Γ.onsagerTensor.mulVec X)

/-- Under the PSD hypothesis the connection-difference production is nonnegative. -/
theorem entropyProduction_nonnegative
    (Γ : DoubledConnection (n := n))
    (hΓ : IsOnsagerDissipative Γ) (X : n → ℝ) :
    0 ≤ entropyProduction Γ X := by
  rw [entropyProduction_eq_onsager_quad]
  exact hΓ X

/-- Coincident forward/backward branches give zero production. -/
theorem reversible_branch_zero_production
    (Γ : DoubledConnection (n := n))
    (hΓ : Γ.gammaPlus = Γ.gammaMinus) (X : n → ℝ) :
    entropyProduction Γ X = 0 := by
  simp [entropyProduction, DoubledConnection.gammaDiff, hΓ]

/-- A proved dissipativity witness packages the symmetric projection into the
repository's native `OnsagerMetricData` carrier. -/
noncomputable def toOnsagerMetricData
    (Γ : DoubledConnection (n := n))
    (hΓ : IsOnsagerDissipative Γ) : OnsagerMetricData (n → ℝ) where
  onsager := Matrix.toLin' Γ.onsagerTensor
  pairing := dotProduct
  metric_symmetric := by
    intro x y
    calc
      dotProduct x (Γ.onsagerTensor.mulVec y) =
          Matrix.vecMul x Γ.onsagerTensor ⬝ᵥ y := Matrix.dotProduct_mulVec x _ y
      _ = dotProduct (Γ.onsagerTensor.transpose.mulVec x) y := by
          rw [Matrix.mulVec_transpose]
      _ = dotProduct (Γ.onsagerTensor.mulVec x) y := by
          rw [Γ.onsagerTensor_transpose]
      _ = dotProduct y (Γ.onsagerTensor.mulVec x) := dotProduct_comm _ _
  metric_nonnegative := hΓ
  pairing_zero_right := by intro x; simp

/-- The native Onsager packet quadratic is exactly the symmetric production form. -/
theorem toOnsagerMetricData_quadratic
    (Γ : DoubledConnection (n := n))
    (hΓ : IsOnsagerDissipative Γ) (X : n → ℝ) :
    (toOnsagerMetricData Γ hΓ).quadratic X = entropyProduction Γ X := by
  rw [entropyProduction_eq_onsager_quad]
  rfl

end InfoGeometry.Canonical.ThermofieldOnsagerDifference
