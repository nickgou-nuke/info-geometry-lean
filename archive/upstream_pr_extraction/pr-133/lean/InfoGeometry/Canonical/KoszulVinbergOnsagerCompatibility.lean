import Mathlib
import InfoGeometry.Jordan.SPD
import InfoGeometry.Canonical.ThermofieldOnsagerDifference

noncomputable section

namespace InfoGeometry.Canonical.KoszulVinbergOnsagerCompatibility

open Matrix
open InfoGeometry.Jordan
open InfoGeometry.Canonical.ThermofieldOnsagerDifference

variable {n : ℕ}

/-- Finite inverse-Hessian mobility associated with an SPD metric matrix. -/
def kvMobility (g : SPD n) : Matrix (Fin n) (Fin n) ℝ :=
  g.mat⁻¹

/-- Inverse-Hessian mobility inherits symmetry from the SPD Hessian. -/
@[simp] theorem kvMobility_transpose (g : SPD n) :
    (kvMobility g).transpose = kvMobility g := by
  simp [kvMobility, Matrix.transpose_nonsing_inv, g.transpose_eq_self]

/-- The inverse of an SPD Hessian is again positive definite. -/
theorem kvMobility_posDef (g : SPD n) :
    (kvMobility g).PosDef := by
  simpa [kvMobility] using g.pos.inv

/-- Hence the inverse-Hessian quadratic form is nonnegative in every direction. -/
theorem kvMobility_quadratic_nonnegative
    (g : SPD n) (X : Fin n → ℝ) :
    0 ≤ dotProduct X ((kvMobility g).mulVec X) := by
  by_cases hX : X = 0
  · subst X
    simp
  · exact le_of_lt ((kvMobility_posDef g).dotProduct_mulVec_pos hX)

/-- Squared Newton decrement / dual Dikin norm of a force covector. -/
def squaredNewtonDecrement (g : SPD n) (X : Fin n → ℝ) : ℝ :=
  dotProduct X ((kvMobility g).mulVec X)

@[simp] theorem squaredNewtonDecrement_nonnegative
    (g : SPD n) (X : Fin n → ℝ) :
    0 ≤ squaredNewtonDecrement g X :=
  kvMobility_quadratic_nonnegative g X

/-- Sign reversal of the force leaves the squared Newton decrement unchanged. -/
@[simp] theorem squaredNewtonDecrement_neg
    (g : SPD n) (X : Fin n → ℝ) :
    squaredNewtonDecrement g (-X) = squaredNewtonDecrement g X := by
  simp [squaredNewtonDecrement, kvMobility, Matrix.mulVec_neg, dotProduct]

/-- Compatibility condition between the symmetric thermofield response and the
inverse Koszul--Vinberg/Dikin Hessian metric. -/
def IsKVCompatible
    (Γ : DoubledConnection (n := Fin n)) (g : SPD n) : Prop :=
  Γ.onsagerTensor = kvMobility g

/-- KV compatibility supplies the PSD hypothesis required by the second law. -/
theorem compatible_isOnsagerDissipative
    (Γ : DoubledConnection (n := Fin n)) (g : SPD n)
    (hcompat : IsKVCompatible Γ g) :
    IsOnsagerDissipative Γ := by
  intro X
  rw [hcompat]
  exact kvMobility_quadratic_nonnegative g X

/-- Under KV compatibility, full connection-difference production is nonnegative. -/
theorem compatible_entropyProduction_nonnegative
    (Γ : DoubledConnection (n := Fin n)) (g : SPD n)
    (hcompat : IsKVCompatible Γ g) (X : Fin n → ℝ) :
    0 ≤ entropyProduction Γ X := by
  exact entropyProduction_nonnegative Γ
    (compatible_isOnsagerDissipative Γ g hcompat) X

/-- The connection-difference production equals the squared Newton decrement. -/
theorem entropyProduction_eq_squaredNewtonDecrement
    (Γ : DoubledConnection (n := Fin n)) (g : SPD n)
    (hcompat : IsKVCompatible Γ g) (X : Fin n → ℝ) :
    entropyProduction Γ X = squaredNewtonDecrement g X := by
  rw [entropyProduction_eq_onsager_quad, hcompat]
  rfl

/-- In particular the force `-grad F` has the same production as the usual
Newton-decrement quadratic form of `grad F`. -/
theorem entropyProduction_neg_gradient_readout
    (Γ : DoubledConnection (n := Fin n)) (g : SPD n)
    (hcompat : IsKVCompatible Γ g) (gradF : Fin n → ℝ) :
    entropyProduction Γ (-gradF) = squaredNewtonDecrement g gradF := by
  rw [entropyProduction_eq_squaredNewtonDecrement Γ g hcompat]
  exact squaredNewtonDecrement_neg g gradF

/-- Dual Dikin unit ball in force/covector coordinates. -/
def dualDikinBall (g : SPD n) : Set (Fin n → ℝ) :=
  {X | squaredNewtonDecrement g X ≤ 1}

/-- Unit entropy-production contour agrees exactly with the dual Dikin ball
under `L = g⁻¹`. -/
theorem production_le_one_iff_mem_dualDikinBall
    (Γ : DoubledConnection (n := Fin n)) (g : SPD n)
    (hcompat : IsKVCompatible Γ g) (X : Fin n → ℝ) :
    entropyProduction Γ X ≤ 1 ↔ X ∈ dualDikinBall g := by
  rw [entropyProduction_eq_squaredNewtonDecrement Γ g hcompat]
  rfl

end InfoGeometry.Canonical.KoszulVinbergOnsagerCompatibility
