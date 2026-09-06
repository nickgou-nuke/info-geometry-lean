import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Exceptional.SplitOctonionZornReal

namespace InfoGeometry.Exceptional.SpinZorn

open InfoGeometry.Exceptional
open InfoGeometry.Exceptional.RealZorn

/--
A Zorn Vector represents a 4D Minkowski spacetime vector embedded in the 
8D Zorn Matrix (Split Octonion) algebra.
We identify this subspace by constraining the matrix to be symmetric in a specific way:
$a = b$ (time component) and $u = v$ (space component).
Its split norm is exactly the Lorentz interval: $a^2 - u \cdot u$.
-/
structure ZornVector where
  val : ZornMatrixReal
  h_time : ZornMatrixReal.a val = ZornMatrixReal.b val
  h_space : ZornMatrixReal.u val = ZornMatrixReal.v val

/-- A finite sandwich readout for two constrained Zorn vectors. -/
def ZornReflection (N X : ZornVector) : ZornMatrixReal :=
  -(N.val * X.val * N.val)

/-- A finite sandwich carrier for a Zorn transformation readout. -/
structure ZornRotor where
  val : ZornMatrixReal

/-- The finite transformation readout associated with a sandwich carrier. -/
def ZornSandwichAction (R : ZornRotor) (X : ZornVector) : ZornMatrixReal :=
  R.val * X.val * R.val

/-- Split norm multiplicativity for the sandwich readout. -/
theorem Spin_Preserves_Norm (R : ZornMatrixReal) (X : ZornMatrixReal) :
  (R * X * R).norm = R.norm * X.norm * R.norm := by
  -- norm_mul is already proven natively for ZornMatrixReal!
  have h1 := norm_mul (R * X) R
  have h2 := norm_mul R X
  rw [h1, h2]

/--
A Spatial Unit Vector in the Zorn representation.
This is a Zorn Vector where the time component is zero, and the spatial part has unit length.
-/
structure ZornSpatialUnitVector extends ZornVector where
  h_time_zero : ZornMatrixReal.a toZornVector.val = 0
  h_unit_length : (ZornMatrixReal.u toZornVector.val).1 * (ZornMatrixReal.u toZornVector.val).1 + (ZornMatrixReal.u toZornVector.val).2.1 * (ZornMatrixReal.u toZornVector.val).2.1 + (ZornMatrixReal.u toZornVector.val).2.2 * (ZornMatrixReal.u toZornVector.val).2.2 = 1

/-- A finite hyperbolic-parameterized Zorn carrier. -/
noncomputable def LorentzBoostRotor (φ : ℝ) (v : ZornSpatialUnitVector) : ZornMatrixReal :=
  { a := Real.cosh (φ / 2), 
    b := Real.cosh (φ / 2), 
    u := (Real.sinh (φ / 2) * v.val.u.1, Real.sinh (φ / 2) * v.val.u.2.1, Real.sinh (φ / 2) * v.val.u.2.2), 
    v := (Real.sinh (φ / 2) * v.val.v.1, Real.sinh (φ / 2) * v.val.v.2.1, Real.sinh (φ / 2) * v.val.v.2.2) }

/-- The hyperbolic carrier has unit split norm. -/
theorem lorentzBoostRotor_norm (φ : ℝ) (v : ZornSpatialUnitVector) : 
    (LorentzBoostRotor φ v).norm = 1 := by
  dsimp [LorentzBoostRotor, ZornMatrixReal.norm, dot]
  have h_space : v.val.u = v.val.v := v.h_space
  have h_unit : v.val.u.1 * v.val.u.1 + v.val.u.2.1 * v.val.u.2.1 + v.val.u.2.2 * v.val.u.2.2 = 1 := v.h_unit_length
  have h_symm : v.val.v.1 = v.val.u.1 ∧ v.val.v.2.1 = v.val.u.2.1 ∧ v.val.v.2.2 = v.val.u.2.2 := by
    rw [h_space]; exact ⟨rfl, rfl, rfl⟩
  rcases h_symm with ⟨h1, h2, h3⟩
  rw [h1, h2, h3]
  have h_alg : (Real.sinh (φ / 2) * v.val.u.1) * (Real.sinh (φ / 2) * v.val.u.1) +
               (Real.sinh (φ / 2) * v.val.u.2.1) * (Real.sinh (φ / 2) * v.val.u.2.1) +
               (Real.sinh (φ / 2) * v.val.u.2.2) * (Real.sinh (φ / 2) * v.val.u.2.2) = 
               Real.sinh (φ / 2) * Real.sinh (φ / 2) * (v.val.u.1 * v.val.u.1 + v.val.u.2.1 * v.val.u.2.1 + v.val.u.2.2 * v.val.u.2.2) := by ring
  rw [h_alg, h_unit]
  have h_cosh_sinh : Real.cosh (φ / 2) * Real.cosh (φ / 2) - Real.sinh (φ / 2) * Real.sinh (φ / 2) * 1 = 1 := by
    calc Real.cosh (φ / 2) * Real.cosh (φ / 2) - Real.sinh (φ / 2) * Real.sinh (φ / 2) * 1
      _ = Real.cosh (φ / 2) ^ 2 - Real.sinh (φ / 2) ^ 2 := by ring
      _ = 1 := Real.cosh_sq_sub_sinh_sq (φ / 2)
  exact h_cosh_sinh

/-- The sandwich readout preserves the split norm when the carrier has unit
    norm. -/
theorem lorentz_boost_preserves_spacetime_interval (φ : ℝ) (v : ZornSpatialUnitVector) (X : ZornMatrixReal) :
    (LorentzBoostRotor φ v * X * LorentzBoostRotor φ v).norm = X.norm := by
  have h_spin := Spin_Preserves_Norm (LorentzBoostRotor φ v) X
  have h_rotor_norm := lorentzBoostRotor_norm φ v
  rw [h_rotor_norm] at h_spin
  calc (LorentzBoostRotor φ v * X * LorentzBoostRotor φ v).norm
    _ = 1 * X.norm * 1 := h_spin
    _ = X.norm := by ring

end InfoGeometry.Exceptional.SpinZorn
