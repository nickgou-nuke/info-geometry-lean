/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.LipschitzWittRieszPrimary
import InfoGeometry.Geometry.RindlerLapseCalculus
import InfoGeometry.Geometry.RindlerSpinTorsion
import InfoGeometry.Canonical.RealSpacetime4x4Closure
import InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.BogoliubovClosedForms
import InfoGeometry.Krein.ExponentialIsometry
import InfoGeometry.OperatorAlgebra.KreinInnerDerivation

/-!
# Souriau equilibrium, Killing flows, and the finite `Cl(1,1)` Lipschitz rotor

This owner gives a convention-explicit finite Minkowski formalization of the
recoverable part of the Souriau/Killing/Lipschitz synthesis:

* an affine inverse-temperature field with antisymmetric Lorentz generator is
  Killing for the Minkowski bilinear form;
* the corresponding boost is a one-parameter isometric flow;
* the real `Cl(1,1)` rotor acts on vectors by the same boost;
* the rotor has unit Clifford-star norm, so its scalar normalization cancels
  in the sandwich action;
* the Rindler Tolman product is connected to the existing coordinate owner.

This does not identify an arbitrary curved-spacetime thermal field with a
Lipschitz flow, and it does not claim a Kerr or BKM/Kosmann theorem without the
missing connection, spinor bundle, and differentiability data.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.SouriauKillingLipschitzBridge

open scoped Matrix
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.LipschitzWittRieszPrimary
open InfoGeometry.Dynamics.HyperbolicComponent
open InfoGeometry.Dynamics.RapiditySpace
open InfoGeometry.Geometry.RindlerLapseCalculus
open InfoGeometry.Geometry.RindlerSpinTorsion
open InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis

abbrev Vec11 := InfoGeometry.Clifford.Cl11Matrix.Vec11
abbrev Mat2 := InfoGeometry.Clifford.Cl11Matrix.Mat2

/-- The split Minkowski bilinear form in signature `(-,+)`. -/
def minkowskiForm (u v : Vec11) : ℝ :=
  -(u.1 * v.1) + u.2 * v.2

/-- The boost Killing generator `K = x ∂ₜ + t ∂ₓ`. -/
def boostGenerator (v : Vec11) : Vec11 :=
  (v.2, v.1)

/-- The affine inverse-temperature field `β(x) = b + K x`. -/
def affineTemperatureField (b v : Vec11) : Vec11 :=
  (b.1 + v.2, b.2 + v.1)

/-- The finite Lorentz boost flow. -/
def boostFlow (s : ℝ) (v : Vec11) : Vec11 :=
  (Real.cosh s * v.1 + Real.sinh s * v.2,
    Real.sinh s * v.1 + Real.cosh s * v.2)

/-- Light-cone coordinates for the `(t,z)` convention used by the Rindler
owner: `x₊ = z + t` and `x₋ = z - t`. -/
def lightConeCoordinates (v : Vec11) : LightConeColumn :=
  !![v.2 + v.1; v.2 - v.1]

/-- The two null coordinates adapted to the future timelike cone for the
`(-,+)` Minkowski convention. Unlike `lightConeCoordinates`, both coordinates
are positive on future timelike vectors. -/
def temperatureNullCoordinates : Vec11 →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v.1 + v.2, v.1 - v.2]
  map_add' u v := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r v := by
    ext i
    fin_cases i <;> simp <;> ring

/-- The future cone in the actual real Minkowski carrier, pulled back from the
positive orthant in its two null coordinates. -/
def rindlerTemperatureCone : ProperCone ℝ Vec11 :=
  (ProperCone.positive ℝ (Fin 2 → ℝ)).comap
    temperatureNullCoordinates.toContinuousLinearMap

@[simp] theorem mem_rindlerTemperatureCone (v : Vec11) :
    v ∈ rindlerTemperatureCone ↔ 0 ≤ v.1 + v.2 ∧ v.2 ≤ v.1 := by
  change 0 ≤ temperatureNullCoordinates v ↔ _
  constructor
  · intro h
    constructor
    · have h₀ := h 0
      simpa [temperatureNullCoordinates] using h₀
    · have h₁ := h 1
      have h₁' : 0 ≤ v.1 - v.2 := by simpa [temperatureNullCoordinates] using h₁
      exact (sub_nonneg.mp h₁')
  · rintro ⟨h₀, h₁⟩ i
    fin_cases i
    · simpa [temperatureNullCoordinates] using h₀
    · have h₁' : 0 ≤ v.1 - v.2 := sub_nonneg.mpr h₁
      simpa [temperatureNullCoordinates] using h₁'

/-- The future cone is preserved by every real Rindler boost. On the two null
coordinates the boost acts by the strictly positive factors `exp s` and
`exp (-s)`. -/
theorem boostFlow_preserves_rindlerTemperatureCone {s : ℝ} {v : Vec11}
    (hv : v ∈ rindlerTemperatureCone) :
    boostFlow s v ∈ rindlerTemperatureCone := by
  rw [mem_rindlerTemperatureCone] at hv ⊢
  rcases v with ⟨t, z⟩
  dsimp [boostFlow]
  constructor
  · have h := hv.1
    have heq : Real.cosh s * t + Real.sinh s * z +
        (Real.sinh s * t + Real.cosh s * z) = Real.exp s * (t + z) := by
      calc
        _ = (Real.cosh s + Real.sinh s) * (t + z) := by ring
        _ = Real.exp s * (t + z) := by rw [Real.cosh_add_sinh]
    rw [heq]
    exact mul_nonneg (le_of_lt (Real.exp_pos s)) h
  · have h := hv.2
    have heq : Real.cosh s * t + Real.sinh s * z -
        (Real.sinh s * t + Real.cosh s * z) = Real.exp (-s) * (t - z) := by
      calc
        _ = (Real.cosh s - Real.sinh s) * (t - z) := by ring
        _ = Real.exp (-s) * (t - z) := by
          rw [Real.cosh_sub_sinh]
    apply sub_nonneg.mp
    rw [heq]
    exact mul_nonneg (le_of_lt (Real.exp_pos (-s))) (sub_nonneg.mpr h)

/-- Vectors in the future temperature cone are causal for the `(-,+)`
Minkowski form. -/
theorem rindlerTemperatureCone_minkowski_nonpos {v : Vec11}
    (hv : v ∈ rindlerTemperatureCone) :
    minkowskiForm v v ≤ 0 := by
  have h := (mem_rindlerTemperatureCone v).mp hv
  rw [show minkowskiForm v v = -((v.1 + v.2) * (v.1 - v.2)) by
    simp [minkowskiForm]; ring]
  exact neg_nonpos.mpr (mul_nonneg h.1 (sub_nonneg.mpr h.2))

/-- Strict positivity of both null coordinates is exactly a strict timelike
inequality for the `(-,+)` Minkowski form. -/
theorem temperatureNullCoordinates_strict_timelike {v : Vec11}
    (h₁ : 0 < v.1 + v.2) (h₂ : v.2 < v.1) :
    minkowskiForm v v < 0 := by
  rw [show minkowskiForm v v = -((v.1 + v.2) * (v.1 - v.2)) by
    simp [minkowskiForm]; ring]
  exact neg_lt_zero.mpr (mul_pos h₁ (sub_pos.mpr h₂))

/-- The pulled-back orthant cone is salient: a vector and its negative can
both lie in the future cone only when the vector is zero. -/
theorem rindlerTemperatureCone_salient :
    (rindlerTemperatureCone.toPointedCone.toConvexCone).Salient := by
  intro v hv hvne hvneg
  apply hvne
  rcases (mem_rindlerTemperatureCone v).mp hv with ⟨h₁, h₂⟩
  rcases (mem_rindlerTemperatureCone (-v)).mp hvneg with ⟨h₃, h₄⟩
  rcases v with ⟨t, z⟩
  change 0 ≤ -t + -z at h₃
  change -z ≤ -t at h₄
  have ht : t = 0 := by linarith
  have hz : z = 0 := by linarith
  simp [ht, hz]

/-- The explicit Lorentz boost is exactly the diagonal real `A`-component
flow after transport to light-cone coordinates. -/
theorem componentAReal_lightConeCoordinates (s : ℝ) (v : Vec11) :
    componentAReal s * lightConeCoordinates v =
      lightConeCoordinates (boostFlow s v) := by
  rcases v with ⟨t, z⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [componentAReal, lightConeCoordinates, boostFlow,
      Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← Real.cosh_add_sinh]
    ring
  · rw [← Real.cosh_sub_sinh]
    ring

/-- Mathlib's basis-free Lipschitz action preserves the same quadratic form.
This is the abstract group-level statement; `boostFlow` is its explicit
finite `Cl(1,1)` representative below. -/
theorem lipschitz_action_preserves_q11
    (g : _root_.lipschitzGroup q11) (v : Vec11) :
    q11 (lipschitzGroupToIsometryHom q11 g v) = q11 v := by
  exact (lipschitzGroupToIsometryHom q11 g).map_app v

@[simp] theorem boostFlow_zero (v : Vec11) : boostFlow 0 v = v := by
  simp [boostFlow]

theorem boostFlow_add (s t : ℝ) (v : Vec11) :
    boostFlow (s + t) v = boostFlow s (boostFlow t v) := by
  rcases v with ⟨v₁, v₂⟩
  simp only [boostFlow]
  rw [Real.cosh_add, Real.sinh_add]
  ring_nf

/-- The one-parameter conformal flow combining the Lorentz boost with a
uniform real dilation. The complex structure is not used as a scalar. -/
def conformalBoostFlow (sigma s : ℝ) (v : Vec11) : Vec11 :=
  Real.exp (2 * sigma * s) • boostFlow s v

private theorem boostFlow_smul (r s : ℝ) (v : Vec11) :
    boostFlow s (r • v) = r • boostFlow s v := by
  rcases v with ⟨v₁, v₂⟩
  ext <;> simp [boostFlow] <;> ring

@[simp] theorem conformalBoostFlow_zero (sigma : ℝ) (v : Vec11) :
    conformalBoostFlow sigma 0 v = v := by
  simp [conformalBoostFlow, boostFlow]

/-- The real boost-homothety flow has the additive one-parameter group law. -/
theorem conformalBoostFlow_add (sigma s t : ℝ) (v : Vec11) :
    conformalBoostFlow sigma (s + t) v =
      conformalBoostFlow sigma s (conformalBoostFlow sigma t v) := by
  unfold conformalBoostFlow
  rw [show 2 * sigma * (s + t) = 2 * sigma * s + 2 * sigma * t by ring,
    Real.exp_add, boostFlow_add, boostFlow_smul]
  rw [← smul_smul]

theorem boostFlow_preserves_minkowski (s : ℝ) (u v : Vec11) :
    minkowskiForm (boostFlow s u) (boostFlow s v) = minkowskiForm u v := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have h := Real.cosh_sq_sub_sinh_sq s
  calc
    minkowskiForm (boostFlow s (u₁, u₂)) (boostFlow s (v₁, v₂)) =
        (Real.cosh s ^ 2 - Real.sinh s ^ 2) *
          (-(u₁ * v₁) + u₂ * v₂) := by
            simp [minkowskiForm, boostFlow]
            linear_combination (-(u₁ * v₁) + u₂ * v₂) * h
    _ = minkowskiForm (u₁, u₂) (v₁, v₂) := by
      rw [h]
      simp [minkowskiForm]

/-- Simultaneously scaling both arguments scales the real Minkowski pairing
quadratically. -/
theorem minkowskiForm_smul_smul (r : ℝ) (u v : Vec11) :
    minkowskiForm (r • u) (r • v) = r ^ 2 * minkowskiForm u v := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  simp [minkowskiForm]
  ring

/-- The conformal boost flow scales the indefinite pairing by the expected
factor `exp (4 * sigma * s)`. -/
theorem conformalBoostFlow_scales_minkowski
    (sigma s : ℝ) (u v : Vec11) :
    minkowskiForm (conformalBoostFlow sigma s u)
        (conformalBoostFlow sigma s v) =
      Real.exp (4 * sigma * s) * minkowskiForm u v := by
  change minkowskiForm
      (Real.exp (2 * sigma * s) • boostFlow s u)
      (Real.exp (2 * sigma * s) • boostFlow s v) = _
  rw [minkowskiForm_smul_smul, boostFlow_preserves_minkowski]
  have hexp : Real.exp (2 * sigma * s) ^ 2 = Real.exp (4 * sigma * s) := by
    calc
      Real.exp (2 * sigma * s) ^ 2 =
          Real.exp (2 * sigma * s) * Real.exp (2 * sigma * s) := by rw [pow_two]
      _ = Real.exp (2 * sigma * s + 2 * sigma * s) := by rw [← Real.exp_add]
      _ = Real.exp (4 * sigma * s) := by congr 1; ring
  rw [hexp]

/-- The infinitesimal Lorentz generator is skew for the Minkowski form. -/
theorem boostGenerator_minkowski_skew (u v : Vec11) :
    minkowskiForm (boostGenerator u) v + minkowskiForm u (boostGenerator v) = 0 := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  dsimp [minkowskiForm, boostGenerator]
  ring

/-- The infinitesimal generator combining a Lorentz boost with a uniform
homothety of rate `2 * sigma`. -/
def conformalBoostGenerator (sigma : ℝ) (v : Vec11) : Vec11 :=
  (2 * sigma * v.1 + v.2, 2 * sigma * v.2 + v.1)

/-- The boost-plus-homothety generator is conformal Killing for the real
`(1,1)` Minkowski pairing, with conformal factor `2 * sigma` (so the
symmetrized pairing has factor `4 * sigma`). -/
theorem conformalBoostGenerator_minkowski_conformal
    (sigma : ℝ) (u v : Vec11) :
    minkowskiForm (conformalBoostGenerator sigma u) v +
      minkowskiForm u (conformalBoostGenerator sigma v) =
        4 * sigma * minkowskiForm u v := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  dsimp [minkowskiForm, conformalBoostGenerator]
  ring_nf

/-- Setting the homothety rate to zero recovers the strict Killing
generator identity. -/
theorem conformalBoostGenerator_zero_minkowski_skew (u v : Vec11) :
    minkowskiForm (conformalBoostGenerator 0 u) v +
      minkowskiForm u (conformalBoostGenerator 0 v) = 0 := by
  simpa [conformalBoostGenerator, boostGenerator] using
    boostGenerator_minkowski_skew u v

/-- Subtracting the field at the origin removes the affine translation. -/
theorem affineTemperatureField_sub_base (b u : Vec11) :
    affineTemperatureField b u - affineTemperatureField b (0, 0) =
      boostGenerator u := by
  rcases b with ⟨b₁, b₂⟩
  rcases u with ⟨u₁, u₂⟩
  simp [affineTemperatureField, boostGenerator]

/-- The affine Souriau inverse-temperature field has the flat Killing
identity after its constant translation is removed. -/
theorem affineTemperatureField_linear_part_killing (b u v : Vec11) :
    minkowskiForm (affineTemperatureField b u - affineTemperatureField b (0, 0)) v +
      minkowskiForm u (affineTemperatureField b v - affineTemperatureField b (0, 0)) = 0 := by
  rw [affineTemperatureField_sub_base, affineTemperatureField_sub_base]
  exact boostGenerator_minkowski_skew u v

/-- The two coordinate derivatives of the boost flow reproduce its generator. -/
theorem hasDerivAt_boostFlow_fst (v : Vec11) (s : ℝ) :
    HasDerivAt (fun r => (boostFlow r v).1) (boostFlow s v).2 s := by
  rcases v with ⟨v₁, v₂⟩
  convert (((hasDerivAt_id s).cosh.const_mul v₁).add
      ((hasDerivAt_id s).sinh.const_mul v₂)) using 1
  · ext r
    simp [boostFlow]
    ring
  · simp [boostFlow]
    ring

theorem hasDerivAt_boostFlow_snd (v : Vec11) (s : ℝ) :
    HasDerivAt (fun r => (boostFlow r v).2) (boostFlow s v).1 s := by
  rcases v with ⟨v₁, v₂⟩
  convert (((hasDerivAt_id s).sinh.const_mul v₁).add
      ((hasDerivAt_id s).cosh.const_mul v₂)) using 1
  · ext r
    simp [boostFlow]
    ring
  · simp [boostFlow]
    ring

/-- The derivative at zero is exactly the boost Killing generator. -/
theorem boostFlow_derivative_at_zero (v : Vec11) :
    HasDerivAt (fun s => (boostFlow s v).1) (boostGenerator v).1 0 ∧
      HasDerivAt (fun s => (boostFlow s v).2) (boostGenerator v).2 0 := by
  constructor
  · simpa [boostGenerator] using hasDerivAt_boostFlow_fst v 0
  · simpa [boostGenerator] using hasDerivAt_boostFlow_snd v 0

/-- The conformal boost flow differentiates at the identity to the sum of
the Lorentz Killing generator and its real scalar-dilation generator. -/
theorem conformalBoostFlow_derivative_at_zero (sigma : ℝ) (v : Vec11) :
    HasDerivAt (fun s => (conformalBoostFlow sigma s v).1)
      (conformalBoostGenerator sigma v).1 0 ∧
    HasDerivAt (fun s => (conformalBoostFlow sigma s v).2)
      (conformalBoostGenerator sigma v).2 0 := by
  have hExp : HasDerivAt (fun s : ℝ => Real.exp (2 * sigma * s))
      (2 * sigma) 0 := by
    have hArg : HasDerivAt (fun s : ℝ => 2 * sigma * s) (2 * sigma) 0 := by
      convert (hasDerivAt_id 0).const_mul (2 * sigma) using 1 <;> simp
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (2 * sigma * 0)).comp 0 hArg
  constructor
  · convert hExp.mul (hasDerivAt_boostFlow_fst v 0) using 1
    · ext s
      simp [conformalBoostFlow]
    · simp [boostFlow, conformalBoostGenerator]
  · convert hExp.mul (hasDerivAt_boostFlow_snd v 0) using 1
    · ext s
      simp [conformalBoostFlow]
    · simp [boostFlow, conformalBoostGenerator]

/-! ## The Rindler Killing plane inside real `(1,3)` Minkowski space

The `Cl(1,1)` rotor acts on the time/longitudinal plane of the existing
four-dimensional real Minkowski carrier. The transverse coordinates remain
fixed; no complex scalar carrier is introduced. -/

abbrev Minkowski4 := InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4

/-- The real `(1,3)` Minkowski bilinear pairing in `(t,x,y,z)` coordinates. -/
def minkowski4Form (u v : Minkowski4) : ℝ :=
  u.t * v.t - u.x * v.x - u.y * v.y - u.z * v.z

/-- The self-pairing uses exactly the established interval owner and its
`(+---)` signature; this prevents the bridge from silently introducing a
second metric convention. -/
theorem minkowski4Form_self_eq_interval (X : Minkowski4) :
    minkowski4Form X X =
      InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X := by
  cases X with
  | mk t x y z =>
    simp [minkowski4Form,
      InfoGeometry.Canonical.RealSpacetime4x4Closure.interval]
    ring

/-- A general real Lorentz-algebra infinitesimal on the established
`(+---)` coordinate carrier. The first three parameters are boosts in the
`tx`, `ty`, and `tz` planes; the remaining three are rotations in the
`xy`, `xz`, and `yz` planes. -/
def lorentzGenerator4 (btx bty btz rxy rxz ryz : ℝ) (X : Minkowski4) : Minkowski4 :=
  ⟨btx * X.x + bty * X.y + btz * X.z,
    btx * X.t + rxy * X.y + rxz * X.z,
    bty * X.t - rxy * X.x + ryz * X.z,
    btz * X.t - rxz * X.x - ryz * X.y⟩

/-- The affine inverse-temperature vector field with arbitrary constant
translation and constant real Lorentz-algebra linear part. -/
def affineLorentzTemperatureField4
    (btx bty btz rxy rxz ryz : ℝ) (c X : Minkowski4) : Minkowski4 :=
  ⟨c.t + (lorentzGenerator4 btx bty btz rxy rxz ryz X).t,
    c.x + (lorentzGenerator4 btx bty btz rxy rxz ryz X).x,
    c.y + (lorentzGenerator4 btx bty btz rxy rxz ryz X).y,
    c.z + (lorentzGenerator4 btx bty btz rxy rxz ryz X).z⟩

/-- Every linear generator in the real six-dimensional Lorentz Lie algebra
is skew with respect to the actual Minkowski bilinear form. This is the
coordinate Killing identity for arbitrary simultaneous boosts and rotations. -/
theorem lorentzGenerator4_minkowski_skew
    (btx bty btz rxy rxz ryz : ℝ) (u v : Minkowski4) :
    minkowski4Form (lorentzGenerator4 btx bty btz rxy rxz ryz u) v +
      minkowski4Form u (lorentzGenerator4 btx bty btz rxy rxz ryz v) = 0 := by
  cases u with
  | mk ut ux uy uz =>
    cases v with
    | mk vt vx vy vz =>
      simp [minkowski4Form, lorentzGenerator4]
      ring_nf

/-- The conformal extension of a Lorentz infinitesimal by uniform dilation
with infinitesimal scale `2 * sigma`. -/
def conformalLorentzGenerator4 (sigma btx bty btz rxy rxz ryz : ℝ)
    (X : Minkowski4) : Minkowski4 :=
  ⟨2 * sigma * X.t + (lorentzGenerator4 btx bty btz rxy rxz ryz X).t,
    2 * sigma * X.x + (lorentzGenerator4 btx bty btz rxy rxz ryz X).x,
    2 * sigma * X.y + (lorentzGenerator4 btx bty btz rxy rxz ryz X).y,
    2 * sigma * X.z + (lorentzGenerator4 btx bty btz rxy rxz ryz X).z⟩

/-- Adding a uniform infinitesimal dilation to a Lorentz generator changes
the metric derivative by the conformal factor `4 * sigma`. -/
theorem conformalLorentzGenerator4_metric_derivative
    (sigma btx bty btz rxy rxz ryz : ℝ) (u v : Minkowski4) :
    minkowski4Form (conformalLorentzGenerator4 sigma btx bty btz rxy rxz ryz u) v +
      minkowski4Form u (conformalLorentzGenerator4 sigma btx bty btz rxy rxz ryz v) =
        4 * sigma * minkowski4Form u v := by
  have hLor := lorentzGenerator4_minkowski_skew btx bty btz rxy rxz ryz u v
  cases u with
  | mk ut ux uy uz =>
    cases v with
    | mk vt vx vy vz =>
      simp [conformalLorentzGenerator4, minkowski4Form, lorentzGenerator4] at hLor ⊢
      linear_combination (2 * sigma) * hLor

/-- Adding a constant inverse-temperature vector to a Lorentz-linear field
does not change its directional increment. -/
theorem affineLorentzTemperatureField_directional_increment
    (btx bty btz rxy rxz ryz : ℝ) (c X h : Minkowski4) :
    affineLorentzTemperatureField4 btx bty btz rxy rxz ryz c
      ⟨X.t + h.t, X.x + h.x, X.y + h.y, X.z + h.z⟩ =
      ⟨c.t + (lorentzGenerator4 btx bty btz rxy rxz ryz X).t +
          (lorentzGenerator4 btx bty btz rxy rxz ryz h).t,
        c.x + (lorentzGenerator4 btx bty btz rxy rxz ryz X).x +
          (lorentzGenerator4 btx bty btz rxy rxz ryz h).x,
        c.y + (lorentzGenerator4 btx bty btz rxy rxz ryz X).y +
          (lorentzGenerator4 btx bty btz rxy rxz ryz h).y,
        c.z + (lorentzGenerator4 btx bty btz rxy rxz ryz X).z +
          (lorentzGenerator4 btx bty btz rxy rxz ryz h).z⟩ := by
  cases c with
  | mk ct cx cy cz =>
    cases X with
    | mk xt xx xy xz =>
      cases h with
      | mk ht hx hy hz =>
        simp [affineLorentzTemperatureField4, lorentzGenerator4]
        ring_nf
        trivial

/-- The boost Killing field in the longitudinal `(t,z)` plane. -/
def rindlerKillingGenerator (X : Minkowski4) : Minkowski4 :=
  ⟨X.z, 0, 0, X.t⟩

/-- A constant-shifted inverse-temperature vector field with the Rindler
boost as its linear part. -/
def rindlerInverseTemperatureField (b X : Minkowski4) : Minkowski4 :=
  ⟨b.t + X.z, b.x, b.y, b.z + X.t⟩

/-- The existing Rindler inverse-temperature field is exactly the pure
`tz`-boost member of the six-parameter affine Lorentz family. -/
theorem rindlerInverseTemperatureField_eq_affineLorentzTemperatureField4
    (c X : Minkowski4) :
    rindlerInverseTemperatureField c X =
      affineLorentzTemperatureField4 0 0 1 0 0 0 c X := by
  cases c with
  | mk ct cx cy cz =>
    cases X with
    | mk xt xx xy xz =>
      simp [rindlerInverseTemperatureField,
        affineLorentzTemperatureField4, lorentzGenerator4]

/-- The longitudinal projection used by the native real `Cl(1,1)` rotor. -/
def rindlerPlaneProjection (X : Minkowski4) : Vec11 := (X.t, X.z)

/-- The Rindler generator is Killing for the full real `(1,3)` Minkowski
pairing, not only for its `(1,1)` longitudinal restriction. -/
theorem rindlerKillingGenerator_minkowski4_skew (u v : Minkowski4) :
    minkowski4Form (rindlerKillingGenerator u) v +
      minkowski4Form u (rindlerKillingGenerator v) = 0 := by
  cases u with
  | mk ut ux uy uz =>
    cases v with
    | mk vt vx vy vz =>
      simp [minkowski4Form, rindlerKillingGenerator]

/-- The affine inverse-temperature field has the Rindler Killing generator
as its exact directional increment. This records the derivative without
assuming an additive-group structure on the spacetime record. -/
theorem rindlerInverseTemperatureField_directional_increment
    (b X h : Minkowski4) :
    rindlerInverseTemperatureField b
        ⟨X.t + h.t, X.x + h.x, X.y + h.y, X.z + h.z⟩ =
      ⟨(rindlerInverseTemperatureField b X).t +
          (rindlerKillingGenerator h).t,
        (rindlerInverseTemperatureField b X).x +
          (rindlerKillingGenerator h).x,
        (rindlerInverseTemperatureField b X).y +
          (rindlerKillingGenerator h).y,
        (rindlerInverseTemperatureField b X).z +
          (rindlerKillingGenerator h).z⟩ := by
  rw [rindlerInverseTemperatureField_eq_affineLorentzTemperatureField4,
    rindlerInverseTemperatureField_eq_affineLorentzTemperatureField4]
  simpa [rindlerKillingGenerator, lorentzGenerator4,
    affineLorentzTemperatureField4] using
    affineLorentzTemperatureField_directional_increment
      0 0 1 0 0 0 b X h

/-- Projection of the full four-dimensional Rindler boost agrees exactly
with the existing real `Cl(1,1)` boost flow. -/
theorem rindler_boost_projects_to_lipschitz_flow
    (X : Minkowski4) (s : ℝ) :
    rindlerPlaneProjection
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s) =
      boostFlow s (rindlerPlaneProjection X) := by
  cases X with
  | mk t x y z =>
    change (t * Real.cosh s + z * Real.sinh s,
        z * Real.cosh s + t * Real.sinh s) =
      (Real.cosh s * t + Real.sinh s * z,
        Real.sinh s * t + Real.cosh s * z)
    congr 1 <;> ring

/-- The full Rindler flow preserves the real `(1,3)` Minkowski form; its
longitudinal part is the already-owned spin/Lipschitz rotor flow. -/
theorem rindler_boost_preserves_minkowski4 (X : Minkowski4) (s : ℝ) :
    minkowski4Form
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s)
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s) =
      minkowski4Form X X := by
  cases X with
  | mk t x y z =>
    simp [minkowski4Form,
      InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost]
    have h := Real.cosh_sq_sub_sinh_sq s
    nlinarith [h]

/-- The closed future causal cone on the real `(1,3)` carrier, expressed in
the two null coordinates of the longitudinal boost plane. The transverse
causal bound is `x² + y² ≤ (t + z)(t - z)`, equivalent to nonnegative
Minkowski square when both null coordinates are nonnegative. -/
def rindlerFutureCausalCone4 (X : Minkowski4) : Prop :=
  0 ≤ X.t + X.z ∧ 0 ≤ X.t - X.z ∧
    X.x ^ 2 + X.y ^ 2 ≤ (X.t + X.z) * (X.t - X.z)

/-- The full real Rindler boost preserves the future causal cone in `(1,3)`.
Its two longitudinal null coordinates acquire positive reciprocal factors
`exp(s)` and `exp(-s)`, while the transverse bound is unchanged. -/
theorem rindler_boost_preserves_futureCausalCone4
    (X : Minkowski4) (s : ℝ) (hX : rindlerFutureCausalCone4 X) :
    rindlerFutureCausalCone4
      (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s) := by
  cases X with
  | mk t x y z =>
    change 0 ≤ t + z ∧ 0 ≤ t - z ∧
      x ^ 2 + y ^ 2 ≤ (t + z) * (t - z) at hX
    change 0 ≤ _ ∧ 0 ≤ _ ∧ _ ≤ _
    simp only [InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost]
    rcases hX with ⟨hPlus, hMinus, hTransverse⟩
    have hPlusFlow :
        (t * Real.cosh s + z * Real.sinh s) +
            (z * Real.cosh s + t * Real.sinh s) =
          Real.exp s * (t + z) := by
      calc
        _ = (Real.cosh s + Real.sinh s) * (t + z) := by ring
        _ = Real.exp s * (t + z) := by rw [Real.cosh_add_sinh]
    have hMinusFlow :
        (t * Real.cosh s + z * Real.sinh s) -
            (z * Real.cosh s + t * Real.sinh s) =
          Real.exp (-s) * (t - z) := by
      calc
        _ = (Real.cosh s - Real.sinh s) * (t - z) := by ring
        _ = Real.exp (-s) * (t - z) := by rw [Real.cosh_sub_sinh]
    have hProduct :
        (Real.exp s * (t + z)) * (Real.exp (-s) * (t - z)) =
          (t + z) * (t - z) := by
      calc
        _ = (Real.exp s * Real.exp (-s)) * ((t + z) * (t - z)) := by ring
        _ = (t + z) * (t - z) := by
          rw [← Real.exp_add]
          simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hPlusFlow]
      exact mul_nonneg (le_of_lt (Real.exp_pos s)) hPlus
    · rw [hMinusFlow]
      exact mul_nonneg (le_of_lt (Real.exp_pos (-s))) hMinus
    · rw [hPlusFlow, hMinusFlow, hProduct]
      exact hTransverse

/-- The time and longitudinal coordinates of the full Rindler boost have
infinitesimal derivatives given by the boosted longitudinal coordinate and
time coordinate, respectively. -/
theorem hasDerivAt_rindler_boost_t (X : Minkowski4) (s : ℝ) :
    HasDerivAt
      (fun r =>
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X r).t)
      (rindlerKillingGenerator
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s)).t s := by
  cases X with
  | mk t x y z =>
    convert (((hasDerivAt_id s).cosh.const_mul t).add
      ((hasDerivAt_id s).sinh.const_mul z)) using 1
    · ext r
      simp [InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost]
    · simp [InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost,
        rindlerKillingGenerator]
      ring

/-- The longitudinal coordinate derivative is the time coordinate of the
boosted point. -/
theorem hasDerivAt_rindler_boost_z (X : Minkowski4) (s : ℝ) :
    HasDerivAt
      (fun r =>
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X r).z)
      (rindlerKillingGenerator
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s)).z s := by
  cases X with
  | mk t x y z =>
    convert (((hasDerivAt_id s).cosh.const_mul z).add
      ((hasDerivAt_id s).sinh.const_mul t)) using 1
    · ext r
      simp [InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost]
    · simp [InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost,
        rindlerKillingGenerator]
      ring

/-- At zero rapidity, the coordinatewise derivative of the full Rindler boost
is exactly its affine Killing generator. The transverse derivatives vanish. -/
theorem rindler_boost_derivative_at_zero (X : Minkowski4) :
    HasDerivAt
        (fun s =>
          (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s).t)
        (rindlerKillingGenerator X).t 0 ∧
    HasDerivAt
        (fun s =>
          (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s).x)
        0 0 ∧
    HasDerivAt
        (fun s =>
          (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s).y)
        0 0 ∧
    HasDerivAt
        (fun s =>
          (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s).z)
        (rindlerKillingGenerator X).z 0 := by
  cases X with
  | mk t x y z =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [rindlerKillingGenerator,
        InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost] using
        hasDerivAt_rindler_boost_t ⟨t, x, y, z⟩ 0
    · simpa [InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost] using
        (hasDerivAt_const (0 : ℝ) x)
    · simpa [InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost] using
        (hasDerivAt_const (0 : ℝ) y)
    · simpa [rindlerKillingGenerator,
        InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost] using
        hasDerivAt_rindler_boost_z ⟨t, x, y, z⟩ 0

/-! ## The finite `Cl(1,1)` rotor -/

/-- The finite algebraic factor in Kosmann's spinorial correction, for `B`
interpreted as the already-contracted Clifford bivector
`(∇ₐ βᵦ) γᵃγᵇ`. This is only the correction term: this owner does not define a
spinor bundle, a connection, or a curved-spacetime Kosmann derivative. -/
def kosmannCorrection (B ψ : Mat2) : Mat2 :=
  ((-1 : ℝ) / 4) • (B * ψ)

/-- The finite Kosmann correction agrees with the established Rindler spin
lift's left action when the contracted bivector is normalized as
`2 * a * v.1 * J1`. This is an algebraic interface only; the existing owner
supplies the connection and its spin-to-vector adjoint, not a curved spinor
bundle. -/
theorem kosmannCorrection_eq_rindlerSpinLift_left_action
    (a : ℝ) (v : InfoGeometry.Geometry.RindlerCartanFrame.Tangent) (ψ : Mat2) :
    kosmannCorrection ((2 * a * v.1) • J1) ψ =
      spinLift a 0 0
        (0 : InfoGeometry.Geometry.RindlerCartanFrame.Tangent →ₗ[ℝ] ℝ) v * ψ := by
  simp [kosmannCorrection, spinLift, smul_smul, neg_smul]
  rw [← neg_smul]
  congr 1
  ring

/-- A finite, conditional Kosmann datum records the concrete carriers needed
for a spinorial Lie-derivative calculation. It is not a spinor bundle: the
connection, covariant derivative, and Killing field are explicit finite data.
The Rindler instance below supplies all fields from existing owners. -/
structure FiniteKosmannDatum where
  killingGenerator : Vec11 → Vec11
  vectorConnection : InfoGeometry.Geometry.RindlerCartanFrame.Tangent → Mat2
  spinConnection : InfoGeometry.Geometry.RindlerCartanFrame.Tangent → Mat2
  contractedBivector : InfoGeometry.Geometry.RindlerCartanFrame.Tangent → Mat2
  killing_generator_skew : ∀ u v,
    minkowskiForm (killingGenerator u) v +
      minkowskiForm u (killingGenerator v) = 0
  vectorConnection_lorentz_skew : ∀ v,
    (vectorConnection v).transpose *
          InfoGeometry.Geometry.RindlerCartanFrame.metricMatrix +
      InfoGeometry.Geometry.RindlerCartanFrame.metricMatrix * vectorConnection v = 0
  spinConnection_adjoint : ∀ v u,
    spinConnection v * cliffordVector u -
      cliffordVector u * spinConnection v =
      cliffordVector ((vectorConnection v).mulVec u)

/-- The finite spinor covariant derivative is constructed by the stored spin
connection acting on the explicit matrix-spinor carrier. The connection law
is therefore definitional, not a field assumed of each datum. -/
def FiniteKosmannDatum.covariantDerivative (D : FiniteKosmannDatum)
    (v : InfoGeometry.Geometry.RindlerCartanFrame.Tangent) (ψ : Mat2) : Mat2 :=
  D.spinConnection v * ψ

/-- The concrete finite Rindler Kosmann datum. -/
def rindlerFiniteKosmannDatum (a : ℝ) : FiniteKosmannDatum where
  killingGenerator := boostGenerator
  vectorConnection := fun v => lorentzConnection a 0 0 v
  spinConnection := fun v =>
    spinLift a 0 0
      (0 : InfoGeometry.Geometry.RindlerCartanFrame.Tangent →ₗ[ℝ] ℝ) v
  contractedBivector := fun v => (2 * a * v.1) • J1
  killing_generator_skew := boostGenerator_minkowski_skew
  vectorConnection_lorentz_skew := by
    intro v
    exact lorentzConnection_lorentz_skew a 0 0 v
  spinConnection_adjoint := by
    intro v u
    exact spinLift_adjoint a 0 0
      (0 : InfoGeometry.Geometry.RindlerCartanFrame.Tangent →ₗ[ℝ] ℝ) v u

/-- In the finite Rindler datum, the contracted Kosmann correction is the
spin-connection action on the explicit matrix spinor carrier. -/
theorem rindlerFiniteKosmannDatum_correction_eq_covariantDerivative
    (a : ℝ) (v : InfoGeometry.Geometry.RindlerCartanFrame.Tangent) (ψ : Mat2) :
    kosmannCorrection
        ((rindlerFiniteKosmannDatum a).contractedBivector v) ψ =
      (rindlerFiniteKosmannDatum a).covariantDerivative v ψ := by
  simpa [rindlerFiniteKosmannDatum, FiniteKosmannDatum.covariantDerivative] using
    kosmannCorrection_eq_rindlerSpinLift_left_action a v ψ

theorem kosmannCorrection_add (B₁ B₂ ψ : Mat2) :
    kosmannCorrection (B₁ + B₂) ψ =
      kosmannCorrection B₁ ψ + kosmannCorrection B₂ ψ := by
  simp [kosmannCorrection, add_mul, smul_add]

theorem kosmannCorrection_smul (r : ℝ) (B ψ : Mat2) :
    kosmannCorrection (r • B) ψ = r • kosmannCorrection B ψ := by
  simp [kosmannCorrection, smul_smul]
  congr 1
  ring

/-- The matrix rotor with generator `J1 = E₊E₋`.  The minus sign fixes the
orientation so that its vector action is the positive Rindler boost. -/
def boostRotor (s : ℝ) : Mat2 :=
  (Real.cosh (s / 2)) • (1 : Mat2) - (Real.sinh (s / 2)) • J1

/-- Matrix reversal of the boost rotor. -/
def boostRotorReverse (s : ℝ) : Mat2 :=
  (Real.cosh (s / 2)) • (1 : Mat2) + (Real.sinh (s / 2)) • J1

/-- Under the explicit `Cl(1,1)` normalization that assigns the contracted
Rindler bivector `2 * J1`, the finite Kosmann correction is the infinitesimal
left action of the real boost rotor. -/
theorem kosmannCorrection_rindler_generator (ψ : Mat2) :
    kosmannCorrection ((2 : ℝ) • J1) ψ =
      (-((1 / 2 : ℝ) • J1)) * ψ := by
  simp [kosmannCorrection]
  rw [smul_smul]
  norm_num

/-- The derivative at zero of each matrix coefficient of the Rindler rotor
is the same bivector generator that appears in the finite Kosmann term. -/
theorem hasDerivAt_boostRotor_zero (i j : Fin 2) :
    HasDerivAt (fun s : ℝ => boostRotor s i j)
      ((-((1 / 2 : ℝ) • J1)) i j) 0 := by
  fin_cases i <;> fin_cases j
  · simpa [boostRotor, J1, Matrix.smul_apply, Matrix.sub_apply] using
      (((hasDerivAt_id (0 : ℝ)).div_const 2).cosh)
  · convert (((hasDerivAt_id (0 : ℝ)).div_const 2).sinh).neg using 1
    · funext s
      simp [boostRotor, J1, Matrix.smul_apply, Matrix.sub_apply]
    · norm_num [J1]
  · convert (((hasDerivAt_id (0 : ℝ)).div_const 2).sinh).neg using 1
    · funext s
      simp [boostRotor, J1, Matrix.smul_apply, Matrix.sub_apply]
    · norm_num [J1]
  · simpa [boostRotor, J1, Matrix.smul_apply, Matrix.sub_apply] using
      (((hasDerivAt_id (0 : ℝ)).div_const 2).cosh)

/-- The infinitesimal left action of the Rindler rotor on a real matrix
spinor is exactly the finite Kosmann correction under the stated contracted
bivector normalization `2 * J1`. This is a coefficientwise derivative on
`M₂(ℝ)`. -/
theorem hasDerivAt_boostRotor_spinorAction_zero (ψ : Mat2) (i j : Fin 2) :
    HasDerivAt (fun s : ℝ => (boostRotor s * ψ) i j)
      (kosmannCorrection ((2 : ℝ) • J1) ψ i j) 0 := by
  have h₀ := (hasDerivAt_boostRotor_zero i 0).mul_const (ψ 0 j)
  have h₁ := (hasDerivAt_boostRotor_zero i 1).mul_const (ψ 1 j)
  convert h₀.add h₁ using 1
  · funext s
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [kosmannCorrection_rindler_generator]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- The matrix rotor used below is exactly the image of the reverse of the
existing real `Cl(1,1)` spin rotor at half rapidity. This fixes both the basis
and the factor-of-two convention against the Hestenes owner. -/
theorem boostRotor_eq_cl11SpinRotorReverse (s : ℝ) :
    boostRotor s = cl11EquivMat
      (CliffordAlgebra.reverse (cl11HyperbolicRotor (s / 2))) := by
  rw [cl11HyperbolicRotor_reverse]
  have hJ : cl11EquivMat J1_cl = J1 := by
    rw [show J1_cl = CliffordAlgebra.ι q11 (1, 0) *
        CliffordAlgebra.ι q11 (0, 1) from rfl,
      map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg,
      Eplus_mul_Eminus]
  simp [boostRotor, hJ]

/-- The inverse rotor in the matrix sandwich comes from a genuine member of
Mathlib's real spin group, rather than merely a matrix satisfying a norm
identity. -/
theorem cl11SpinRotor_halfRapidity_mem_spinGroup (s : ℝ) :
    cl11HyperbolicRotor (s / 2) ∈ spinGroup q11 :=
  cl11HyperbolicRotor_mem_spinGroup (s / 2)

private theorem cl11EquivMat_iota_eq_gen (v : Vec11) :
    cl11EquivMat (CliffordAlgebra.ι q11 v) = gen v := by
  change cl11ToMat (CliffordAlgebra.ι q11 v) = gen v
  simp [cl11ToMat]

@[simp] theorem boostRotor_mul_reverse (s : ℝ) :
    boostRotor s * boostRotorReverse s = (1 : Mat2) := by
  have h := Real.cosh_sq_sub_sinh_sq (s / 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostRotor, boostRotorReverse, J1, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply]
  all_goals nlinarith [h]

@[simp] theorem boostRotor_reverse_mul (s : ℝ) :
    boostRotorReverse s * boostRotor s = (1 : Mat2) := by
  have h := Real.cosh_sq_sub_sinh_sq (s / 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostRotor, boostRotorReverse, J1, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply]
  all_goals nlinarith [h]

/-- The matrix-side spin sandwich on the Clifford vector representation. -/
def rotorVectorAction (s : ℝ) (v : Vec11) : Mat2 :=
  boostRotor s * gen v * boostRotorReverse s

/-- A real scalar-dilated boost rotor. Its reverse uses the same positive
scalar factor, so its Clifford norm is no longer forced to be one. -/
def homothetyBoostRotor (sigma s : ℝ) : Mat2 :=
  Real.exp (sigma * s) • boostRotor s

/-- Reverse of the scalar-dilated boost rotor. -/
def homothetyBoostRotorReverse (sigma s : ℝ) : Mat2 :=
  Real.exp (sigma * s) • boostRotorReverse s

/-- The spinor norm of the homothety rotor is the expected positive scale. -/
theorem homothetyBoostRotor_norm (sigma s : ℝ) :
    homothetyBoostRotor sigma s * homothetyBoostRotorReverse sigma s =
      Real.exp (2 * sigma * s) • (1 : Mat2) := by
  simp [homothetyBoostRotor, homothetyBoostRotorReverse, smul_smul,
    boostRotor_mul_reverse, show 2 * sigma * s = sigma * s + sigma * s by ring,
    Real.exp_add]

theorem rotorVectorAction_eq_gen_boostFlow (s : ℝ) (v : Vec11) :
    rotorVectorAction s v = gen (boostFlow s v) := by
  rcases v with ⟨v₁, v₂⟩
  have hc : Real.cosh s = Real.cosh (s / 2) ^ 2 +
      Real.sinh (s / 2) ^ 2 := by
    rw [show s = 2 * (s / 2) by ring, Real.cosh_two_mul]
    congr 1 <;> ring_nf
  have hs : Real.sinh s = 2 * Real.sinh (s / 2) * Real.cosh (s / 2) := by
    rw [show s = 2 * (s / 2) by ring, Real.sinh_two_mul]
    congr 1 <;> ring_nf
  dsimp [rotorVectorAction, boostRotor, boostRotorReverse, gen, boostFlow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply]
  all_goals
    rw [hc, hs]
    ring

/-- The unnormalized rotor sandwich realizes the conformal boost flow on
the real vector representation. -/
theorem homothetyBoostRotor_sandwich (sigma s : ℝ) (v : Vec11) :
    homothetyBoostRotor sigma s * gen v * homothetyBoostRotorReverse sigma s =
      gen (conformalBoostFlow sigma s v) := by
  rw [homothetyBoostRotor, homothetyBoostRotorReverse]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  change (Real.exp (sigma * s) * Real.exp (sigma * s)) •
      rotorVectorAction s v = gen (conformalBoostFlow sigma s v)
  rw [rotorVectorAction_eq_gen_boostFlow, conformalBoostFlow, gen.map_smul]
  have hexp : Real.exp (sigma * s) * Real.exp (sigma * s) =
      Real.exp (2 * sigma * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]

/-- The boost action is the Clifford-algebra sandwich transported through
the real algebra equivalence `Cl(1,1) ≃ₐ[ℝ] M₂(ℝ)`. -/
theorem rotorVectorAction_eq_cl11SpinSandwich (s : ℝ) (v : Vec11) :
    rotorVectorAction s v = cl11EquivMat
      (CliffordAlgebra.reverse (cl11HyperbolicRotor (s / 2)) *
        CliffordAlgebra.ι q11 v * cl11HyperbolicRotor (s / 2)) := by
  have hR : boostRotorReverse s =
      cl11EquivMat (cl11HyperbolicRotor (s / 2)) := by
    rw [cl11EquivMat_cl11HyperbolicRotor]
    rfl
  rw [rotorVectorAction, boostRotor_eq_cl11SpinRotorReverse, hR]
  simp only [map_mul, cl11EquivMat_iota_eq_gen]

/-- The explicit boost flow is the action of a genuine `Cl(1,1)` spin-group
element under the existing basis-free isometry homomorphism. The inverse
rapidity is chosen because the spin action is `g v reverse(g)` while the
matrix formula above is written with the reverse rotor on the left. -/
theorem cl11SpinGroupAction_eq_boostFlow (s : ℝ) (v : Vec11) :
    spinGroupToIsometryHom q11
      ⟨cl11HyperbolicRotor (-s / 2),
        cl11HyperbolicRotor_mem_spinGroup (-s / 2)⟩ v = boostFlow s v := by
  apply InfoGeometry.Clifford.GradedGraceContraction.clifford_ι_injective q11
  change CliffordAlgebra.ι q11
      (spinGroupIsometryEquiv q11
        ⟨cl11HyperbolicRotor (-s / 2),
          cl11HyperbolicRotor_mem_spinGroup (-s / 2)⟩ v) = _
  rw [ι_spinGroupIsometryEquiv]
  apply cl11EquivMat.injective
  have hJ : cl11EquivMat J1_cl = J1 := by
    rw [show J1_cl = CliffordAlgebra.ι q11 (1, 0) *
        CliffordAlgebra.ι q11 (0, 1) from rfl,
      map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg,
      Eplus_mul_Eminus]
  have hRotor : cl11EquivMat (cl11HyperbolicRotor (-s / 2)) =
      boostRotor s := by
    rw [cl11EquivMat_cl11HyperbolicRotor]
    simp [boostRotor, Real.cosh_neg, Real.sinh_neg, neg_div]
    rw [sub_eq_add_neg]
  have hReverse : cl11EquivMat
      (CliffordAlgebra.reverse (cl11HyperbolicRotor (-s / 2))) =
        boostRotorReverse s := by
    rw [cl11HyperbolicRotor_reverse, map_sub, map_smul, map_smul, map_one,
      hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [boostRotorReverse, Real.cosh_neg, Real.sinh_neg, neg_div,
        J1, Matrix.smul_apply]
  rw [map_mul, map_mul, cl11EquivMat_iota_eq_gen, hRotor, hReverse]
  rw [← rotorVectorAction]
  rw [cl11EquivMat_iota_eq_gen]
  exact rotorVectorAction_eq_gen_boostFlow s v

/-- The infinitesimal real spin-group orbit of the Rindler boost is the
translation-free part of the affine inverse-temperature field. Thus the
affine Killing generator is represented by the existing `Cl(1,1)` spin
action, with the constant inverse-temperature offset kept separate. -/
theorem affineTemperatureField_linear_part_eq_spinGroup_orbit_derivative
    (b v : Vec11) :
    HasDerivAt
      (fun s => (spinGroupToIsometryHom q11
        ⟨cl11HyperbolicRotor (-s / 2),
          cl11HyperbolicRotor_mem_spinGroup (-s / 2)⟩ v).1)
      (affineTemperatureField b v - affineTemperatureField b (0, 0)).1 0 ∧
    HasDerivAt
      (fun s => (spinGroupToIsometryHom q11
        ⟨cl11HyperbolicRotor (-s / 2),
          cl11HyperbolicRotor_mem_spinGroup (-s / 2)⟩ v).2)
      (affineTemperatureField b v - affineTemperatureField b (0, 0)).2 0 := by
  have hOrbit : (fun s => spinGroupToIsometryHom q11
      ⟨cl11HyperbolicRotor (-s / 2),
        cl11HyperbolicRotor_mem_spinGroup (-s / 2)⟩ v) =
      fun s => boostFlow s v := by
    funext s
    exact cl11SpinGroupAction_eq_boostFlow s v
  have hOrbitFst := congrArg
    (fun f : ℝ → Vec11 => fun s => (f s).1) hOrbit
  have hOrbitSnd := congrArg
    (fun f : ℝ → Vec11 => fun s => (f s).2) hOrbit
  rw [hOrbitFst, hOrbitSnd]
  simpa [affineTemperatureField_sub_base, boostGenerator] using
    boostFlow_derivative_at_zero v

/-- The same explicit boost, now stated through Mathlib's Lipschitz-group
action. The spin element is included in the pin group and then mapped into
`lipschitzGroup q11` using the owner inclusion theorem. -/
theorem cl11LipschitzAction_eq_boostFlow (s : ℝ) (v : Vec11) :
    lipschitzGroupToIsometryHom q11
      ⟨_root_.pinGroup.toUnits
          (⟨cl11HyperbolicRotor (-s / 2),
            _root_.spinGroup.mem_pin
              (cl11HyperbolicRotor_mem_spinGroup (-s / 2))⟩ : _root_.pinGroup q11),
        _root_.pinGroup.units_mem_lipschitzGroup
          (⟨cl11HyperbolicRotor (-s / 2),
            _root_.spinGroup.mem_pin
              (cl11HyperbolicRotor_mem_spinGroup (-s / 2))⟩ : _root_.pinGroup q11).2⟩ v =
      boostFlow s v := by
  let g : spinGroup q11 :=
    ⟨cl11HyperbolicRotor (-s / 2), cl11HyperbolicRotor_mem_spinGroup (-s / 2)⟩
  let p : _root_.pinGroup q11 := ⟨g.1, _root_.spinGroup.mem_pin g.2⟩
  change pinGroupToIsometryHom q11 p v = boostFlow s v
  rw [spinGroup_to_lipschitz_eq_spinGroupToIsometryHom]
  exact cl11SpinGroupAction_eq_boostFlow s v

/-- The concrete `Cl(1,1)` Lipschitz rotor preserves the Souriau future cone
on the real Minkowski carrier. This composes the basis-free Lipschitz action
identification with the null-coordinate cone invariance theorem. -/
theorem cl11LipschitzRotor_preserves_temperatureCone
    (s : ℝ) {v : Vec11} (hv : v ∈ rindlerTemperatureCone) :
    lipschitzGroupToIsometryHom q11
      ⟨_root_.pinGroup.toUnits
          (⟨cl11HyperbolicRotor (-s / 2),
            _root_.spinGroup.mem_pin
              (cl11HyperbolicRotor_mem_spinGroup (-s / 2))⟩ : _root_.pinGroup q11),
        _root_.pinGroup.units_mem_lipschitzGroup
          (⟨cl11HyperbolicRotor (-s / 2),
            _root_.spinGroup.mem_pin
              (cl11HyperbolicRotor_mem_spinGroup (-s / 2))⟩ : _root_.pinGroup q11).2⟩ v ∈
      rindlerTemperatureCone := by
  rw [cl11LipschitzAction_eq_boostFlow]
  exact boostFlow_preserves_rindlerTemperatureCone hv

/-- The rotor sandwich preserves the Clifford quadratic form on vectors. -/
theorem rotorVectorAction_preserves_q11 (s : ℝ) (v : Vec11) :
    q11 (boostFlow s v) = q11 v := by
  rcases v with ⟨v₁, v₂⟩
  rw [q11_apply, q11_apply]
  dsimp [boostFlow]
  calc
    _ = (Real.cosh s ^ 2 - Real.sinh s ^ 2) * (v₁ ^ 2 - v₂ ^ 2) := by ring
    _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]; ring

/-- The scalar normalization cancels in a normalized sandwich: the relevant
vector action is determined by the rotor and its reverse, not by an external
positive scalar factor. -/
theorem positive_scalar_sandwich_cancels (r : ℝ) (hr : r ≠ 0)
    (A : Mat2) :
    ((r : ℝ) • (1 : Mat2)) * A * ((r⁻¹ : ℝ) • (1 : Mat2)) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
    <;> field_simp [hr]

/-! ## Souriau/Rindler thermal normalization -/

theorem rindler_tolman_readback (T₀ a x : ℝ) (hx : lapse a x ≠ 0) :
    localTemperature T₀ a x * lapse a x = T₀ :=
  tolman_product T₀ a x hx

/-! ## Doubled-real modular flow on the canonical Krein carrier

This section reuses `BogoliubovTransport` on `DoubledSpace E`. Its results
concern the bounded operator generator `hMod ∘ clockAxis`; they do not assert
a curved-manifold spinor-bundle lift or identify this generator with an
arbitrary spacetime Killing field.
-/

section DoubledKreinModularFlow

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance

/-- The negative-sheet seed realizes the existing real sheet-swap operator. -/
@[simp] theorem doubled_relativeModularKGenerator_negativeSheet_eq_modular_j :
    relativeModularKGenerator (E := E) (-(spectral_epsilon (E := E))) =
      modular_j (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [relativeModularKGenerator, modularTransportGenerator, clockAxis]

section CompleteKrein

variable [CompleteSpace E]

local instance : KreinSpace H₂ := instKreinSpaceProdL2 (E := E)

/-- The relative modular generator `hMod ∘ clockAxis` has Krein adjoint
`clockAxis ∘ hMod♯` on the doubled real carrier. -/
theorem doubled_relativeModularKGenerator_kreinAdjoint (hMod : EndH) :
    KreinSpace.kreinAdjoint (relativeModularKGenerator (E := E) hMod) =
      (clockAxis (E := E)).comp (KreinSpace.kreinAdjoint hMod) := by
  simp only [relativeModularKGenerator, modularTransportGenerator,
    KreinSpace.kreinAdjoint_comp, clockAxis, kreinAdjoint_complex_i]

/-- Exact seed criterion for the relative modular generator to be
Krein-skew-adjoint. -/
theorem doubled_relativeModularKGenerator_isKreinSkewAdjoint_iff
    (hMod : EndH) :
    KreinSpace.IsKreinSkewAdjoint (relativeModularKGenerator (E := E) hMod) ↔
      (clockAxis (E := E)).comp (KreinSpace.kreinAdjoint hMod) =
        -(hMod.comp (clockAxis (E := E))) := by
  change
    KreinSpace.kreinAdjoint (relativeModularKGenerator (E := E) hMod) =
        -(hMod.comp (clockAxis (E := E))) ↔
      (clockAxis (E := E)).comp (KreinSpace.kreinAdjoint hMod) =
        -(hMod.comp (clockAxis (E := E)))
  rw [doubled_relativeModularKGenerator_kreinAdjoint]

/-- A Krein-self-adjoint seed that is antilinear for the real sheet axis
produces a Krein-skew-adjoint relative modular generator. -/
theorem doubled_relativeModularKGenerator_isKreinSkewAdjoint_of_seed
    (hMod : EndH)
    (hSelf : KreinSpace.IsKreinSelfAdjoint hMod)
    (hAnti : IsPhaseAntilinear (E := E) hMod) :
    KreinSpace.IsKreinSkewAdjoint (relativeModularKGenerator (E := E) hMod) := by
  apply (doubled_relativeModularKGenerator_isKreinSkewAdjoint_iff hMod).2
  change KreinSpace.kreinAdjoint hMod = hMod at hSelf
  rw [hSelf]
  change hMod.comp (clockAxis (E := E)) =
    -((clockAxis (E := E)).comp hMod) at hAnti
  simpa only [neg_neg] using congrArg Neg.neg hAnti.symm

/-- The concrete negative-sheet seed generates the real modular sheet swap,
which is already proved Krein-skew by the doubled-space owner. -/
theorem doubled_relativeModularKGenerator_negativeSheet_skew :
    KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) (-(spectral_epsilon (E := E)))) := by
  rw [doubled_relativeModularKGenerator_negativeSheet_eq_modular_j]
  exact isKreinSkewAdjoint_modular_j (E := E)

/-- Every Krein-skew relative modular generator exponentiates to an
isometry of the actual doubled signed pairing. -/
theorem doubled_modularTransportFlow_isKreinIsometry
    (hMod : EndH)
    (hGenerator : KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) hMod)) (t : ℝ) :
    KreinSpace.IsKreinIsometry (modularTransportFlow (E := E) hMod t) := by
  exact exp_preservesMetric (relativeModularKGenerator (E := E) hMod)
    hGenerator t

/-- The negative-sheet seed supplies a concrete Krein-isometric modular
flow, without replacing the indefinite pairing by a positive norm. -/
theorem doubled_negativeSheet_modularTransportFlow_isKreinIsometry (t : ℝ) :
    KreinSpace.IsKreinIsometry
      (modularTransportFlow (E := E) (-(spectral_epsilon (E := E))) t) := by
  exact doubled_modularTransportFlow_isKreinIsometry
    (-(spectral_epsilon (E := E)))
    doubled_relativeModularKGenerator_negativeSheet_skew t

/-- The exponential flow preserves the difference of the two real sheet
pairings, with the canonical `to_doubled` convention. -/
theorem doubled_modularTransportFlow_preserves_pairing
    (hMod : EndH)
    (hGenerator : KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) hMod))
    (t : ℝ) (x ξ y η : E) :
    KreinSpace.kreinInner
      (modularTransportFlow (E := E) hMod t (to_doubled x ξ))
      (modularTransportFlow (E := E) hMod t (to_doubled y η)) =
      inner ℝ x y - inner ℝ ξ η := by
  rw [doubled_modularTransportFlow_isKreinIsometry hMod hGenerator t]
  exact kreinInner_to_doubled x ξ y η

/-- The relative modular commutator preserves the Krein adjoint when its
generator is Krein-skew-adjoint. -/
theorem doubled_relativeModularDeriv_kreinAdjoint
    (hMod A : EndH)
    (hGenerator : KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) hMod)) :
    KreinSpace.kreinAdjoint (relativeModularDeriv (E := E) hMod A) =
      relativeModularDeriv (E := E) hMod (KreinSpace.kreinAdjoint A) := by
  simpa only [InfoGeometry.OperatorAlgebra.kreinCommutator_apply,
    InfoGeometry.OperatorAlgebra.kreinAdjoint, relativeModularDeriv,
    modularDeriv, transportCommutator, relativeModularKGenerator,
    ContinuousLinearMap.mul_def] using
    (InfoGeometry.OperatorAlgebra.kreinCommutator_kreinStar
      (relativeModularKGenerator (E := E) hMod) A hGenerator).symm

/-- The same derivation preserves Krein-self-adjoint observables. -/
theorem doubled_relativeModularDeriv_preserves_kreinSelfAdjoint
    (hMod A : EndH)
    (hGenerator : KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) hMod))
    (hA : KreinSpace.IsKreinSelfAdjoint A) :
    KreinSpace.IsKreinSelfAdjoint (relativeModularDeriv (E := E) hMod A) := by
  change KreinSpace.kreinAdjoint (relativeModularDeriv (E := E) hMod A) =
    relativeModularDeriv (E := E) hMod A
  rw [doubled_relativeModularDeriv_kreinAdjoint hMod A hGenerator]
  exact congrArg (relativeModularDeriv (E := E) hMod) hA

/-- The commutator derivation also preserves the Krein-skew-adjoint sector. -/
theorem doubled_relativeModularDeriv_preserves_kreinSkewAdjoint
    (hMod A : EndH)
    (hGenerator : KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) hMod))
    (hA : KreinSpace.IsKreinSkewAdjoint A) :
    KreinSpace.IsKreinSkewAdjoint (relativeModularDeriv (E := E) hMod A) := by
  change KreinSpace.IsKreinSkewAdjoint
    (transportCommutator (relativeModularKGenerator (E := E) hMod) A)
  rw [← lieBracket_eq_transportCommutator]
  exact KreinSpace.isKreinSkewAdjoint_lie hGenerator hA

end CompleteKrein

end DoubledKreinModularFlow

/-! ## Identification with the existing real `Cl(1,1)` boost -/

/-- Under the native coordinate readout `Vec11 → DoubledSpace ℝ`, the doubled
Krein pairing is the negative of the owner’s `(-,+)` Minkowski form. -/
theorem doubledKrein_pairing_eq_neg_minkowskiForm (u v : Vec11) :
    InfoGeometry.Krein.KreinSpace.kreinInner
      (InfoGeometry.Krein.to_doubled u.1 u.2)
      (InfoGeometry.Krein.to_doubled v.1 v.2) = -minkowskiForm u v := by
  rw [InfoGeometry.Krein.kreinInner_to_doubled]
  simp [minkowskiForm, mul_comm]
  ring

/-- The exact exponential flow generated by the negative-sheet relative
modular seed agrees, coordinate for coordinate, with the existing real
Rindler `Cl(1,1)` boost. This is a finite flat-space identification on
`DoubledSpace ℝ`, not a curved-spacetime Kosmann theorem. -/
theorem negativeSheet_modularFlow_eq_boostFlow (s : ℝ) (v : Vec11) :
    InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow (E := ℝ)
        (-(InfoGeometry.Krein.spectral_epsilon (E := ℝ))) s
        (InfoGeometry.Krein.to_doubled v.1 v.2) =
      InfoGeometry.Krein.to_doubled (boostFlow s v).1 (boostFlow s v).2 := by
  have hFlow :
      InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow (E := ℝ)
          (-(InfoGeometry.Krein.spectral_epsilon (E := ℝ))) s =
        InfoGeometry.Canonical.BogoliubovTransport.JBoost (E := ℝ) s := by
    apply ContinuousLinearMap.ext
    intro u
    change NormedSpace.exp
        (s • InfoGeometry.Canonical.BogoliubovTransport.relativeModularKGenerator (E := ℝ)
          (-(InfoGeometry.Krein.spectral_epsilon (E := ℝ)))) u =
      NormedSpace.exp
        (s • InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ
          (E := ℝ)) u
    rw [doubled_relativeModularKGenerator_negativeSheet_eq_modular_j]
  rw [hFlow,
    InfoGeometry.Canonical.BogoliubovClosedForms.JBoost_apply_modular_j]
  apply InfoGeometry.Krein.DoubledSpace.ext
  · simp [boostFlow, InfoGeometry.Krein.to_doubled]
  · simp [boostFlow, InfoGeometry.Krein.to_doubled]; ring

end InfoGeometry.Canonical.SouriauKillingLipschitzBridge
