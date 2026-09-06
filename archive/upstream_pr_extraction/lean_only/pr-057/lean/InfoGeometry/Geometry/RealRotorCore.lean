/-
InfoGeometry/Geometry/RealRotorCore.lean

Real rotor/chiral phase primitives for the geometric core.

Hard invariant:
- no scalar `Complex.I`;
- all phases are real rotors;
- all boosts are real split-Clifford boosts;
- all state motion occurs on a doubled real Krein space.

The complex compatibility layer, when needed, must be downstream only.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import InfoGeometry.Geometry.RealUpperHalfPlane

noncomputable section

namespace InfoGeometry.Geometry

/-- A real `SL₂(ℝ)` matrix, written by entries. -/
abbrev SL2RMatrix := Matrix.SpecialLinearGroup (Fin 2) ℝ

namespace SL2RMatrix

abbrev a (g : SL2RMatrix) : ℝ := g.1 0 0
abbrev b (g : SL2RMatrix) : ℝ := g.1 0 1
abbrev c (g : SL2RMatrix) : ℝ := g.1 1 0
abbrev d (g : SL2RMatrix) : ℝ := g.1 1 1
abbrev det_eq_one (g : SL2RMatrix) : g.1.det = 1 := g.2

end SL2RMatrix

/--
Real chiral phase element.

Interpretation: `scalar + bivector * J`, where `J² = -1`.
This is not a complex number. It is a real two-component rotor coordinate.
-/
abbrev RealChiralPhase := ℝ × ℝ

namespace RealChiralPhase

abbrev scalar (z : RealChiralPhase) : ℝ := z.1
abbrev bivector (z : RealChiralPhase) : ℝ := z.2

/-- Norm square of a real chiral phase. -/
def normSq (z : RealChiralPhase) : ℝ :=
  z.scalar ^ 2 + z.bivector ^ 2

/-- The norm square of a real chiral phase is nonnegative. -/
theorem normSq_nonneg (z : RealChiralPhase) : 0 ≤ normSq z := by
  unfold normSq
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The norm square vanishes exactly when both coordinates vanish. -/
theorem normSq_eq_zero_iff (z : RealChiralPhase) :
    normSq z = 0 ↔ z.scalar = 0 ∧ z.bivector = 0 := by
  constructor
  · intro h
    have hpair :
        z.scalar ^ 2 = 0 ∧ z.bivector ^ 2 = 0 := by
      exact (add_eq_zero_iff_of_nonneg (sq_nonneg z.scalar) (sq_nonneg z.bivector)).mp h
    exact ⟨sq_eq_zero_iff.mp hpair.1, sq_eq_zero_iff.mp hpair.2⟩
  · intro h0
    rcases h0 with ⟨hs, hb⟩
    simp [normSq, hs, hb]

/-! Differential readout of the two real Madelung quadratures. -/

theorem hasDerivAt_normSq_of_components
    (a b : ℝ → ℝ) (da db t : ℝ)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun u => normSq (a u, b u))
      (2 * a t * da + 2 * b t * db) t := by
  have haa := ha.mul ha
  have hbb := hb.mul hb
  have hsum := haa.add hbb
  unfold normSq
  convert hsum using 1
  · funext u
    simp [RealChiralPhase.scalar, RealChiralPhase.bivector,
      Pi.add_apply, Pi.mul_apply, pow_two]
  · ring

/-- A skew rotation of the two quadratures preserves their density to first order. -/
theorem hasDerivAt_normSq_of_skew_rotation
    (a b : ℝ → ℝ) (ω t : ℝ)
    (ha : HasDerivAt a (-ω * b t) t)
    (hb : HasDerivAt b (ω * a t) t) :
    HasDerivAt (fun u => normSq (a u, b u)) 0 t := by
  have h := hasDerivAt_normSq_of_components a b
    (-ω * b t) (ω * a t) t ha hb
  convert h using 1; ring

/-- Radial and phase numerators of a pair of real chiral amplitudes. -/
def radialNumerator (z dz : RealChiralPhase) : ℝ :=
  z.scalar * dz.scalar + z.bivector * dz.bivector

def phaseNumerator (z dz : RealChiralPhase) : ℝ :=
  z.scalar * dz.bivector - z.bivector * dz.scalar

/-- The radial/phase numerators satisfy the two-dimensional Gram identity. -/
theorem radial_phase_gram_identity (z dz : RealChiralPhase) :
    radialNumerator z dz ^ 2 + phaseNumerator z dz ^ 2 =
      normSq z * normSq dz := by
  simp only [radialNumerator, phaseNumerator, normSq]
  ring

/-! Normalized radial and angular rates for a nonzero chiral amplitude. -/

/-- The radial logarithmic rate `(1/2) ρ'/ρ` in chiral coordinates. -/
def chiralRadialRate (z dz : RealChiralPhase) : ℝ :=
  radialNumerator z dz / normSq z

/-- The angular phase rate in chiral coordinates. -/
def chiralPhaseRate (z dz : RealChiralPhase) : ℝ :=
  phaseNumerator z dz / normSq z

/-- Finite Madelung current numerator with explicit scale constants. -/
def phaseCurrent (hbar mass : ℝ) (z dz : RealChiralPhase) : ℝ :=
  (hbar / mass) * phaseNumerator z dz

theorem hasDerivAt_log_normSq_of_components
    (a b : ℝ → ℝ) (da db t : ℝ)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hρ : normSq (a t, b t) ≠ 0) :
    HasDerivAt (fun u => Real.log (normSq (a u, b u)))
      (2 * chiralRadialRate (a t, b t) (da, db)) t := by
  have hnorm := hasDerivAt_normSq_of_components a b da db t ha hb
  have hlog := (Real.hasDerivAt_log hρ).comp t hnorm
  convert hlog using 1
  unfold chiralRadialRate radialNumerator
  field_simp [hρ]

theorem chiralPhaseRate_mul_normSq
    (z dz : RealChiralPhase) (hρ : normSq z ≠ 0) :
    normSq z * chiralPhaseRate z dz = phaseNumerator z dz := by
  unfold chiralPhaseRate
  field_simp [hρ]

theorem chiralRadialRate_mul_normSq
    (z dz : RealChiralPhase) (hρ : normSq z ≠ 0) :
    normSq z * chiralRadialRate z dz = radialNumerator z dz := by
  unfold chiralRadialRate
  field_simp [hρ]

theorem phaseCurrent_eq_density_mul_phaseRate
    (hbar mass : ℝ) (z dz : RealChiralPhase) (hρ : normSq z ≠ 0) :
    phaseCurrent hbar mass z dz =
      (hbar / mass) * (normSq z * chiralPhaseRate z dz) := by
  unfold phaseCurrent
  rw [chiralPhaseRate_mul_normSq z dz hρ]

/-! The stationary-current readout is a genuine differential identity. -/

theorem hasDerivAt_phaseNumerator_of_components
    (a b da db : ℝ → ℝ) (dda ddb t : ℝ)
    (ha : HasDerivAt a (da t) t) (hb : HasDerivAt b (db t) t)
    (hda : HasDerivAt da dda t) (hdb : HasDerivAt db ddb t) :
    HasDerivAt
      (fun u => phaseNumerator (a u, b u) (da u, db u))
      (a t * ddb - b t * dda) t := by
  have hleft := ha.mul hdb
  have hright := hb.mul hda
  have hsub := hleft.sub hright
  convert hsub using 1; ring

theorem hasDerivAt_phaseCurrent_of_components
    (hbar mass : ℝ) (a b da db : ℝ → ℝ) (dda ddb t : ℝ)
    (ha : HasDerivAt a (da t) t) (hb : HasDerivAt b (db t) t)
    (hda : HasDerivAt da dda t) (hdb : HasDerivAt db ddb t) :
    HasDerivAt
      (fun u => phaseCurrent hbar mass
        (a u, b u) (da u, db u))
      ((hbar / mass) * (a t * ddb - b t * dda)) t := by
  have hnum := hasDerivAt_phaseNumerator_of_components
    a b da db dda ddb t ha hb hda hdb
  have hcurrent := hnum.const_mul (hbar / mass)
  simpa [phaseCurrent] using hcurrent

theorem hasDerivAt_phaseCurrent_zero_of_stationary_condition
    (hbar mass : ℝ) (a b da db : ℝ → ℝ) (dda ddb t : ℝ)
    (ha : HasDerivAt a (da t) t) (hb : HasDerivAt b (db t) t)
    (hda : HasDerivAt da dda t) (hdb : HasDerivAt db ddb t)
    (hstationary : a t * ddb = b t * dda) :
    HasDerivAt
      (fun u => phaseCurrent hbar mass
        (a u, b u) (da u, db u)) 0 t := by
  have hcurrent := hasDerivAt_phaseCurrent_of_components
    hbar mass a b da db dda ddb t ha hb hda hdb
  convert hcurrent using 1
  rw [hstationary]
  ring

/-- Multiplication in the real rotor plane, with `J² = -1`. -/
def mul (z w : RealChiralPhase) : RealChiralPhase where
  fst := z.scalar * w.scalar - z.bivector * w.bivector
  snd := z.scalar * w.bivector + z.bivector * w.scalar

/-- Identity chiral phase. -/
def one : RealChiralPhase where
  fst := 1
  snd := 0

instance : One RealChiralPhase where
  one := one

instance : Mul RealChiralPhase where
  mul := mul

@[simp]
theorem one_scalar : (1 : RealChiralPhase).scalar = 1 := rfl

@[simp]
theorem one_bivector : (1 : RealChiralPhase).bivector = 0 := rfl

@[simp]
theorem mul_scalar (z w : RealChiralPhase) :
    (z * w).scalar = z.scalar * w.scalar - z.bivector * w.bivector := rfl

@[simp]
theorem mul_bivector (z w : RealChiralPhase) :
    (z * w).bivector = z.scalar * w.bivector + z.bivector * w.scalar := rfl

/-- The real chiral rotor norm is multiplicative. -/
theorem normSq_mul (z w : RealChiralPhase) :
    normSq (z * w) = normSq z * normSq w := by
  simp only [normSq, mul_scalar, mul_bivector]
  ring

@[simp]
theorem normSq_one : normSq (1 : RealChiralPhase) = 1 := by
  simp [normSq]

/--
The normalized rotor associated to a nonzero chiral phase.

This is the internal real rotor readout; it is not a complex phase.
-/
abbrev NormalizedRotor := {z : RealChiralPhase // normSq z = 1}

abbrev NormalizedRotor.scalar (z : NormalizedRotor) : ℝ := z.1.scalar
abbrev NormalizedRotor.bivector (z : NormalizedRotor) : ℝ := z.1.bivector
abbrev NormalizedRotor.normSq (z : NormalizedRotor) : z.1.normSq = 1 := z.2

end RealChiralPhase

/--
Unit real Spin2 rotor.

This is the real replacement for a unit complex phase.
-/
abbrev Spin2 := RealChiralPhase.NormalizedRotor

/--
The unnormalized real modular denominator:

`cτ + d = (c x + d) + (c y)J`.

No complex numbers are used.
-/
def realModularDenominator
    (g : SL2RMatrix)
    (τ : RealUpperHalfPlane) : RealChiralPhase where
  fst := g.c * τ.x + g.d
  snd := g.c * τ.y

/-- Denominator norm square: `(c x + d)^2 + (c y)^2`. -/
def realModularDenominatorNormSq
    (g : SL2RMatrix)
    (τ : RealUpperHalfPlane) : ℝ :=
  (realModularDenominator g τ).normSq

/--
Real Möbius denominator for the upper-half-plane action.

This is the denominator that appears in the real formula for the action.
-/
def realMoebiusDenSq
    (g : SL2RMatrix)
    (τ : RealUpperHalfPlane) : ℝ :=
  (g.c * τ.x + g.d) ^ 2 + (g.c * τ.y) ^ 2

/-- The modular denominator norm square is exactly the displayed quadratic form. -/
theorem realModularDenominatorNormSq_eq_realMoebiusDenSq
    (g : SL2RMatrix) (τ : RealUpperHalfPlane) :
    realModularDenominatorNormSq g τ = realMoebiusDenSq g τ := by
  rfl

/-- The real Möbius denominator square is nonnegative. -/
theorem realMoebiusDenSq_nonneg
    (g : SL2RMatrix) (τ : RealUpperHalfPlane) :
    0 ≤ realMoebiusDenSq g τ := by
  unfold realMoebiusDenSq
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The rotor denominator norm square is nonnegative. -/
theorem realModularDenominatorNormSq_nonneg
    (g : SL2RMatrix) (τ : RealUpperHalfPlane) :
    0 ≤ realModularDenominatorNormSq g τ := by
  simpa [realModularDenominatorNormSq_eq_realMoebiusDenSq] using
    realMoebiusDenSq_nonneg g τ

/--
Real Möbius action formula, stated with an explicit positivity gate.

The positivity proof is separated so the core formula remains purely algebraic.
-/
def realMoebiusApply
    (g : SL2RMatrix)
    (τ : RealUpperHalfPlane)
    (hden : 0 < realMoebiusDenSq g τ) :
    RealUpperHalfPlane :=
  ( ((g.a * τ.x + g.b) * (g.c * τ.x + g.d)
      + g.a * g.c * τ.y ^ 2) / realMoebiusDenSq g τ,
    ⟨τ.y / realMoebiusDenSq g τ, by
      exact div_pos τ.y_pos hden⟩ )

/-- The real Möbius action lands back in the positive-height half-plane. -/
theorem realMoebiusApply_y_pos
    (g : SL2RMatrix) (τ : RealUpperHalfPlane)
    (hden : 0 < realMoebiusDenSq g τ) :
    0 < (realMoebiusApply g τ hden).y := by
  simpa [realMoebiusApply] using div_pos τ.y_pos hden

end InfoGeometry.Geometry
