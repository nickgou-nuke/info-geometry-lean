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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import InfoGeometry.Geometry.RealUpperHalfPlane

noncomputable section

namespace InfoGeometry.Geometry

/-- A real `SL₂(ℝ)` matrix, written by entries. -/
structure SL2RMatrix where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  det_eq_one : a * d - b * c = 1

/--
Real chiral phase element.

Interpretation: `scalar + bivector * J`, where `J² = -1`.
This is not a complex number. It is a real two-component rotor coordinate.
-/
structure RealChiralPhase where
  scalar : ℝ
  bivector : ℝ

namespace RealChiralPhase

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

/-- Multiplication in the real rotor plane, with `J² = -1`. -/
def mul (z w : RealChiralPhase) : RealChiralPhase where
  scalar := z.scalar * w.scalar - z.bivector * w.bivector
  bivector := z.scalar * w.bivector + z.bivector * w.scalar

/-- Identity chiral phase. -/
def one : RealChiralPhase where
  scalar := 1
  bivector := 0

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

@[simp]
theorem normSq_one : normSq (1 : RealChiralPhase) = 1 := by
  simp [normSq]

@[ext]
theorem ext {z w : RealChiralPhase}
    (hs : z.scalar = w.scalar)
    (hb : z.bivector = w.bivector) :
    z = w := by
  cases z
  cases w
  simp_all

/-- Real conjugation: reverse the oriented bivector. -/
def conj (z : RealChiralPhase) : RealChiralPhase where
  scalar := z.scalar
  bivector := -z.bivector

/-- Oriented phase rate numerator `scalar * d.2 - bivector * d.1`. -/
def phaseNumerator (z : RealChiralPhase) (d : ℝ × ℝ) : ℝ :=
  z.scalar * d.2 - z.bivector * d.1

/-- Chiral phase rate `phaseNumerator / normSq`. -/
def chiralPhaseRate (z : RealChiralPhase) (d : ℝ × ℝ) : ℝ :=
  phaseNumerator z d / normSq z

/-- Madelung phase current `(ℏ / m) * phaseNumerator`. -/
def phaseCurrent (hbar mass : ℝ) (z : RealChiralPhase) (d : ℝ × ℝ) : ℝ :=
  (hbar / mass) * phaseNumerator z d

/-- Derivative of normSq given component derivatives. -/
theorem hasDerivAt_normSq_of_components
    (f g : ℝ → ℝ) (df dg t : ℝ)
    (hf : HasDerivAt f df t)
    (hg : HasDerivAt g dg t) :
    HasDerivAt
      (fun u => normSq { scalar := f u, bivector := g u })
      (2 * f t * df + 2 * g t * dg) t := by
  have h1 : HasDerivAt (fun u => (f u) ^ 2) (2 * f t * df) t := by
    have h := hf.pow 2
    simpa [mul_assoc] using h
  have h2 : HasDerivAt (fun u => (g u) ^ 2) (2 * g t * dg) t := by
    have h := hg.pow 2
    simpa [mul_assoc] using h
  exact h1.add h2

/--
The normalized rotor associated to a nonzero chiral phase.

This is the internal real rotor readout; it is not a complex phase.
-/
structure NormalizedRotor where
  scalar : ℝ
  bivector : ℝ
  normSq : scalar ^ 2 + bivector ^ 2 = 1

end RealChiralPhase

/--
Unit real Spin2 rotor.

This is the real replacement for a unit complex phase.
-/
structure Spin2 where
  scalar : ℝ
  bivector : ℝ
  unit_norm : scalar ^ 2 + bivector ^ 2 = 1

/--
The unnormalized real modular denominator:

`cτ + d = (c x + d) + (c y)J`.

No complex numbers are used.
-/
def realModularDenominator
    (g : SL2RMatrix)
    (τ : RealUpperHalfPlane) : RealChiralPhase where
  scalar := g.c * τ.x + g.d
  bivector := g.c * τ.y

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
    RealUpperHalfPlane where
  x :=
    ((g.a * τ.x + g.b) * (g.c * τ.x + g.d)
      + g.a * g.c * τ.y ^ 2) / realMoebiusDenSq g τ
  y :=
    τ.y / realMoebiusDenSq g τ
  y_pos := by
    exact div_pos τ.y_pos hden

/-- The real Möbius action lands back in the positive-height half-plane. -/
theorem realMoebiusApply_y_pos
    (g : SL2RMatrix) (τ : RealUpperHalfPlane)
    (hden : 0 < realMoebiusDenSq g τ) :
    0 < (realMoebiusApply g τ hden).y := by
  simpa [realMoebiusApply] using div_pos τ.y_pos hden

end InfoGeometry.Geometry
