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

end InfoGeometry.Geometry
