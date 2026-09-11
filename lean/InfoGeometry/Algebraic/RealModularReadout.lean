/- 
InfoGeometry/Algebraic/RealModularReadout.lean

Arithmetic-to-real readout for the modular boundary cusp interface.

This file stays on the real side of the quarantine:
- it provides the `SL(2, ℤ) → SL(2, ℝ)` lift as a monoid hom;
- it packages the `T`-identity hypothesis at the readout level;
- it also exposes a generic automorphy-factor pullback API;
- it turns the denominator cocycle into a rotor cocycle through the
  real chiral phase readout;
- it does not import complex analysis or Mathlib's complex upper half-plane.
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic
import InfoGeometry.Geometry.RealUpperHalfPlane

noncomputable section

open scoped MatrixGroups

namespace InfoGeometry.Algebraic

open InfoGeometry.Geometry

abbrev SL2Z : Type := SL(2, ℤ)
abbrev SL2R : Type := SL(2, ℝ)

/--
The pure arithmetic translation generator.

This is the real-core replacement for `ModularGroup.T`.
Do not import `Mathlib.NumberTheory.Modular` in the core just to obtain `T`.
-/
def matrixT : SL2Z :=
  ⟨!![(1 : ℤ), 1; 0, 1], by
    norm_num [Matrix.det_fin_two_of]⟩

/--
The canonical arithmetic lift `SL(2, ℤ) → SL(2, ℝ)`.

This is the lift used by the real modular readout layer.
-/
def sl2zToSL2R : SL2Z →* SL2R :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

/--
A real scalar/bivector pair.
-/
structure ChiralPhase where
  scalar : ℝ
  bivector : ℝ

namespace ChiralPhase

instance : One ChiralPhase where
  one := ⟨1, 0⟩

instance : Mul ChiralPhase where
  mul z w :=
    ⟨z.scalar * w.scalar - z.bivector * w.bivector,
     z.scalar * w.bivector + z.bivector * w.scalar⟩

@[ext]
theorem ext {z w : ChiralPhase}
    (hs : z.scalar = w.scalar)
    (hb : z.bivector = w.bivector) :
    z = w := by
  cases z
  cases w
  simp_all

@[simp]
theorem one_scalar : (1 : ChiralPhase).scalar = 1 := rfl

@[simp]
theorem one_bivector : (1 : ChiralPhase).bivector = 0 := rfl

@[simp]
theorem mul_scalar (z w : ChiralPhase) :
    (z * w).scalar = z.scalar * w.scalar - z.bivector * w.bivector := rfl

@[simp]
theorem mul_bivector (z w : ChiralPhase) :
    (z * w).bivector = z.scalar * w.bivector + z.bivector * w.scalar := rfl

@[simp]
theorem one_mul (z : ChiralPhase) :
    (1 : ChiralPhase) * z = z := by
  ext <;> simp

@[simp]
theorem mul_one (z : ChiralPhase) :
    z * (1 : ChiralPhase) = z := by
  ext <;> simp

theorem mul_assoc (x y z : ChiralPhase) :
    (x * y) * z = x * (y * z) := by
  ext <;> simp <;> ring

instance : Monoid ChiralPhase where
  one := 1
  mul := (· * ·)
  one_mul := one_mul
  mul_one := mul_one
  mul_assoc := mul_assoc

/-- Real conjugation: reverse the oriented bivector. -/
def conj (z : ChiralPhase) : ChiralPhase :=
  ⟨z.scalar, -z.bivector⟩

/-- Squared norm of the chiral phase. -/
def normSq (z : ChiralPhase) : ℝ :=
  z.scalar ^ 2 + z.bivector ^ 2

@[simp]
theorem normSq_one : normSq (1 : ChiralPhase) = 1 := by
  norm_num [normSq]

@[simp]
theorem normSq_conj (z : ChiralPhase) :
    normSq z.conj = normSq z := by
  simp [normSq, conj]

theorem normSq_mul (z w : ChiralPhase) :
    normSq (z * w) = normSq z * normSq w := by
  dsimp [normSq]
  ring

/-- The positive bivector generator. -/
def bivectorI : ChiralPhase :=
  ⟨0, 1⟩

/-- The negative bivector generator. -/
def bivectorNegI : ChiralPhase :=
  ⟨0, -1⟩

end ChiralPhase

/--
Nonzero chiral phases: the correct domain for a rotor readout into a group.
-/
def NonzeroChiralPhase :=
  { z : ChiralPhase // z.normSq ≠ 0 }

namespace NonzeroChiralPhase

instance : Coe NonzeroChiralPhase ChiralPhase where
  coe z := z.1

@[ext]
theorem ext {z w : NonzeroChiralPhase}
    (h : (z : ChiralPhase) = (w : ChiralPhase)) :
    z = w :=
  Subtype.ext h

instance : One NonzeroChiralPhase where
  one :=
    ⟨1, by
      norm_num [ChiralPhase.normSq]⟩

instance : Mul NonzeroChiralPhase where
  mul z w :=
    ⟨(z : ChiralPhase) * (w : ChiralPhase), by
      intro h
      have hmul : (z : ChiralPhase).normSq * (w : ChiralPhase).normSq = 0 := by
        simpa [ChiralPhase.normSq_mul] using h
      exact (mul_ne_zero z.property w.property) hmul⟩

@[simp]
theorem coe_one :
    ((1 : NonzeroChiralPhase) : ChiralPhase) = 1 := rfl

@[simp]
theorem coe_mul (z w : NonzeroChiralPhase) :
    ((z * w : NonzeroChiralPhase) : ChiralPhase) =
      (z : ChiralPhase) * (w : ChiralPhase) := rfl

instance : Monoid NonzeroChiralPhase where
  one := 1
  mul := (· * ·)
  one_mul z := by
    ext <;> simp
  mul_one z := by
    ext <;> simp
  mul_assoc x y z := by
    ext <;> simp <;> ring

end NonzeroChiralPhase

/-- Real chiral readout into a rotor monoid/group. -/
abbrev ChiralRotorReadout (R : Type*) [Monoid R] :=
  NonzeroChiralPhase →* R

/--
The cocycle structure used by the real modular readout layer.

This is the real-side version of a multiplicative action cocycle.
-/
structure MulActionCocycle
    (Γ X R : Type*)
    [Group Γ] [MulAction Γ X] [Monoid R] where
  toFun : Γ → X → R
  map_one : ∀ x, toFun 1 x = 1
  map_mul : ∀ g h x, toFun (g * h) x = toFun g (h • x) * toFun h x

instance
    {Γ X R : Type*} [Group Γ] [MulAction Γ X] [Monoid R] :
    CoeFun (MulActionCocycle Γ X R) (fun _ => Γ → X → R) where
  coe C := C.toFun

/--
A generic multiplicative automorphy factor over a group action.

This is the reusable algebraic layer underneath the modular readout.
-/
structure ChiralAutomorphyFactor
    (G X R : Type*)
    [Group G] [MulAction G X] [Monoid R] where
  toFun : G → X → R
  map_one : ∀ x, toFun 1 x = 1
  map_mul :
    ∀ g h x,
      toFun (g * h) x =
        toFun g (h • x) * toFun h x

instance
    {G X R : Type*} [Group G] [MulAction G X] [Monoid R] :
    CoeFun (ChiralAutomorphyFactor G X R) (fun _ => G → X → R) where
  coe J := J.toFun

namespace ChiralAutomorphyFactor

variable
    {G H X R : Type*}
    [Group G] [Group H]
    [MulAction G X] [MulAction H X]
    [Monoid R]

/--
Pull back a chiral automorphy factor along a group homomorphism, provided
that the two actions agree through that homomorphism.
-/
def pullback
    (φ : G →* H)
    (hsmul : ∀ (g : G) (x : X), φ g • x = g • x)
    (J : ChiralAutomorphyFactor H X R) :
    ChiralAutomorphyFactor G X R where
  toFun g x := J (φ g) x
  map_one x := by
    simpa using J.map_one x
  map_mul g h x := by
    calc
      J (φ (g * h)) x
          = J (φ g * φ h) x := by
              rw [φ.map_mul]
      _ = J (φ g) ((φ h) • x) * J (φ h) x :=
            J.map_mul (φ g) (φ h) x
      _ = J (φ g) (h • x) * J (φ h) x := by
            rw [hsmul h x]

/--
Convert a chiral automorphy factor into a rotor cocycle through a monoid
homomorphism.
-/
def toRotorCocycle
    {G X : Type*}
    [Group G] [MulAction G X]
    {R : Type*} [Monoid R]
    (J : ChiralAutomorphyFactor G X NonzeroChiralPhase)
    (weightReadout : ChiralRotorReadout R) :
    MulActionCocycle G X R where
  toFun g x := weightReadout (J g x)
  map_one x := by
    rw [J.map_one x]
    exact weightReadout.map_one
  map_mul g h x := by
    rw [J.map_mul g h x]
    exact weightReadout.map_mul (J g (h • x)) (J h x)

end ChiralAutomorphyFactor

/--
A real denominator pair on the ambient real upper half-plane.
-/
def rawChiralDenominator
    (c d : SL2R → ℝ)
    (g : SL2R)
    (τ : RealUpperHalfPlane) :
    ChiralPhase :=
  ⟨c g * τ.x + d g,
   c g * τ.y⟩

/-- Convenience accessors for the lower row of `SL(2,ℝ)`. -/
def extractC (g : SL2R) : ℝ := g.1 1 0

def extractD (g : SL2R) : ℝ := g.1 1 1

/-- The real `SL(2,ℤ)` chiral automorphy factor obtained by pulling back the
real `SL(2,ℝ)` automorphy factor. -/
def SL2Z_AutomorphyFactor
    [MulAction SL2R RealUpperHalfPlane]
    [MulAction SL2Z RealUpperHalfPlane]
    (J : ChiralAutomorphyFactor SL2R RealUpperHalfPlane NonzeroChiralPhase)
    (hsmul :
      ∀ (g : SL2Z) (τ : RealUpperHalfPlane),
        sl2zToSL2R g • τ = g • τ) :
    ChiralAutomorphyFactor SL2Z RealUpperHalfPlane NonzeroChiralPhase :=
  J.pullback sl2zToSL2R hsmul

/--
Convert a phase-valued chiral automorphy factor into a rotor-valued cocycle.
-/
def RealBerryRotorCocycle
    [MulAction SL2R RealUpperHalfPlane]
    [MulAction SL2Z RealUpperHalfPlane]
    {R : Type*} [Monoid R]
    (J : ChiralAutomorphyFactor SL2R RealUpperHalfPlane NonzeroChiralPhase)
    (hsmul :
      ∀ (g : SL2Z) (τ : RealUpperHalfPlane),
        sl2zToSL2R g • τ = g • τ)
    (weightReadout : ChiralRotorReadout R) :
    MulActionCocycle SL2Z RealUpperHalfPlane R :=
  (SL2Z_AutomorphyFactor J hsmul).toRotorCocycle weightReadout

/--
A modular readout with a distinguished `T` element.

The only closed theorem we need for the boundary cusp lane is the
`T`-identity hypothesis.
-/
def RealModularReadoutData (R : Type*) [Monoid R] :=
  {readout : SL2Z → RealUpperHalfPlane → R //
    ∃ T : SL2Z, ∀ τ : RealUpperHalfPlane, readout T τ = 1}

namespace RealModularReadoutData

variable {R : Type*} [Monoid R]

def readout (D : RealModularReadoutData R) :
    SL2Z → RealUpperHalfPlane → R :=
  D.1

noncomputable def T (D : RealModularReadoutData R) : SL2Z :=
  Classical.choose D.2

theorem T_identity (D : RealModularReadoutData R) :
    ∀ τ : RealUpperHalfPlane, D.readout D.T τ = 1 :=
  Classical.choose_spec D.2

/-- The `T`-identity hypothesis in theorem form. -/
theorem t_identity (D : RealModularReadoutData R) :
    ∀ τ : RealUpperHalfPlane, D.readout D.T τ = 1 :=
  D.T_identity

end RealModularReadoutData

/-- Pull back a readout along the arithmetic lift of `T`. -/
def pullbackReadout
    {R : Type*} [Monoid R]
    (J : SL2R → RealUpperHalfPlane → R)
    (T : SL2Z) :
    RealUpperHalfPlane → R :=
  fun τ => J (sl2zToSL2R T) τ

/--
If a lifted real readout is trivial on `T`, then its pullback is also trivial
on the same `T` element.
-/
theorem pullbackReadout_T_eq_one
    {R : Type*} [Monoid R]
    (J : SL2R → RealUpperHalfPlane → R)
    (T : SL2Z)
    (hT : ∀ τ : RealUpperHalfPlane, J (sl2zToSL2R T) τ = 1) :
    ∀ τ : RealUpperHalfPlane, pullbackReadout J T τ = 1 := by
  intro τ
  simp [pullbackReadout, hT τ]

/--
The real `T`-identity packaged as a readout theorem for the pulled-back
`SL(2,ℤ)` automorphy factor.
-/
theorem SL2Z_AutomorphyFactor_T_eq_one
    {R : Type*} [Monoid R]
    [MulAction SL2R RealUpperHalfPlane]
    [MulAction SL2Z RealUpperHalfPlane]
    (J : ChiralAutomorphyFactor SL2R RealUpperHalfPlane NonzeroChiralPhase)
    (hsmul :
      ∀ (g : SL2Z) (τ : RealUpperHalfPlane),
        sl2zToSL2R g • τ = g • τ)
    (hT : ∀ τ : RealUpperHalfPlane,
      J (sl2zToSL2R matrixT) τ = 1) :
    ∀ τ : RealUpperHalfPlane,
      SL2Z_AutomorphyFactor J hsmul matrixT τ = 1 := by
  intro τ
  simpa [SL2Z_AutomorphyFactor] using hT τ

end InfoGeometry.Algebraic
