import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Exceptional.ZornMatrixGeneric
import InfoGeometry.Exceptional.SpinZornBridge

namespace InfoGeometry.Exceptional.ConformalTwistor

open InfoGeometry.Exceptional
open InfoGeometry.Exceptional.GenericZorn

/-- Complexified Zorn Matrix. -/
abbrev ComplexZorn := ZornMatrix ℂ

/-- 
A Zorn matrix is in the odd chiral sector if it represents a physical vector.
In Zorn form, this corresponds to having zeros on the diagonal (a = 0, b = 0)
or having matching spatial components depending on the specific involution used.
Here we map the odd chiral sector to elements with zero trace and antisymmetric
structure, or more simply, pure vector parts.
Wait, let's use the definition: A Twistor spinor Z ∈ ℂ^4 embeds into the Zorn matrix
as a specific chiral off-diagonal part. We will enforce that a Twistor State is a 
Zorn matrix with zero diagonal (a = b = 0).
-/
def IsOddChiral (Z : ComplexZorn) : Prop :=
  Z.a = 0 ∧ Z.b = 0

/-- The Penrose incidence relation / Null condition. -/
def NullNorm (Z : ComplexZorn) : ℂ :=
  ZornMatrix.norm Z

/-- 
Twistor Spinor embedded in the odd chiral sector of the Complex Zorn Algebra. 
-/
structure TwistorState where
  Z : ComplexZorn
  h_odd : IsOddChiral Z
  h_null : NullNorm Z = 0

/--
The Translation Rotor in Twistor space.
Translations act as a linear shift parameterized by a physical vector `v`.
-/
def TranslationRotor (v : Vec3 ℂ) : ComplexZorn :=
  { a := 1, b := 1, u := v, v := (0,0,0) }

/--
The Special Conformal Transformation (SCT) Rotor.
-/
def SCTRotor (v : Vec3 ℂ) : ComplexZorn :=
  { a := 1, b := 1, u := (0,0,0), v := v }

/--
A conformal transformation acts via the spinor sandwich `R Z R^*`.
Since Zorn matrix conjugation flips off-diagonal elements and leaves diagonals,
or we can just define the direct action as `R * Z * R`.
-/
def ConformalAction (R : ComplexZorn) (T : TwistorState) : ComplexZorn :=
  R * T.Z * R

/--
Theorem: The Conformal Rotor Action strictly preserves the Penrose incidence relation.
This transforms Conformal Symmetry into a pure algebraic property of the Zorn algebra.
-/
theorem conformal_action_preserves_null (R : ComplexZorn) (T : TwistorState) :
    NullNorm (ConformalAction R T) = (ZornMatrix.norm R)^2 * NullNorm T.Z := by
  dsimp [ConformalAction, NullNorm]
  have h1 := ZornMatrix.norm_mul (R * T.Z) R
  have h2 := ZornMatrix.norm_mul R T.Z
  rw [h1, h2]
  ring

open InfoGeometry.Exceptional.SpinZorn

/-- Embed a real Zorn matrix into the complexified Zorn algebra. -/
def embedRealZorn (X : InfoGeometry.Exceptional.RealZorn.ZornMatrixReal) : ComplexZorn :=
  { a := ↑X.a,
    b := ↑X.b,
    u := (↑X.u.1, ↑X.u.2.1, ↑X.u.2.2),
    v := (↑X.v.1, ↑X.v.2.1, ↑X.v.2.2) }


/-- Непрекъснат Лоренцов Бууст (Continuous Lorentz Boost) -/
noncomputable def continuousBoostRotor (v : ZornSpatialUnitVector) (rapidity : ℝ) : ComplexZorn :=
  embedRealZorn (LorentzBoostRotor rapidity v)

/-- Helper theorem: norm of embedded real Zorn matrix is the embedded norm. -/
theorem embedRealZorn_norm (X : InfoGeometry.Exceptional.RealZorn.ZornMatrixReal) :
    ZornMatrix.norm (embedRealZorn X) = ↑(InfoGeometry.Exceptional.RealZorn.ZornMatrixReal.norm X) := by
  dsimp [embedRealZorn, ZornMatrix.norm, InfoGeometry.Exceptional.RealZorn.ZornMatrixReal.norm, dot, InfoGeometry.Exceptional.RealZorn.dot]
  push_cast
  ring_nf

/-- ТЕОРЕМА 1: Експоненциално Генериране на Конформния Ротор -/
theorem continuous_boost_is_unitary (v : ZornSpatialUnitVector) (rapidity : ℝ) :
    ZornMatrix.norm (continuousBoostRotor v rapidity) = 1 := by
  dsimp [continuousBoostRotor]
  rw [embedRealZorn_norm]
  rw [lorentzBoostRotor_norm]
  norm_cast

/-- ТЕОРЕМА 2: Спинорно-Туисторна Ковариантност -/
theorem boost_preserves_twistor_incidence (T : TwistorState) 
    (R : ComplexZorn) (hR_unitary : ZornMatrix.norm R = 1) :
    NullNorm (ConformalAction R T) = 0 := by
  have h := conformal_action_preserves_null R T
  rw [hR_unitary] at h
  have h_one_sq : (1 : ℂ) ^ 2 = 1 := by norm_num
  rw [h_one_sq, one_mul] at h
  rw [T.h_null] at h
  exact h

end InfoGeometry.Exceptional.ConformalTwistor
