/-
InfoGeometry/Compatibility/MathlibUpperHalfPlaneShadow.lean

Compatibility shadow between the pure real upper half-plane substrate and
Mathlib's complex-backed `UpperHalfPlane`.

Complex numbers are allowed here only because this is a downstream readout /
compatibility file.
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Data.Complex.Basic
import InfoGeometry.Geometry.RealUpperHalfPlane
import InfoGeometry.Geometry.RealMoebiusAction
import InfoGeometry.Algebraic.RealModularReadout

noncomputable section

open scoped MatrixGroups

namespace InfoGeometry.Compatibility

open InfoGeometry.Geometry
open InfoGeometry.Algebraic
open InfoGeometry.Geometry.RealUpperHalfPlane

abbrev SL2R : Type := InfoGeometry.Geometry.SL2R
abbrev MathlibUHP := UpperHalfPlane

/-! ### 1. Coordinate equivalence -/

/-- Real coordinates as a Mathlib complex-backed upper-half-plane point. -/
def realToMathlibUHP (τ : RealUpperHalfPlane) : MathlibUHP :=
  ⟨Complex.mk τ.x τ.y, by
    simpa using τ.y_pos⟩

/-- Mathlib's complex-backed upper-half-plane point as real coordinates. -/
def mathlibUHPToReal (z : MathlibUHP) : RealUpperHalfPlane :=
  (z.re, ⟨z.im, z.im_pos⟩)

/--
The coordinate equivalence between the real substrate and Mathlib's
complex-backed upper half-plane.

This is a type equivalence. A topological equivalence should be packaged later
as a `Homeomorph`, after continuity is proved on both sides.
-/
def realToComplexEquiv : RealUpperHalfPlane ≃ MathlibUHP where
  toFun := realToMathlibUHP
  invFun := mathlibUHPToReal
  left_inv τ := by
    cases τ
    simp [realToMathlibUHP, mathlibUHPToReal]
  right_inv z := by
    apply UpperHalfPlane.ext_re_im <;>
      simp [realToMathlibUHP, mathlibUHPToReal]

@[simp]
theorem realToMathlibUHP_re (τ : RealUpperHalfPlane) :
    (realToMathlibUHP τ).re = τ.x := by
  rfl

@[simp]
theorem realToMathlibUHP_im (τ : RealUpperHalfPlane) :
    (realToMathlibUHP τ).im = τ.y := by
  rfl

private lemma realToMathlibUHP_eq_toComplex (τ : RealUpperHalfPlane) :
    realToMathlibUHP τ =
      InfoGeometry.Geometry.RealUpperHalfPlane.toComplex τ := by
  apply UpperHalfPlane.ext
  rfl

/-- The usual complex notation is a theorem about the shadow map. -/
theorem realToMathlibUHP_eq_re_add_im (τ : RealUpperHalfPlane) :
    realToMathlibUHP τ = (τ.x : ℂ) + (τ.y : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [realToMathlibUHP]

/-! ### 2. Chiral phase / complex shadow -/

/-- Complex readout of a real scalar/bivector phase. -/
def chiralToComplex (z : ChiralPhase) : ℂ :=
  Complex.mk z.scalar z.bivector

@[simp]
theorem chiralToComplex_re (z : ChiralPhase) :
    (chiralToComplex z).re = z.scalar := by
  rfl

@[simp]
theorem chiralToComplex_im (z : ChiralPhase) :
    (chiralToComplex z).im = z.bivector := by
  rfl

/--
The usual scalar-plus-bivector-times-`I` notation is a downstream theorem.
-/
theorem chiralToComplex_eq_scalar_add_bivector_I (z : ChiralPhase) :
    chiralToComplex z =
      (z.scalar : ℂ) + (z.bivector : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [chiralToComplex]

/--
The real scalar/bivector product shadows complex multiplication.
-/
theorem chiral_mul_shadow (z w : ChiralPhase) :
    chiralToComplex (z * w) =
      chiralToComplex z * chiralToComplex w := by
  apply Complex.ext <;> simp [chiralToComplex]

/--
The real norm square shadows the complex norm square.

This is useful when upgrading nonzero chiral phases to `Units ℂ`, and
unit-norm chiral phases to `Circle`.
-/
theorem chiral_normSq_shadow (z : ChiralPhase) :
    Complex.normSq (chiralToComplex z) =
      z.normSq := by
  simp [chiralToComplex, ChiralPhase.normSq, Complex.normSq]
  ring

/-! ### 3. Denominator shadow -/

/-- Expanded determinant equation for `SL(2,ℝ)`. -/
lemma SL2R_det_eq_one (g : SL2R) :
    ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) *
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1)
    -
    ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) *
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0)
    =
    1 := by
  have hdet' := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet'
  simpa using hdet'

/-- The real denominator square used by the real fractional-linear action. -/
abbrev realDenomSq (g : SL2R) (τ : RealUpperHalfPlane) : ℝ :=
  RealUpperHalfPlane.denomSq g τ

/-- Positivity of the real denominator square. -/
theorem realDenomSq_pos (g : SL2R) (τ : RealUpperHalfPlane) :
    0 < realDenomSq g τ := by
  simpa [realDenomSq] using RealUpperHalfPlane.realDenomSq_pos g τ

/--
The real chiral denominator shadows the usual complex automorphy denominator.

This theorem is deliberately written in terms of `extractC` and `extractD`,
so it is stable under changes to the internal representation of `SL2R`.
-/
theorem denom_shadow
    (g : SL2R) (τ : RealUpperHalfPlane) :
    chiralToComplex
      (rawChiralDenominator extractC extractD g τ)
    =
      ((extractC g : ℝ) : ℂ) * realToMathlibUHP τ
        + ((extractD g : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [chiralToComplex, rawChiralDenominator,
      realToMathlibUHP, extractC, extractD]

/--
Matrix-coordinate denominator shadow.

This is the version matching the standard modular-form notation
`cτ + d`.
-/
theorem denom_shadow_matrix (g : SL2R) (τ : RealUpperHalfPlane) :
    chiralToComplex
      (rawChiralDenominator extractC extractD g τ)
    =
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ)
        * realToMathlibUHP τ
      +
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) := by
  simpa [extractC, extractD] using denom_shadow g τ

/-! ### 4. Möbius action shadow -/

/--
The real fractional-linear action, pushed through the coordinate equivalence,
agrees with Mathlib's complex-backed upper-half-plane action.
-/
theorem smul_shadow_SL2R_proof
    (g : SL2R) (τ : RealUpperHalfPlane) :
    realToComplexEquiv (g • τ) =
      g • realToComplexEquiv τ := by
  simpa [realToComplexEquiv, Equiv.coe_fn_mk,
    realToMathlibUHP_eq_toComplex,
    InfoGeometry.Geometry.RealUpperHalfPlane.smul_def] using
    (InfoGeometry.Geometry.RealUpperHalfPlane.toComplex_moebius g τ)
end InfoGeometry.Compatibility
