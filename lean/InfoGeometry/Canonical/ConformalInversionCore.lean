import Mathlib

/-!
# InfoGeometry.Canonical.ConformalInversionCore

Direct canonical inversion core.

This file does not wrap a bridge theorem. It records the radial inversion map
`x ↦ ‖x‖⁻² • x` on a punctured normed space and the elementary fact that the
unit sphere is fixed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConformalInversionCore

abbrev PuncturedSpace (E : Type*) [Zero E] := {x : E // x ≠ 0}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial conformal inversion on the punctured space. -/
def conformalInversion (x : PuncturedSpace E) : PuncturedSpace E := by
  refine ⟨((‖(x : E)‖ ^ 2)⁻¹ : ℝ) • x, ?_⟩
  intro hx
  have hzero : ((‖(x : E)‖ ^ 2)⁻¹ : ℝ) = 0 ∨ (x : E) = 0 := by
    exact smul_eq_zero.mp hx
  rcases hzero with hscalar | hvec
  · exact (inv_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.2 x.2))) hscalar
  · exact x.2 hvec

@[simp] theorem conformalInversion_apply (x : PuncturedSpace E) :
    (conformalInversion (E := E) x : E) = ((‖(x : E)‖ ^ 2)⁻¹ : ℝ) • x :=
  rfl

/--
The unit sphere is fixed by radial inversion.

This is the Lean-level version of the celestial-sphere fixed-point statement:
if `‖x‖ = 1`, then `x` is a fixed point of the inversion.
-/
theorem conformalInversion_fixed_of_norm_one (x : PuncturedSpace E)
    (hx : ‖(x : E)‖ = 1) :
    conformalInversion (E := E) x = x := by
  ext
  simp [conformalInversion, hx]

section UnitSphere

variable [InnerProductSpace ℝ E]

/-- A direct canonical carrier for the unit sphere. -/
structure UnitSphere (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  val : E
  property : val ∈ Metric.sphere (0 : E) 1

namespace UnitSphere

/-- The unit sphere is fixed by geometric inversion. -/
def inversion (x : UnitSphere E) : UnitSphere E := by
  refine ⟨EuclideanGeometry.inversion (0 : E) 1 x.val, ?_⟩
  have hfix : EuclideanGeometry.inversion (0 : E) 1 x.val = x.val :=
    EuclideanGeometry.inversion_of_mem_sphere
      (c := (0 : E)) (R := (1 : ℝ)) x.property
  rw [hfix]
  exact x.property

omit [NormedSpace ℝ E] in
@[simp] theorem inversion_apply (x : UnitSphere E) :
    (inversion (E := E) x).val = EuclideanGeometry.inversion (0 : E) 1 x.val :=
  rfl

omit [NormedSpace ℝ E] in
@[simp] theorem inversion_fixed (x : UnitSphere E) : inversion (E := E) x = x := by
  cases x with
  | mk v hv =>
      dsimp [inversion]
      have hfix : EuclideanGeometry.inversion (0 : E) 1 v = v :=
        EuclideanGeometry.inversion_of_mem_sphere
          (c := (0 : E)) (R := (1 : ℝ)) hv
      simp [hfix]

omit [NormedSpace ℝ E] in
theorem inversion_involutive : Function.Involutive (inversion (E := E)) := by
  intro x
  have hxx : inversion (E := E) (inversion (E := E) x) = inversion (E := E) x :=
    inversion_fixed (E := E) (inversion (E := E) x)
  have hx : inversion (E := E) x = x :=
    inversion_fixed (E := E) x
  exact hxx.trans hx

end UnitSphere

end UnitSphere

end InfoGeometry.Canonical.ConformalInversionCore
