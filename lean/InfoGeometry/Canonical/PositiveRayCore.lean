import InfoGeometry.Projective.Normalize
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.PositiveRayCore

Low-level root language for positive projective states in the finite orthant model:
- positive rays (`PositiveMeasure.Proj`)
- cone-interior realization
- canonical normalization gauge section
- logarithmic density and modular potential

This file is a direct realization of **Goutev's Principle (Absolute Relativity of 
Measurement)**: measurement is projective; observables are relational invariants.
The base ontology here is not the absolute count, but the ray class.

This is the projective positive-state spine underneath normalized counts,
relative densities, RN/Jacobian volume factors, and modular lifts.
-/

namespace InfoGeometry.Canonical.PositiveRayCore

universe u

/-- Projective positive states: positive measures modulo positive rescaling. -/
abbrev PositiveRay (α : Type u) := InfoGeometry.PositiveMeasure.Proj (α := α)

/-- Cone-interior realization of the positive orthant projective state space. -/
abbrev PositiveOrthantRaySpace (α : Type u) [Fintype α] [Nonempty α] :=
  InfoGeometry.Projective.ConeInteriorStateSpace
    ((InfoGeometry.Projective.positiveOrthant (α := α)).cone)

section FiniteOrthant

variable {α : Type u} [Fintype α] [Nonempty α]

/-- Realize a positive ray as a cone-interior state in the positive orthant. -/
noncomputable def toConeInteriorStateSpace :
    PositiveRay α → PositiveOrthantRaySpace α :=
  InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace (α := α)

/-- Forget the cone representative back to the underlying positive ray. -/
noncomputable def ofConeInteriorStateSpace :
    PositiveOrthantRaySpace α → PositiveRay α :=
  InfoGeometry.Projective.coneInteriorStateSpaceToProjectiveClass (α := α)

@[simp] theorem toConeInteriorStateSpace_ofConeInteriorStateSpace
    (s : PositiveOrthantRaySpace α) :
    toConeInteriorStateSpace (α := α) (ofConeInteriorStateSpace (α := α) s) = s := by
  simp [toConeInteriorStateSpace, ofConeInteriorStateSpace]

@[simp] theorem ofConeInteriorStateSpace_toConeInteriorStateSpace
    (q : PositiveRay α) :
    ofConeInteriorStateSpace (α := α) (toConeInteriorStateSpace (α := α) q) = q := by
  simp [toConeInteriorStateSpace, ofConeInteriorStateSpace]

/-- Canonical simplex gauge section of a positive ray. -/
noncomputable def gaugeSection : PositiveRay α → InfoGeometry.PositiveMeasure α ℝ :=
  InfoGeometry.Projective.Normalize.normalizeOnProj (α := α)

@[simp] theorem gaugeSection_mk (μ : InfoGeometry.PositiveMeasure α ℝ) :
    gaugeSection (α := α) (Quotient.mk _ μ) =
      InfoGeometry.PositiveMeasure.normalize (α := α) (R := ℝ) μ := by
  simp [gaugeSection]

/-- The canonical gauge representative has unit total mass. -/
@[simp] theorem Z_gaugeSection (q : PositiveRay α) :
    InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) (gaugeSection (α := α) q) = 1 := by
  simpa [gaugeSection] using
    (InfoGeometry.Projective.Normalize.Z_normalizeOnProj (α := α) q)

/-- Logarithmic density of the canonical gauge representative. -/
@[rep_depth projective]
noncomputable def logDensity (q : PositiveRay α) : α → ℝ :=
  fun a => Real.log (gaugeSection (α := α) q a)

/-- Modular potential: negative logarithmic density. -/
noncomputable def modularPotential (q : PositiveRay α) : α → ℝ :=
  fun a => -logDensity (α := α) q a

@[simp] theorem modularPotential_eq_neg_logDensity
    (q : PositiveRay α) (a : α) :
    modularPotential (α := α) q a = -logDensity (α := α) q a := rfl

@[simp] theorem logDensity_eq_neg_modularPotential
    (q : PositiveRay α) (a : α) :
    logDensity (α := α) q a = -modularPotential (α := α) q a := by
  simp [modularPotential]

@[simp] theorem exp_logDensity
    (q : PositiveRay α) (a : α) :
    Real.exp (logDensity (α := α) q a) = gaugeSection (α := α) q a := by
  unfold logDensity
  exact Real.exp_log ((gaugeSection (α := α) q).pos a)

@[simp] theorem gaugeSection_eq_exp_logDensity
    (q : PositiveRay α) (a : α) :
    gaugeSection (α := α) q a = Real.exp (logDensity (α := α) q a) := by
  symm
  exact exp_logDensity (α := α) q a

@[simp] theorem gaugeSection_eq_exp_neg_modularPotential
    (q : PositiveRay α) (a : α) :
    gaugeSection (α := α) q a = Real.exp (-(modularPotential (α := α) q a)) := by
  calc
    gaugeSection (α := α) q a = Real.exp (logDensity (α := α) q a) :=
      gaugeSection_eq_exp_logDensity (α := α) q a
    _ = Real.exp (-(modularPotential (α := α) q a)) := by
      congr 1
      unfold modularPotential
      ring

end FiniteOrthant

end InfoGeometry.Canonical.PositiveRayCore
