import InfoGeometry.Canonical.PositiveRayCore
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.RelativePotentialCore

Relative affine-potential layer over projective positive states.

This file separates three levels cleanly:
- representative-level relative densities and their scaling laws
- ray-level relative quantities via the canonical gauge section
- the modular potential as the negative relative log-density

In accordance with **Goutev's Principle (Absolute Relativity of Measurement)**,
the base ontology remains projective; absolute magnitudes are not physically 
primitive. The primary observables here are relational invariants: ratios, 
relative densities, and logarithmic contrasts (potentials).
-/

namespace InfoGeometry.Canonical.RelativePotentialCore

open InfoGeometry.Canonical.PositiveRayCore

universe u

section Representatives

variable {α : Type u}

/-- Relative density between positive representatives. -/
noncomputable def representativeRelativeDensity
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) : α → ℝ :=
  fun a => μ a / ν a

/-- Relative logarithmic density between positive representatives. -/
noncomputable def representativeRelativeLogDensity
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) : α → ℝ :=
  fun a => Real.log (representativeRelativeDensity μ ν a)

/-- Modular potential attached to a pair of positive representatives. -/
noncomputable def representativeModularPotential
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) : α → ℝ :=
  fun a => -representativeRelativeLogDensity μ ν a

@[simp] theorem representativeRelativeLogDensity_eq_log_sub_log
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeRelativeLogDensity μ ν a = Real.log (μ a) - Real.log (ν a) := by
  unfold representativeRelativeLogDensity representativeRelativeDensity
  rw [Real.log_div (by exact (μ.pos a).ne') (by exact (ν.pos a).ne')]

@[simp] theorem representativeRelativeDensity_eq_exp_representativeRelativeLogDensity
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeRelativeDensity μ ν a
      = Real.exp (representativeRelativeLogDensity μ ν a) := by
  symm
  unfold representativeRelativeLogDensity
  exact Real.exp_log (div_pos (μ.pos a) (ν.pos a))

@[simp] theorem representativeModularPotential_eq_neg_representativeRelativeLogDensity
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeModularPotential μ ν a = -representativeRelativeLogDensity μ ν a := rfl

@[simp] theorem representativeRelativeDensity_scale_left
    (c : ℝ) (hc : 0 < c)
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeRelativeDensity (InfoGeometry.PositiveMeasure.scale c hc μ) ν a
      = c * representativeRelativeDensity μ ν a := by
  unfold representativeRelativeDensity
  rw [InfoGeometry.PositiveMeasure.scale_apply]
  ring

@[simp] theorem representativeRelativeDensity_scale_right
    (d : ℝ) (hd : 0 < d)
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeRelativeDensity μ (InfoGeometry.PositiveMeasure.scale d hd ν) a
      = d⁻¹ * representativeRelativeDensity μ ν a := by
  unfold representativeRelativeDensity
  rw [InfoGeometry.PositiveMeasure.scale_apply]
  field_simp [hd.ne', (ν.pos a).ne']

@[simp] theorem representativeRelativeLogDensity_scale_left
    (c : ℝ) (hc : 0 < c)
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeRelativeLogDensity (InfoGeometry.PositiveMeasure.scale c hc μ) ν a
      = Real.log c + representativeRelativeLogDensity μ ν a := by
  rw [representativeRelativeLogDensity_eq_log_sub_log]
  rw [InfoGeometry.PositiveMeasure.scale_apply, Real.log_mul hc.ne' ((μ.pos a).ne')]
  rw [representativeRelativeLogDensity_eq_log_sub_log]
  ring

@[simp] theorem representativeRelativeLogDensity_scale_right
    (d : ℝ) (hd : 0 < d)
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeRelativeLogDensity μ (InfoGeometry.PositiveMeasure.scale d hd ν) a
      = representativeRelativeLogDensity μ ν a - Real.log d := by
  rw [representativeRelativeLogDensity_eq_log_sub_log]
  rw [InfoGeometry.PositiveMeasure.scale_apply, Real.log_mul hd.ne' ((ν.pos a).ne')]
  rw [representativeRelativeLogDensity_eq_log_sub_log]
  ring

@[simp] theorem representativeRelativeLogDensity_scale_scale
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeRelativeLogDensity
        (InfoGeometry.PositiveMeasure.scale c hc μ)
        (InfoGeometry.PositiveMeasure.scale d hd ν) a
      = representativeRelativeLogDensity μ ν a + Real.log (c / d) := by
  rw [representativeRelativeLogDensity_scale_left]
  rw [representativeRelativeLogDensity_scale_right]
  rw [Real.log_div hc.ne' hd.ne']
  ring

@[simp] theorem representativeModularPotential_scale_left
    (c : ℝ) (hc : 0 < c)
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeModularPotential (InfoGeometry.PositiveMeasure.scale c hc μ) ν a
      = representativeModularPotential μ ν a - Real.log c := by
  unfold representativeModularPotential
  rw [representativeRelativeLogDensity_scale_left]
  ring

@[simp] theorem representativeModularPotential_scale_right
    (d : ℝ) (hd : 0 < d)
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeModularPotential μ (InfoGeometry.PositiveMeasure.scale d hd ν) a
      = representativeModularPotential μ ν a + Real.log d := by
  unfold representativeModularPotential
  rw [representativeRelativeLogDensity_scale_right]
  ring

@[simp] theorem representativeRelativeLogDensity_cocycle
    (μ ν ξ : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeRelativeLogDensity μ ξ a
      = representativeRelativeLogDensity μ ν a
        + representativeRelativeLogDensity ν ξ a := by
  rw [representativeRelativeLogDensity_eq_log_sub_log]
  rw [representativeRelativeLogDensity_eq_log_sub_log]
  rw [representativeRelativeLogDensity_eq_log_sub_log]
  ring

@[simp] theorem representativeRelativeDensity_cocycle
    (μ ν ξ : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeRelativeDensity μ ξ a
      = representativeRelativeDensity μ ν a
        * representativeRelativeDensity ν ξ a := by
  rw [representativeRelativeDensity_eq_exp_representativeRelativeLogDensity]
  rw [representativeRelativeDensity_eq_exp_representativeRelativeLogDensity]
  rw [representativeRelativeDensity_eq_exp_representativeRelativeLogDensity]
  rw [representativeRelativeLogDensity_cocycle]
  rw [Real.exp_add]

@[simp] theorem representativeModularPotential_cocycle
    (μ ν ξ : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    representativeModularPotential μ ξ a
      = representativeModularPotential μ ν a
        + representativeModularPotential ν ξ a := by
  unfold representativeModularPotential
  rw [representativeRelativeLogDensity_cocycle]
  ring

end Representatives

section Rays

variable {α : Type u} [Fintype α] [Nonempty α]

/-- Relative density between projective positive states using the canonical gauge. -/
noncomputable def relativeDensity
    (q q0 : PositiveRay α) : α → ℝ :=
  representativeRelativeDensity (gaugeSection (α := α) q) (gaugeSection (α := α) q0)

/-- Relative logarithmic density between projective positive states. -/
noncomputable def relativeLogDensity
    (q q0 : PositiveRay α) : α → ℝ :=
  representativeRelativeLogDensity (gaugeSection (α := α) q) (gaugeSection (α := α) q0)

/-- Modular potential between projective positive states. -/
noncomputable def relativeModularPotential
    (q q0 : PositiveRay α) : α → ℝ :=
  representativeModularPotential (gaugeSection (α := α) q) (gaugeSection (α := α) q0)

/-- Global additive gauge shift induced by canonical normalization of representatives. -/
noncomputable def representativeMassShift
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) : ℝ :=
  Real.log
    (InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) ν /
      InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) μ)

@[simp] theorem representativeMassShift_self
    (μ : InfoGeometry.PositiveMeasure α ℝ) :
    representativeMassShift μ μ = 0 := by
  unfold representativeMassShift
  rw [div_self (InfoGeometry.PositiveMeasure.Z_ne_zero μ), Real.log_one]

@[simp] theorem representativeMassShift_symm
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) :
    representativeMassShift ν μ = -representativeMassShift μ ν := by
  unfold representativeMassShift
  have hZμ : InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) μ ≠ 0 :=
    InfoGeometry.PositiveMeasure.Z_ne_zero μ
  have hZν : InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) ν ≠ 0 :=
    InfoGeometry.PositiveMeasure.Z_ne_zero ν
  rw [Real.log_div hZμ hZν]
  rw [Real.log_div hZν hZμ]
  ring

@[simp] theorem representativeMassShift_cocycle
    (μ ν ξ : InfoGeometry.PositiveMeasure α ℝ) :
    representativeMassShift μ ξ = representativeMassShift μ ν + representativeMassShift ν ξ := by
  unfold representativeMassShift
  have hZμ : InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) μ ≠ 0 :=
    InfoGeometry.PositiveMeasure.Z_ne_zero μ
  have hZν : InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) ν ≠ 0 :=
    InfoGeometry.PositiveMeasure.Z_ne_zero ν
  have hZξ : InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) ξ ≠ 0 :=
    InfoGeometry.PositiveMeasure.Z_ne_zero ξ
  rw [Real.log_div hZξ hZμ]
  rw [Real.log_div hZν hZμ]
  rw [Real.log_div hZξ hZν]
  ring

/--
For concrete positive representatives, the projective relative density is the
representative relative density corrected by the global mass ratio coming from
canonical normalization.
-/
@[simp] theorem relativeDensity_mk_eq_massRatio_mul_representativeRelativeDensity
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    relativeDensity (Quotient.mk _ μ) (Quotient.mk _ ν) a
      = (InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) ν /
          InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) μ)
          * representativeRelativeDensity μ ν a := by
  unfold relativeDensity representativeRelativeDensity
  rw [gaugeSection_mk, gaugeSection_mk]
  rw [InfoGeometry.PositiveMeasure.normalize_apply, InfoGeometry.PositiveMeasure.normalize_apply]
  have hZμ : InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) μ ≠ 0 :=
    InfoGeometry.PositiveMeasure.Z_ne_zero μ
  have hZν : InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) ν ≠ 0 :=
    InfoGeometry.PositiveMeasure.Z_ne_zero ν
  have hμ : μ a ≠ 0 := (μ.pos a).ne'
  have hν : ν a ≠ 0 := (ν.pos a).ne'
  field_simp [hZμ, hZν, hμ, hν]

/--
For concrete positive representatives, the projective relative log-density is
the representative relative log-density shifted by the logarithm of the global
mass ratio induced by canonical normalization.
-/
@[simp] theorem relativeLogDensity_mk_eq_representativeRelativeLogDensity_add_massShift
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    relativeLogDensity (Quotient.mk _ μ) (Quotient.mk _ ν) a
      = representativeRelativeLogDensity μ ν a
        + representativeMassShift μ ν := by
  unfold relativeLogDensity representativeRelativeLogDensity representativeRelativeDensity
  rw [gaugeSection_mk, gaugeSection_mk]
  rw [InfoGeometry.PositiveMeasure.normalize_apply, InfoGeometry.PositiveMeasure.normalize_apply]
  have hZμ : InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) μ ≠ 0 :=
    InfoGeometry.PositiveMeasure.Z_ne_zero μ
  have hZν : InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) ν ≠ 0 :=
    InfoGeometry.PositiveMeasure.Z_ne_zero ν
  have hμ : μ a ≠ 0 := (μ.pos a).ne'
  have hν : ν a ≠ 0 := (ν.pos a).ne'
  have hsplit :
      μ a / InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) μ /
          (ν a / InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) ν)
        = (InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) ν /
            InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) μ)
            * (μ a / ν a) := by
    field_simp [hZμ, hZν, hμ, hν]
  rw [hsplit]
  rw [Real.log_mul
    (show (InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) ν /
        InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) μ) ≠ 0 by
      exact div_ne_zero hZν hZμ)
    (show μ a / ν a ≠ 0 by exact div_ne_zero hμ hν)]
  rw [show representativeMassShift μ ν =
      Real.log
        (InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) ν /
          InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) μ) by rfl]
  ring

/--
For concrete positive representatives, the projective modular potential is the
representative modular potential shifted by the logarithm of the inverse global
mass ratio induced by canonical normalization.
-/
@[simp] theorem relativeModularPotential_mk_eq_representativeModularPotential_sub_massShift
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    relativeModularPotential (Quotient.mk _ μ) (Quotient.mk _ ν) a
      = representativeModularPotential μ ν a - representativeMassShift μ ν := by
  change -relativeLogDensity (Quotient.mk _ μ) (Quotient.mk _ ν) a
      = representativeModularPotential μ ν a - representativeMassShift μ ν
  rw [relativeLogDensity_mk_eq_representativeRelativeLogDensity_add_massShift]
  rw [representativeModularPotential_eq_neg_representativeRelativeLogDensity]
  ring

@[simp] theorem relativeLogDensity_eq_logDensity_sub_logDensity
    (q q0 : PositiveRay α) (a : α) :
    relativeLogDensity q q0 a =
      InfoGeometry.Canonical.PositiveRayCore.logDensity (α := α) q a
        - InfoGeometry.Canonical.PositiveRayCore.logDensity (α := α) q0 a := by
  exact representativeRelativeLogDensity_eq_log_sub_log
    (μ := gaugeSection (α := α) q)
    (ν := gaugeSection (α := α) q0) a

@[simp] theorem relativeDensity_eq_exp_relativeLogDensity
    (q q0 : PositiveRay α) (a : α) :
    relativeDensity q q0 a = Real.exp (relativeLogDensity q q0 a) := by
  exact representativeRelativeDensity_eq_exp_representativeRelativeLogDensity
    (μ := gaugeSection (α := α) q)
    (ν := gaugeSection (α := α) q0) a

@[simp] theorem relativeModularPotential_eq_neg_relativeLogDensity
    (q q0 : PositiveRay α) (a : α) :
    relativeModularPotential q q0 a = -relativeLogDensity q q0 a := by
  exact representativeModularPotential_eq_neg_representativeRelativeLogDensity
    (μ := gaugeSection (α := α) q)
    (ν := gaugeSection (α := α) q0) a

@[rep_depth projective, simp]
theorem relativeModularPotential_eq_logDensity_base_sub_logDensity
    (q q0 : PositiveRay α) (a : α) :
    relativeModularPotential q q0 a =
      InfoGeometry.Canonical.PositiveRayCore.logDensity (α := α) q0 a
        - InfoGeometry.Canonical.PositiveRayCore.logDensity (α := α) q a := by
  rw [relativeModularPotential_eq_neg_relativeLogDensity]
  rw [relativeLogDensity_eq_logDensity_sub_logDensity]
  ring

@[simp] theorem gaugeSection_eq_relativeDensity_mul_gaugeSection
    (q q0 : PositiveRay α) (a : α) :
    gaugeSection (α := α) q a =
      relativeDensity q q0 a * gaugeSection (α := α) q0 a := by
  unfold relativeDensity representativeRelativeDensity
  have h0 : gaugeSection (α := α) q0 a ≠ 0 := ((gaugeSection (α := α) q0).pos a).ne'
  calc
    gaugeSection (α := α) q a
      = gaugeSection (α := α) q a * 1 := by ring
    _ = gaugeSection (α := α) q a * ((gaugeSection (α := α) q0 a)⁻¹ * gaugeSection (α := α) q0 a) := by
      rw [inv_mul_cancel₀ h0]
    _ = (gaugeSection (α := α) q a / gaugeSection (α := α) q0 a) * gaugeSection (α := α) q0 a := by
      ring

@[simp] theorem relativeDensity_self
    (q : PositiveRay α) (a : α) :
    relativeDensity q q a = 1 := by
  unfold relativeDensity representativeRelativeDensity
  exact div_self ((gaugeSection (α := α) q).pos a).ne'

@[simp] theorem relativeLogDensity_self
    (q : PositiveRay α) (a : α) :
    relativeLogDensity q q a = 0 := by
  rw [relativeLogDensity_eq_logDensity_sub_logDensity]
  ring

@[simp] theorem relativeModularPotential_self
    (q : PositiveRay α) (a : α) :
    relativeModularPotential q q a = 0 := by
  rw [relativeModularPotential_eq_logDensity_base_sub_logDensity]
  ring

@[simp] theorem relativeLogDensity_cocycle
    (q q0 q1 : PositiveRay α) (a : α) :
    relativeLogDensity q q1 a
      = relativeLogDensity q q0 a + relativeLogDensity q0 q1 a := by
  exact representativeRelativeLogDensity_cocycle
    (μ := gaugeSection (α := α) q)
    (ν := gaugeSection (α := α) q0)
    (ξ := gaugeSection (α := α) q1) a

@[simp] theorem relativeDensity_cocycle
    (q q0 q1 : PositiveRay α) (a : α) :
    relativeDensity q q1 a
      = relativeDensity q q0 a * relativeDensity q0 q1 a := by
  exact representativeRelativeDensity_cocycle
    (μ := gaugeSection (α := α) q)
    (ν := gaugeSection (α := α) q0)
    (ξ := gaugeSection (α := α) q1) a

@[simp] theorem relativeModularPotential_cocycle
    (q q0 q1 : PositiveRay α) (a : α) :
    relativeModularPotential q q1 a
      = relativeModularPotential q q0 a + relativeModularPotential q0 q1 a := by
  exact representativeModularPotential_cocycle
    (μ := gaugeSection (α := α) q)
    (ν := gaugeSection (α := α) q0)
    (ξ := gaugeSection (α := α) q1) a

end Rays

end InfoGeometry.Canonical.RelativePotentialCore
