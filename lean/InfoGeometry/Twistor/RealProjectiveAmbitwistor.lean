/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealDualTwistor
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Real projective dual incidence

Incidence is a relation between an actual projective vector and an actual
projective covector.  It is defined by inclusion in the native dual
annihilator, so it is independent of both representative choices by
construction.  Its representative theorem recovers `φ(v) = 0`, and frame
covariance uses the genuine contragredient dual action.

The subtype below is a projective algebraic incidence space.  Identifying it
with a null-geodesic space, or equipping it with analytic or contact geometry,
requires further theorems.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Twistor.RealProjectiveAmbitwistor

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- A dual ray is incident with a primal ray when it annihilates that ray. -/
def Incident (Z : ℙ ℝ V) (Φ : ℙ ℝ (Module.Dual ℝ V)) : Prop :=
  Φ.submodule ≤ Z.submodule.dualAnnihilator

@[simp] theorem incident_mk_iff (v : V) (φ : Module.Dual ℝ V)
    (hv : v ≠ 0) (hφ : φ ≠ 0) :
    Incident (Projectivization.mk ℝ v hv) (Projectivization.mk ℝ φ hφ) ↔
      φ v = 0 := by
  change ℝ ∙ φ ≤ (ℝ ∙ v).dualAnnihilator ↔ φ v = 0
  rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_dualAnnihilator]
  constructor
  · intro h
    exact h v (Submodule.mem_span_singleton_self v)
  · intro h w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [h]

/-- Native projective incidence with separately projectivized primal/dual
factors; this is not projectivization of their direct sum. -/
abbrev Space (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  {p : ℙ ℝ V × ℙ ℝ (Module.Dual ℝ V) // Incident p.1 p.2}

def mk (v : V) (φ : Module.Dual ℝ V) (hv : v ≠ 0) (hφ : φ ≠ 0)
    (h : φ v = 0) : Space V :=
  ⟨(Projectivization.mk ℝ v hv, Projectivization.mk ℝ φ hφ),
    (incident_mk_iff v φ hv hφ).mpr h⟩

/-- Exact nilpotence criterion for any nonzero representatives. -/
theorem incident_mk_iff_dyad_sq_zero (v : V) (φ : Module.Dual ℝ V)
    (hv : v ≠ 0) (hφ : φ ≠ 0) :
    Incident (Projectivization.mk ℝ v hv) (Projectivization.mk ℝ φ hφ) ↔
      RealDualTwistor.dyad (v, φ) * RealDualTwistor.dyad (v, φ) = 0 := by
  rw [incident_mk_iff, RealDualTwistor.dyad_sq_zero_iff _ hv hφ]
  rfl

/-- Real changes of frame preserve and reflect projective dual incidence. -/
theorem incident_frame_iff (e : V ≃ₗ[ℝ] W)
    (Z : ℙ ℝ V) (Φ : ℙ ℝ (Module.Dual ℝ V)) :
    Incident (Projectivization.map e.toLinearMap e.injective Z)
      (Projectivization.map e.symm.dualMap.toLinearMap e.symm.dualMap.injective Φ) ↔
        Incident Z Φ := by
  induction Z using Projectivization.ind with
  | h v hv =>
    induction Φ using Projectivization.ind with
    | h φ hφ =>
      simp only [Projectivization.map_mk, incident_mk_iff,
        LinearEquiv.coe_coe, LinearEquiv.dualMap_apply,
        LinearEquiv.symm_apply_apply]

end InfoGeometry.Twistor.RealProjectiveAmbitwistor
