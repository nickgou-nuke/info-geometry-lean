import Mathlib.Topology.Instances.Real.Lemmas
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Instances.Matrix
import InfoGeometry.Dynamics.RindlerWedge

noncomputable section

namespace InfoGeometry.Dynamics.RindlerWedgeTopology

open InfoGeometry.Dynamics.RindlerWedge
open InfoGeometry.Dynamics.RapiditySpace

instance : TopologicalSpace RindlerCoordinates :=
  TopologicalSpace.induced (fun c => (c.radius, c.time)) inferInstance

def timeShift (lam : ℝ) (coords : RindlerCoordinates) : RindlerCoordinates :=
  { radius := coords.radius
    time := coords.time + lam
    radius_pos := coords.radius_pos }

theorem continuous_timeShift (lam : ℝ) :
    Continuous (timeShift lam) := by
  have hr : Continuous (fun c : RindlerCoordinates => c.radius) :=
    continuous_fst.comp (continuous_induced_dom :
      Continuous (fun c : RindlerCoordinates => (c.radius, c.time)))
  have ht : Continuous (fun c : RindlerCoordinates => c.time) :=
    continuous_snd.comp (continuous_induced_dom :
      Continuous (fun c : RindlerCoordinates => (c.radius, c.time)))
  apply continuous_induced_rng.mpr
  exact Continuous.prodMk hr (ht.add continuous_const)

def timeShiftHomeomorph (lam : ℝ) : RindlerCoordinates ≃ₜ RindlerCoordinates where
  toFun := timeShift lam
  invFun := timeShift (-lam)
  left_inv := by
    intro coords
    cases coords
    simp [timeShift]
  right_inv := by
    intro coords
    cases coords
    simp [timeShift]
  continuous_toFun := continuous_timeShift lam
  continuous_invFun := by
    simpa using continuous_timeShift (-lam)

@[simp] theorem timeShiftHomeomorph_apply (lam : ℝ) (coords : RindlerCoordinates) :
    timeShiftHomeomorph lam coords = timeShift lam coords := rfl

def radiusSquared : RindlerCoordinates → ℝ :=
  fun coords => coords.radius ^ 2

theorem continuous_radiusSquared : Continuous radiusSquared := by
  have hr : Continuous (fun c : RindlerCoordinates => c.radius) :=
    continuous_fst.comp (continuous_induced_dom :
      Continuous (fun c : RindlerCoordinates => (c.radius, c.time)))
  exact hr.pow 2

theorem radiusSquared_timeShift (lam : ℝ) (coords : RindlerCoordinates) :
    radiusSquared (timeShift lam coords) = radiusSquared coords := by
  simp [radiusSquared, timeShift]

theorem radiusSquared_timeShiftHomeomorph (lam : ℝ) (coords : RindlerCoordinates) :
    radiusSquared (timeShiftHomeomorph lam coords) = radiusSquared coords := by
  rw [timeShiftHomeomorph_apply]
  exact radiusSquared_timeShift lam coords

theorem continuous_rindlerToMinkowski :
    Continuous (rindlerToMinkowski : RindlerCoordinates → LightConeColumn) := by
  have hr : Continuous (fun c : RindlerCoordinates => c.radius) :=
    continuous_fst.comp (continuous_induced_dom :
      Continuous (fun c : RindlerCoordinates => (c.radius, c.time)))
  have ht : Continuous (fun c : RindlerCoordinates => c.time) :=
    continuous_snd.comp (continuous_induced_dom :
      Continuous (fun c : RindlerCoordinates => (c.radius, c.time)))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [rindlerToMinkowski, RindlerCoordinates.radius, RindlerCoordinates.time] <;>
    fun_prop

def lightConeProduct : LightConeColumn → ℝ :=
  fun x => x 0 0 * x 1 0

theorem continuous_lightConeProduct : Continuous lightConeProduct := by
  unfold lightConeProduct
  fun_prop

def rindlerLightConeProduct : RindlerCoordinates → ℝ :=
  fun coords => lightConeProduct (rindlerToMinkowski coords)

theorem continuous_rindlerLightConeProduct :
    Continuous rindlerLightConeProduct := by
  exact Continuous.comp continuous_lightConeProduct continuous_rindlerToMinkowski

theorem rindlerLightConeProduct_eq_radiusSquared (coords : RindlerCoordinates) :
    rindlerLightConeProduct coords = radiusSquared coords := by
  simpa [rindlerLightConeProduct, lightConeProduct, radiusSquared] using
    rindler_lightcone_product coords

end InfoGeometry.Dynamics.RindlerWedgeTopology
