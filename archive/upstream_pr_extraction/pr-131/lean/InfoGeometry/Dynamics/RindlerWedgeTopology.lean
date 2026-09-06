import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Matrix
import InfoGeometry.Dynamics.RindlerWedge

noncomputable section

namespace InfoGeometry.Dynamics.RindlerWedgeTopology

open InfoGeometry.Dynamics.RindlerWedge
open InfoGeometry.Dynamics.RapiditySpace

def timeShift (lam : ℝ) (coords : RindlerCoordinates) : RindlerCoordinates :=
  ⟨(coords.radius, coords.time + lam), coords.radius_pos⟩

theorem continuous_timeShift (lam : ℝ) :
    Continuous (timeShift lam) := by
  apply Continuous.subtype_mk
  exact Continuous.prodMk (continuous_subtype_val.fst)
    ((continuous_subtype_val.snd).add continuous_const)

def timeShiftHomeomorph (lam : ℝ) : RindlerCoordinates ≃ₜ RindlerCoordinates where
  toFun := timeShift lam
  invFun := timeShift (-lam)
  left_inv := by
    intro coords
    apply Subtype.ext
    change (coords.radius, (coords.time + lam) + -lam) =
      (coords.radius, coords.time)
    congr 1
    ring
  right_inv := by
    intro coords
    apply Subtype.ext
    change (coords.radius, (coords.time + -lam) + lam) =
      (coords.radius, coords.time)
    congr 1
    ring
  continuous_toFun := continuous_timeShift lam
  continuous_invFun := by
    simpa using continuous_timeShift (-lam)

@[simp] theorem timeShiftHomeomorph_apply (lam : ℝ) (coords : RindlerCoordinates) :
    timeShiftHomeomorph lam coords = timeShift lam coords := rfl

def radiusSquared : RindlerCoordinates → ℝ :=
  fun coords => coords.radius ^ 2

theorem continuous_radiusSquared : Continuous radiusSquared := by
  exact (continuous_subtype_val.fst).pow 2

theorem radiusSquared_timeShift (lam : ℝ) (coords : RindlerCoordinates) :
    radiusSquared (timeShift lam coords) = radiusSquared coords := by
  rfl

theorem radiusSquared_timeShiftHomeomorph (lam : ℝ) (coords : RindlerCoordinates) :
    radiusSquared (timeShiftHomeomorph lam coords) = radiusSquared coords := by
  rw [timeShiftHomeomorph_apply]
  exact radiusSquared_timeShift lam coords

theorem continuous_rindlerToMinkowski :
    Continuous (rindlerToMinkowski : RindlerCoordinates → LightConeColumn) := by
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
