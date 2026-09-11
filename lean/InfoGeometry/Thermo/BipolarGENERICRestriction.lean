import InfoGeometry.Thermo.BipolarDissipativeGENERIC
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Thermo.BipolarThreeCoordinateGENERIC
import InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
import InfoGeometry.Analysis.BipolarCrossRatioLog

/-!
# Restriction of the three-coordinate bipolar GENERIC model

The two-coordinate dissipative model is the projection of the explicit
three-coordinate model onto its `(eta, theta)` coordinates.  This is the
canonical carrier map available here: the auxiliary coordinate is retained by
the larger model, while the projected dissipative flow agrees with the smaller
model.  No identification of the two state spaces is introduced.
-/

noncomputable section

namespace InfoGeometry.Thermo.BipolarGENERICRestriction

open InfoGeometry.Thermo.GenericMetriplecticFlow
open InfoGeometry.Thermo.BipolarDissipativeGENERIC
open InfoGeometry.Thermo.BipolarThreeCoordinateGENERIC
open InfoGeometry.Analysis.BipolarCrossRatioLog

def project (x : Fin 3 → ℝ) : ℝ × ℝ := (x 0, x 1)

def projectLinear : (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := project
  map_add' x y := by
    simp [project]
  map_smul' a x := by
    simp [project]

def sectionMap : (ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![x.1, x.2, 0]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' a x := by
    ext i
    fin_cases i <;> simp

def bipolarState (s : ℂ) : Fin 3 → ℝ :=
  sectionMap (eta s, theta s)

theorem project_sectionMap (x : ℝ × ℝ) :
    project (sectionMap x) = x := by
  ext <;> simp [project, sectionMap]

theorem project_bipolarState (s : ℂ) :
    project (bipolarState s) = (eta s, theta s) := by
  exact project_sectionMap (eta s, theta s)

theorem bipolarState_criticalLine (y : ℝ) :
    bipolarState (criticalLine y) = ![0, theta (criticalLine y), 0] := by
  ext i
  fin_cases i <;> simp [bipolarState, sectionMap, eta_criticalLine]

theorem projectLinear_comp_sectionMap :
    projectLinear.comp sectionMap = LinearMap.id := by
  ext <;> simp [projectLinear, project, sectionMap]

theorem sectionMap_injective : Function.Injective sectionMap := by
  intro x y hxy
  have h := congrArg project hxy
  simpa [project_sectionMap] using h

theorem projected_three_coordinate_flow :
    project BipolarThreeCoordinateGENERIC.system.flow =
      BipolarDissipativeGENERIC.etaMetriplecticSystem.flow := by
  rw [BipolarThreeCoordinateGENERIC.flow_explicit]
  dsimp [BipolarDissipativeGENERIC.etaMetriplecticSystem, System.flow]
  ext <;> simp [project, BipolarThreeCoordinateGENERIC.basis,
    BipolarDissipativeGENERIC.dissipative,
    BipolarDissipativeGENERIC.dEta,
    BipolarDissipativeGENERIC.eEta]

theorem sectionMap_projected_flow_eq_full_flow_add_auxiliary :
    sectionMap (project BipolarThreeCoordinateGENERIC.system.flow) =
      BipolarThreeCoordinateGENERIC.system.flow +
        BipolarThreeCoordinateGENERIC.basis 2 := by
  rw [BipolarThreeCoordinateGENERIC.flow_explicit]
  ext i
  fin_cases i <;> simp [project, sectionMap,
    BipolarThreeCoordinateGENERIC.basis]

theorem projected_energy_rate_zero :
    BipolarDissipativeGENERIC.dTheta
        (project BipolarThreeCoordinateGENERIC.system.flow) = 0 := by
  rw [projected_three_coordinate_flow]
  exact BipolarDissipativeGENERIC.energy_rate_zero

theorem projected_entropy_rate_one :
    BipolarDissipativeGENERIC.dEta
        (project BipolarThreeCoordinateGENERIC.system.flow) = 1 := by
  rw [projected_three_coordinate_flow]
  exact BipolarDissipativeGENERIC.entropy_rate_formula

/-- The two existing entropy conventions are related by reversing only eta. -/
def etaReflection : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![-x 0, x 1, x 2]
  invFun x := ![-x 0, x 1, x 2]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' a x := by ext i; fin_cases i <;> simp

/-- Exact equality of all GENERIC data after transport, not just agreement of
the entropy production rates. -/
theorem transport_etaReflection :
    BipolarThreeCoordinateGENERIC.system.transport etaReflection =
      BipolarGENERICThreeCoordinateModel.bipolarGENERIC := by
  apply System.ext
  · ext x
    simp [System.transport, etaReflection, BipolarThreeCoordinateGENERIC.system,
      BipolarThreeCoordinateGENERIC.dTheta, coordinate,
      BipolarGENERICThreeCoordinateModel.bipolarGENERIC,
      BipolarGENERICThreeCoordinateModel.thetaCovector]
  · ext x
    simp [System.transport, etaReflection, BipolarThreeCoordinateGENERIC.system,
      BipolarThreeCoordinateGENERIC.dEta, coordinate,
      BipolarGENERICThreeCoordinateModel.bipolarGENERIC,
      BipolarGENERICThreeCoordinateModel.etaCovector]
  · ext α i
    fin_cases i <;>
      simp [System.transport, etaReflection, BipolarThreeCoordinateGENERIC.system,
        reversible, basis, BipolarGENERICThreeCoordinateModel.bipolarGENERIC,
        BipolarGENERICThreeCoordinateModel.reversibleOperator,
        BipolarGENERICThreeCoordinateModel.thetaBasis3,
        BipolarGENERICThreeCoordinateModel.auxiliaryBasis3]
  · have hneg : (![-1, 0, 0] : Fin 3 → ℝ) = -![1, 0, 0] := by
      ext i
      fin_cases i <;> simp
    ext α i
    fin_cases i <;>
      simp [System.transport, etaReflection, BipolarThreeCoordinateGENERIC.system,
        BipolarThreeCoordinateGENERIC.dissipative, basis,
        BipolarGENERICThreeCoordinateModel.bipolarGENERIC,
        BipolarGENERICThreeCoordinateModel.dissipativeOperator,
        BipolarGENERICThreeCoordinateModel.etaBasis3]
    rw [hneg, map_neg, neg_neg]

/-- Projecting the negative-eta convention yields the reflected positive-eta
flow; the two conventions must not be equated without this coordinate map. -/
theorem projected_negative_entropy_flow :
    project BipolarGENERICThreeCoordinateModel.bipolarGENERIC.flow = (-1, 0) := by
  rw [← transport_etaReflection, System.transport_flow,
    BipolarThreeCoordinateGENERIC.flow_explicit]
  simp [project, etaReflection, basis]

end InfoGeometry.Thermo.BipolarGENERICRestriction
