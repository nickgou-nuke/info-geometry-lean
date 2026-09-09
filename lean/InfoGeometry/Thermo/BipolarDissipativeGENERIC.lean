import InfoGeometry.Thermo.GenericMetriplecticFlow

/-! A concrete finite dissipative bipolar submodel.

On a two-dimensional carrier a nonzero skew map cannot have a one-dimensional
kernel.  Accordingly this owner realizes the exact entropy-gradient lane and
keeps the reversible map zero; a nonzero reversible lane requires an enlarged
carrier.
-/

noncomputable section

namespace InfoGeometry.Thermo.BipolarDissipativeGENERIC

open InfoGeometry.Thermo.GenericMetriplecticFlow

abbrev State := ℝ × ℝ
abbrev Covector := GenericMetriplecticFlow.Covector State

def eEta : State := (1, 0)
def eTheta : State := (0, 1)

def dEta : Covector where
  toFun x := x.1
  map_add' x y := by simp
  map_smul' a x := by simp

def dTheta : Covector where
  toFun x := x.2
  map_add' x y := by simp
  map_smul' a x := by simp

def dissipative : Covector →ₗ[ℝ] State where
  toFun α := (α eEta, 0)
  map_add' α β := by ext <;> simp
  map_smul' a α := by ext <;> simp

def etaMetriplecticSystem : GenericMetriplecticFlow.System State where
  dH := dTheta
  dS := dEta
  L := 0
  M := dissipative
  L_skew := by
    intro α β
    simp
  L_entropy_casimir := by
    rfl
  M_symmetric := by
    intro α β
    have hα : (β eEta, 0) = (β eEta) • eEta := by
      ext <;> simp [eEta]
    have hβ : (α eEta, 0) = (α eEta) • eEta := by
      ext <;> simp [eEta]
    change α (β eEta, 0) = β (α eEta, 0)
    rw [hα, hβ, map_smul, map_smul]
    exact mul_comm _ _
  M_hamiltonian_casimir := by
    ext <;> simp [dissipative, dTheta, eEta]
  M_nonneg := by
    intro α
    have hα : (α eEta, 0) = (α eEta) • eEta := by
      ext <;> simp [eEta]
    change 0 ≤ α (α eEta, 0)
    rw [hα, map_smul]
    have hs : (α eEta • α eEta : ℝ) = (α eEta) ^ 2 := by
      simp [smul_eq_mul, pow_two]
    rw [hs]
    exact sq_nonneg (α eEta)

theorem energy_rate_zero :
    etaMetriplecticSystem.dH etaMetriplecticSystem.flow = 0 :=
  etaMetriplecticSystem.energy_rate

theorem entropy_rate_nonneg :
    0 ≤ etaMetriplecticSystem.dS etaMetriplecticSystem.flow :=
  etaMetriplecticSystem.entropy_rate_nonneg

theorem entropy_rate_formula :
    etaMetriplecticSystem.dS etaMetriplecticSystem.flow = 1 := by
  rw [etaMetriplecticSystem.entropy_rate_eq_dissipative]
  change dEta (dissipative dEta) = 1
  simp [dEta, dissipative, eEta]

end InfoGeometry.Thermo.BipolarDissipativeGENERIC
