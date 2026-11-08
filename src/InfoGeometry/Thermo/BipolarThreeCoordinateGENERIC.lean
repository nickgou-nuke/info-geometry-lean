import InfoGeometry.Thermo.GenericMetriplecticFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! A concrete three-coordinate GENERIC carrier.

The third coordinate supplies the reversible partner needed for a nonzero
skew map whose kernel contains the entropy covector.
-/

noncomputable section

namespace InfoGeometry.Thermo.BipolarThreeCoordinateGENERIC

open InfoGeometry.Thermo.GenericMetriplecticFlow

abbrev State := InfoGeometry.Algebra.FiniteSpin.Vec3R
abbrev Covector := GenericMetriplecticFlow.Covector State

def basis (i : Fin 3) : State := Pi.single i 1

def coordinate (i : Fin 3) : Covector where
  toFun x := x i
  map_add' x y := by simp
  map_smul' a x := by simp

def evaluate (i : Fin 3) : Covector →ₗ[ℝ] ℝ where
  toFun α := α (basis i)
  map_add' α β := by simp
  map_smul' a α := by simp

def reversible : Covector →ₗ[ℝ] State where
  toFun α := fun i => if i = 1 then α (basis 2) else if i = 2 then -α (basis 1) else 0
  map_add' α β := by
    funext i
    by_cases hi : i = 1 <;> by_cases hj : i = 2 <;> simp [hi, hj] <;> ring
  map_smul' a α := by
    funext i
    by_cases hi : i = 1 <;> by_cases hj : i = 2 <;> simp [hi, hj]

def dissipative : Covector →ₗ[ℝ] State where
  toFun α := fun i => if i = 0 then α (basis 0) else 0
  map_add' α β := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  map_smul' a α := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]

def dEta : Covector := coordinate 0
def dTheta : Covector := coordinate 1

lemma coordinate_basis (i j : Fin 3) : coordinate i (basis j) = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp [coordinate, basis]
  · simp [coordinate, basis, h]

lemma reversible_expand (α : Covector) :
    reversible α = α (basis 2) • basis 1 + (-α (basis 1)) • basis 2 := by
  funext i
  fin_cases i <;> simp [reversible, basis]

lemma dissipative_expand (α : Covector) :
    dissipative α = α (basis 0) • basis 0 := by
  funext i
  fin_cases i <;> simp [dissipative, basis]

lemma reversible_dEta : reversible dEta = 0 := by
  funext i
  fin_cases i
  · simp [reversible]
  · simp [reversible, dEta, coordinate_basis]
  · simp [reversible, dEta, coordinate_basis]

def system : GenericMetriplecticFlow.System State where
  dH := dTheta
  dS := dEta
  L := reversible
  M := dissipative
  L_skew := by
    intro α β
    rw [reversible_expand, reversible_expand, map_add, map_add,
      map_smul, map_smul, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  L_entropy_casimir := by
    exact reversible_dEta
  M_symmetric := by
    intro α β
    rw [dissipative_expand, dissipative_expand, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  M_hamiltonian_casimir := by
    rw [dissipative_expand]
    simp [dTheta, coordinate, basis]
  M_nonneg := by
    intro α
    rw [dissipative_expand, map_smul]
    simpa [smul_eq_mul, pow_two] using sq_nonneg (α (basis 0))

theorem energy_rate_zero : system.dH system.flow = 0 := system.energy_rate

theorem entropy_rate_nonneg : 0 ≤ system.dS system.flow := system.entropy_rate_nonneg

theorem reversible_entropy_casimir : reversible dEta = 0 := system.L_entropy_casimir

theorem flow_explicit : system.flow = basis 0 - basis 2 := by
  dsimp [system, GenericMetriplecticFlow.System.flow]
  rw [reversible_expand, dissipative_expand]
  simp [dEta, dTheta, coordinate_basis, sub_eq_add_neg]
  abel

theorem flow_eta_component : system.flow 0 = 1 := by
  rw [flow_explicit]
  simp [basis]

theorem flow_theta_component : system.flow 1 = 0 := by
  rw [flow_explicit]
  simp [basis]

theorem flow_auxiliary_component : system.flow 2 = -1 := by
  rw [flow_explicit]
  simp [basis]

end InfoGeometry.Thermo.BipolarThreeCoordinateGENERIC
