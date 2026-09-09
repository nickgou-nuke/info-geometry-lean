import InfoGeometry.Thermo.GenericMetriplecticFlow
import Mathlib.Tactic

/-!
# A concrete GENERIC model for bipolar coordinate lanes

The informal assignment `dS = -dη`, `dH = dθ` does not by itself define a
metriplectic system. The skew operator, positive symmetric operator, and both
Casimir conditions must be supplied and proved.

This file gives one explicit nontrivial finite model. The state carrier has
three real coordinates `(η, θ, a)`. The auxiliary coordinate `a` is conjugate
to `θ` in the reversible plane, while `η` is a Casimir of the skew operator.
The dissipative operator is the positive rank-one projector in the `η`
direction.

With

`dH = dθ`,  `dS = -dη`,

we obtain

`L dH = -e_a`,  `M dS = -e_η`,

energy rate zero, and entropy rate one. In particular, the condition `η = 0`
at a state does not imply `dη = 0` or make the dissipative lane disappear.

This is a finite linear GENERIC realization, not a BKM identification or a
state-dependent thermodynamic constitutive law.
-/

noncomputable section

namespace InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel

open InfoGeometry.Thermo.GenericMetriplecticFlow

/-- Three-coordinate state carrier `(η, θ, auxiliary)`. -/
abbrev State3 := Fin 3 → ℝ

/-- Basis vector in the longitudinal `η` direction. -/
def etaBasis3 : State3 := ![1, 0, 0]

/-- Basis vector in the angular `θ` direction. -/
def thetaBasis3 : State3 := ![0, 1, 0]

/-- Auxiliary vector conjugate to `θ` in the reversible plane. -/
def auxiliaryBasis3 : State3 := ![0, 0, 1]

/-- Coordinate covector `dη`. -/
def etaCovector : Covector State3 where
  toFun x := x 0
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Coordinate covector `dθ`. -/
def thetaCovector : Covector State3 where
  toFun x := x 1
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Auxiliary coordinate covector. -/
def auxiliaryCovector : Covector State3 where
  toFun x := x 2
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp] theorem etaCovector_etaBasis3 : etaCovector etaBasis3 = 1 := by
  simp [etaCovector, etaBasis3]

@[simp] theorem etaCovector_thetaBasis3 : etaCovector thetaBasis3 = 0 := by
  simp [etaCovector, thetaBasis3]

@[simp] theorem etaCovector_auxiliaryBasis3 : etaCovector auxiliaryBasis3 = 0 := by
  simp [etaCovector, auxiliaryBasis3]

@[simp] theorem thetaCovector_etaBasis3 : thetaCovector etaBasis3 = 0 := by
  simp [thetaCovector, etaBasis3]

@[simp] theorem thetaCovector_thetaBasis3 : thetaCovector thetaBasis3 = 1 := by
  simp [thetaCovector, thetaBasis3]

@[simp] theorem thetaCovector_auxiliaryBasis3 : thetaCovector auxiliaryBasis3 = 0 := by
  simp [thetaCovector, auxiliaryBasis3]

@[simp] theorem auxiliaryCovector_etaBasis3 : auxiliaryCovector etaBasis3 = 0 := by
  simp [auxiliaryCovector, etaBasis3]

@[simp] theorem auxiliaryCovector_thetaBasis3 : auxiliaryCovector thetaBasis3 = 0 := by
  simp [auxiliaryCovector, thetaBasis3]

@[simp] theorem auxiliaryCovector_auxiliaryBasis3 :
    auxiliaryCovector auxiliaryBasis3 = 1 := by
  simp [auxiliaryCovector, auxiliaryBasis3]

/-- Degenerate Poisson operator on the `(θ, auxiliary)` plane. -/
def reversibleOperator : Covector State3 →ₗ[ℝ] State3 where
  toFun α :=
    α auxiliaryBasis3 • thetaBasis3 -
      α thetaBasis3 • auxiliaryBasis3
  map_add' α β := by
    ext i
    fin_cases i <;>
      simp [etaBasis3, thetaBasis3, auxiliaryBasis3] <;>
      ring
  map_smul' c α := by
    ext i
    fin_cases i <;>
      simp [etaBasis3, thetaBasis3, auxiliaryBasis3] <;>
      ring

/-- Positive rank-one Onsager operator in the `η` direction. -/
def dissipativeOperator : Covector State3 →ₗ[ℝ] State3 where
  toFun α := α etaBasis3 • etaBasis3
  map_add' α β := by
    ext i
    fin_cases i <;> simp [etaBasis3] <;> ring
  map_smul' c α := by
    ext i
    fin_cases i <;> simp [etaBasis3] <;> ring

/-- The reversible operator is skew with respect to covector evaluation. -/
theorem reversibleOperator_skew (α β : Covector State3) :
    α (reversibleOperator β) = -β (reversibleOperator α) := by
  simp [reversibleOperator]
  ring

/-- The dissipative operator is symmetric. -/
theorem dissipativeOperator_symmetric (α β : Covector State3) :
    α (dissipativeOperator β) = β (dissipativeOperator α) := by
  simp [dissipativeOperator]
  ring

/-- The dissipative quadratic response is a square. -/
theorem dissipativeOperator_nonneg (α : Covector State3) :
    0 ≤ α (dissipativeOperator α) := by
  simpa [dissipativeOperator, pow_two] using sq_nonneg (α etaBasis3)

/-- Longitudinal entropy covector is a Casimir of the skew operator. -/
theorem reversibleOperator_neg_eta_zero :
    reversibleOperator (-etaCovector) = 0 := by
  ext i
  fin_cases i <;>
    simp [reversibleOperator, etaCovector, etaBasis3,
      thetaBasis3, auxiliaryBasis3]

/-- Angular Hamiltonian covector lies in the kernel of the dissipative operator. -/
theorem dissipativeOperator_theta_zero :
    dissipativeOperator thetaCovector = 0 := by
  ext i
  fin_cases i <;>
    simp [dissipativeOperator, thetaCovector, etaBasis3]

/-- Concrete nontrivial finite GENERIC system. -/
def bipolarGENERIC : System State3 where
  dH := thetaCovector
  dS := -etaCovector
  L := reversibleOperator
  M := dissipativeOperator
  L_skew := reversibleOperator_skew
  L_entropy_casimir := reversibleOperator_neg_eta_zero
  M_symmetric := dissipativeOperator_symmetric
  M_hamiltonian_casimir := dissipativeOperator_theta_zero
  M_nonneg := dissipativeOperator_nonneg

/-- Exact reversible component. -/
theorem reversible_component :
    bipolarGENERIC.L bipolarGENERIC.dH = -auxiliaryBasis3 := by
  ext i
  fin_cases i <;>
    simp [bipolarGENERIC, reversibleOperator, thetaCovector,
      thetaBasis3, auxiliaryBasis3]

/-- Exact dissipative component. -/
theorem dissipative_component :
    bipolarGENERIC.M bipolarGENERIC.dS = -etaBasis3 := by
  ext i
  fin_cases i <;>
    simp [bipolarGENERIC, dissipativeOperator, etaCovector, etaBasis3]

/-- The full GENERIC velocity contains both independent components. -/
theorem bipolarGENERIC_flow :
    bipolarGENERIC.flow = -auxiliaryBasis3 - etaBasis3 := by
  change bipolarGENERIC.L bipolarGENERIC.dH +
      bipolarGENERIC.M bipolarGENERIC.dS =
    -auxiliaryBasis3 - etaBasis3
  rw [reversible_component, dissipative_component]
  abel

/-- Energy is conserved by the concrete GENERIC flow. -/
theorem bipolarGENERIC_energy_rate :
    bipolarGENERIC.dH bipolarGENERIC.flow = 0 := by
  exact bipolarGENERIC.energy_rate

/-- Entropy production is exactly one in this normalized finite model. -/
theorem bipolarGENERIC_entropy_rate :
    bipolarGENERIC.dS bipolarGENERIC.flow = 1 := by
  rw [bipolarGENERIC_flow]
  simp [bipolarGENERIC, etaCovector, etaBasis3, auxiliaryBasis3]

/-- Hence entropy production is nonnegative. -/
theorem bipolarGENERIC_entropy_rate_nonneg :
    0 ≤ bipolarGENERIC.dS bipolarGENERIC.flow := by
  rw [bipolarGENERIC_entropy_rate]
  norm_num

/-- State on the coordinate hypersurface `η = 0`. -/
def criticalCoordinateState (θ a : ℝ) : State3 := ![0, θ, a]

@[simp] theorem etaCovector_criticalCoordinateState (θ a : ℝ) :
    etaCovector (criticalCoordinateState θ a) = 0 := by
  simp [etaCovector, criticalCoordinateState]

/-- The entropy covector itself remains nonzero when evaluated on its dual basis
vector; a zero coordinate value does not annihilate its differential. -/
theorem entropyCovector_etaBasis3 :
    bipolarGENERIC.dS etaBasis3 = -1 := by
  simp [bipolarGENERIC, etaCovector, etaBasis3]

/-- The dissipative component does not vanish merely because the state lies on
`η = 0`. -/
theorem critical_coordinate_dissipative_lane_survives (θ a : ℝ) :
    etaCovector (criticalCoordinateState θ a) = 0 ∧
      bipolarGENERIC.M bipolarGENERIC.dS = -etaBasis3 ∧
      bipolarGENERIC.M bipolarGENERIC.dS ≠ 0 := by
  refine ⟨etaCovector_criticalCoordinateState θ a, dissipative_component, ?_⟩
  rw [dissipative_component]
  intro h
  have h0 := congrArg (fun x : State3 => x 0) h
  norm_num [etaBasis3] at h0

/-- Compact corrected GENERIC packet. -/
theorem bipolar_GENERIC_packet :
    bipolarGENERIC.L bipolarGENERIC.dS = 0 ∧
      bipolarGENERIC.M bipolarGENERIC.dH = 0 ∧
      bipolarGENERIC.L bipolarGENERIC.dH = -auxiliaryBasis3 ∧
      bipolarGENERIC.M bipolarGENERIC.dS = -etaBasis3 ∧
      bipolarGENERIC.dH bipolarGENERIC.flow = 0 ∧
      bipolarGENERIC.dS bipolarGENERIC.flow = 1 := by
  exact ⟨bipolarGENERIC.L_entropy_casimir,
    bipolarGENERIC.M_hamiltonian_casimir,
    reversible_component,
    dissipative_component,
    bipolarGENERIC_energy_rate,
    bipolarGENERIC_entropy_rate⟩

end InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel

