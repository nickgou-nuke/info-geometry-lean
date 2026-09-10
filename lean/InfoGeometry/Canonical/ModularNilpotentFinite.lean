import InfoGeometry.Canonical.SplitCliffordSourceWickBase
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.OperatorAlgebra.SuperVirasoroExtension
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.ModularNilpotentFinite

Parabolic nilpotent modular flow and global mode zero-anomaly readouts.
-/

namespace InfoGeometry.Canonical.ModularNilpotentFinite

open Matrix
open Filter
open InfoGeometry.Canonical.SplitCliffordSourceWickBase
open InfoGeometry.Canonical.CurrentSugawaraBridge

/-- Local concrete matrix carrier for this finite nilpotent lane. -/
abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- Local modular perturbation `Δ = 1 + N`. -/
def Delta : M2R :=
  (1 : M2R) + N

/-- Local modular Hamiltonian/logarithmic coordinate in the square-zero sector. -/
def logModular : M2R :=
  N

/-- Regularized modular flux coordinate `Δ - 1`. -/
def modularFlux : M2R :=
  Delta - (1 : M2R)

/-- Local information free-energy operator `(Δ - 1) - log(Δ)`. -/
def informationFreeEnergy : M2R :=
  modularFlux - logModular

@[simp]
theorem N_sq_zero :
    N * N = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem modularFlux_eq_N :
    modularFlux = N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularFlux, Delta, N]

@[simp]
theorem logModular_eq_N :
    logModular = N := rfl

@[simp]
theorem informationFreeEnergy_eq_zero :
    informationFreeEnergy = (0 : M2R) := by
  unfold informationFreeEnergy
  rw [modularFlux_eq_N, logModular_eq_N]
  simp

@[simp]
theorem modularFlux_vacuum :
    modularFlux * vac = 0 := by
  rw [modularFlux_eq_N]
  exact vacuum_annihilation

@[simp]
theorem Delta_vacuum :
    Delta * vac = vac := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Delta, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

def ketFunctional
    (w : Matrix (Fin 2) (Fin 1) ℝ) : M2R →ₗ[ℝ] ℝ where
  toFun A := (A * w) 0 0
  map_add' A B := by
    simp [Matrix.add_mul]
  map_smul' c A := by
    simp

def vacuumFunctional : M2R →ₗ[ℝ] ℝ :=
  ketFunctional vac

def modularFluxVacuumFunctional : M2R →ₗ[ℝ] ℝ :=
  ketFunctional (modularFlux * vac)

@[simp]
theorem modularFluxVacuumFunctional_apply
    (A : M2R) :
    modularFluxVacuumFunctional A =
      (A * (modularFlux * vac)) 0 0 := rfl

theorem modularFluxVacuumFunctional_apply_zero
    (A : M2R) :
    modularFluxVacuumFunctional A = 0 := by
  change (A * (modularFlux * vac)) 0 0 = 0
  rw [modularFlux_vacuum]
  simp

theorem modularFluxVacuumFunctional_eq_zero :
    modularFluxVacuumFunctional = 0 := by
  ext A
  exact modularFluxVacuumFunctional_apply_zero A

theorem ketFunctional_Delta_vac_eq_vacuumFunctional :
    ketFunctional (Delta * vac) = vacuumFunctional := by
  rw [Delta_vacuum]
  rfl

theorem vacuumFunctional_Delta_apply
    (A : M2R) :
    ketFunctional (Delta * vac) A = vacuumFunctional A := by
  rw [ketFunctional_Delta_vac_eq_vacuumFunctional]

def nilpotentFlow (t : ℝ) : M2R :=
  (1 : M2R) + t • N

@[simp]
theorem nilpotentFlow_zero :
    nilpotentFlow 0 = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotentFlow, N]

@[simp]
theorem nilpotentFlow_one :
    nilpotentFlow 1 = Delta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotentFlow, Delta, N]

theorem nilpotentFlow_mul
    (s t : ℝ) :
    nilpotentFlow s * nilpotentFlow t = nilpotentFlow (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

@[simp]
theorem nilpotentFlow_mul_neg
    (t : ℝ) :
    nilpotentFlow t * nilpotentFlow (-t) = (1 : M2R) := by
  rw [nilpotentFlow_mul]
  simp

@[simp]
theorem nilpotentFlow_neg_mul
    (t : ℝ) :
    nilpotentFlow (-t) * nilpotentFlow t = (1 : M2R) := by
  rw [nilpotentFlow_mul]
  simp

theorem nilpotentFlow_flux_vacuum
    (t : ℝ) :
    (nilpotentFlow t - (1 : M2R)) * vac = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilpotentFlow, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

theorem nilpotentFlow_flux_functional_zero
    (t : ℝ) (A : M2R) :
    ketFunctional ((nilpotentFlow t - (1 : M2R)) * vac) A = 0 := by
  change (A * ((nilpotentFlow t - (1 : M2R)) * vac)) 0 0 = 0
  rw [nilpotentFlow_flux_vacuum]
  simp

def modularAutomorphism
    (t : ℝ) (A : M2R) : M2R :=
  nilpotentFlow t * A * nilpotentFlow (-t)

theorem modularAutomorphism_exact_expansion
    (t : ℝ) (A : M2R) :
    modularAutomorphism t A =
      A + t • (N * A - A * N) - (t * t) • (N * A * N) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    simp [mul_comm, add_comm]

@[simp]
theorem modularAutomorphism_zero
    (A : M2R) :
    modularAutomorphism 0 A = A := by
  unfold modularAutomorphism
  simp

theorem modularAutomorphism_comp
    (s t : ℝ) (A : M2R) :
    modularAutomorphism s (modularAutomorphism t A) =
      modularAutomorphism (s + t) A := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [modularAutomorphism, nilpotentFlow, N, Matrix.mul_apply, Fin.sum_univ_two]
    ring

@[simp]
theorem modularAutomorphism_neg_comp
    (t : ℝ) (A : M2R) :
    modularAutomorphism (-t) (modularAutomorphism t A) = A := by
  rw [modularAutomorphism_comp]
  simp

@[simp]
theorem modularAutomorphism_comp_neg
    (t : ℝ) (A : M2R) :
    modularAutomorphism t (modularAutomorphism (-t) A) = A := by
  rw [modularAutomorphism_comp]
  simp

theorem nilpotentFlow_vacuum
    (t : ℝ) :
    nilpotentFlow t * vac = vac := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilpotentFlow, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

/-- Closed finite theorem: local information free energy is zero. -/
theorem local_information_free_energy_zero :
    informationFreeEnergy = 0 :=
  informationFreeEnergy_eq_zero

/-- Closed finite theorem: flux functional is zero at the exact vacuum. -/
theorem vacuum_flux_functional_zero :
    modularFluxVacuumFunctional = 0 :=
  modularFluxVacuumFunctional_eq_zero

/-- Global mode Heisenberg/Sugawara central charge term vanishes. -/
theorem sugawaraCentralTerm_zero_of_global_mode_from_bridge
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    {m n : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    (if m + n = 0 then
      (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
    else
      0) = 0 :=
  H.sugawaraCentralTerm_zero_of_global_mode hm

/-- Global mode Heisenberg/Sugawara stress mode Virasoro bracket closures. -/
theorem sugawaraStressMode_virasoroBracket_global_mode_from_bridge
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (H : CurrentHeisenbergRep 𝕜 V)
    {m n : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    ((H.sugawaraStressMode m).commutator
      (H.sugawaraStressMode n)) =
    (m - n) • H.sugawaraStressMode (m + n) :=
  H.sugawaraStressMode_virasoroBracket_global_mode hm

/-- Global mode super-Virasoro central polynomial vanishes. -/
theorem superVirasoroCentralPolynomial_zero_of_global_mode
    {m : ℤ}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    InfoGeometry.OperatorAlgebra.SuperVirasoroExtension.virasoroCentralPolynomial m = 0 :=
  InfoGeometry.OperatorAlgebra.SuperVirasoroExtension.anomalyCoefficient_zero_on_global_modes m hm

end InfoGeometry.Canonical.ModularNilpotentFinite

namespace InfoGeometry.OperatorAlgebra.SuperVirasoroExtension

/-- Closed global-mode anomaly vanishing theorem under the SuperVirasoroExtension namespace. -/
theorem virasoroCentralPolynomial_zero_on_global_modes_readout
    {m : ℤ}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    virasoroCentralPolynomial m = 0 :=
  anomalyCoefficient_zero_on_global_modes m hm

end InfoGeometry.OperatorAlgebra.SuperVirasoroExtension

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
* `modularFlux_eq_N`
* `modularFlux_vacuum`
* `modularFluxVacuumFunctional_eq_zero`
* `nilpotentFlow_mul`
* `modularAutomorphism_exact_expansion`
* `informationFreeEnergy_eq_zero`
* `sugawaraCentralTerm_zero_of_global_mode_from_bridge`
* `superVirasoroCentralPolynomial_zero_of_global_mode`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Theorems that compile conditionally based on explicitly named, valid premises or external verified witnesses. No hidden assumptions.]
* `sugawaraCentralTerm_zero_of_global_mode_from_bridge` depends on an explicit `CurrentSugawaraBridge.CurrentHeisenbergRep`.
* `sugawaraStressMode_virasoroBracket_global_mode_from_bridge` depends on an explicit `CurrentSugawaraBridge.CurrentHeisenbergRep`.

#### BUCKET 3: OPEN CLOSURE DEBT
[Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]
* No theorem here identifies `N ⊗ N` with the Virasoro central cocycle.
* No theorem here proves Type III modular theory, KMS analyticity, hyperfinite convergence, or a predual-topology theorem.
* No theorem here proves an inductive-limit bridge from finite nilpotent cross-flux to the already-formalized Virasoro central extension.
-/
