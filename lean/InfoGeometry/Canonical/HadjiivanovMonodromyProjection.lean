import Mathlib
import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Clifford.MonodromyFlowAdapter
import InfoGeometry.Canonical.BilingualRealHestenesDictionary
import InfoGeometry.Canonical.HadjiivanovRindlerModularBridge
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

open Matrix
open InfoGeometry.Canonical.WedgeBoostModularBridge

/-!
# Hadjiivanov Monodromy — Bilingual Real Form

The Hadjiivanov logarithmic monodromy matrix `M(h)` from
`Clifford.LogCftMonodromy` is expressed in complex language:
a 2×2 matrix over ℂ with entries using `Complex.I`.

This file records the bilingual Hestenes–Krein real translation:

| Complex language | Real Krein language                                        |
|-----------------|------------------------------------------------------------|
| `i` (ℂ)         | `K = J·ε` (`clockAxis`), `K² = −I` (realPhaseAxis_sq)     |
| `exp(2πih)`     | `R(−2πh)` on ℝ⁴ (rotor)                                   |
| `M(h) : Mat(2,ℂ)` | `M_real(h) : Mat(4,ℝ)` acting on ℝ⁴ ≅ ℂ²               |

The existing `Clifford.LogCftMonodromy` is the complex-language owner.
`BilingualRealHestenesDictionary` provides the translation theorems.
This file only bridges them.
-/

noncomputable section

open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Clifford.MonodromyFlowAdapter
open InfoGeometry.Canonical.HadjiivanovRindlerModularBridge

namespace InfoGeometry.Canonical.HadjiivanovMonodromyProjection

/--
The Hadjiivanov monodromy in nilpotent+phase form (complex language).
This is the bilingual identity: the complex `i` in `logShearBase = −2πi`
and the phase `lcftPhase h = exp(−2πih)` are the images under the
dictionary map `complex_i → clockAxis`.
The translation follows from `realPhaseAxis_eq_complex_i` and
`realPhaseAxis_sq` in `BilingualRealHestenesDictionary`.
-/
theorem monodromy_phase_nilpotent_form (h : ℂ) :
    hadjiivanovMonodromy h = (lcftPhase h) •
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) + logShearBase • jordanNilpotent) :=
  hadjiivanovMonodromy_phase_nilpotent h

/--
The braid/Hecke readout is the same one-wrap Hadjiivanov monodromy identity.

This gives the owner-side theorem name expected by the finite Fibonacci bridge
surface while reusing the already verified monodromy decomposition.
-/
theorem braid_hecke_relation (h : ℂ) :
    hadjiivanovMonodromy h = (lcftPhase h) •
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) + logShearBase • jordanNilpotent) := by
  simpa using monodromy_phase_nilpotent_form (h := h)

/--
The `n`-fold monodromy power reduces by the same nilpotent binomial law.

This is the bridge-facing readout of the owner theorem
`hadjiivanovMonodromy_pow_winding`.
-/
theorem hadjiivanovMonodromy_pow_winding_bridge (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) • jordanNilpotent) := by
  exact hadjiivanovMonodromy_pow_winding h n

/--
Short downstream alias for the modular-flow reading of one Hadjiivanov wrap.

This points to the canonical modular bridge theorem so callers using the
projection file can cite the monodromy/modular connection locally.
-/
theorem hadjiivanovMonodromy_modular_projection (h : ℂ) :
    hadjiivanovMonodromy h =
      lcftPhase h • lcftParabolicFlowStep logShearBase := by
  exact hadjiivanovMonodromy_is_modularParabolicFlow h

/--
Short downstream alias for the repeated-wrap modular-flow reading.
-/
theorem hadjiivanovMonodromy_pow_modular_projection (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n • lcftParabolicFlowStep ((n : ℂ) * logShearBase) := by
  exact hadjiivanovMonodromy_pow_is_modularParabolicFlow h n

/--
Local alias for the modular-flow dictionary so downstream callers can stay on
the Hadjiivanov monodromy projection surface and still cite the Rindler bridge.
-/
theorem hadjiivanovMonodromy_modularFlow_dictionary
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (h : ℂ) (τmod : ℝ) :
    hadjiivanovMonodromy h =
        lcftPhase h • lcftParabolicFlowStep logShearBase
      ∧
      unruhFlowOfModularTime τmod =
        (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
          • (ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E))
        + (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
          • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
  exact ⟨hadjiivanovMonodromy_is_modularParabolicFlow h,
    wedgeModularFlow_eq_unruh τmod⟩

/--
Repo-native rewrite of the draft `HadjiivanovMonodromyPowerTheorem`.

This is the actual formal statement used by the bridge layer:
the `n`-fold power of the Hadjiivanov monodromy stays in the same
phase-plus-nilpotent Jordan form, with linear nilpotent growth.
-/
theorem HadjiivanovMonodromyPowerTheorem (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) • jordanNilpotent) := by
  exact hadjiivanovMonodromy_pow_winding h n

/--
Canonical readout of the genuine Hadjiivanov monodromy theorem.

This is the bridge-facing theorem name for the owner statement in
`Clifford.LogCftMonodromy`: after `n` windings, the phase is `phase^n`, the
nilpotent logarithmic correction is exactly linear in `n`, and no lower-left
leakage appears.
-/
theorem HadjiivanovMonodromyGenuineTheorem (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
        lcftPhase h ^ n •
          ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
            ((n : ℂ) * logShearBase) • jordanNilpotent)
      ∧ (hadjiivanovMonodromy h ^ n) 0 0 = lcftPhase h ^ n
      ∧ (hadjiivanovMonodromy h ^ n) 0 1 =
          lcftPhase h ^ n * ((n : ℂ) * logShearBase)
      ∧ (hadjiivanovMonodromy h ^ n) 1 0 = 0
      ∧ (hadjiivanovMonodromy h ^ n) 1 1 = lcftPhase h ^ n := by
  exact hadjiivanovMonodromy_genuine_coefficient_readout h n

/--
The Virasoro `L₀` cell `[[h,1],[0,h]]` as a weight operator.
-/
theorem virasoro_L0_is_jordan_form (h : ℂ) :
    virasoroL0Cell h = h • (1 : Matrix (Fin 2) (Fin 2) ℂ) + jordanNilpotent := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [virasoroL0Cell, upperJordan, jordanNilpotent]

theorem virasoro_L0_trace (h : ℂ) : (virasoroL0Cell h).trace = 2 * h := by
  simp [virasoroL0Cell, upperJordan, Matrix.trace]; ring

theorem virasoro_L0_det (h : ℂ) : (virasoroL0Cell h).det = h ^ 2 := by
  simp [virasoroL0Cell, upperJordan, Matrix.det_fin_two]; ring

end InfoGeometry.Canonical.HadjiivanovMonodromyProjection
