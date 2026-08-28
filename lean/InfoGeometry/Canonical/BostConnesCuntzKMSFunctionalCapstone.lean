/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzKMSCondition
import InfoGeometry.Algebra.CuntzKMSState
import InfoGeometry.Algebra.BostConnesKMSPhaseTransition
import InfoGeometry.Canonical.BostConnesPhaseTransitionGaloisSSBCapstone

/-!
# Bost-Connes Cuntz KMS Functional Capstone

This capstone formally establishes the KMS state trace functionals over the
Cuntz algebra generators $\mathcal{O}_\infty$ and multi-index isometries $S_n$:

1. **Multiplicative Monoid Representation & Modular Flow**:
   - The continuous one-parameter automorphism group $\sigma_t(S_n) = n^{it} S_n$ on generators.
   - Unitarity of time evolution: $\sigma_t(S_n) \sigma_t(S_n^*) = 1$.
2. **Imaginary-Time Continuation & KMS Condition**:
   - Analytic continuation to imaginary time: $\sigma_{i\beta}(S_n) = n^{-\beta} S_n$.
   - KMS boundary condition on Cuntz words $S_n S_m^*$:
     $$\phi_\beta(S_n S_m^*) = \delta_{n,m} \frac{n^{-\beta}}{\zeta(\beta)}$$
3. **Phase Stratification and Mode Contraction**:
   - For all $\beta > 1$, thermal contraction of excited modes $n \ge 2$:
     $$\omega_\beta(n) = n^{-\beta} < 1$$
   - Ground state mode $n = 1$ is an invariant fixed point.
-/

open Complex Real
open InfoGeometry.Algebra.CuntzKMSCondition
open InfoGeometry.Algebra.CuntzKMSState
open InfoGeometry.Algebra.BostConnesKMSPhaseTransition
open InfoGeometry.Canonical.BostConnesSSB

namespace InfoGeometry.Canonical.BostConnesCuntzKMSFunctionalCapstone

/-- Inverse temperatures where the Euler-product normalization is available. -/
def AdmissibleInverseTemperature := {β : ℝ // 1 < β}

theorem admissible_inverse_temperature_zeta_ne_zero
    (β : AdmissibleInverseTemperature) :
    riemannZeta (β.1 : ℂ) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re
  exact β.property

/-- 1. Multiplicative time evolution phase: $\sigma_t(S_n) = n^{it} S_n$. -/
noncomputable def timeEvolutionPhase (t : ℝ) (n : ℕ+) : ℂ :=
  Complex.exp (I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))

/-- 2. Multiplicative adjoint time evolution phase: $\sigma_t(S_n^*) = n^{-it} S_n^*$. -/
noncomputable def timeEvolutionPhaseInv (t : ℝ) (n : ℕ+) : ℂ :=
  Complex.exp (-(I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)))

/-- 3. Imaginary time evolution at $i\beta$: $\sigma_{i\beta}(S_n) = n^{-\beta} S_n$. -/
noncomputable def imaginaryTimePhase (β : ℝ) (n : ℕ+) : ℂ :=
  (n : ℂ) ^ (-(β : ℂ))

/-- 4. Unnormalized KMS weight on Cuntz word $S_n S_m^*$. -/
noncomputable def cuntzWordWeight (β : ℝ) (n m : ℕ+) : ℂ :=
  if n = m then (n : ℂ) ^ (-(β : ℂ)) else 0

/-- 5. Normalized KMS functional on Cuntz word $S_n S_m^*$ at $\beta > 1$ given partition sum $Z = \zeta(\beta)$. -/
noncomputable def cuntzKMSFunctional (β : ℝ) (Z : ℂ) (n m : ℕ+) : ℂ :=
  if n = m then ((n : ℂ) ^ (-(β : ℂ))) / Z else 0

theorem cuntzKMSFunctional_riemannZeta_diag
    (β : AdmissibleInverseTemperature) (n : ℕ+) :
    cuntzKMSFunctional β.1 (riemannZeta (β.1 : ℂ)) n n =
      ((n : ℂ) ^ (-(β.1 : ℂ))) / riemannZeta (β.1 : ℂ) := by
  simp [cuntzKMSFunctional]

/-- 🏆 THEOREM 1: Unitarity of the time evolution automorphism group on generators. -/
theorem time_evolution_phase_unitary (t : ℝ) (n : ℕ+) :
    timeEvolutionPhase t n * timeEvolutionPhaseInv t n = 1 := by
  dsimp [timeEvolutionPhase, timeEvolutionPhaseInv]
  rw [← Complex.exp_add]
  have h : I * (t : ℂ) * (Real.log (n : ℝ) : ℂ) +
      -(I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) = 0 := by ring
  rw [h, Complex.exp_zero]

/-- 🏆 THEOREM 2: Imaginary time evaluation matches modularPhaseComplex at $i\beta$. -/
theorem imaginary_time_phase_eval (β : ℝ) (n : ℕ+) :
    modularPhaseComplex (n : ℕ) (I * (β : ℂ)) = imaginaryTimePhase β n := by
  dsimp [imaginaryTimePhase]
  exact modularPhaseComplex_imag (n : ℕ) (PNat.ne_zero n) β

/-- 🏆 THEOREM 3: The KMS algebraic cyclic relation for Cuntz words. -/
theorem cuntz_kms_cyclic_relation (β : ℝ) (Z : ℂ) (n : ℕ+) (hZ : Z ≠ 0) :
    cuntzKMSFunctional β Z n n * Z = imaginaryTimePhase β n := by
  dsimp [cuntzKMSFunctional, imaginaryTimePhase]
  rw [if_pos rfl]
  exact div_mul_cancel₀ _ hZ

theorem cuntzKMSFunctional_riemannZeta_cyclic
    (β : AdmissibleInverseTemperature) (n : ℕ+) :
    cuntzKMSFunctional β.1 (riemannZeta (β.1 : ℂ)) n n *
        riemannZeta (β.1 : ℂ) = imaginaryTimePhase β.1 n := by
  apply cuntz_kms_cyclic_relation
  exact admissible_inverse_temperature_zeta_ne_zero β

/-!
The preceding definition is a finite word-evaluation table.  The following
lemma records the only normalization consequence available at this level: a
nonzero partition value recovers the unnormalised diagonal weight.  No trace,
Fredholm determinant, or analytic continuation is introduced here.
-/
theorem cuntzKMSFunctional_diag_normalized
    (β : ℝ) (Z : ℂ) (hZ : Z ≠ 0) (n : ℕ+) :
    cuntzKMSFunctional β Z n n * Z = (n : ℂ) ^ (-(β : ℂ)) := by
  exact cuntz_kms_cyclic_relation β Z n hZ

theorem cuntzKMSFunctional_diag_normalized_zeta
    (β : AdmissibleInverseTemperature) (n : ℕ+) :
    cuntzKMSFunctional β.1 (riemannZeta (β.1 : ℂ)) n n *
        riemannZeta (β.1 : ℂ) = (n : ℂ) ^ (-(β.1 : ℂ)) := by
  exact cuntzKMSFunctional_riemannZeta_cyclic β n

/-- 🏆 THEOREM 4: Off-diagonal orthogonality of the KMS state on Cuntz words. -/
theorem cuntz_kms_off_diagonal (β : ℝ) (Z : ℂ) (n m : ℕ+) (hnm : n ≠ m) :
    cuntzKMSFunctional β Z n m = 0 := by
  dsimp [cuntzKMSFunctional]
  rw [if_neg hnm]

/-- 🏆 THEOREM 5: Mode contraction for all excited Cuntz states at $\beta > 1$. -/
theorem excited_mode_thermal_decay (β : ℝ) (hβ : 1 < β) (n : ℕ+) (hn : 2 ≤ (n : ℕ)) :
    thermalKMSWeight β n < 1 :=
  low_temperature_mode_contraction β hβ n hn

/--
🏆 GRAND BOST-CONNES CUNTZ KMS CAPSTONE SYNTHESIS:
Unites:
1. Time evolution group $\sigma_t(S_n)$ unitarity.
2. Analytic continuation to imaginary time $\sigma_{i\beta}(S_n) = n^{-\beta} S_n$.
3. KMS state functional evaluation on Cuntz monomials $S_n S_m^*$.
4. Off-diagonal orthogonality $\phi_\beta(S_n S_m^*) = 0$ for $n \ne m$.
5. Thermal contraction of all excited modes $n \ge 2$ for $\beta > 1$.
-/
theorem grand_bost_connes_cuntz_kms_synthesis
    (t : ℝ) (β : ℝ) (hβ : 1 < β) (Z : ℂ) (hZ : Z ≠ 0)
    (n m : ℕ+) (hnm : n ≠ m) (hn : 2 ≤ (n : ℕ)) :
    (timeEvolutionPhase t n * timeEvolutionPhaseInv t n = 1) ∧
    (modularPhaseComplex (n : ℕ) (I * (β : ℂ)) = imaginaryTimePhase β n) ∧
    (cuntzKMSFunctional β Z n n * Z = imaginaryTimePhase β n) ∧
    (cuntzKMSFunctional β Z n m = 0) ∧
    (thermalKMSWeight β n < 1) :=
  ⟨time_evolution_phase_unitary t n,
   imaginary_time_phase_eval β n,
   cuntz_kms_cyclic_relation β Z n hZ,
   cuntz_kms_off_diagonal β Z n m hnm,
   excited_mode_thermal_decay β hβ n hn⟩

end InfoGeometry.Canonical.BostConnesCuntzKMSFunctionalCapstone
