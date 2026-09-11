/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Arithmetic.BostConnesCriticality
import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Physics.AmplituhedronZetaSum
import InfoGeometry.Physics.AmplituhedronVolume

/-!
# Bost-Connes Amplituhedron Criticality Bridge

This module formalizes the mathematical connection between the Bost-Connes
C*-algebraic dynamical system and the positive Grassmannian / Amplituhedron
partition function across the thermal phase boundary:

1. **High-Temperature Region ($\beta > 1$)**:
   The Bost-Connes diagonal eigenvalue model `bc_eigenvalues β` is summable
   (`bc_eigenvalues_summable_of_one_lt`), and the Amplituhedron volume
   partition sum evaluates exactly to the Riemann zeta function
   $\mathcal{Z}_{\mathrm{amp}}(\beta) = \zeta(\beta)$
   (`amplituhedron_bost_connes_partition_eq`).

2. **Strict Positivity**:
   The diagonal KMS state readouts are strictly positive for all $n \in \mathbb{N}$
   and all inverse temperatures $\beta$ (`amplituhedron_kms_readout_pos`).

3. **Critical Hagedorn Horizon ($\beta = 1$)**:
   At the critical inverse temperature $\beta = 1$, the diagonal readout
   degenerates to the harmonic term $1 / (n + 1)$ (`amplituhedron_kms_readout_at_one`).

4. **Phase Transition Non-Summability Divergence**:
   The Amplituhedron KMS state sequence at $\beta = 1$ is not summable
   (`amplituhedron_kms_not_summable_at_one`), matching the non-trace-class
   divergence of the Bost-Connes system (`bc_critical_divergence`), which
   signals the geometric boundary of the Amplituhedron.

5. **Master Criticality Synthesis**:
   Unifies all five properties into a single kernel-checked conjunction
   (`bost_connes_amplituhedron_criticality_synthesis`).
-/

noncomputable section

open Real
open InfoGeometry.Arithmetic.BostConnesCriticality
open InfoGeometry.Canonical.BostConnesKMS
open InfoGeometry.Physics.AmplituhedronZetaSum
open InfoGeometry.Physics.AmplituhedronVolume

namespace InfoGeometry.Physics.BostConnesAmplituhedronCriticality

/-- At any inverse temperature β > 1, the power sequence n^(-β) is summable. -/
lemma summable_nat_rpow_neg (β : ℝ) (hβ : 1 < β) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-β)) := by
  have h := Real.summable_nat_rpow_inv.2 hβ
  refine h.congr (fun n => ?_)
  by_cases hn : n = 0
  · subst hn
    have h0 : (0 : ℝ) ^ (-β) = 0 := by
      have : -β ≠ 0 := by linarith
      exact Real.zero_rpow this
    have h0' : ((0 : ℝ) ^ β)⁻¹ = 0 := by
      have : (0 : ℝ) ^ β = 0 := Real.zero_rpow (by linarith)
      rw [this, inv_zero]
    rw [Nat.cast_zero, h0, h0']
  · rw [Real.rpow_neg (Nat.cast_nonneg n)]

/-- At any inverse temperature β > 1, the Bost-Connes eigenvalue model is summable. -/
theorem bc_eigenvalues_summable_of_one_lt (β : ℝ) (hβ : 1 < β) :
    Summable (bc_eigenvalues β) := by
  have h_nat := summable_nat_rpow_neg β hβ
  apply Summable.of_nonneg_of_le
  · intro n
    dsimp [bc_eigenvalues]
    split_ifs
    · exact le_refl 0
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) (-β)
  · intro n
    dsimp [bc_eigenvalues]
    split_ifs with hn
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) (-β)
    · exact le_refl _
  · exact h_nat

/-- At the critical boundary β = 1, the Bost-Connes partition model fails to be trace-class. -/
theorem bc_critical_divergence :
    ¬ Summable (bc_eigenvalues 1) :=
  operator_not_trace_class_at_critical

/-- The Amplituhedron volume partition sum equals the Bost-Connes partition function for β > 1. -/
theorem amplituhedron_bost_connes_partition_eq (β : ℝ) (hβ : 1 < β) :
    (∑' (n : ℕ),
      ((kmsProjectionReadout β 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩) : ℂ)) =
        riemannZeta (β : ℂ) :=
  amplituhedron_partition_sum_eq_zeta β hβ

/-- The diagonal KMS readout at any inverse temperature β is given by (n+1)^(-β). -/
theorem amplituhedron_kms_readout_eq (β : ℝ) (n : ℕ) :
    kmsProjectionReadout β 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩ =
      ((n + 1 : ℕ) : ℝ) ^ (-β) := by
  have h := kmsProjectionReadout_self β 1 ⟨n + 1, Nat.succ_pos n⟩
  rw [h]
  simp

/-- The diagonal KMS readout at the critical temperature β = 1 equals the harmonic term 1/(n+1). -/
theorem amplituhedron_kms_readout_at_one (n : ℕ) :
    kmsProjectionReadout 1 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩ =
      1 / ((n + 1 : ℕ) : ℝ) := by
  rw [amplituhedron_kms_readout_eq 1 n]
  simp [Real.rpow_neg_one, one_div]

/-- The diagonal KMS readout is strictly positive for all n and any β. -/
theorem amplituhedron_kms_readout_pos (β : ℝ) (n : ℕ) :
    0 < kmsProjectionReadout β 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩ := by
  rw [amplituhedron_kms_readout_eq β n]
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  exact Real.rpow_pos_of_pos hpos (-β)

/-- The Amplituhedron KMS state sequence at β = 1 is not summable. -/
theorem amplituhedron_kms_not_summable_at_one :
    ¬ Summable (fun (n : ℕ) => kmsProjectionReadout 1 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩) := by
  intro h
  have h_eq : (fun (n : ℕ) => kmsProjectionReadout 1 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩) =
              (fun (n : ℕ) => 1 / ((n + 1 : ℕ) : ℝ)) := by
    ext n
    exact amplituhedron_kms_readout_at_one n
  rw [h_eq] at h
  have h_f_succ : (fun n : ℕ => if (n + 1) = 0 then (0 : ℝ) else (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) =
                  (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    ext n
    rw [if_neg (Nat.succ_ne_zero n)]
  have h_succ_summable : Summable (fun n : ℕ => if (n + 1) = 0 then (0 : ℝ) else (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    rw [h_f_succ]
    exact h
  have h_full : Summable (fun (n : ℕ) => if n = 0 then (0 : ℝ) else (1 : ℝ) / (n : ℝ)) :=
    (summable_nat_add_iff 1).mp h_succ_summable
  exact harmonic_series_diverges h_full

/-- Master synthesis theorem unifying high-temperature Amplituhedron KMS convergence,
    exact Riemann zeta partition identity, harmonic boundary identification, and
    critical Hagedorn non-summability divergence. -/
theorem bost_connes_amplituhedron_criticality_synthesis :
    (∀ (β : ℝ), 1 < β → Summable (bc_eigenvalues β)) ∧
    (∀ (β : ℝ), 1 < β →
      (∑' (n : ℕ),
        ((kmsProjectionReadout β 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩) : ℂ)) =
          riemannZeta (β : ℂ)) ∧
    (∀ (n : ℕ),
      kmsProjectionReadout 1 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩ =
        1 / ((n + 1 : ℕ) : ℝ)) ∧
    (∀ (β : ℝ) (n : ℕ),
      0 < kmsProjectionReadout β 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩) ∧
    (¬ Summable (bc_eigenvalues 1)) ∧
    (¬ Summable (fun (n : ℕ) => kmsProjectionReadout 1 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩)) :=
  ⟨bc_eigenvalues_summable_of_one_lt,
   amplituhedron_bost_connes_partition_eq,
   amplituhedron_kms_readout_at_one,
   amplituhedron_kms_readout_pos,
   bc_critical_divergence,
   amplituhedron_kms_not_summable_at_one⟩

end InfoGeometry.Physics.BostConnesAmplituhedronCriticality
