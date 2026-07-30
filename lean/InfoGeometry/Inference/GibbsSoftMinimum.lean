/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsInference
import InfoGeometry.GrandCanonical.Core
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order

/-!
# Finite Gibbs soft minimum

The finite free energy is a soft minimum of the observation energies. This
module records its elementary finite bounds; no thermodynamic-limit claim is
made.
-/

open scoped BigOperators
open Filter
open scoped Topology

namespace InfoGeometry.Inference.FiniteGibbs

variable {Data : Type*} [Fintype Data] [Nonempty Data]

noncomputable def softMinimum (E : Data → ℝ) (ε : ℝ) : ℝ :=
  -ε * Real.log (∑ i : Data, Real.exp (-E i / ε))

theorem softMinimum_le_energy
    (E : Data → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Data) :
    softMinimum E ε ≤ E i := by
  unfold softMinimum
  have hsum_pos : 0 < ∑ j : Data, Real.exp (-E j / ε) := by
    exact Finset.sum_pos (fun j hj => Real.exp_pos _) Finset.univ_nonempty
  have hterm_le : Real.exp (-E i / ε) ≤
      ∑ j : Data, Real.exp (-E j / ε) := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset Data))
      (f := fun j => Real.exp (-E j / ε))
      (fun j hj => (Real.exp_pos _).le) (Finset.mem_univ i)
  have hlog : Real.log (Real.exp (-E i / ε)) ≤
      Real.log (∑ j : Data, Real.exp (-E j / ε)) :=
    Real.strictMonoOn_log.monotoneOn
      (Real.exp_pos _) hsum_pos hterm_le
  rw [Real.log_exp] at hlog
  have hmul := mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hε.le)
  calc
    softMinimum E ε = -ε * Real.log (∑ j : Data, Real.exp (-E j / ε)) := rfl
    _ ≤ -ε * (-E i / ε) := hmul
    _ = E i := by
      field_simp [ne_of_gt hε]

/-- A minimizing energy bounds the finite soft minimum from below up to the
finite-volume entropy correction `ε * log(card Data)`. -/
theorem energy_sub_temperature_mul_log_card_le_softMinimum_of_min
    (E : Data → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Data)
    (hmin : ∀ j : Data, E i ≤ E j) :
    E i - ε * Real.log (Fintype.card Data) ≤ softMinimum E ε := by
  unfold softMinimum
  have hsum_pos : 0 < ∑ j : Data, Real.exp (-E j / ε) := by
    exact Finset.sum_pos (fun j hj => Real.exp_pos _) Finset.univ_nonempty
  have hpointwise : ∀ j : Data,
      Real.exp (-E j / ε) ≤ Real.exp (-E i / ε) := by
    intro j
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff_of_pos_right hε).2
    linarith [hmin j]
  have hsum_le :
      (∑ j : Data, Real.exp (-E j / ε)) ≤
        (Fintype.card Data : ℝ) * Real.exp (-E i / ε) := by
    calc
      ∑ j : Data, Real.exp (-E j / ε) ≤
          ∑ _j : Data, Real.exp (-E i / ε) := by
            exact Finset.sum_le_sum (fun j hj => hpointwise j)
      _ = (Fintype.card Data : ℝ) * Real.exp (-E i / ε) := by
        simp [nsmul_eq_mul]
  have hcard_pos : 0 < (Fintype.card Data : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hlog :
      Real.log (∑ j : Data, Real.exp (-E j / ε)) ≤
        Real.log ((Fintype.card Data : ℝ) * Real.exp (-E i / ε)) := by
    exact Real.strictMonoOn_log.monotoneOn hsum_pos
      (mul_pos hcard_pos (Real.exp_pos _)) hsum_le
  rw [Real.log_mul (ne_of_gt hcard_pos) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hmul := mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hε.le)
  calc
    E i - ε * Real.log (Fintype.card Data) =
        -ε * (Real.log (Fintype.card Data) + -E i / ε) := by
          field_simp [ne_of_gt hε]
          ring
    _ ≤ -ε * Real.log (∑ j : Data, Real.exp (-E j / ε)) := hmul

/-- The finite Gibbs soft minimum converges to the hard minimum along positive
temperatures. -/
theorem tendsto_softMinimum_nhdsWithin_zero_of_min
    (E : Data → ℝ) (i : Data)
    (hmin : ∀ j : Data, E i ≤ E j) :
    Tendsto (fun ε : ℝ => softMinimum E ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (E i)) := by
  have hid : Tendsto (fun ε : ℝ => ε)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [id_eq] using
      (tendsto_nhdsWithin_of_tendsto_nhds
        (Filter.tendsto_id (x := 𝓝 (0 : ℝ))))
  have hcard : Tendsto
      (fun ε : ℝ => ε * Real.log (Fintype.card Data))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.mul tendsto_const_nhds
  have hlower : Tendsto
      (fun ε : ℝ => E i - ε * Real.log (Fintype.card Data))
      (𝓝[>] (0 : ℝ)) (𝓝 (E i)) := by
    simpa using tendsto_const_nhds.sub hcard
  have hupper : Tendsto (fun _ε : ℝ => E i)
      (𝓝[>] (0 : ℝ)) (𝓝 (E i)) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (energy_sub_temperature_mul_log_card_le_softMinimum_of_min
      E hε i hmin)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (softMinimum_le_energy E hε i)

/-- The generic soft minimum is definitionally the finite Gibbs free energy
of the corresponding observation-energy model. -/
theorem softMinimum_eq_freeEnergy
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) :
    softMinimum (fun i : Data => M.energy i θ) ε = freeEnergy M θ ε := rfl

/-- The finite Gibbs free energy converges to a minimizing observation energy
along positive temperatures. -/
theorem tendsto_freeEnergy_nhdsWithin_zero_of_min
    {Theta : Type*} (M : Model (Data := Data) (Theta := Theta)) (θ : Theta)
    (i : Data) (hmin : ∀ j : Data, M.energy i θ ≤ M.energy j θ) :
    Tendsto (fun ε : ℝ => freeEnergy M θ ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (M.energy i θ)) := by
  simpa [freeEnergy, softMinimum] using
    (tendsto_softMinimum_nhdsWithin_zero_of_min
      (fun j : Data => M.energy j θ) i hmin)

/-- The finite Massieu potential is the logarithm of the partition function. -/
noncomputable def massieuPotential
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) : ℝ :=
  Real.log (partitionFunction M θ ε)

theorem freeEnergy_eq_neg_temperature_mul_massieu
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) :
    freeEnergy M θ ε = -ε * massieuPotential M θ ε := rfl

/-- The finite Massieu potential is the grand-canonical log-partition
potential after the inverse-temperature change of variables `β = 1 / ε`. -/
theorem massieuPotential_eq_grandCanonical_potential_of_nonzero
    {Theta : Type*} (M : Model (Data := Data) (Theta := Theta)) (θ : Theta)
    {ε : ℝ} (hε : ε ≠ 0) :
    massieuPotential M θ ε =
      InfoGeometry.GrandCanonical.potential
        { energy := fun i : Data => M.energy i θ } (1 / ε) := by
  unfold massieuPotential InfoGeometry.GrandCanonical.potential
    InfoGeometry.GrandCanonical.partition partitionFunction
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  field_simp [hε]

/-- The scaled Massieu potential converges to the negative hard minimum at
positive-temperature zero. -/
theorem tendsto_temperature_mul_massieu_nhdsWithin_zero_of_min
    {Theta : Type*} (M : Model (Data := Data) (Theta := Theta)) (θ : Theta)
    (i : Data) (hmin : ∀ j : Data, M.energy i θ ≤ M.energy j θ) :
    Tendsto (fun ε : ℝ => ε * massieuPotential M θ ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (-M.energy i θ)) := by
  have hfree := tendsto_freeEnergy_nhdsWithin_zero_of_min M θ i hmin
  have hneg : Tendsto (fun ε : ℝ => -freeEnergy M θ ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (-M.energy i θ)) := hfree.neg
  apply hneg.congr'
  filter_upwards [] with ε
  dsimp [freeEnergy, massieuPotential]
  ring

end InfoGeometry.Inference.FiniteGibbs
