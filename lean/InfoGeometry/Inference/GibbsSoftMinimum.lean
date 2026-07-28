/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsInference

/-!
# Finite Gibbs soft minimum

The finite free energy is a soft minimum of the observation energies. This
module records its elementary finite bounds; no thermodynamic-limit claim is
made.
-/

open scoped BigOperators

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

end InfoGeometry.Inference.FiniteGibbs
