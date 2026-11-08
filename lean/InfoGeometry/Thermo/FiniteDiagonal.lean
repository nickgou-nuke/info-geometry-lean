import Mathlib.Algebra.BigOperators.Field
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Tactic

open scoped BigOperators

/-!
# Finite Diagonal Gibbs Thermal Model

A finite-dimensional thermal model on matrix observables `Matrix (Fin n) (Fin n) ℝ`:

- Hamiltonian is diagonal (energy levels `H : Fin n → ℝ`)
- Gibbs density is diagonal and positive
- Modular shift is explicit on matrix coefficients
- Gibbs state is a weighted diagonal expectation
- KMS-like kernel identity appears as a detailed-balance relation on entries
-/

namespace InfoGeometry.Thermo.FiniteDiagonal

section FiniteDiagonal

variable {n : ℕ} [Nonempty (Fin n)]

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Finite partition function for energy levels `H`. -/
noncomputable def partition (H : Fin n → ℝ) (β : ℝ) : ℝ :=
  ∑ i, Real.exp (-β * H i)

/-- Log-density on the diagonal (the scalar `log ρᵢ`). -/
noncomputable def logDensityEntry (H : Fin n → ℝ) (β : ℝ) (i : Fin n) : ℝ :=
  -β * H i - Real.log (partition H β)

/-- Gibbs weights `ρᵢ = exp(-β Hᵢ)/Z`. -/
noncomputable def gibbsWeight (H : Fin n → ℝ) (β : ℝ) (i : Fin n) : ℝ :=
  Real.exp (-β * H i) / partition H β

/-- Diagonal Hamiltonian operator. -/
def hamiltonianOp (H : Fin n → ℝ) : Mat n :=
  Matrix.diagonal H

/-- Diagonal log-density operator `log ρ`. -/
noncomputable def logDensityOp (H : Fin n → ℝ) (β : ℝ) : Mat n :=
  Matrix.diagonal (logDensityEntry H β)

/-- Diagonal Gibbs density operator `ρ`. -/
noncomputable def gibbsDensity (H : Fin n → ℝ) (β : ℝ) : Mat n :=
  Matrix.diagonal (gibbsWeight H β)

/-- Entrywise modular shift induced by a diagonal Hamiltonian. -/
noncomputable def modularShift (H : Fin n → ℝ) (t : ℝ) (A : Mat n) : Mat n :=
  fun i j => Real.exp (t * (H i - H j)) * A i j

/-- Gibbs state on finite matrix observables: `ω_β(A) = ∑ᵢ ρᵢ Aᵢᵢ`. -/
noncomputable def gibbsState (H : Fin n → ℝ) (β : ℝ) (A : Mat n) : ℝ :=
  ∑ i, gibbsWeight H β i * A i i

lemma partition_pos (H : Fin n → ℝ) (β : ℝ) :
    0 < partition H β := by
  classical
  unfold partition
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => Real.exp (-β * H i))
      (by
        intro i hi
        exact Real.exp_pos _)
      Finset.univ_nonempty)

lemma partition_ne_zero (H : Fin n → ℝ) (β : ℝ) :
    partition H β ≠ 0 :=
  (partition_pos H β).ne'

lemma gibbsWeight_pos (H : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    0 < gibbsWeight H β i := by
  unfold gibbsWeight
  exact div_pos (Real.exp_pos _) (partition_pos H β)

lemma gibbsWeight_nonneg (H : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    0 ≤ gibbsWeight H β i :=
  (gibbsWeight_pos H β i).le

lemma gibbsWeight_sum_one (H : Fin n → ℝ) (β : ℝ) :
    ∑ i, gibbsWeight H β i = 1 := by
  unfold gibbsWeight partition
  have hZne : (∑ j : Fin n, Real.exp (-β * H j)) ≠ 0 := by
    exact (partition_pos H β).ne'
  calc
    ∑ i : Fin n, Real.exp (-β * H i) / ∑ j : Fin n, Real.exp (-β * H j)
        = (∑ i : Fin n, Real.exp (-β * H i)) / ∑ j : Fin n, Real.exp (-β * H j) := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset (Fin n)))
                (f := fun i : Fin n => Real.exp (-β * H i))
                (a := ∑ j : Fin n, Real.exp (-β * H j)))
    _ = 1 := by
          exact div_self hZne

lemma gibbsWeight_le_one (H : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    gibbsWeight H β i ≤ 1 := by
  have hnonneg : ∀ j : Fin n, 0 ≤ gibbsWeight H β j := fun j => gibbsWeight_nonneg H β j
  have hsum : ∑ j : Fin n, gibbsWeight H β j = 1 := gibbsWeight_sum_one H β
  have hi_le_sum : gibbsWeight H β i ≤ ∑ j : Fin n, gibbsWeight H β j := by
    exact Finset.single_le_sum (fun j _hj => hnonneg j) (Finset.mem_univ i)
  simpa [hsum] using hi_le_sum

lemma gibbsWeight_eq_exp_logDensity (H : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    gibbsWeight H β i = Real.exp (logDensityEntry H β i) := by
  unfold gibbsWeight logDensityEntry
  have hZpos : 0 < partition H β := partition_pos H β
  calc
    Real.exp (-β * H i) / partition H β
        = Real.exp (-β * H i) / Real.exp (Real.log (partition H β)) := by
            rw [Real.exp_log hZpos]
    _ = Real.exp (-β * H i - Real.log (partition H β)) := by
          exact (Real.exp_sub (-β * H i) (Real.log (partition H β))).symm

omit [Nonempty (Fin n)] in
@[simp] lemma modularShift_apply (H : Fin n → ℝ) (t : ℝ) (A : Mat n) (i j : Fin n) :
    modularShift H t A i j = Real.exp (t * (H i - H j)) * A i j := rfl

omit [Nonempty (Fin n)] in
lemma modularShift_zero (H : Fin n → ℝ) (A : Mat n) :
    modularShift H 0 A = A := by
  ext i j
  simp [modularShift]

omit [Nonempty (Fin n)] in
lemma modularShift_add (H : Fin n → ℝ) (s t : ℝ) (A : Mat n) :
    modularShift H (s + t) A = modularShift H s (modularShift H t A) := by
  ext i j
  have hsplit : (s + t) * (H i - H j) = s * (H i - H j) + t * (H i - H j) := by
    ring
  simp [modularShift, hsplit, Real.exp_add, mul_assoc]

omit [Nonempty (Fin n)] in
lemma modularShift_diag_fixed (H : Fin n → ℝ) (t : ℝ) (A : Mat n) (i : Fin n) :
    modularShift H t A i i = A i i := by
  simp [modularShift]

/-- The Gibbs state is normalized on the identity observable. -/
lemma gibbsState_one (H : Fin n → ℝ) (β : ℝ) :
    gibbsState H β (1 : Mat n) = 1 := by
  unfold gibbsState
  calc
    ∑ i, gibbsWeight H β i * (1 : Mat n) i i = ∑ i, gibbsWeight H β i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp
    _ = 1 := gibbsWeight_sum_one H β

/- The Gibbs state is invariant under modular shift (diagonal model). -/
omit [Nonempty (Fin n)] in
theorem gibbsState_modularShift_invariant (H : Fin n → ℝ) (β t : ℝ) (A : Mat n) :
    gibbsState H β (modularShift H t A) = gibbsState H β A := by
  unfold gibbsState
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [modularShift]

/-- Gibbs-weight transport identity (kernel detailed-balance factor). -/
lemma gibbsWeight_transport (H : Fin n → ℝ) (β : ℝ) (i j : Fin n) :
    gibbsWeight H β i * Real.exp (β * (H i - H j)) = gibbsWeight H β j := by
  rw [gibbsWeight_eq_exp_logDensity (H := H) (β := β) (i := i)]
  rw [gibbsWeight_eq_exp_logDensity (H := H) (β := β) (i := j)]
  have h :
      logDensityEntry H β i + β * (H i - H j) = logDensityEntry H β j := by
    unfold logDensityEntry
    ring
  calc
    Real.exp (logDensityEntry H β i) * Real.exp (β * (H i - H j))
        = Real.exp (logDensityEntry H β i + β * (H i - H j)) := by
            rw [← Real.exp_add]
    _ = Real.exp (logDensityEntry H β j) := by rw [h]

/-- Entrywise KMS-like detailed-balance identity at imaginary time `β`. -/
lemma gibbs_detailedBalance_entry
    (H : Fin n → ℝ) (β : ℝ) (A : Mat n) (i j : Fin n) :
    gibbsWeight H β i * (modularShift H β A i j)
      = gibbsWeight H β j * A i j := by
  calc
    gibbsWeight H β i * (modularShift H β A i j)
        = gibbsWeight H β i * (Real.exp (β * (H i - H j)) * A i j) := by
            rfl
    _ = (gibbsWeight H β i * Real.exp (β * (H i - H j))) * A i j := by
          ring
    _ = gibbsWeight H β j * A i j := by
          rw [gibbsWeight_transport]

/-- Diagonal entries of Gibbs density are strictly positive. -/
lemma gibbsDensity_diag_pos (H : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    0 < gibbsDensity H β i i := by
  simpa [gibbsDensity] using gibbsWeight_pos H β i

/-- Diagonal entries of Gibbs density are bounded by one. -/
lemma gibbsDensity_diag_le_one (H : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    gibbsDensity H β i i ≤ 1 := by
  simpa [gibbsDensity] using gibbsWeight_le_one H β i

/-- Log-density exponentiates back to Gibbs diagonal entries. -/
lemma logDensityOp_exp_entry (H : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    Real.exp (logDensityOp H β i i) = gibbsDensity H β i i := by
  simp [logDensityOp, gibbsDensity, gibbsWeight_eq_exp_logDensity]

end FiniteDiagonal

end InfoGeometry.Thermo.FiniteDiagonal
