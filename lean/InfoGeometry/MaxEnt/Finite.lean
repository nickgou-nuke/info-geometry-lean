import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

open scoped BigOperators

/-!
# Finite Jaynes MaxEnt

Finite-state Jaynes-style maximum-entropy primitives:
- partition function
- Gibbs form
- normalization and positivity lemmas
- a packaged feasible point under a target expectation constraint
-/

namespace InfoGeometry.MaxEnt

section Finite

variable {n : ℕ}

/-- Shannon entropy with scale factor `K`. -/
noncomputable def entropy (p : Fin n → ℝ) (K : ℝ) : ℝ :=
  -K * ∑ i, p i * Real.log (p i)

/-- Finite MaxEnt feasibility package with one moment constraint. -/
structure MaxEntProblem
    (f : Fin n → ℝ) (expectationVal : ℝ) where
  p : Fin n → ℝ
  norm : ∑ i, p i = 1
  expectation : ∑ i, p i * f i = expectationVal
  nonneg : ∀ i, 0 ≤ p i

/-- Jaynes partition function `Z(lam) = ∑ᵢ exp(-lam fᵢ)`. -/
noncomputable def partition (f : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, Real.exp (-lam * f i)

/-- Log-partition `log Z(lam)`. -/
noncomputable def logPartition (f : Fin n → ℝ) (lam : ℝ) : ℝ :=
  Real.log (partition f lam)

/-- Jaynes Gibbs form `pᵢ(lam) = exp(-lam fᵢ) / Z(lam)`. -/
noncomputable def gibbs (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) : ℝ :=
  Real.exp (-lam * f i) / partition f lam

/-- Gibbs expectation of the observable `f`. -/
noncomputable def gibbsExpectation (f : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, gibbs f lam i * f i

lemma partition_pos
    (f : Fin n → ℝ) (lam : ℝ) [Nonempty (Fin n)] :
    0 < partition f lam := by
  classical
  unfold partition
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => Real.exp (-lam * f i))
      (by
        intro i hi
        exact Real.exp_pos _)
      Finset.univ_nonempty)

lemma partition_ne_zero
    (f : Fin n → ℝ) (lam : ℝ) [Nonempty (Fin n)] :
    partition f lam ≠ 0 :=
  (partition_pos f lam).ne'

lemma gibbs_pos
    (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) [Nonempty (Fin n)] :
    0 < gibbs f lam i := by
  unfold gibbs
  exact div_pos (Real.exp_pos _) (partition_pos f lam)

lemma gibbs_nonneg
    (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) [Nonempty (Fin n)] :
    0 ≤ gibbs f lam i :=
  (gibbs_pos f lam i).le

lemma gibbs_sum_one
    (f : Fin n → ℝ) (lam : ℝ) [Nonempty (Fin n)] :
    ∑ i, gibbs f lam i = 1 := by
  unfold gibbs partition
  have hZne : (∑ j : Fin n, Real.exp (-lam * f j)) ≠ 0 := by
    exact (partition_pos f lam).ne'
  calc
    ∑ i : Fin n, Real.exp (-lam * f i) / ∑ j : Fin n, Real.exp (-lam * f j)
        = (∑ i : Fin n, Real.exp (-lam * f i)) / ∑ j : Fin n, Real.exp (-lam * f j) := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset (Fin n)))
                (f := fun i : Fin n => Real.exp (-lam * f i))
                (a := ∑ j : Fin n, Real.exp (-lam * f j)))
    _ = 1 := by
          exact div_self hZne

/-- Gibbs form rewritten as a single exponential with `logPartition`. -/
lemma gibbs_eq_exp_sub_logPartition
    (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) [Nonempty (Fin n)] :
    gibbs f lam i = Real.exp (-lam * f i - logPartition f lam) := by
  unfold gibbs logPartition
  have hZpos : 0 < partition f lam := partition_pos f lam
  calc
    Real.exp (-lam * f i) / partition f lam
        = Real.exp (-lam * f i) / Real.exp (Real.log (partition f lam)) := by
            rw [Real.exp_log hZpos]
    _ = Real.exp (-lam * f i - Real.log (partition f lam)) := by
          rw [Real.exp_sub]

/-- The Gibbs point is feasible for MaxEnt once the target expectation is matched. -/
noncomputable def gibbsMaxEntProblemOfExpectation
    (f : Fin n → ℝ) (lam expectationVal : ℝ)
    [Nonempty (Fin n)]
    (hE : gibbsExpectation f lam = expectationVal) :
    MaxEntProblem (n := n) f expectationVal where
  p := gibbs f lam
  norm := gibbs_sum_one f lam
  expectation := by
    simpa [gibbsExpectation] using hE
  nonneg := by
    intro i
    exact gibbs_nonneg f lam i

end Finite

end InfoGeometry.MaxEnt
