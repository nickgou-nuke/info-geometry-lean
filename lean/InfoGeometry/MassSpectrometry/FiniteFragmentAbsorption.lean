import InfoGeometry.Algebra.RankedMatrixPowers
import InfoGeometry.MassSpectrometry.TerminatingFragmentation

/-!
# Exact finite absorption of ranked fragmentation grammars

Uses the existing substochastic weights and their Option-indexed completion.
The transient block is nilpotent; the completed Markov matrix stabilizes at an
absorbing projection rather than becoming zero. Rank bounds include the final
transition into `none` and are not asserted minimal.
-/

noncomputable section
namespace InfoGeometry.MassSpectrometry
open scoped BigOperators
open InfoGeometry.Algebra.RankedMatrixPowers

/-- The projection that sends every row distribution to the absorbing state. -/
def absorptionProjection (n : ℕ) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℝ :=
  fun _ j => if j = none then 1 else 0

namespace StochasticGrammar
variable {n : ℕ} {D : FragmentationDAG n}

/-- An explicit matrix view prevents confusion with pointwise function powers. -/
abbrev transientMatrix (G : StochasticGrammar D) : Matrix (Fin n) (Fin n) ℝ := G.weight

theorem transient_pow_eq_zero_of_rank_bound (G : StochasticGrammar D)
    (N : ℕ) (hN : ∀ u, D.rank u < N) : G.transientMatrix ^ N = 0 :=
  pow_eq_zero_of_rank_bound G.transientMatrix D.rank
    (fun _ _ h => G.rank_decreases_of_weight_ne_zero h) N hN

theorem transient_pow_rankHorizon_eq_zero (G : StochasticGrammar D) :
    G.transientMatrix ^ rankHorizon D.rank = 0 :=
  G.transient_pow_eq_zero_of_rank_bound _ (rank_lt_rankHorizon D.rank)

theorem transient_row_zero_after_rank (G : StochasticGrammar D)
    (u v : Fin n) : (G.transientMatrix ^ (D.rank u + 1)) u v = 0 := by
  apply pow_entry_eq_zero_of_rank_lt G.transientMatrix D.rank
    (fun _ _ h => G.rank_decreases_of_weight_ne_zero h)
  omega

/-- The absorbing row is already stationary, including at the zeroth power. -/
theorem absorbingCompletion_pow_none (G : StochasticGrammar D) (m : ℕ)
    (j : Option (Fin n)) :
    (G.absorbingCompletion ^ m) none j = if j = none then 1 else 0 := by
  induction m with
  | zero => cases j <;> simp [Matrix.one_apply]
  | succ m ih =>
      simp [pow_succ', Matrix.mul_apply, Fintype.sum_option, absorbingCompletion, ih]

/-- Original-to-original entries are exactly powers of the transient block. -/
theorem absorbingCompletion_pow_original (G : StochasticGrammar D) (m : ℕ)
    (u v : Fin n) :
    (G.absorbingCompletion ^ m) (some u) (some v) =
      (G.transientMatrix ^ m) u v := by
  induction m generalizing u v with
  | zero => simp [Matrix.one_apply]
  | succ m ih =>
      simp [pow_succ, Matrix.mul_apply, Fintype.sum_option, absorbingCompletion,
        transientMatrix, ih]

/-- All powers preserve row normalization, not just the one-step completion. -/
theorem absorbingCompletion_pow_row_sum (G : StochasticGrammar D) (m : ℕ)
    (u : Option (Fin n)) : ∑ v, (G.absorbingCompletion ^ m) u v = 1 := by
  induction m generalizing u with
  | zero => simp [Matrix.one_apply]
  | succ m ih =>
      calc
        ∑ v, (G.absorbingCompletion ^ (m + 1)) u v =
            ∑ w, (G.absorbingCompletion ^ m) u w *
              (∑ v, G.absorbingCompletion w v) := by
          simp only [pow_succ, Matrix.mul_apply]
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
        _ = ∑ w, (G.absorbingCompletion ^ m) u w := by
          simp only [G.absorbingCompletion_row_sum, mul_one]
        _ = 1 := ih u

/-- Exact block-power formula for the absorption column. -/
theorem absorbingCompletion_pow_absorption (G : StochasticGrammar D)
    (m : ℕ) (u : Fin n) :
    (G.absorbingCompletion ^ m) (some u) none =
      1 - ∑ v, (G.transientMatrix ^ m) u v := by
  have h := G.absorbingCompletion_pow_row_sum m (some u)
  rw [Fintype.sum_option] at h
  simp only [G.absorbingCompletion_pow_original] at h
  linarith

/-- Pointwise absorption includes one final step from a terminal fragment. -/
theorem absorbingCompletion_absorbed_after_rank (G : StochasticGrammar D) (u : Fin n) :
    (G.absorbingCompletion ^ (D.rank u + 1)) (some u) none = 1 := by
  rw [G.absorbingCompletion_pow_absorption]
  simp [G.transient_row_zero_after_rank]

theorem absorbingCompletion_pow_eq_projection_of_transient_zero
    (G : StochasticGrammar D) (N : ℕ) (hN : G.transientMatrix ^ N = 0) :
    G.absorbingCompletion ^ N = absorptionProjection n := by
  ext i j
  cases i with
  | none => simpa [absorptionProjection] using G.absorbingCompletion_pow_none N j
  | some u =>
      cases j with
      | none => simp [G.absorbingCompletion_pow_absorption, hN, absorptionProjection]
      | some v => simp [G.absorbingCompletion_pow_original, hN, absorptionProjection]

theorem absorbingCompletion_pow_rankHorizon (G : StochasticGrammar D) :
    G.absorbingCompletion ^ rankHorizon D.rank = absorptionProjection n :=
  G.absorbingCompletion_pow_eq_projection_of_transient_zero _
    G.transient_pow_rankHorizon_eq_zero

theorem completion_mul_absorptionProjection (G : StochasticGrammar D) :
    G.absorbingCompletion * absorptionProjection n = absorptionProjection n := by
  ext i j
  cases j <;> simp [Matrix.mul_apply, absorptionProjection, G.absorbingCompletion_row_sum]

theorem absorptionProjection_mul_completion (G : StochasticGrammar D) :
    absorptionProjection n * G.absorbingCompletion = absorptionProjection n := by
  ext i j
  cases j <;> simp [Matrix.mul_apply, Fintype.sum_option, absorptionProjection,
    absorbingCompletion]

theorem absorbingCompletion_stabilizes (G : StochasticGrammar D) (t : ℕ) :
    G.absorbingCompletion ^ (rankHorizon D.rank + t) = absorptionProjection n := by
  induction t with
  | zero => simpa using G.absorbingCompletion_pow_rankHorizon
  | succ t ih =>
      rw [show rankHorizon D.rank + (t + 1) = (rankHorizon D.rank + t) + 1 by omega,
        pow_succ, ih, G.absorptionProjection_mul_completion]

end StochasticGrammar

theorem absorptionProjection_idempotent (n : ℕ) :
    absorptionProjection n * absorptionProjection n = absorptionProjection n := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_option, absorptionProjection]

end InfoGeometry.MassSpectrometry
