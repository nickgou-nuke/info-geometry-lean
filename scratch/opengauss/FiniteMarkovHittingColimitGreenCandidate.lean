/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
import InfoGeometry.QuantumContext.FiniteMarkovDirichletOrderColimit
import InfoGeometry.QuantumContext.MarkovAttentionKemenyTrace

/-!
# Candidate: identify a finite Markov Dirichlet order colimit with its Green solution

The intended argument stays in the real order colimit of finite Bellman
approximants.  The first reusable leaf below says that a finite sum of
coordinatewise increasing bounded sequences has supremum equal to the sum of
the coordinate suprema.  Its proof uses a common maximum horizon for the
finitely many approximating coordinates.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovHittingColimitGreenCandidate

open scoped BigOperators

/-- Suprema commute with a synchronized sum of two monotone bounded real
sequences. The common index is valid because the two sequences are monotone:
the larger of two approximating indices approximates both coordinates. -/
theorem csSup_range_add_of_monotone
    (f g : ℕ → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hfb : BddAbove (Set.range f)) (hgb : BddAbove (Set.range g)) :
    sSup (Set.range (fun n => f n + g n)) =
      sSup (Set.range f) + sSup (Set.range g) := by
  have hdb : BddAbove (Set.range (fun n => f n + g n)) := by
    obtain ⟨a, ha⟩ := hfb
    obtain ⟨b, hb⟩ := hgb
    refine ⟨a + b, ?_⟩
    rintro y ⟨n, rfl⟩
    exact add_le_add (ha ⟨n, rfl⟩) (hb ⟨n, rfl⟩)
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨n, rfl⟩
    exact add_le_add (le_csSup hfb ⟨n, rfl⟩) (le_csSup hgb ⟨n, rfl⟩)
  · apply le_of_forall_pos_lt_add
    intro ε hε
    let δ := ε / 3
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hfapprox : sSup (Set.range f) - δ < sSup (Set.range f) := by linarith
    have hgapprox : sSup (Set.range g) - δ < sSup (Set.range g) := by linarith
    obtain ⟨fn, hnmem, hnlt⟩ :=
      exists_lt_of_lt_csSup (Set.range_nonempty f) hfapprox
    obtain ⟨gn, hgmem, hmlt⟩ :=
      exists_lt_of_lt_csSup (Set.range_nonempty g) hgapprox
    obtain ⟨n, rfl⟩ := hnmem
    obtain ⟨m, rfl⟩ := hgmem
    let N := max n m
    have hnN : n ≤ N := Nat.le_max_left _ _
    have hmN : m ≤ N := Nat.le_max_right _ _
    have hflow : sSup (Set.range f) - δ + (sSup (Set.range g) - δ) <
        f N + g N := by
      exact add_lt_add (lt_of_lt_of_le hnlt (hf hnN))
        (lt_of_lt_of_le hmlt (hg hmN))
    have hNsup : f N + g N ≤ sSup (Set.range (fun k => f k + g k)) :=
      le_csSup hdb ⟨N, rfl⟩
    dsimp [δ] at hflow
    linarith

/-- Suprema commute with finite synchronized sums of monotone bounded real
sequences. The finite induction combines two coordinates at a time, while the
two-sequence lemma supplies the common horizon. -/
theorem csSup_range_finset_sum_of_monotone
    {ι : Type*} (s : Finset ι) (f : ℕ → ι → ℝ)
    (hmono : ∀ i, Monotone (fun n => f n i))
    (upper : ι → ℝ) (hupper : ∀ n i, f n i ≤ upper i) :
    sSup (Set.range (fun n => ∑ i ∈ s, f n i)) =
      ∑ i ∈ s, sSup (Set.range (fun n => f n i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
      have htail_mono : Monotone (fun n => ∑ i ∈ s, f n i) := by
        intro n m hnm
        apply Finset.sum_le_sum
        intro i hi
        exact hmono i hnm
      have htail_upper (n : ℕ) :
          (∑ i ∈ s, f n i) ≤ ∑ i ∈ s, upper i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hupper n i
      have htail_bdd : BddAbove (Set.range (fun n => ∑ i ∈ s, f n i)) :=
        ⟨∑ i ∈ s, upper i, by
          rintro z ⟨n, rfl⟩
          exact htail_upper n⟩
      have ha_bdd : BddAbove (Set.range (fun n => f n a)) :=
        ⟨upper a, by rintro z ⟨n, rfl⟩; exact hupper n a⟩
      have hsum_insert (n : ℕ) :
          (∑ i ∈ insert a s, f n i) = f n a + ∑ i ∈ s, f n i := by
        simp [Finset.sum_insert, has]
      rw [show (fun n => ∑ i ∈ insert a s, f n i) =
          fun n => f n a + ∑ i ∈ s, f n i from funext hsum_insert]
      rw [csSup_range_add_of_monotone
        (fun n => f n a) (fun n => ∑ i ∈ s, f n i)
        (hmono a) htail_mono ha_bdd htail_bdd]
      rw [ih]
      simp [Finset.sum_insert, has]

/-- Finite weighted-sum/supremum interchange for synchronized monotone
sequences and nonnegative fixed coefficients. -/
theorem csSup_range_weighted_finset_sum_of_monotone
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (f : ℕ → ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hmono : ∀ i, Monotone (fun n => f n i))
    (upper : ι → ℝ) (hupper : ∀ n i, f n i ≤ upper i) :
    sSup (Set.range (fun n => ∑ i ∈ s, w i * f n i)) =
      ∑ i ∈ s, sSup (Set.range (fun n => w i * f n i)) := by
  exact csSup_range_finset_sum_of_monotone s
    (fun n i => w i * f n i)
    (fun i n m hnm => mul_le_mul_of_nonneg_left
      (hmono i hnm) (hw i))
    (fun i => w i * upper i)
    (fun n i => mul_le_mul_of_nonneg_left (hupper n i) (hw i))

/-- Multiplication by a fixed nonnegative real commutes with a bounded
sequence supremum. The zero coefficient is handled directly; for a positive
coefficient, use its order isomorphism on `ℝ`. -/
theorem csSup_range_mul_left_of_nonneg
    (w : ℝ) (hw : 0 ≤ w) (f : ℕ → ℝ)
    (hfb : BddAbove (Set.range f)) :
    sSup (Set.range (fun n => w * f n)) = w * sSup (Set.range f) := by
  by_cases hw0 : w = 0
  · simp [hw0]
  · have hpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    let e := OrderIso.mulLeft₀ w hpos
    have himage : Set.range (fun n => w * f n) = e '' Set.range f := by
      ext y
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨f n, ⟨n, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
    calc
      sSup (Set.range (fun n => w * f n)) = sSup (e '' Set.range f) := by rw [himage]
      _ = e (sSup (Set.range f)) := (e.map_csSup' (Set.range_nonempty f) hfb).symm
      _ = w * sSup (Set.range f) := rfl

/-- Removing the first term of a monotone sequence does not change its
bounded supremum. -/
theorem csSup_range_succ_eq_of_monotone
    (f : ℕ → ℝ) (hmono : Monotone f) (hfb : BddAbove (Set.range f)) :
    sSup (Set.range (fun n => f (n + 1))) = sSup (Set.range f) := by
  have htail_bdd : BddAbove (Set.range (fun n => f (n + 1))) := by
    obtain ⟨b, hb⟩ := hfb
    refine ⟨b, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hb ⟨n + 1, rfl⟩
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨n, rfl⟩
    exact le_csSup hfb ⟨n + 1, rfl⟩
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨n, rfl⟩
    cases n with
    | zero =>
        exact le_trans (hmono (Nat.zero_le 1)) (le_csSup htail_bdd ⟨0, rfl⟩)
    | succ n => exact le_csSup htail_bdd ⟨n, rfl⟩

open InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation
open InfoGeometry.QuantumContext.FiniteMarkovDirichletOrderColimit
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

/-- For a strictly positive finite row-stochastic matrix, the order colimit
of the finite first-hit Bellman approximants is the existing group-inverse
Dirichlet potential. The proof passes the finite stochastic sum through the
order supremum using a common horizon; it invokes no path-space expectation. -/
theorem firstHitApproximationColimit_eq_groupInversePotentialDifference
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hG : IsGroupInverse (1 - P) G)
    (target i : ι) :
    firstHitApproximationColimit P hP target i =
      groupInversePotentialDifference π G i target := by
  classical
  obtain ⟨ε, hε, hminor⟩ := exists_target_minorization_of_positive P target hPpos
  let x : ι → ℝ := fun j => firstHitApproximationColimit P hP target j
  have happroxBound (n : ℕ) (j : ι) :
      firstHitApproximation P target n j ≤ ε⁻¹ :=
    firstHitApproximation_le_inv_of_target_minorization
      P hP target ε hε hminor n j
  have happroxMono (j : ι) :
      Monotone (fun n => firstHitApproximation P target n j) := by
    apply monotone_nat_of_le_succ
    intro n
    exact firstHitApproximation_mono P hP target n j
  have happroxBdd (j : ι) :
      BddAbove (Set.range (fun n => firstHitApproximation P target n j)) := by
    refine ⟨ε⁻¹, ?_⟩
    rintro y ⟨n, rfl⟩
    exact happroxBound n j
  have hcolimitLUB (j : ι) :
      IsLUB (Set.range (fun n => firstHitApproximation P target n j)) (x j) := by
    change IsLUB
      (Set.range (firstHitApproximationDiagram P hP target j).obj)
      (firstHitApproximationColimit P hP target j)
    exact firstHitApproximationColimit_isLUB P hP target ε hε hminor j
  have hxTarget : x target = 0 := by
    change sSup (Set.range
      (fun n => firstHitApproximation P target n target)) = 0
    simp [firstHitApproximation_target]
  have hweightedSup (r : ι) :
      sSup (Set.range (fun n => (P.mulVec
        (firstHitApproximation P target n)) r)) = (P.mulVec x) r := by
    change sSup (Set.range (fun n =>
      ∑ j ∈ Finset.univ, P r j * firstHitApproximation P target n j)) = _
    rw [csSup_range_weighted_finset_sum_of_monotone
      Finset.univ (fun j => P r j)
      (fun n j => firstHitApproximation P target n j)
      (fun j => Matrix.nonneg_of_mem_rowStochastic hP)
      (fun j => happroxMono j)
      (fun _ => ε⁻¹)
      (fun n j => happroxBound n j)]
    calc
      (∑ j ∈ Finset.univ,
          sSup (Set.range (fun n => P r j * firstHitApproximation P target n j))) =
          ∑ j ∈ Finset.univ, P r j * x j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [csSup_range_mul_left_of_nonneg
          (P r j) (Matrix.nonneg_of_mem_rowStochastic hP)
          (fun n => firstHitApproximation P target n j) (happroxBdd j)]
        rfl
      _ = (P.mulVec x) r := by
        simp [Matrix.mulVec, dotProduct]
  have hweightedSeqMono (r : ι) :
      Monotone (fun n => (P.mulVec
        (firstHitApproximation P target n)) r) := by
    intro n m hnm
    simp [Matrix.mulVec, dotProduct]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (happroxMono j hnm) (Matrix.nonneg_of_mem_rowStochastic hP)
  have hweightedSeqBdd (r : ι) :
      BddAbove (Set.range (fun n => (P.mulVec
        (firstHitApproximation P target n)) r)) := by
    refine ⟨ε⁻¹, ?_⟩
    rintro z ⟨n, rfl⟩
    calc
      (P.mulVec (firstHitApproximation P target n)) r =
          ∑ j, P r j * firstHitApproximation P target n j := by
            simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ j, P r j * ε⁻¹ := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (happroxBound n j) (Matrix.nonneg_of_mem_rowStochastic hP)
      _ = ε⁻¹ := by
        rw [← Finset.sum_mul]
        rw [Matrix.sum_row_of_mem_rowStochastic hP r]
        simp
  have hbellman (r : ι) (hr : r ≠ target) :
      x r = 1 + (P.mulVec x) r := by
    have hrec (n : ℕ) :
        firstHitApproximation P target (n + 1) r =
          1 + (P.mulVec (firstHitApproximation P target n)) r :=
      firstHitApproximation_succ_of_ne P target n r hr
    have hrecFun :
        (fun n => firstHitApproximation P target (n + 1) r) =
          fun n => 1 + (P.mulVec (firstHitApproximation P target n)) r := by
      funext n
      exact hrec n
    have hshift := csSup_range_succ_eq_of_monotone
      (fun n => firstHitApproximation P target n r)
      (happroxMono r) (happroxBdd r)
    have hadd := csSup_range_add_of_monotone
      (fun _ : ℕ => (1 : ℝ))
      (fun n => (P.mulVec (firstHitApproximation P target n)) r)
      (monotone_const) (hweightedSeqMono r)
      (by exact ⟨1, by rintro z ⟨n, rfl⟩; rfl⟩)
      (hweightedSeqBdd r)
    calc
      x r = sSup (Set.range (fun n => firstHitApproximation P target (n + 1) r)) := by
        symm
        change sSup (Set.range (fun n => firstHitApproximation P target (n + 1) r)) =
          sSup (Set.range (fun n => firstHitApproximation P target n r))
        exact hshift
      _ = sSup (Set.range (fun n =>
          1 + (P.mulVec (firstHitApproximation P target n)) r)) := by
        rw [hrecFun]
      _ = 1 + sSup (Set.range (fun n =>
          (P.mulVec (firstHitApproximation P target n)) r)) := by
        simpa using hadd
      _ = 1 + (P.mulVec x) r := by rw [hweightedSup r]
  have hdirichlet (r : ι) (hr : r ≠ target) :
      ((1 - P).mulVec x) r = 1 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    change x r - (P.mulVec x) r = 1
    rw [hbellman r hr]
    ring
  have hsolution := groupInversePotentialDifference_unique_dirichlet_solution
    P G π hP hPpos hπnonneg hπsum hπstat hG target x hxTarget hdirichlet
  exact congrFun hsolution i

end InfoGeometry.QuantumContext.FiniteMarkovHittingColimitGreenCandidate
