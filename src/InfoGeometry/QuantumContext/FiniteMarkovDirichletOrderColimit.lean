/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import InfoGeometry.Categorical.InductivePosetColimit
import InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation

/-!
# Order colimit of finite Markov Dirichlet approximants

Under a uniform lower bound on transitions into a target, the monotone
finite-horizon Bellman approximants are bounded above. Their supremum is
therefore an actual colimit in the preorder category of real numbers, using
the repository's preorder-colimit owner. This establishes an order colimit of
finite stages; it does not identify that colimit with a path-law expectation.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovDirichletOrderColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Categorical.InductivePosetColimit
open InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Monotonicity of the Bellman approximants between arbitrary horizons. -/
theorem firstHitApproximation_mono_of_le
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) {n m : ℕ} (hnm : n ≤ m) (i : ι) :
    firstHitApproximation P target n i ≤ firstHitApproximation P target m i := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
      exact le_trans ih (firstHitApproximation_mono P hP target m i)

/-- The finite-horizon approximants, ordered by their horizon, form a diagram
in the preorder category of real values. -/
def firstHitApproximationDiagram
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) (i : ι) : ℕ ⥤ ℝ :=
  Functor.ofSequence (fun n =>
    homOfLE (firstHitApproximation_mono P hP target n i))

/-- The order-colimit value of the finite-horizon approximants. -/
noncomputable def firstHitApproximationColimit
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target i : ι) : ℝ :=
  sSup (Set.range (firstHitApproximationDiagram P hP target i).obj)

/-- Under a uniform target minorization, the order-colimit value is the least
upper bound of all finite-horizon approximants. -/
theorem firstHitApproximationColimit_isLUB
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) (ε : ℝ) (hε : 0 < ε)
    (hminor : ∀ i, ε ≤ P i target) (i : ι) :
    IsLUB (Set.range (firstHitApproximationDiagram P hP target i).obj)
      (firstHitApproximationColimit P hP target i) := by
  apply isLUB_csSup
  · exact ⟨_, ⟨0, rfl⟩⟩
  · refine ⟨ε⁻¹, ?_⟩
    rintro y ⟨n, rfl⟩
    exact firstHitApproximation_le_inv_of_target_minorization
      P hP target ε hε hminor n i

/-- The bounded finite-horizon approximants have a categorical colimit in the
real preorder. This is the canonical least-upper-bound colimit, not a claim
that the value is a probability expectation. -/
noncomputable def firstHitApproximationColimitCocone
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) (ε : ℝ) (hε : 0 < ε)
    (hminor : ∀ i, ε ≤ P i target) (i : ι) :
    ColimitCocone (firstHitApproximationDiagram P hP target i) :=
  colimitCoconeOfIsLUB
    (firstHitApproximationDiagram P hP target i)
    (firstHitApproximationColimit_isLUB P hP target ε hε hminor i)

omit [DecidableEq ι] in
/-- Strict positivity on a finite carrier gives a single positive lower bound
for every transition into the chosen target. -/
theorem exists_target_minorization_of_positive
    (P : Matrix ι ι ℝ) (target : ι)
    (hPpos : ∀ i j, 0 < P i j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ P i target := by
  classical
  let S : Finset ℝ := Finset.univ.image (fun i => P i target)
  have hS : S.Nonempty := by
    refine ⟨P target target, ?_⟩
    exact Finset.mem_image.mpr ⟨target, Finset.mem_univ _, rfl⟩
  let ε : ℝ := S.min' hS
  refine ⟨ε, ?_, ?_⟩
  · have hεmem : ε ∈ S := Finset.min'_mem S hS
    obtain ⟨j, _, hjeq⟩ := Finset.mem_image.mp hεmem
    rw [← hjeq]
    exact hPpos j target
  · intro i
    exact Finset.min'_le S (P i target)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- A strictly positive finite row-stochastic matrix has a genuine order
colimit for each target's finite-horizon Bellman diagram. The existence proof
uses the finite minimum target probability and the categorical LUB-colimit
construction above. -/
theorem exists_firstHitApproximationColimitCocone_of_positive
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) (hPpos : ∀ i j, 0 < P i j) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ j, ε ≤ P j target) ∧
      ∀ i, Nonempty
        (ColimitCocone (firstHitApproximationDiagram P hP target i)) := by
  obtain ⟨ε, hε, hminor⟩ := exists_target_minorization_of_positive P target hPpos
  refine ⟨ε, hε, hminor, ?_⟩
  intro i
  exact ⟨firstHitApproximationColimitCocone P hP target ε hε hminor i⟩

end InfoGeometry.QuantumContext.FiniteMarkovDirichletOrderColimit
