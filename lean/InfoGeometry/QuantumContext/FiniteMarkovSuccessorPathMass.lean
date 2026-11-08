/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation

/-!
# Singleton masses of finite Markov successor paths

The path-state accessor adjoins the initial state to a successor path. This
module proves that the recursively defined successor PMF assigns each path
the product of its one-step transition probabilities.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovSuccessorPathMass

open ProbabilityTheory
open scoped ENNReal BigOperators
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The recursive path constructor used by the production successor PMF. -/
private def consPath {n : ℕ} (j : ι) (tail : Fin n → ι) : Fin (n + 1) → ι :=
  @Fin.cons n (fun _ => ι) j tail

/-- The state at each time in a path with its initial state adjoined. -/
def stateAt {n : ℕ} (i : ι) (path : Fin n → ι) : Fin (n + 1) → ι :=
  Fin.cases i path

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem stateAt_zero {n : ℕ} (i : ι) (path : Fin n → ι) :
    stateAt i path 0 = i := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem stateAt_succ {n : ℕ} (i : ι) (path : Fin n → ι) (k : Fin n) :
    stateAt i path k.succ = path k := rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem prependPath_injective {n : ℕ} (j : ι) :
    Function.Injective (consPath j : (Fin n → ι) → Fin (n + 1) → ι) := by
  intro x y h
  funext k
  exact congrFun h k.succ

omit [Fintype ι] in
private theorem map_prependPath_apply {n : ℕ} (j : ι)
    (p : PMF (Fin n → ι)) (path : Fin (n + 1) → ι) :
    (p.map (consPath j)) path =
      if path 0 = j then p (fun k => path k.succ) else 0 := by
  classical
  by_cases hj : path 0 = j
  · subst j
    have hpath : path = consPath (path 0) (fun k => path k.succ) := by
      funext k
      refine Fin.cases ?_ ?_ k
      · rfl
      · intro k
        rfl
    rw [hpath, PMF.map_apply, tsum_eq_single (fun k => path k.succ)]
    · simp [consPath]
    · intro x hx
      have hneq : consPath (path 0) (fun k => path k.succ) ≠
          consPath (path 0) x := by
        intro heq
        exact hx (prependPath_injective (path 0) heq.symm)
      have hhead : consPath (path 0) (fun k => path k.succ) 0 = path 0 := rfl
      rw [hhead, ite_eq_right hneq]
  · rw [ite_eq_right hj]
    rw [PMF.map_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    have hneq : path ≠ consPath j x := by
      intro heq
      have hhead : path 0 = j := by
        simpa [consPath, Fin.cons] using congrFun heq 0
      exact hj hhead
    rw [ite_eq_right hneq]

omit [Fintype ι] [DecidableEq ι] in
private theorem stateAt_tail_castSucc {n : ℕ} (path : Fin (n + 1) → ι)
    (k : Fin n) :
    stateAt (path 0) (fun j => path j.succ) k.castSucc = path k.castSucc := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ n =>
      refine Fin.cases ?_ ?_ k
      · rfl
      · intro k
        rw [← Fin.succ_castSucc, stateAt_succ]

/-- Singleton-mass product formula for the finite successor-path PMF.
`stateAt` includes the initial state, so each factor is the transition from
time `k` to time `k + 1`. -/
theorem successorPathPMF_apply_eq_prod (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∀ (n : ℕ) (i : ι) (path : Fin n → ι),
      successorPathPMF P hP n i path =
        ∏ k : Fin n,
          ENNReal.ofReal (P (stateAt i path k.castSucc) (stateAt i path k.succ)) := by
  intro n
  induction n with
  | zero =>
      intro i path
      have hpath : path = Fin.elim0 := by
        funext k
        exact Fin.elim0 k
      subst path
      simp [successorPathPMF, stateAt]
  | succ n ih =>
      intro i path
      rw [successorPathPMF, PMF.bind_apply]
      change (∑' j, rowPMF P hP i j *
        ((successorPathPMF P hP n j).map (consPath j)) path) = _
      simp only [tsum_fintype]
      rw [Finset.sum_eq_single (path 0)]
      · simp only [rowPMF, PMF.ofFintype_apply]
        rw [map_prependPath_apply]
        rw [ih (path 0) (fun k => path k.succ)]
        rw [Fin.prod_univ_succ]
        simp only [stateAt_zero, stateAt_succ, Fin.castSucc_zero]
        apply congrArg (fun z => ENNReal.ofReal (P i (path 0)) * z)
        apply Finset.prod_congr rfl
        intro k hk
        rw [stateAt_tail_castSucc, ← Fin.succ_castSucc, stateAt_succ]
      · intro j hj hji
        rw [map_prependPath_apply]
        have hj' : path 0 ≠ j := fun heq => hji heq.symm
        simp [hj']
      · intro h
        exact (h (Finset.mem_univ _)).elim

end InfoGeometry.QuantumContext.FiniteMarkovSuccessorPathMass
end
