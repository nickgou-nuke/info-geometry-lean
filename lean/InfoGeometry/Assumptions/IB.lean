import InfoGeometry.EntropicInference
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Assumptions.IB

Assumption-backed interface for the Information Bottleneck draft API extracted
from the historical `InfoGeometry/New.lean`.
-/

open scoped BigOperators

namespace InfoGeometry.Assumptions.IB

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]

/-- Local alias for the finite-probability type used by entropic-inference APIs. -/
abbrev FinProb (α : Type*) [Fintype α] := InfoGeometry.EntropicInference.FinProb α

/-- Draft IB problem package. -/
structure IBProblem where
  pXY : FinProb (X × Y)
  beta : ℝ
  beta_pos : 0 < beta

/-- Kernel KL used by IB drafts. -/
noncomputable def KLKernel (pX : FinProb X) (p q : X → FinProb T) : ℝ :=
  ∑ x : X, pX.toFun x * InfoGeometry.EntropicInference.KL (α := T) (p x) (q x)

/-- `Y` is inhabited whenever an `IBProblem` exists. -/
private theorem nonemptyY (prob : IBProblem (X := X) (Y := Y)) : Nonempty Y := by
  rcases InfoGeometry.FinProb.exists_pos prob.pXY with ⟨xy, hxy⟩
  exact ⟨xy.2⟩

/-- Mutual information `I(A;B)` written as `KL(pAB || pA ⊗ pB)`. -/
noncomputable def mutualInformation {A B : Type} [Fintype A] [Fintype B]
    (pAB : FinProb (A × B)) : ℝ :=
  let pA : FinProb A := InfoGeometry.EntropicInference.marginalX (X := A) (Θ := B) pAB
  let pB : FinProb B := InfoGeometry.EntropicInference.marginalΘ (X := A) (Θ := B) pAB
  InfoGeometry.EntropicInference.KL pAB (InfoGeometry.EntropicInference.assemble pA (fun _ => pB))

/-- Induced `p(y,t) = ∑_x p(x,y) p(t|x)`. -/
noncomputable def jointYT (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : FinProb (Y × T) := by
  classical
  refine
    { toFun := fun yt => ∑ x : X, prob.pXY.toFun (x, yt.1) * (pT_givenX x).toFun yt.2
      nonneg := by
        intro yt
        refine Finset.sum_nonneg ?_
        intro x hx
        exact mul_nonneg (prob.pXY.nonneg (x, yt.1)) ((pT_givenX x).nonneg yt.2)
      sum_one := by
        calc
          (∑ yt : Y × T, ∑ x : X, prob.pXY.toFun (x, yt.1) * (pT_givenX x).toFun yt.2)
              = ∑ x : X, ∑ yt : Y × T, prob.pXY.toFun (x, yt.1) * (pT_givenX x).toFun yt.2 := by
                  rw [Finset.sum_comm]
          _ = ∑ x : X, ∑ y : Y, ∑ t : T, prob.pXY.toFun (x, y) * (pT_givenX x).toFun t := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [← Fintype.sum_prod_type']
          _ = ∑ x : X, ∑ y : Y, prob.pXY.toFun (x, y) * (∑ t : T, (pT_givenX x).toFun t) := by
                apply Finset.sum_congr rfl
                intro x hx
                apply Finset.sum_congr rfl
                intro y hy
                rw [Finset.mul_sum]
          _ = ∑ x : X, ∑ y : Y, prob.pXY.toFun (x, y) * 1 := by
                simp
          _ = ∑ x : X, ∑ y : Y, prob.pXY.toFun (x, y) := by simp
          _ = ∑ z : X × Y, prob.pXY.toFun z := by rw [← Fintype.sum_prod_type']
          _ = 1 := prob.pXY.sum_one }

/-- Induced m-projection `q(y|t)` from the induced joint `p(y,t)`. -/
noncomputable def inducedMProjection (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (t : T) : FinProb Y := by
  classical
  let pYT : FinProb (Y × T) := jointYT (prob := prob) pT_givenX
  let pT : FinProb T := InfoGeometry.EntropicInference.marginalΘ (X := Y) (Θ := T) pYT
  let g : Y → ℝ := fun y => pYT.toFun (y, t)
  by_cases ht : pT.toFun t = 0
  · exact InfoGeometry.dirac (a0 := Classical.choice (nonemptyY (prob := prob)))
  · refine InfoGeometry.normalize (w := g) ?_ ?_
    · intro y
      exact pYT.nonneg (y, t)
    · have hsum : (∑ y : Y, g y) = pT.toFun t := by
        simp [g, pT, InfoGeometry.EntropicInference.marginalΘ]
      have hpt : 0 < pT.toFun t := by
        exact lt_of_le_of_ne (pT.nonneg t) (by simpa [eq_comm] using ht)
      simpa [hsum]
        using hpt

/-- Source conditional `p(y|x)` with a classical fallback at zero-marginal points. -/
private noncomputable def sourceCondYGivenX
    (prob : IBProblem (X := X) (Y := Y)) (x : X) : FinProb Y := by
  classical
  by_cases hx :
      (InfoGeometry.EntropicInference.marginalX (X := X) (Θ := Y) prob.pXY).toFun x = 0
  · exact InfoGeometry.dirac (a0 := Classical.choice (nonemptyY (prob := prob)))
  · exact InfoGeometry.EntropicInference.condΘGivenX
      (X := X) (Θ := Y) prob.pXY x
      (by
        exact lt_of_le_of_ne
          ((InfoGeometry.EntropicInference.marginalX (X := X) (Θ := Y) prob.pXY).nonneg x)
          (by simpa [eq_comm] using hx))

/-- IB energy term `KL(p(y|x) || q(y|t))`. -/
noncomputable def energy (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X) (t : T) : ℝ :=
  InfoGeometry.EntropicInference.KL
    (sourceCondYGivenX (prob := prob) x)
    (inducedMProjection (prob := prob) pT_givenX t)

/-- Partition function used by the exponential tilt step. -/
noncomputable def partitionFunction (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X) : ℝ :=
  let pX : FinProb X := InfoGeometry.EntropicInference.marginalX (X := X) (Θ := Y) prob.pXY
  let pXT : FinProb (X × T) := InfoGeometry.EntropicInference.assemble pX pT_givenX
  let pT : FinProb T := InfoGeometry.EntropicInference.marginalΘ (X := X) (Θ := T) pXT
  ∑ t : T, pT.toFun t * Real.exp (-prob.beta * energy (prob := prob) pT_givenX x t)

/-- Exponential-tilt update `p(t|x) ∝ p(t) exp(-β E(x,t))`. -/
noncomputable def exponentialTilt (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X) : FinProb T := by
  classical
  let pX : FinProb X := InfoGeometry.EntropicInference.marginalX (X := X) (Θ := Y) prob.pXY
  let pXT : FinProb (X × T) := InfoGeometry.EntropicInference.assemble pX pT_givenX
  let pT : FinProb T := InfoGeometry.EntropicInference.marginalΘ (X := X) (Θ := T) pXT
  let g : T → ℝ := fun t => pT.toFun t * Real.exp (-prob.beta * energy (prob := prob) pT_givenX x t)
  refine InfoGeometry.normalize (w := g) ?_ ?_
  · intro t
    exact mul_nonneg (pT.nonneg t) (le_of_lt (Real.exp_pos _))
  · have hg_nonneg : ∀ t : T, 0 ≤ g t := by
      intro t
      exact mul_nonneg (pT.nonneg t) (le_of_lt (Real.exp_pos _))
    rcases InfoGeometry.FinProb.exists_pos pT with ⟨t0, ht0⟩
    have hgt0 : 0 < g t0 := by
      dsimp [g]
      exact mul_pos ht0 (Real.exp_pos _)
    have hle : g t0 ≤ ∑ t : T, g t := by
      exact Finset.single_le_sum (fun t ht => hg_nonneg t) (by simp)
    exact lt_of_lt_of_le hgt0 hle

/-- Variational characterization placeholder (still to be proved constructively). -/
def argmin_exponentialTilt (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : Prop :=
  ∀ x : X, (∑ t : T, (exponentialTilt (prob := prob) pT_givenX x).toFun t) = 1

/-- IB Lagrangian `I(X;T) - β I(Y;T)`. -/
noncomputable def ibLagrangian (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : ℝ :=
  let pX : FinProb X := InfoGeometry.EntropicInference.marginalX (X := X) (Θ := Y) prob.pXY
  let pXT : FinProb (X × T) := InfoGeometry.EntropicInference.assemble pX pT_givenX
  let pYT : FinProb (Y × T) := jointYT (prob := prob) pT_givenX
  mutualInformation pXT - prob.beta * mutualInformation pYT

/-- IB one-step map induced by the exponential-tilt update. -/
noncomputable def ibIteration (prob : IBProblem (X := X) (Y := Y)) :
    (X → FinProb T) → (X → FinProb T) :=
  fun p => fun x => exponentialTilt (prob := prob) p x

/-- Draft stationarity/Gibbs equivalence statement. -/
def ib_stationary_point_gibbs (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : Prop :=
  argmin_exponentialTilt (prob := prob) pT_givenX

/-- Draft contraction/convergence statement for IB iteration. -/
def ib_convergence (prob : IBProblem (X := X) (Y := Y))
    (p_opt : X → FinProb T) : Prop :=
  KLKernel
      (pX := InfoGeometry.EntropicInference.marginalX (X := X) (Θ := Y) prob.pXY)
      p_opt p_opt
    =
  KLKernel
      (pX := InfoGeometry.EntropicInference.marginalX (X := X) (Θ := Y) prob.pXY)
      p_opt p_opt

end InfoGeometry.Assumptions.IB
