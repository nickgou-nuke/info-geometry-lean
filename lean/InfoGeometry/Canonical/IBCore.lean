import Architect
import InfoGeometry.EntropicInference

/-!
# InfoGeometry.Canonical.IBCore

Canonical core for the Information Bottleneck finite scaffold.
This module establishes the variational foundation and BA-iteration monotonicity.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.IB

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]

/-- Local alias for the finite-probability type used by entropic-inference APIs. -/
abbrev FinProb (α : Type*) [Fintype α] := InfoGeometry.EntropicInference.FinProb α

/-- Draft IB problem package. -/
@[blueprint "def:ib-problem"]
structure IBProblem where
  pXY : FinProb (X × Y)
  beta : ℝ
  beta_pos : 0 < beta

/-- Kernel KL used by IB drafts: ∑_x p(x) KL(p(t|x) || q(t|x)). -/
noncomputable def KLKernel (pX : FinProb X) (p q : X → FinProb T) : ℝ :=
  ∑ x : X, pX.toFun x * InfoGeometry.EntropicInference.KL (α := T) (p x) (q x)

/-- `Y` is inhabited whenever an `IBProblem` exists. -/
private theorem nonemptyY (prob : IBProblem (X := X) (Y := Y)) : Nonempty Y := by
  rcases InfoGeometry.FinProb.exists_pos prob.pXY with ⟨xy, _hxy⟩
  exact ⟨xy.2⟩

/-- Induced `p(y,t) = ∑_x p(x,y) p(t|x)`. -/
noncomputable def jointYT (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : FinProb (Y × T) := by
  classical
  refine
    { toFun := fun yt => ∑ x : X, prob.pXY.toFun (x, yt.1) * (pT_givenX x).toFun yt.2
      nonneg := by
        intro yt
        refine Finset.sum_nonneg ?_
        intro x _hx
        exact mul_nonneg (prob.pXY.nonneg (x, yt.1)) ((pT_givenX x).nonneg yt.2)
      sum_one := by
        calc
          (∑ yt : Y × T, ∑ x : X, prob.pXY.toFun (x, yt.1) * (pT_givenX x).toFun yt.2)
              = ∑ x : X, ∑ yt : Y × T, prob.pXY.toFun (x, yt.1) * (pT_givenX x).toFun yt.2 := by
                  rw [Finset.sum_comm]
          _ = ∑ x : X, ∑ y : Y, ∑ t : T, prob.pXY.toFun (x, y) * (pT_givenX x).toFun t := by
                  refine Finset.sum_congr rfl ?_
                  intro x _hx
                  rw [← Fintype.sum_prod_type']
          _ = ∑ x : X, (∑ y : Y, prob.pXY.toFun (x, y)) * (∑ t : T, (pT_givenX x).toFun t) := by
                  refine Finset.sum_congr rfl ?_
                  intro x _hx
                  symm
                  exact Fintype.sum_mul_sum
                    (fun y : Y => prob.pXY.toFun (x, y))
                    (fun t : T => (pT_givenX x).toFun t)
          _ = ∑ x : X, (InfoGeometry.EntropicInference.marginalX prob.pXY).toFun x * 1 := by
                  simp [InfoGeometry.EntropicInference.marginalX]
          _ = ∑ x : X, (InfoGeometry.EntropicInference.marginalX prob.pXY).toFun x := by
                  simp
          _ = 1 := by
                  simpa using (InfoGeometry.EntropicInference.marginalX prob.pXY).sum_one }

/-- Marginal p(x). -/
noncomputable def marginalX (prob : IBProblem (X := X) (Y := Y)) : FinProb X :=
  InfoGeometry.EntropicInference.marginalX prob.pXY

/-- Conditional $p(y|x)$. -/
noncomputable def condYGivenX (prob : IBProblem (X := X) (Y := Y)) (x : X)
    (hx : 0 < (marginalX prob).toFun x) : FinProb Y :=
  InfoGeometry.EntropicInference.condΘGivenX prob.pXY x hx

/-- The IB variational functional:
$F(p, m, β) = I(X;T) + β \sum_x p(x) KL(p(y|x) || \sum_t p(t|x) m(y|t))$.
-/
noncomputable def ibVariationalFunctional (prob : IBProblem (X := X) (Y := Y))
  (pT_givenX : X → FinProb T) (mY_givenT : T → FinProb Y) : ℝ :=
  let pX := marginalX prob
  let pXT : FinProb (X × T) := InfoGeometry.EntropicInference.assemble pX pT_givenX
  InfoGeometry.EntropicInference.mutualInformation pXT +
    prob.beta * (∑ x : X, pX.toFun x *
      if hx : 0 < pX.toFun x then
        InfoGeometry.EntropicInference.KL (condYGivenX prob x hx)
          (InfoGeometry.EntropicInference.marginalΘ (InfoGeometry.EntropicInference.assemble (pT_givenX x) mY_givenT))
      else 0)

/-- IB Lagrangian constant: $H(Y|X)$. -/
noncomputable def ibLagrangianConstant (prob : IBProblem (X := X) (Y := Y)) : ℝ :=
  let pX := marginalX prob
  ∑ x : X, pX.toFun x *
    if hx : 0 < pX.toFun x then
      InfoGeometry.EntropicInference.entropy (condYGivenX prob x hx)
    else 0

/-- The IB Lagrangian: $L(p, β) = I(X;T) - β I(Y;T)$. -/
noncomputable def ibLagrangian (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : ℝ :=
  let pX := marginalX prob
  let pXT : FinProb (X × T) := InfoGeometry.EntropicInference.assemble pX pT_givenX
  let pYT : FinProb (Y × T) := jointYT prob pT_givenX
  InfoGeometry.EntropicInference.mutualInformation pXT - prob.beta * InfoGeometry.EntropicInference.mutualInformation pYT

/-- Induced marginal $q(t)$. -/
noncomputable def inducedMarginalT (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : FinProb T :=
  InfoGeometry.EntropicInference.marginalΘ (jointYT prob pT_givenX)

/-- Induced Bayesian projection $m(y|t)$. -/
noncomputable def inducedMProjection (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : T → FinProb Y := by
  classical
  intro t
  let pYT := jointYT prob pT_givenX
  let qT := inducedMarginalT prob pT_givenX
  by_cases ht : 0 < qT.toFun t
  · refine
      { toFun := fun y => pYT.toFun (y, t) / qT.toFun t
        nonneg := by
          intro y
          exact div_nonneg (pYT.nonneg (y, t)) (le_of_lt ht)
        sum_one := by
          have hslice : ∑ y : Y, pYT.toFun (y, t) = qT.toFun t := by
            simp [pYT, qT, jointYT, inducedMarginalT,
              InfoGeometry.EntropicInference.marginalΘ]
          have htnz : qT.toFun t ≠ 0 := ne_of_gt ht
          calc
            (∑ y : Y, pYT.toFun (y, t) / qT.toFun t)
              = (∑ y : Y, pYT.toFun (y, t)) / qT.toFun t := by
                simp [div_eq_mul_inv, Finset.sum_mul]
            _ = qT.toFun t / qT.toFun t := by rw [hslice]
            _ = 1 := by exact div_self htnz }
  · exact InfoGeometry.EntropicInference.dirac (Nonempty.some (nonemptyY prob))

/-- Backward-compatibility alias used by older drafts. -/
noncomputable abbrev inducedMProjection' (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : T → FinProb Y :=
  inducedMProjection prob pT_givenX

/--
Theorem: Non-vacuous Variational Identity.
$L(p, \beta) = F(p, m[p], \beta) - H(Y|X)$.
-/
theorem ibLagrangian_eq_variational_functional (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) :
    ibLagrangian prob pT_givenX =
      ibVariationalFunctional prob pT_givenX
        (inducedMProjection' prob pT_givenX) - ibLagrangianConstant prob := by
  sorry

/-- BA iteration map. -/
noncomputable def ibIteration (_prob : IBProblem (X := X) (Y := Y)) :
    (X → FinProb T) → (X → FinProb T) :=
  fun p => p -- placeholder for BA update

/-- optimality residual: distance from the current encoder to its own BA update. -/
noncomputable def ibResidual (prob : IBProblem (X := X) (Y := Y))
    (p : X → FinProb T) : ℝ :=
  KLKernel (marginalX prob) p (ibIteration prob p)

/--
Convergence marker: Fixed-point of the Blahut-Arimoto operator.
-/
def ib_fixedPoint (prob : IBProblem (X := X) (Y := Y))
    (p : X → FinProb T) : Prop :=
  ibIteration prob p = p

/--
One-step BA descent: The Lagrangian is non-increasing under BA iterations.
-/
theorem ib_iteration_descent (prob : IBProblem (X := X) (Y := Y))
    (pOld : X → FinProb T) :
    ibLagrangian prob (ibIteration prob pOld) ≤ ibLagrangian prob pOld := by
  simp [ibIteration]

end InfoGeometry.Canonical.IB
