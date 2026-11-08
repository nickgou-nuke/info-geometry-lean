import InfoGeometry.LLM.DiscreteRouterBayesStep
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LLM.PromptDefectRegularization
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM

open DiscreteRouterBayesStep

section RouterRegularization

variable {S Tok Pos Expert : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
variable [Fintype Tok] [DecidableEq Tok]
variable [Fintype Expert] [DecidableEq Expert]

local notation "N" => InfoGeometry.Krein.NeutralSpace S
local notation "EndN" => N →L[ℝ] N

variable {n : Nat} [Nonempty (Fin n)]

/-- Tokenwise signal after defect-regularized core update. -/
noncomputable def regularizedSignal
    (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (lambda : ℝ) (x : Tok → EndN) : Tok → EndN :=
  fun i => regularizedCoreUpdate (B := B) lambda (x i)

/-- Tokenwise signal after canonical core update. -/
noncomputable def coreSignal
    (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (x : Tok → EndN) : Tok → EndN :=
  fun i => B.coreUpdate (x i)

section OmitTokInstances

omit [Fintype Tok] [DecidableEq Tok] [DecidableEq Expert]

/-- Defect-regularized tokenwise signal is independent of `λ`. -/

@[rep_depth transport]
theorem regularizedSignal_lambda_invariant
    (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (lambda1 lambda2 : ℝ) (x : Tok → EndN) :
    regularizedSignal (B := B) lambda1 x = regularizedSignal (B := B) lambda2 x := by
  funext i
  exact regularizedCoreUpdate_lambda_invariant (B := B) lambda1 lambda2 (x i)

/-- Defect-regularized tokenwise signal collapses to canonical core signal. -/
@[rep_depth transport]
theorem regularizedSignal_eq_coreSignal
    (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (lambda : ℝ) (x : Tok → EndN) :
    regularizedSignal (B := B) lambda x = coreSignal (B := B) x := by
  funext i
  exact regularizedCoreUpdate_eq_coreUpdate (B := B) lambda (x i)

end OmitTokInstances

section OmitNonemptyFinN

omit [Fintype Tok] [DecidableEq Tok] [DecidableEq Expert] [Nonempty (Fin n)]

/--
Bayes router update is invariant under defect-regularization weight `λ`
on the tokenwise regularized signal.
-/

@[rep_depth transport]
theorem bayesRouterUpdate_regularizedSignal_lambda_invariant
    (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (beta lambda1 lambda2 : ℝ) (x : Tok → EndN) (i : Tok) :
    bayesRouterUpdate (n := n) beta (regularizedSignal (B := B) lambda1 x) i
      = bayesRouterUpdate (n := n) beta (regularizedSignal (B := B) lambda2 x) i := by
  rw [regularizedSignal_lambda_invariant (B := B) lambda1 lambda2 x]

/--
Bayes router update on defect-regularized signals equals Bayes update
on canonical core signals.
-/
@[rep_depth transport]
theorem bayesRouterUpdate_regularizedSignal_eq_coreSignal
    (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (beta lambda : ℝ) (x : Tok → EndN) (i : Tok) :
    bayesRouterUpdate (n := n) beta (regularizedSignal (B := B) lambda x) i
      = bayesRouterUpdate (n := n) beta (coreSignal (B := B) x) i := by
  rw [regularizedSignal_eq_coreSignal (B := B) lambda x]

end OmitNonemptyFinN

end RouterRegularization

end InfoGeometry.LLM
