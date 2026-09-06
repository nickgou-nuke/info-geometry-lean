import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Algebra.Basic

/-!
SANDBOX: AlgHom Construction
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "EndH" => E →L[ℝ] E

/-- Test Construction -/
def testAlgHom : ℝ →ₐ[ℝ] EndH :=
  Algebra.ofId ℝ EndH

/-- Another Test -/
def testAlgHomComp : ℝ →ₐ[ℝ] EndH :=
  (Algebra.ofId ℝ EndH).comp (Algebra.ofId ℝ ℝ)
