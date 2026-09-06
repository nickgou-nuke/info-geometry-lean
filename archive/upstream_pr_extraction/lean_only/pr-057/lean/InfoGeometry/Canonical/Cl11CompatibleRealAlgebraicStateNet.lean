import InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState
import InfoGeometry.Prequantum.AlgebraicGNSState
import InfoGeometry.Clifford.Cl11MarkovJonesEngine

/-!
# Compatible real algebraic states on the split Clifford matrix tower

This owner packages the already proved finite normalized traces as the
repository's existing `CompatibleAlgebraicStateNet`.  It makes no claim about
an analytic completion, a C*-algebraic state space, or K-theory.
-/

namespace InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNet

open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Meta.MarkovJonesInduction

noncomputable section

/-- Positivity of the concrete Markov trace on the tower. -/
theorem cl11MarkovTraceNet_positive
    (n : ℕ) (A : MatStage n) :
    0 ≤ cl11MarkovTraceNet.trace n (star A * A) := by
  simpa [cl11MarkovTraceNet_apply] using
    (Cl11FiniteNormalizedTraceState.normalizedTraceState_positive n A)

/-- The normalized trace as a compatible algebraic state net. -/
def cl11CompatibleRealAlgebraicStateNet :
    CompatibleAlgebraicStateNet cl11InductiveAlgebraNet :=
  CompatibleAlgebraicStateNet.ofMarkovTraceNet
    cl11MarkovTraceNet
    (by
      intro n A
      exact cl11MarkovTraceNet_positive n A)

@[simp] theorem state_eq_markovTrace
    (n : ℕ) (A : MatStage n) :
    cl11CompatibleRealAlgebraicStateNet.state n A =
      cl11MarkovTraceNet.trace n A := by
  rfl

@[simp] theorem state_eq_normalizedTrace
    (n : ℕ) (A : MatStage n) :
    cl11CompatibleRealAlgebraicStateNet.state n A =
      normalizedTrace n A := by
  rw [state_eq_markovTrace]
  exact cl11MarkovTraceNet_apply n A

theorem state_is_finite_normalized_trace
    (n : ℕ) :
    cl11CompatibleRealAlgebraicStateNet.state n =
      (Cl11FiniteNormalizedTraceState.normalizedTraceState n).toLinearMap := by
  ext A
  rfl

theorem stable_one_step
    (n : ℕ) (A : MatStage n) :
    cl11CompatibleRealAlgebraicStateNet.state (n + 1)
        (cl11InductiveAlgebraNet.embed n A) =
      cl11CompatibleRealAlgebraicStateNet.state n A := by
  exact cl11CompatibleRealAlgebraicStateNet.stable_one_step n A

theorem stable_embedMap
    (m n : ℕ) (h : m ≤ n) (A : MatStage m) :
    cl11CompatibleRealAlgebraicStateNet.state n
        (cl11InductiveAlgebraNet.embedMap m n h A) =
      cl11CompatibleRealAlgebraicStateNet.state m A := by
  exact cl11CompatibleRealAlgebraicStateNet.stable_embedMap m n h A

end

end InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNet
