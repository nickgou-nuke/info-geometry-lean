import InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNet
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState
import InfoGeometry.Prequantum.GNSBridge

/-!
# Algebraic GNS readout for the finite real trace stages

This owner rewraps the already proved finite normalized trace as the native
abstract GNS state.  The resulting quotient is algebraic only; no Hilbert
completion, bounded representation, or von Neumann closure is claimed.
-/

namespace InfoGeometry.Canonical.Cl11FiniteTraceGNSReadout

open InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNet
open InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Prequantum.GNSBridge
open InfoGeometry.Prequantum.GNSBridge.AbstractGNSState

noncomputable section

noncomputable def cl11AbstractGNSState (n : ℕ) :
    AbstractGNSState (MatStage n) :=
  atStage
    cl11CompatibleRealAlgebraicStateNet n (by
      intro X Y
      simpa [state_eq_normalizedTrace] using
        (normalizedTraceState n).symmetric X Y)

abbrev cl11GNSQuotient (n : ℕ) : Type _ :=
  AbstractGNSState.gnsQuotient (cl11AbstractGNSState n)

@[simp] theorem cl11AbstractGNSState_eval
    (n : ℕ) (X : MatStage n) :
    (cl11AbstractGNSState n).eval X = normalizedTrace n X := by
  change cl11CompatibleRealAlgebraicStateNet.state n X = normalizedTrace n X
  exact state_eq_normalizedTrace n X

theorem cl11AbstractGNSState_normalized
    (n : ℕ) :
    (cl11AbstractGNSState n).eval (1 : MatStage n) = 1 := by
  exact AbstractGNSState.eval_one (cl11AbstractGNSState n)

theorem cl11AbstractGNSState_positive
    (n : ℕ) (X : MatStage n) :
    0 ≤ (cl11AbstractGNSState n).state.eval (star X * X) := by
  exact (cl11AbstractGNSState n).state.positive X

theorem cl11AbstractGNSState_zero_null
    (n : ℕ) :
    (0 : MatStage n) ∈ (cl11AbstractGNSState n).gnsNullSet := by
  exact AbstractGNSState.zero_mem_gnsNullSet (cl11AbstractGNSState n)

end

end InfoGeometry.Canonical.Cl11FiniteTraceGNSReadout
