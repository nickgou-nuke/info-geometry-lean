import Mathlib
import InfoGeometry.Canonical.NPotentOperatorEigenspaceBridge

/-!
# General `N`-potent invariant carriers

This is the `N`-potent analogue of the tripotent horizon packet.  For
`T ^ N = T`, the canonical zero-mode projector is
`P₀⁽ᴺ⁾ = 1 - T ^ (N - 1)`.  The packet records only finite algebraic
commutation and restriction statements; it makes no analytic, braid, or KMS
claim by itself.
-/

noncomputable section

namespace InfoGeometry.Physics.Algebra

open InfoGeometry.Canonical.NPotentOperatorEigenspaceBridge

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A family of endomorphisms sharing the zero-mode carrier of an `N`-potent
operator. -/
structure NPotentInvariantPacket (V : Type*) [AddCommGroup V] [Module ℂ V] where
  N : ℕ
  N_ge_two : 2 ≤ N
  T : Module.End ℂ V
  nPotent : IsNPotent N T
  action : Type*
  operator : action → Module.End ℂ V
  commutes_zero : ∀ a,
    operator a * nPotentZeroProjector N T =
      nPotentZeroProjector N T * operator a

abbrev NPotentHorizonCarrier (P : NPotentInvariantPacket V) : Submodule ℂ V :=
  LinearMap.ker P.T

theorem nPotent_horizonCarrier_eq_projector_range
    (P : NPotentInvariantPacket V) :
    NPotentHorizonCarrier P =
      LinearMap.range (nPotentZeroProjector P.N P.T) := by
  exact (nPotentZeroProjector_range_eq_ker P.N P.N_ge_two P.T P.nPotent).symm

/-- Every packet action preserves the canonical zero-mode carrier. -/
theorem nPotent_action_preserves_horizon
    (P : NPotentInvariantPacket V) (a : P.action) :
    ∀ x, x ∈ NPotentHorizonCarrier P →
      P.operator a x ∈ NPotentHorizonCarrier P := by
  intro x hx
  have hxP : nPotentZeroProjector P.N P.T x = x :=
    nPotent_zeroProjector_apply_of_mem_ker P.N P.N_ge_two P.T x hx
  have hcomm := congrArg (fun F : Module.End ℂ V => F x) (P.commutes_zero a)
  have hcomm_apply :
      nPotentZeroProjector P.N P.T (P.operator a x) =
        P.operator a (nPotentZeroProjector P.N P.T x) := by
    simpa only [Module.End.mul_apply] using hcomm.symm
  rw [LinearMap.mem_ker]
  have hzero : P.T * nPotentZeroProjector P.N P.T = 0 :=
    nPotent_mul_zeroProjector P.N P.N_ge_two P.T P.nPotent
  calc
    P.T (P.operator a x) =
        P.T (nPotentZeroProjector P.N P.T (P.operator a x)) := by
          rw [hcomm_apply, hxP]
    _ = (P.T * nPotentZeroProjector P.N P.T) (P.operator a x) := rfl
    _ = 0 := by rw [hzero]; simp

/-- The action restricted to the `N`-potent zero-mode carrier. -/
def nPotentRestrictedAction
    (P : NPotentInvariantPacket V) (a : P.action) :
    Module.End ℂ (NPotentHorizonCarrier P) :=
  LinearMap.restrict (P.operator a) (nPotent_action_preserves_horizon P a)

@[simp] theorem nPotentRestrictedAction_apply
    (P : NPotentInvariantPacket V) (a : P.action)
    (x : NPotentHorizonCarrier P) :
    (nPotentRestrictedAction P a x : V) = P.operator a x := rfl

theorem sixPotent_horizonCarrier_eq_projector_range
    (P : NPotentInvariantPacket V) (hN : P.N = 6) :
    NPotentHorizonCarrier P =
      LinearMap.range (1 - P.T ^ 5) := by
  simpa [hN, nPotentZeroProjector]
    using nPotent_horizonCarrier_eq_projector_range P

theorem tripotent_horizonCarrier_eq_projector_range
    (P : NPotentInvariantPacket V) (hN : P.N = 3) :
    NPotentHorizonCarrier P =
      LinearMap.range (1 - P.T ^ 2) := by
  simpa [hN, nPotentZeroProjector]
    using nPotent_horizonCarrier_eq_projector_range P

end InfoGeometry.Physics.Algebra
