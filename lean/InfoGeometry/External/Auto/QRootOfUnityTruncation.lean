import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite root-of-unity truncation stages

This file isolates the theorem-honest finite content of the root-of-unity
layer.  It models the finite `k`-stage directly:

* states are `Fin k`;
* admissible levels are exactly natural numbers below `k`;
* the endpoint level `k` is not admissible, so only the first `k` levels remain;
* the parity sign has square `1`;
* the state space has exactly `k` elements.

This is the finite combinatorial stage used by the q-super Rosetta layer.
-/

noncomputable section

namespace QRootOfUnityTruncation

/-- A finite q/root-of-unity stage with `k > 0` allowed levels. -/
structure RootOfUnityStage where
  k : ℕ
  positive : 0 < k

namespace RootOfUnityStage

/-- The finite state space of a root-of-unity truncation stage. -/
abbrev State (S : RootOfUnityStage) := Fin S.k

instance (S : RootOfUnityStage) : Fintype S.State := inferInstance
instance (S : RootOfUnityStage) : DecidableEq S.State := inferInstance

/-- Natural-number levels admissible at this finite stage. -/
def Admissible (S : RootOfUnityStage) (n : ℕ) : Prop := n < S.k

/-- The finite signed metric/parity readout on the truncated ladder. -/
def paritySign (_S : RootOfUnityStage) (n : _S.State) : ℤ :=
  if n.val % 2 = 0 then 1 else -1

/-- The finite state space has exactly `k` states. -/
theorem state_card (S : RootOfUnityStage) : Fintype.card S.State = S.k := by
  dsimp [State]
  simp

/-- The first excluded endpoint level is not admissible. -/
theorem boundary_not_admissible (S : RootOfUnityStage) : ¬ S.Admissible S.k := by
  exact Nat.lt_irrefl S.k

/-- The parity/signature readout is involutive at every finite level. -/
theorem paritySign_sq (S : RootOfUnityStage) (n : S.State) :
    S.paritySign n * S.paritySign n = 1 := by
  unfold paritySign
  split <;> norm_num

/-- Capstone: finite root-of-unity stages are finite, exclude their endpoint, and carry
an involutive signed metric. -/
theorem finite_root_of_unity_truncation_synthesis (S : RootOfUnityStage) :
    Fintype.card S.State = S.k ∧
    ¬ S.Admissible S.k ∧
    (∀ n : S.State, S.paritySign n * S.paritySign n = 1) := by
  constructor
  · exact state_card S
  constructor
  · exact boundary_not_admissible S
  · intro n
    exact paritySign_sq S n

end RootOfUnityStage

end QRootOfUnityTruncation

end noncomputable section
