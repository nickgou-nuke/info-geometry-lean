import InfoGeometry.Algebra.ThompsonBraidedCoherenceBridge
import InfoGeometry.Algebra.CuntzConditionalExpectation
import InfoGeometry.Algebra.G2TwistedBraiding

/-!
# Cantor Twisted Thompson Coherence

This file completes the `G = (C, ⊗, α, c, θ, R, T)` datum by attaching the
Cuntz-Cantor tensor tree `T` and the topological framing/twist `θ` to the
Thompson-Braided coherence bridge.

Here:
1. `T` is the Cuntz tree structure (Cuntz algebra generators).
2. `R` is precisely the Cuntz conditional expectation mapping to the diagonal.
3. `θ` is the G₂-style third-root twist ensuring frame orientability.
-/

noncomputable section

namespace InfoGeometry.Algebra.CantorThompsonBridge

open InfoGeometry.Algebra.ThompsonBraidedCoherenceBridge
open InfoGeometry.Algebra.CuntzConditionalExpectation
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.G2

/--
The full coherence geometry over a Cuntz-Cantor tensor tree.
It instantiates the abstract `R` with the concrete `CuntzConditionalExpectation`
and introduces the `θ` twist.
-/
def CantorTwistedThompsonCoherenceLaws (n N : ℕ)
    (baseCoherence : ThompsonBraidedCoherence (CuntzAlg n) N)
    (framingTwist : G2TwistedSystem (Fin N)) : Prop :=
  baseCoherence.coarseGraining = expectation n ∧
    ∀ (x : CuntzAlg n) (i j : Fin N),
      baseCoherence.coarseGraining (framingTwist.val i j • x) =
        framingTwist.val i j • baseCoherence.coarseGraining x

def CantorTwistedThompsonCoherence (n N : ℕ) :=
  {p : ThompsonBraidedCoherence (CuntzAlg n) N × G2TwistedSystem (Fin N) //
    CantorTwistedThompsonCoherenceLaws n N p.1 p.2}

def CantorTwistedThompsonCoherence.baseCoherence
    {n N : ℕ} (A : CantorTwistedThompsonCoherence n N) :
    ThompsonBraidedCoherence (CuntzAlg n) N := A.1.1

def CantorTwistedThompsonCoherence.framingTwist
    {n N : ℕ} (A : CantorTwistedThompsonCoherence n N) :
    G2TwistedSystem (Fin N) := A.1.2

theorem CantorTwistedThompsonCoherence.coarseGraining_eq_cuntzExpectation
    {n N : ℕ} (A : CantorTwistedThompsonCoherence n N) :
    A.baseCoherence.coarseGraining = expectation n := A.2.1

theorem CantorTwistedThompsonCoherence.twist_coherence
    {n N : ℕ} (A : CantorTwistedThompsonCoherence n N)
    (x : CuntzAlg n) (i j : Fin N) :
    A.baseCoherence.coarseGraining (A.framingTwist.val i j • x) =
      A.framingTwist.val i j • A.baseCoherence.coarseGraining x := A.2.2 x i j

end InfoGeometry.Algebra.CantorThompsonBridge
