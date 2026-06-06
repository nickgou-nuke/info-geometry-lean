import Mathlib.Algebra.Colimit.Module
import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
import InfoGeometry.Canonical.LogCftMonodromyBridge

/-!
# InfoGeometry.Canonical.FibonacciHadjiivanovMonodromyBridge

Finite-to-infinite bridge surface for the Fibonacci braid tower and the
Hadjiivanov logarithmic monodromy lane.

This file records the algebraic direct-limit transport pattern explicitly.
It does not assert that the specific Fibonacci braid tower has already been
constructed in the repo, and it does not claim the exact identification of the
staged Fibonacci `B = F R F` family with the parafermion Hilbert-space
monodromy without the missing stage-family owner declarations.

The exact identification remains open owner debt; the bridge theorem below is
the generic direct-limit transport skeleton that such an instantiation will use.
-/

noncomputable section

namespace InfoGeometry.Canonical.FibonacciHadjiivanovMonodromyBridge

open Matrix

universe u

variable {Stage : ℕ → Type u}
variable [∀ n : ℕ, AddCommMonoid (Stage n)]

/-!
BUCKET 3: missing owner declarations:
- `InfoGeometry.Canonical.FiniteFibonacciBraidStage`
- debt type: construction
- needed for: the staged finite Fibonacci braid tower whose colimit should feed the monodromy lane
- `InfoGeometry.Canonical.ParafermionHilbertSpace`
- debt type: construction
- needed for: the target carrier on which the Hadjiivanov monodromy acts
-/

/--
Generic direct-limit transport skeleton for a staged braid family into the
Hadjiivanov monodromy target.

The specific Fibonacci instantiation is still open: it requires the missing
stage family and a compatibility theorem identifying the direct-limit cone with
the logarithmic monodromy action.
-/
theorem fibonacciBraidColimitActsAsHadjiivanovMonodromy
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)
    (toLimit : ∀ n : ℕ, Stage n →+ Matrix (Fin 2) (Fin 2) ℂ)
    (hcone : ∀ m n : ℕ, (h : m ≤ n) → (x : Stage m) →
      toLimit n (f m n h x) = toLimit m x) :
    ∃ lift : AddCommGroup.DirectLimit Stage f →+ Matrix (Fin 2) (Fin 2) ℂ,
      ∀ n : ℕ, ∀ x : Stage n,
        lift (AddCommGroup.DirectLimit.of Stage f n x) = toLimit n x := by
  refine ⟨AddCommGroup.DirectLimit.lift
      Stage f (Matrix (Fin 2) (Fin 2) ℂ) toLimit hcone, ?_⟩
  intro n x
  simpa using
    (AddCommGroup.DirectLimit.lift_of
      (G := Stage) (f := f) (P := Matrix (Fin 2) (Fin 2) ℂ) (g := toLimit) (Hg := hcone) n x)

end InfoGeometry.Canonical.FibonacciHadjiivanovMonodromyBridge
