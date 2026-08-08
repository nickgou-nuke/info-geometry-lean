import Mathlib.Algebra.Colimit.Module
import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
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
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

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
  simp only [
    (AddCommGroup.DirectLimit.lift_of
      (G := Stage) (f := f) (P := Matrix (Fin 2) (Fin 2) ℂ) (g := toLimit) (Hg := hcone) n x)]

/--
Stage-specialized Fibonacci-to-Hadjiivanov readout.

If a finite staged Fibonacci full-twist element is identified by the target
readout with the Hadjiivanov logarithmic monodromy matrix, then the algebraic
direct-limit class of that full twist has the same Hadjiivanov readout.

This is the strongest bridge currently supported by the existing owners.  The
construction of the concrete staged full-twist family and its analytic
identification with the parafermion monodromy remain the explicit debt listed
above.
-/
theorem fibonacciFullTwistColimit_maps_to_hadjiivanovMonodromy
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)
    (toLimit : ∀ n : ℕ, Stage n →+ Matrix (Fin 2) (Fin 2) ℂ)
    (hcone : ∀ m n : ℕ, (h : m ≤ n) → (x : Stage m) →
      toLimit n (f m n h x) = toLimit m x)
    (n : ℕ) (fullTwist : Stage n) (h : ℂ)
    (h_fullTwist :
      toLimit n fullTwist =
        InfoGeometry.Canonical.LogCftMonodromyBridge.hadjiivanovMonodromy h) :
    AddCommGroup.DirectLimit.lift
        Stage f (Matrix (Fin 2) (Fin 2) ℂ) toLimit hcone
        (AddCommGroup.DirectLimit.of Stage f n fullTwist) =
      InfoGeometry.Canonical.LogCftMonodromyBridge.hadjiivanovMonodromy h := by
  calc
    AddCommGroup.DirectLimit.lift
        Stage f (Matrix (Fin 2) (Fin 2) ℂ) toLimit hcone
        (AddCommGroup.DirectLimit.of Stage f n fullTwist) =
        toLimit n fullTwist := by
          simp only [
            (AddCommGroup.DirectLimit.lift_of
              (G := Stage) (f := f) (P := Matrix (Fin 2) (Fin 2) ℂ)
              (g := toLimit) (Hg := hcone) n fullTwist)]
    _ = InfoGeometry.Canonical.LogCftMonodromyBridge.hadjiivanovMonodromy h :=
      h_fullTwist

/--
Finite four-anyon matrix readout for the Fibonacci-to-Hadjiivanov bridge.

This theorem names the concrete finite matrix side already owned by
`FiniteFibonacciFusionMatrix`: the two-generator full-twist word
`R * B * R`, with `B = F R F`.  If a staged full-twist class reads out to this
finite matrix, and that matrix is identified with the Hadjiivanov logarithmic
monodromy matrix, then the direct-limit class has the Hadjiivanov readout.

The theorem deliberately keeps the analytic identification
`R * B * R = hadjiivanovMonodromy weight` as an explicit property.  Proving
that equality from parafermion conformal blocks is the remaining paper-level
owner debt, not something this transport lemma should fake.
-/
theorem finiteFourAnyonFullTwistColimit_maps_to_hadjiivanovMonodromy
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)
    (toLimit : ∀ n : ℕ, Stage n →+ Matrix (Fin 2) (Fin 2) ℂ)
    (hcone : ∀ m n : ℕ, (h : m ≤ n) → (x : Stage m) →
      toLimit n (f m n h x) = toLimit m x)
    (n : ℕ) (fullTwist : Stage n) (q : Units ℂ) (τ s weight : ℂ)
    (h_stage :
      toLimit n fullTwist =
        fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q)
    (h_matrix :
      fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
        InfoGeometry.Canonical.LogCftMonodromyBridge.hadjiivanovMonodromy weight) :
    AddCommGroup.DirectLimit.lift
        Stage f (Matrix (Fin 2) (Fin 2) ℂ) toLimit hcone
        (AddCommGroup.DirectLimit.of Stage f n fullTwist) =
      InfoGeometry.Canonical.LogCftMonodromyBridge.hadjiivanovMonodromy weight :=
  fibonacciFullTwistColimit_maps_to_hadjiivanovMonodromy
    (f := f) (toLimit := toLimit) (hcone := hcone) n fullTwist weight
    (h_stage.trans h_matrix)

end InfoGeometry.Canonical.FibonacciHadjiivanovMonodromyBridge
