import InfoGeometry.Canonical.FiniteFibonacciHigherAnyonBraiding

/-!
# InfoGeometry.Canonical.FiniteFibonacciHigherAnyonPaperBridge

Paper-facing finite bridge for higher Fibonacci anyon braiding.

The paper's Section 5 describes a recursive basis of `n`-point Fibonacci
conformal blocks by admissible Bratteli paths.  This file keeps only the
finite combinatorial/algebraic content already owned by the repository:

* admissible `0/1` path codes with no consecutive zeros;
* the Fibonacci direct-sum recurrence for the recursive basis codes;
* the local `010`, `011`, `110`, and `1 _ 1` braid-block classification;
* the local singlet/doublet phase or matrix readout;
* independence of the doublet readout from the number of electron triples.

No conformal blocks.
No recursive monodromy matrices.
No analytic continuation.
No Artin theorem for all `n`.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciHigherAnyonPaperBridge

open InfoGeometry.Canonical.FiniteFibonacciHigherAnyonBraiding
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Canonical.FiniteFibonacciElectronIndependence

/-- A finite Fibonacci path code has no consecutive zero labels. -/
theorem finiteFibonacciPathCode_noConsecutiveZero {m : ℕ} (α : Fin m → SectorLabel)
    (hα : NoConsecutiveZero α) :
    NoConsecutiveZero α :=
  hα

/-- The finite admissible path code is precisely the no-consecutive-zero condition. -/
def finiteFibonacciPathCode_admissible {m : ℕ} (α : Fin m → SectorLabel)
    (hα : NoConsecutiveZero α) : FibonacciPathCode m :=
  ⟨α, hα⟩

/-- The recursive basis has the direct-sum shape `Vₖ₊₂ = Vₖ ⊕ Vₖ₊₁`. -/
theorem finiteRecursiveBasis_step (k : ℕ) :
    RecursiveFibonacciBlockBasis (k + 2) =
      (RecursiveFibonacciBlockBasis k ⊕ RecursiveFibonacciBlockBasis (k + 1)) :=
  recursiveBasis_step k

/-- The recursive dimension counter satisfies the Fibonacci recurrence. -/
theorem finiteRecursiveFibonacciDimension_step (k : ℕ) :
    recursiveFibonacciDimension (k + 2) =
      recursiveFibonacciDimension k + recursiveFibonacciDimension (k + 1) :=
  recursiveFibonacciDimension_step k

/-- A locally admissible triple with left endpoint `0` is classified as the `010` singlet. -/
theorem finiteLocalBraidBlockKind_of_zero_zero
    {middle : SectorLabel} (h : TripleAdmissible false middle false) :
    localBraidBlockKind false middle false = LocalBraidBlockKind.singletQNegFour :=
  localBraidBlockKind_of_zero_zero h

/-- A locally admissible triple with endpoints `0` and `1` is classified as `011`. -/
theorem finiteLocalBraidBlockKind_of_zero_one
    {middle : SectorLabel} (h : TripleAdmissible false middle true) :
    localBraidBlockKind false middle true = LocalBraidBlockKind.singletQThree :=
  localBraidBlockKind_of_zero_one h

/-- A locally admissible triple with endpoints `1` and `0` is classified as `110`. -/
theorem finiteLocalBraidBlockKind_of_one_zero
    {middle : SectorLabel} (h : TripleAdmissible true middle false) :
    localBraidBlockKind true middle false = LocalBraidBlockKind.singletQThree :=
  localBraidBlockKind_of_one_zero h

/-- A locally admissible triple with endpoints `1` and `1` is the doublet `1 _ 1` block. -/
theorem finiteLocalBraidBlockKind_of_one_one (middle : SectorLabel) :
    localBraidBlockKind true middle true = LocalBraidBlockKind.doubletB :=
  localBraidBlockKind_of_one_one middle

/-- The local `010` singlet carries the `q⁻⁴` phase. -/
theorem finiteLocalSingletPhase_qNegFour (q : Units ℂ) :
    localSingletPhase q LocalBraidBlockKind.singletQNegFour = some (q ^ (-4 : ℤ)) :=
  rfl

/-- The local `011` and `110` singlet carries the `q³` phase. -/
theorem finiteLocalSingletPhase_qThree (q : Units ℂ) :
    localSingletPhase q LocalBraidBlockKind.singletQThree = some (q ^ (3 : ℤ)) :=
  rfl

/-- The local doublet readout is the same `B = F R F` matrix used for four anyons. -/
theorem finiteLocalDoubletMatrix_doublet (q : Units ℂ) (τ root : ℂ) :
    localDoubletMatrix q τ root LocalBraidBlockKind.doubletB =
      some (fibonacciFusionMatrix τ root * fibonacciRMatrix q * fibonacciFusionMatrix τ root) :=
  localDoubletMatrix_doublet q τ root

/-- Electron triples do not affect the local doublet braid block. -/
theorem finiteLocalDoubletMatrix_independent_of_r
    (r s : ℕ) (q : Units ℂ) (τ root : ℂ) :
    (some (fibonacciBMatrixWithElectrons r q τ root) :
        Option (Matrix ChannelIndex ChannelIndex ℂ)) =
      some (fibonacciBMatrixWithElectrons s q τ root) := by
  simpa using localDoubletMatrix_independent_of_r r s q τ root

/-- The four-anyon `B = F R F` block is the local doublet readout used for higher `n`. -/
theorem finiteHigherAnyonLocalDoubletMatrix_eq_FRF (q : Units ℂ) (τ root : ℂ) :
    localDoubletMatrix q τ root LocalBraidBlockKind.doubletB =
      some (fibonacciFusionMatrix τ root * fibonacciRMatrix q * fibonacciFusionMatrix τ root) :=
  finiteLocalDoubletMatrix_doublet q τ root

end InfoGeometry.Canonical.FiniteFibonacciHigherAnyonPaperBridge
