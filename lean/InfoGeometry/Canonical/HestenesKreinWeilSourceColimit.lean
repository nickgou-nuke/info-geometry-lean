import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport
import InfoGeometry.Spectral.WeilPositivityGNSBridge

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinWeilSourceColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Krein

variable {C : HestenesKreinCone}

theorem stageReadout_eq_limitReadout
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, stageReadout n x = limitReadout (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageReadout n x = limitReadout (C.ι n x) :=
  hreadout n x

theorem stageReadout_bond
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, stageReadout n x = limitReadout (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageReadout (n + 1) (C.bond n x) = stageReadout n x := by
  rw [hreadout (n + 1), hreadout n]
  exact congrArg (fun f => limitReadout (f x)) (C.ι_bond n)

theorem stageReadout_bondIterate
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, stageReadout n x = limitReadout (C.ι n x))
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageReadout (n + m) (C.toFilteredPhaseCone.bondIterate n m x) =
      stageReadout n x := by
  rw [hreadout (n + m), hreadout n]
  exact congrArg limitReadout
    (C.toFilteredPhaseCone.ι_bondIterate_apply n m x)

def selfConvolutionValue
    {TestFunction : Type*}
    (convolution : TestFunction → TestFunction → TestFunction)
    (star : TestFunction → TestFunction)
    (weil : TestFunction → ℝ)
    (g : TestFunction) : ℝ :=
  weil (convolution g (star g))

theorem selfConvolutionValue_eq_stageReadout
    {TestFunction : Type*}
    (convolution : TestFunction → TestFunction → TestFunction)
    (star : TestFunction → TestFunction)
    (weil : TestFunction → ℝ)
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (testStage : ∀ n, TestFunction → DoubledSpace (C.Base n))
    (hkernel : ∀ n g,
      selfConvolutionValue convolution star weil g = stageReadout n (testStage n g))
    (n : ℕ) (g : TestFunction) :
    selfConvolutionValue convolution star weil g = stageReadout n (testStage n g) :=
  hkernel n g

theorem sourceWeil_positive_of_limitReadout
    {TestFunction : Type*}
    (convolution : TestFunction → TestFunction → TestFunction)
    (star : TestFunction → TestFunction)
    (weil : TestFunction → ℝ)
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (testStage : ∀ n, TestFunction → DoubledSpace (C.Base n))
    (hreadout : ∀ n x, stageReadout n x = limitReadout (C.ι n x))
    (hkernel : ∀ n g,
      selfConvolutionValue convolution star weil g = stageReadout n (testStage n g))
    (hpositive : ∀ x, 0 ≤ limitReadout x)
    (g : TestFunction) :
    0 ≤ weil (convolution g (star g)) := by
  change 0 ≤ selfConvolutionValue convolution star weil g
  rw [hkernel 0 g, hreadout 0]
  exact hpositive _

theorem sourceWeil_positive_of_stageReadout
    {TestFunction : Type*}
    (convolution : TestFunction → TestFunction → TestFunction)
    (star : TestFunction → TestFunction)
    (weil : TestFunction → ℝ)
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (testStage : ∀ n, TestFunction → DoubledSpace (C.Base n))
    (hkernel : ∀ n g,
      selfConvolutionValue convolution star weil g = stageReadout n (testStage n g))
    (hpositive : ∀ n x, 0 ≤ stageReadout n x)
    (g : TestFunction) :
    0 ≤ weil (convolution g (star g)) := by
  change 0 ≤ selfConvolutionValue convolution star weil g
  rw [hkernel 0 g]
  exact hpositive 0 _

theorem sourceWeil_positive
    {TestFunction : Type*}
    (convolution : TestFunction → TestFunction → TestFunction)
    (star : TestFunction → TestFunction)
    (weil : TestFunction → ℝ)
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (testStage : ∀ n, TestFunction → DoubledSpace (C.Base n))
    (hkernel : ∀ n g,
      selfConvolutionValue convolution star weil g = stageReadout n (testStage n g))
    (hpositive : ∀ n x, 0 ≤ stageReadout n x) :
    ∀ g : TestFunction, 0 ≤ weil (convolution g (star g)) := by
  intro g
  exact sourceWeil_positive_of_stageReadout convolution star weil stageReadout
    testStage hkernel hpositive g

end InfoGeometry.Canonical.HestenesKreinWeilSourceColimit

end noncomputable section
