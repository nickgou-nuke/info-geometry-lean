import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Spectral.WeilPositivityCriterion
import InfoGeometry.Canonical.HestenesKreinWeilSourceColimit

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinWeilCriterionColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.HestenesKreinWeilSourceColimit
open InfoGeometry.Krein

variable {C : HestenesKreinCone}

def colimitWeilPositive
    (limitReadout : DoubledSpace C.LimitBase → ℝ) : Prop :=
  ∀ x, 0 ≤ limitReadout x

theorem weilPositive_of_colimitReadout
    {TestFunction : Type*}
    (convolution : TestFunction → TestFunction → TestFunction)
    (star : TestFunction → TestFunction)
    (weil : TestFunction → ℝ)
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (testStage : ∀ n, TestFunction → DoubledSpace (C.Base n))
    (hreadout : ∀ n x, stageReadout n x = limitReadout (C.ι n x))
    (hkernel : ∀ n g,
      weil (convolution g (star g)) = stageReadout n (testStage n g))
    (hpositive : colimitWeilPositive limitReadout) :
    ∀ g : TestFunction, 0 ≤ weil (convolution g (star g)) := by
  intro g
  rw [hkernel 0 g, hreadout 0]
  exact hpositive _

theorem rh_of_colimitReadout
    {TestFunction : Type*}
    (convolution : TestFunction → TestFunction → TestFunction)
    (star : TestFunction → TestFunction)
    (weil : TestFunction → ℝ)
    (RH : Prop)
    (criterion : RH ↔
      ∀ f : TestFunction, 0 ≤ weil (convolution f (star f)))
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (testStage : ∀ n, TestFunction → DoubledSpace (C.Base n))
    (hreadout : ∀ n x, stageReadout n x = limitReadout (C.ι n x))
    (hkernel : ∀ n g,
      weil (convolution g (star g)) = stageReadout n (testStage n g))
    (hpositive : colimitWeilPositive limitReadout) :
    RH := by
  apply criterion.mpr
  exact weilPositive_of_colimitReadout convolution star weil stageReadout
    limitReadout testStage hreadout hkernel hpositive

theorem colimitReadout_of_rh
    {TestFunction : Type*}
    (RH : Prop)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (hRH : RH)
    (hpositive_of_rh : RH → colimitWeilPositive limitReadout) :
    colimitWeilPositive limitReadout :=
  hpositive_of_rh hRH

theorem rh_iff_colimitReadout
    {TestFunction : Type*}
    (convolution : TestFunction → TestFunction → TestFunction)
    (star : TestFunction → TestFunction)
    (weil : TestFunction → ℝ)
    (RH : Prop)
    (criterion : RH ↔
      ∀ f : TestFunction, 0 ≤ weil (convolution f (star f)))
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (testStage : ∀ n, TestFunction → DoubledSpace (C.Base n))
    (hreadout : ∀ n x, stageReadout n x = limitReadout (C.ι n x))
    (hkernel : ∀ n g,
      weil (convolution g (star g)) = stageReadout n (testStage n g))
    (hpositive_of_rh : RH → colimitWeilPositive limitReadout) :
    RH ↔ colimitWeilPositive limitReadout := by
  constructor
  · exact hpositive_of_rh
  · intro hpositive
    exact rh_of_colimitReadout convolution star weil RH criterion stageReadout
      limitReadout testStage hreadout hkernel hpositive

end InfoGeometry.Canonical.HestenesKreinWeilCriterionColimit

end noncomputable section
