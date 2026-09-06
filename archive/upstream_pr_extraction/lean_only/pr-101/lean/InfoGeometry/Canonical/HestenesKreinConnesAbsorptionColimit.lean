import Mathlib
import InfoGeometry.Arithmetic.CenteredXiTwinKernel
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.HestenesKreinResolventColimit

/-!
# Finite absorption readouts on the Hestenes--Krein colimit

This owner formalizes the theorem-safe algebraic shadow of the absorption
picture: a smooth background minus a finite collection of notch readouts,
twin-wave parity, and a supplied cosine representation.  The scattering
quotient is treated as a totalized field quotient; at a paired zero it is
therefore an indeterminate `0 / 0` datum, not a theorem that a pole exists.

No distributional trace formula, adèle-class-space spectrum, analytic
continuation, or Riemann-Hypothesis conclusion is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinConnesAbsorptionColimit

open InfoGeometry.Arithmetic.CenteredXiTwinKernel
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.HestenesKreinResolventColimit
open InfoGeometry.Krein
open scoped BigOperators

/-! ## Signed finite absorption readouts -/

def signedAbsorptionReadout {ι : Type*}
    (background : ℝ) (marks : Finset ι) (notch : ι → ℝ) : ℝ :=
  background - ∑ i ∈ marks, notch i

@[simp] theorem signedAbsorptionReadout_empty {ι : Type*}
    (background : ℝ) (notch : ι → ℝ) :
    signedAbsorptionReadout background ∅ notch = background := by
  simp [signedAbsorptionReadout]

theorem signedAbsorptionReadout_eq_background_of_notch_zero
    {ι : Type*} (background : ℝ) (marks : Finset ι) (notch : ι → ℝ)
    (hnotch : ∀ i ∈ marks, notch i = 0) :
    signedAbsorptionReadout background marks notch = background := by
  unfold signedAbsorptionReadout
  have hsum : (∑ i ∈ marks, notch i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hnotch i hi
  rw [hsum, sub_zero]

def stageAbsorptionReadout {ι : Type*}
    {C : HestenesKreinCone} (background : ℝ) (marks : Finset ι)
    (notch : ∀ n, ι → DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  signedAbsorptionReadout background marks (fun i => notch n i x)

def limitAbsorptionReadout {ι : Type*}
    {C : HestenesKreinCone} (background : ℝ) (marks : Finset ι)
    (notch : ι → DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  signedAbsorptionReadout background marks (fun i => notch i x)

theorem stageAbsorptionReadout_eq_limit
    {ι : Type*} {C : HestenesKreinCone}
    (background : ℝ) (marks : Finset ι)
    (stageNotch : ∀ n, ι → DoubledSpace (C.Base n) → ℝ)
    (limitNotch : ι → DoubledSpace C.LimitBase → ℝ)
    (hnotch : ∀ n i x, stageNotch n i x = limitNotch i (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageAbsorptionReadout background marks stageNotch n x =
      limitAbsorptionReadout background marks limitNotch (C.ι n x) := by
  unfold stageAbsorptionReadout limitAbsorptionReadout
  apply congrArg (fun q : ℝ => background - q)
  apply Finset.sum_congr rfl
  intro i hi
  exact hnotch n i x

theorem stageAbsorptionReadout_bondIterate
    {ι : Type*} {C : HestenesKreinCone}
    (background : ℝ) (marks : Finset ι)
    (stageNotch : ∀ n, ι → DoubledSpace (C.Base n) → ℝ)
    (hnotch : ∀ n m i x,
      stageNotch (n + m) i
          (C.toFilteredPhaseCone.bondIterate n m x) = stageNotch n i x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageAbsorptionReadout background marks stageNotch (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) =
      stageAbsorptionReadout background marks stageNotch n x := by
  unfold stageAbsorptionReadout signedAbsorptionReadout
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact hnotch n m i x

/-! ## Twin-wave parity and the cosine nodal interface -/

def cosineTransform (Phi : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * ∫ y : ℝ, Phi y * Real.cos (t * y)

def cosineNode (Phi : ℝ → ℝ) (t : ℝ) : Prop :=
  cosineTransform Phi t = 0

theorem cosineNode_iff_integral_zero (Phi : ℝ → ℝ) (t : ℝ) :
    cosineNode Phi t ↔ ∫ y : ℝ, Phi y * Real.cos (t * y) = 0 := by
  unfold cosineNode cosineTransform
  constructor
  · intro h
    linarith
  · intro h
    simp [h]

theorem twinEven_weighted_eq_cosineIntegrand
    (Phi : ℝ → ℝ) (t y : ℝ) :
    Phi y * twinEven t y = 2 * (Phi y * Real.cos (t * y)) := by
  rw [twinEven_eq_two_cos]
  ring

theorem cosineNode_of_representation
    (Xi : ℝ → ℝ) (Phi : ℝ → ℝ)
    (hrepresentation : ∀ t, Xi t = cosineTransform Phi t)
    {γ : ℝ} (hzero : Xi γ = 0) :
    cosineNode Phi γ := by
  unfold cosineNode
  rw [← hrepresentation γ]
  exact hzero

theorem cosineNode_iff_representation_zero
    (Xi : ℝ → ℝ) (Phi : ℝ → ℝ)
    (hrepresentation : ∀ t, Xi t = cosineTransform Phi t)
    (γ : ℝ) :
    cosineNode Phi γ ↔ Xi γ = 0 := by
  unfold cosineNode
  rw [hrepresentation γ]

/-! ## The quotient at a functional-equation zero -/

def completedScatteringRatio (Xi : ℂ → ℂ) (s : ℂ) : ℂ :=
  Xi (1 - s) / Xi s

def scatteringZeroPair (Xi : ℂ → ℂ) (s : ℂ) : Prop :=
  Xi s = 0 ∧ Xi (1 - s) = 0

theorem scatteringZeroPair_is_zero_over_zero
    (Xi : ℂ → ℂ) {s : ℂ} (hpair : scatteringZeroPair Xi s) :
    Xi (1 - s) = 0 ∧ Xi s = 0 := by
  exact ⟨hpair.2, hpair.1⟩

theorem functionalSymmetry_scatteringZeroPair
    (Xi : ℂ → ℂ) (hfunctional : ∀ s, Xi (1 - s) = Xi s)
    {s : ℂ} (hzero : Xi s = 0) :
    scatteringZeroPair Xi s := by
  constructor
  · exact hzero
  · rw [hfunctional s]
    exact hzero

theorem completedScatteringRatio_at_zeroPair
    (Xi : ℂ → ℂ) {s : ℂ} (hpair : scatteringZeroPair Xi s) :
    completedScatteringRatio Xi s = 0 := by
  unfold completedScatteringRatio
  rw [hpair.1]
  simp

theorem completedScatteringRatio_eq_one_of_functionalSymmetry
    (Xi : ℂ → ℂ) (hfunctional : ∀ s, Xi (1 - s) = Xi s)
    {s : ℂ} (hs : Xi s ≠ 0) :
    completedScatteringRatio Xi s = 1 := by
  unfold completedScatteringRatio
  rw [hfunctional s]
  exact div_self hs

end InfoGeometry.Canonical.HestenesKreinConnesAbsorptionColimit

end noncomputable section
