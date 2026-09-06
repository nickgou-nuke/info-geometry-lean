import InfoGeometry.Canonical.Cl11StageTwoMatrixEquivalence
import InfoGeometry.Clifford.SplitCliffordTransformKernel
import InfoGeometry.Algebra.SplitCliffordTransformKernel

/-!
# Local elliptic, hyperbolic, and parabolic flows on native Stage 2

This file is only a Stage-2 adapter.  The algebraic kernel identities are
owned by `Clifford.SplitCliffordTransformKernel`; no second carrier or
exponential API is introduced here.
-/

namespace InfoGeometry.Canonical.Cl11LocalTrifactorFlows

open InfoGeometry.Canonical.Cl11StageTwoMatrixEquivalence
open InfoGeometry.Clifford.SplitCliffordTransformKernel

abbrev StageTwo := Cl11StageTwoMatrixEquivalence.StageTwo

noncomputable def ellipticFlow (J : StageTwo) (t : ℝ) : StageTwo :=
  InfoGeometry.Clifford.SplitCliffordTransformKernel.ellipticKernel J t

noncomputable def hyperbolicFlow (H : StageTwo) (t : ℝ) : StageTwo :=
  InfoGeometry.Clifford.SplitCliffordTransformKernel.hyperbolicKernel H t

def parabolicFlow (N : StageTwo) (t : ℝ) : StageTwo :=
  InfoGeometry.Clifford.SplitCliffordTransformKernel.parabolicKernel N t

@[simp] theorem ellipticFlow_zero (J : StageTwo) :
    ellipticFlow J 0 = 1 := by
  simpa [ellipticFlow] using
    InfoGeometry.Clifford.SplitCliffordTransformKernel.ellipticKernel_zero J

@[simp] theorem hyperbolicFlow_zero (H : StageTwo) :
    hyperbolicFlow H 0 = 1 := by
  simpa [hyperbolicFlow] using
    InfoGeometry.Clifford.SplitCliffordTransformKernel.hyperbolicKernel_zero H

@[simp] theorem parabolicFlow_zero (N : StageTwo) :
    parabolicFlow N 0 = 1 := by
  simpa [parabolicFlow] using
    InfoGeometry.Clifford.SplitCliffordTransformKernel.parabolicKernel_zero N

theorem ellipticFlow_add (J : StageTwo) (hJ : J * J = -1) (s t : ℝ) :
    ellipticFlow J (s + t) = ellipticFlow J s * ellipticFlow J t := by
  exact InfoGeometry.Clifford.SplitCliffordTransformKernel.ellipticKernel_add J hJ s t

theorem ellipticFlow_neg_mul (J : StageTwo) (hJ : J * J = -1) (t : ℝ) :
    ellipticFlow J t * ellipticFlow J (-t) = 1 := by
  exact InfoGeometry.Clifford.SplitCliffordTransformKernel.ellipticKernel_mul_neg J hJ t

theorem hyperbolicFlow_add (H : StageTwo) (hH : H * H = 1) (s t : ℝ) :
    hyperbolicFlow H (s + t) = hyperbolicFlow H s * hyperbolicFlow H t := by
  exact InfoGeometry.Clifford.SplitCliffordTransformKernel.hyperbolicKernel_add H hH s t

theorem hyperbolicFlow_neg_mul (H : StageTwo) (hH : H * H = 1) (t : ℝ) :
    hyperbolicFlow H t * hyperbolicFlow H (-t) = 1 := by
  exact InfoGeometry.Clifford.SplitCliffordTransformKernel.hyperbolicKernel_mul_neg H hH t

theorem parabolicFlow_add (N : StageTwo) (hN : N * N = 0) (s t : ℝ) :
    parabolicFlow N (s + t) = parabolicFlow N s * parabolicFlow N t := by
  exact InfoGeometry.Clifford.SplitCliffordTransformKernel.parabolicKernel_add N hN s t

theorem parabolicFlow_neg_mul (N : StageTwo) (hN : N * N = 0) (t : ℝ) :
    parabolicFlow N t * parabolicFlow N (-t) = 1 := by
  exact InfoGeometry.Clifford.SplitCliffordTransformKernel.parabolicKernel_mul_neg N hN t

noncomputable def loxodromicFlow (J H : StageTwo) (θ t : ℝ) : StageTwo :=
  _root_.SplitCliffordTransformKernel.loxodromicKernel J H θ t

theorem loxodromicFlow_add
    (J H : StageTwo) (hJ : J ^ 2 = -1) (hH : H ^ 2 = 1)
    (hcomm : Commute J H) (θ₁ θ₂ t₁ t₂ : ℝ) :
    loxodromicFlow J H (θ₁ + θ₂) (t₁ + t₂) =
      loxodromicFlow J H θ₁ t₁ * loxodromicFlow J H θ₂ t₂ := by
  letI : _root_.EllipticGenerator J := ⟨hJ⟩
  letI : _root_.HyperbolicGenerator H := ⟨hH⟩
  exact _root_.SplitCliffordTransformKernel.loxodromicKernel_add
    J H hcomm θ₁ θ₂ t₁ t₂

theorem loxodromicFlow_neg_mul
    (J H : StageTwo) (hJ : J ^ 2 = -1) (hH : H ^ 2 = 1)
    (hcomm : Commute J H) (θ t : ℝ) :
    loxodromicFlow J H (-θ) (-t) * loxodromicFlow J H θ t = 1 := by
  letI : _root_.EllipticGenerator J := ⟨hJ⟩
  letI : _root_.HyperbolicGenerator H := ⟨hH⟩
  exact _root_.SplitCliffordTransformKernel.loxodromicKernel_neg_mul
    J H hcomm θ t

end InfoGeometry.Canonical.Cl11LocalTrifactorFlows
