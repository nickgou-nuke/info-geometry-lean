import InfoGeometry.Analysis.BipolarLoopLiftHomotopyInvariant
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Homotopy invariance of the bipolar deck-pair readout

The two entries of `bipolarLiftEndpointPair` are endpoint translations of
native lifts through the exponential covering.  This file records the exact
invariance statement available from the covering API: if the transformed
paths are homotopic relative to their endpoints, then the corresponding deck
integers agree.  It does not identify this readout with a global homology
classification.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarLoopWindingHomotopyBridge

open Complex Topology
open InfoGeometry.Analysis.BipolarAdmissibleLoops
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarNativeExpCoveringBridge
open InfoGeometry.Analysis.BipolarLoopCrossRatioLift
open InfoGeometry.Analysis.BipolarLoopWindingCarrier
open InfoGeometry.Analysis.BipolarLoopLiftHomotopyInvariant

abbrev NonzeroComplex := {z : ℂ // z ≠ 0}

theorem bipolarLiftEndpointPair_eq_of_transformed_homotopicRel
    {γ₀ γ₁ : AdmissibleLoop}
    (hbase : γ₀.base = γ₁.base)
    (hcross :
      (crossRatioPath γ₀ : C(↑unitInterval, NonzeroComplex)).HomotopicRel
        (crossRatioPath γ₁ : C(↑unitInterval, NonzeroComplex)) {0, 1})
    (hshift :
      (shiftedPath γ₀ : C(↑unitInterval, NonzeroComplex)).HomotopicRel
        (shiftedPath γ₁ : C(↑unitInterval, NonzeroComplex)) {0, 1}) :
    bipolarLiftEndpointPair γ₀ = bipolarLiftEndpointPair γ₁ := by
  rcases γ₀ with ⟨b₀, p₀, hp₀, ha₀⟩
  rcases γ₁ with ⟨b₁, p₁, hp₁, ha₁⟩
  dsimp at hbase hcross hshift ⊢
  cases hbase
  let γ₀' : AdmissibleLoop := ⟨b₀, p₀, hp₀, ha₀⟩
  let γ₁' : AdmissibleLoop := ⟨b₀, p₁, hp₁, ha₁⟩
  have hb : b₀ ∈ InfoGeometry.Analysis.BipolarCrossRatioLog.punctured01 := by
    simpa [p₀.source] using ha₀ ⟨(0 : unitInterval), rfl⟩
  have hcross₀ :
      bipolarCrossRatioMap (basePoint γ₀') =
        (⟨Complex.exp (bipolarLog b₀), Complex.exp_ne_zero _⟩ : NonzeroComplex) := by
    apply Subtype.ext
    change crossRatio01 b₀ = Complex.exp (bipolarLog b₀)
    exact (exp_bipolarLog hb).symm
  have hcross₁ :
      bipolarCrossRatioMap (basePoint γ₁') =
        (⟨Complex.exp (bipolarLog b₀), Complex.exp_ne_zero _⟩ : NonzeroComplex) := by
    apply Subtype.ext
    change crossRatio01 b₀ = Complex.exp (bipolarLog b₀)
    exact (exp_bipolarLog hb).symm
  have hshift₀ :
      shiftedBasePoint γ₀' =
        (⟨Complex.exp (Complex.log (b₀ - 1)), Complex.exp_ne_zero _⟩ : NonzeroComplex) := by
    apply Subtype.ext
    change b₀ - 1 = Complex.exp (Complex.log (b₀ - 1))
    exact (Complex.exp_log (sub_ne_zero.mpr hb.2)).symm
  have hshift₁ :
      shiftedBasePoint γ₁' =
        (⟨Complex.exp (Complex.log (b₀ - 1)), Complex.exp_ne_zero _⟩ : NonzeroComplex) := by
    apply Subtype.ext
    change b₀ - 1 = Complex.exp (Complex.log (b₀ - 1))
    exact (Complex.exp_log (sub_ne_zero.mpr hb.2)).symm
  apply Prod.ext
  · apply liftEndpointInteger_eq_of_homotopicRel hcross
      (bipolarLog b₀)
    · exact hcross₀
    · exact hcross₁
  · apply liftEndpointInteger_eq_of_homotopicRel hshift
      (Complex.log (b₀ - 1))
    · exact hshift₀
    · exact hshift₁

end InfoGeometry.Analysis.BipolarLoopWindingHomotopyBridge
