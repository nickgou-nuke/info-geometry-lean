/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitSpinFactorTKKInjectivityNative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitSpinFactorTKKSO66
import InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66
import InfoGeometry.Canonical.SplitSpinFactorHomothetySO55
import InfoGeometry.Canonical.SplitOctonionTKKFiniteDimensionalBridges

noncomputable section

/-! Compatibility path for the native parameter-injectivity owner. -/
namespace InfoGeometry.Canonical.SplitSpinFactorTKKInjectivity

open InfoGeometry.Canonical.SplitSpinFactorTKKInjectivityNative
open InfoGeometry.Canonical.SplitSpinFactorTKKSO66
open InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66
open InfoGeometry.Canonical.SplitSpinFactorHomothetySO55
open InfoGeometry.Canonical.SplitOctonionTKKFiniteDimensionalBridges

abbrev V10 := SplitSpinFactorTKKInjectivityNative.V10
abbrev B10SkewEnd := SplitSpinFactorTKKInjectivityNative.B10SkewEnd
abbrev tkkParamMap := SplitSpinFactorTKKInjectivityNative.tkkParamMap

theorem tkkParamMap_injective : Function.Injective tkkParamMap :=
  SplitSpinFactorTKKInjectivityNative.tkkParamMap_injective


abbrev Carrier12 := SplitSpinFactorTKKSO66.Carrier12
abbrev End12 := V12 → V12

abbrev TKKParam := V10 × ((ℝ × B10SkewEnd) × V10)

abbrev B10_zero_left := SplitSpinFactorTKKConformalSO66.B10_zero_left
abbrev B10_zero_right := SplitSpinFactorTKKConformalSO66.B10_zero_right
abbrev tkk_param_zero_components := SplitSpinFactorTKKInjectivityNative.tkk_param_zero_components
abbrev tkkParamRangeEquiv := SplitSpinFactorTKKInjectivityNative.tkkParamRangeEquiv

/-- Soldering socket between the intrinsic spin-factor skew endomorphisms and
the repository's already certified 45-dimensional `So55` carrier. -/
structure SO55Soldering where
  equiv : B10SkewEnd ≃ₗ[ℝ] So55

theorem B10SkewEnd_finrank_of_soldering (S : SO55Soldering) :
    Module.finrank ℝ B10SkewEnd = 45 := by
  calc
    Module.finrank ℝ B10SkewEnd = Module.finrank ℝ So55 := S.equiv.finrank_eq
    _ = 45 := native_so55_finrank

end InfoGeometry.Canonical.SplitSpinFactorTKKInjectivity
