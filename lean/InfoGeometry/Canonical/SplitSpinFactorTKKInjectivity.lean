import InfoGeometry.Canonical.SplitSpinFactorTKKInjectivityNative
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

/-! Compatibility path for the native parameter-injectivity owner. -/
namespace InfoGeometry.Canonical.SplitSpinFactorTKKInjectivity

open InfoGeometry.Canonical.SplitSpinFactorTKKInjectivityNative

abbrev V10 := SplitSpinFactorTKKInjectivityNative.V10
abbrev B10SkewEnd := SplitSpinFactorTKKInjectivityNative.B10SkewEnd
abbrev tkkParamMap := SplitSpinFactorTKKInjectivityNative.tkkParamMap

theorem tkkParamMap_injective : Function.Injective tkkParamMap :=
  SplitSpinFactorTKKInjectivityNative.tkkParamMap_injective

end InfoGeometry.Canonical.SplitSpinFactorTKKInjectivity
