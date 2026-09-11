import InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeWeylCartanRestriction

/-! Kernel-checked Cartan basis action for the real Weyl generators. -/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2NativeWeylCartanAction

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
open InfoGeometry.Algebra.Zorn.G2NativeWeylCartanRestriction

theorem realWeylCycle_cartanBasis_zero :
    conjugateNativeDerivation realWeylCycle (cartanDerivation 0) =
      (-1 : ℝ) • cartanDerivation 0 + cartanDerivation 1 := by
  have h : cartanDerivation 0 =
      (1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (-1 / 3 : ℝ) •
          ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
    module
  rw [h]
  change conjugateNativeDerivationLinear realWeylCycle _ = _
  rw [map_add, map_smul, map_smul]
  simp only [conjugateNativeDerivationLinear_apply]
  rw [realWeylCycle_cartanPair_zero, realWeylCycle_cartanPair_one]
  module

theorem realWeylCycle_cartanBasis_one :
    conjugateNativeDerivation realWeylCycle (cartanDerivation 1) =
      (-1 : ℝ) • cartanDerivation 0 := by
  have h : cartanDerivation 1 =
      (2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (1 / 3 : ℝ) •
          ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
    module
  rw [h]
  change conjugateNativeDerivationLinear realWeylCycle _ = _
  rw [map_add, map_smul, map_smul]
  simp only [conjugateNativeDerivationLinear_apply]
  rw [realWeylCycle_cartanPair_zero, realWeylCycle_cartanPair_one]
  module

theorem realWeylReflection_cartanBasis_zero :
    conjugateNativeDerivation realWeylReflection (cartanDerivation 0) =
      -(cartanDerivation 1) := by
  have h : cartanDerivation 0 =
      (1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (-1 / 3 : ℝ) •
          ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
    module
  rw [h]
  change conjugateNativeDerivationLinear realWeylReflection _ = _
  rw [map_add, map_smul, map_smul]
  simp only [conjugateNativeDerivationLinear_apply]
  rw [realWeylReflection_cartanPair_zero, realWeylReflection_cartanPair_one]
  module

theorem realWeylReflection_cartanBasis_one :
    conjugateNativeDerivation realWeylReflection (cartanDerivation 1) =
      -(cartanDerivation 0) := by
  have h : cartanDerivation 1 =
      (2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (1 / 3 : ℝ) •
          ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
    module
  rw [h]
  change conjugateNativeDerivationLinear realWeylReflection _ = _
  rw [map_add, map_smul, map_smul]
  simp only [conjugateNativeDerivationLinear_apply]
  rw [realWeylReflection_cartanPair_zero, realWeylReflection_cartanPair_one]
  module

theorem realWeylCycle_cartan_linear_combination (a b : ℝ) :
    conjugateNativeDerivation realWeylCycle
        (a • cartanDerivation 0 + b • cartanDerivation 1) =
      a • (-(cartanDerivation 0) + cartanDerivation 1) +
        b • (-(cartanDerivation 0)) := by
  change conjugateNativeDerivationLinear realWeylCycle _ = _
  simp only [map_add, map_smul, conjugateNativeDerivationLinear_apply]
  rw [realWeylCycle_cartanBasis_zero, realWeylCycle_cartanBasis_one]
  module

theorem realWeylReflection_cartan_linear_combination (a b : ℝ) :
    conjugateNativeDerivation realWeylReflection
        (a • cartanDerivation 0 + b • cartanDerivation 1) =
      a • (-(cartanDerivation 1)) + b • (-(cartanDerivation 0)) := by
  change conjugateNativeDerivationLinear realWeylReflection _ = _
  simp only [map_add, map_smul, conjugateNativeDerivationLinear_apply]
  rw [realWeylReflection_cartanBasis_zero, realWeylReflection_cartanBasis_one]

end InfoGeometry.Algebra.Zorn.G2NativeWeylCartanAction
