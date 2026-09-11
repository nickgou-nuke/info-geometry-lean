import InfoGeometry.Canonical.G2Cl55FiniteHodgeEquivarianceDatum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ChiralFredholmIndex

/-!
# Finite Fredholm index of the master `Cl(5,5)` Hodge operator

The master finite Hodge operator satisfies `D_H² = 3 I`.  This owner turns
that relation into the repository's proof-carrying finite Fredholm datum and
computes its ordinary algebraic index.  It deliberately does not identify the
result with an equivariant analytic index or a `KK`-class.
-/

noncomputable section

namespace InfoGeometry.Canonical.G2Cl55FiniteFredholmIndexBridge

open InfoGeometry.Canonical.G2Cl55FiniteHodgeEquivarianceDatum
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.OperatorAlgebra.ChiralFredholmIndex

abbrev SpinorCarrier32 := InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ
abbrev SpinorLinearMap32 := SpinorCarrier32 →ₗ[ℝ] SpinorCarrier32

def hodgeLinear : SpinorLinearMap32 :=
  Matrix.mulVecLin embeddedSplitOctonionHodgeDirac

@[simp] theorem hodgeLinear_apply (v : SpinorCarrier32) :
    hodgeLinear v = embeddedSplitOctonionHodgeDirac.mulVec v := rfl

theorem hodgeLinear_ker_eq_bot : LinearMap.ker hodgeLinear = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro v w hvw
  have hzero : hodgeLinear (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hzero' : v - w = 0 := by
    apply hodge_kernel_trivial
    change embeddedSplitOctonionHodgeDirac.mulVec (v - w) = 0
    exact hzero
  exact sub_eq_zero.mp hzero'

theorem hodgeLinear_injective : Function.Injective hodgeLinear := by
  rw [← LinearMap.ker_eq_bot]
  exact hodgeLinear_ker_eq_bot

theorem hodgeLinear_surjective : Function.Surjective hodgeLinear :=
  LinearMap.surjective_of_injective hodgeLinear_injective

noncomputable def hodgeFredholm :
    FredholmIndexDatum SpinorCarrier32 SpinorCarrier32 where
  operator := hodgeLinear
  kernelFinite := inferInstance
  cokernelFinite := inferInstance

theorem hodgeFredholm_index_zero :
    (hodgeFredholm).index = 0 := by
  rw [FredholmIndexDatum.index_eq_finrank_ker_sub_finrank_coker]
  change (Module.finrank ℝ (LinearMap.ker hodgeLinear) : ℤ) -
      (Module.finrank ℝ (SpinorCarrier32 ⧸ LinearMap.range hodgeLinear) : ℤ) = 0
  rw [hodgeLinear_ker_eq_bot]
  have hrange : LinearMap.range hodgeLinear = ⊤ :=
    LinearMap.range_eq_top.mpr hodgeLinear_surjective
  rw [hrange]
  rw [Submodule.finrank_quotient]
  simp

end InfoGeometry.Canonical.G2Cl55FiniteFredholmIndexBridge
