import InfoGeometry.Topology.PeirceDifferentialForm

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

structure PeirceCanonicalBoundaryFormContract
    (b : PeirceBoundaryCoordinate)
    (n : ℕ) where
  chartForm : PeirceDifferentialForm n
  chartForm_contDiff : ContDiff ℝ 2 chartForm
  boundaryForm : PeirceBoundaryDifferentialForm n
  boundaryForm_eq_pullback :
    boundaryForm = peirceBoundaryPullback b chartForm

noncomputable def PeirceCanonicalBoundaryFormContract.ofForm
    (b : PeirceBoundaryCoordinate)
    {n : ℕ} (ω : PeirceDifferentialForm n)
    (hω : ContDiff ℝ 2 ω) :
    PeirceCanonicalBoundaryFormContract b n where
  chartForm := ω
  chartForm_contDiff := hω
  boundaryForm := peirceBoundaryPullback b ω
  boundaryForm_eq_pullback := rfl

theorem peirceBoundaryContract_boundaryForm_extDeriv
    {b : PeirceBoundaryCoordinate}
    {n : ℕ} (C : PeirceCanonicalBoundaryFormContract b n)
    (x : PeirceBoundaryChart) :
    extDeriv C.boundaryForm x =
      (extDeriv C.chartForm
        (peirceBoundaryChartMapCLM b x)).compContinuousLinearMap
        (fderiv ℝ (peirceBoundaryChartMapCLM b) x) := by
  rw [C.boundaryForm_eq_pullback]
  exact peirceBoundaryPullback_extDeriv b C.chartForm
    C.chartForm_contDiff x

theorem peirceBoundaryContract_readback
    {b : PeirceBoundaryCoordinate}
    {n : ℕ} (C : PeirceCanonicalBoundaryFormContract b n) :
    C.boundaryForm = peirceBoundaryPullback b C.chartForm :=
  C.boundaryForm_eq_pullback

end InfoGeometry.Topology
