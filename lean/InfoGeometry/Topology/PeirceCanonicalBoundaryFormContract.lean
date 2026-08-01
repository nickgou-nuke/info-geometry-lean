import InfoGeometry.Canonical.PeirceCanonicalBoundaryResidueSocket
import InfoGeometry.Topology.PeirceDifferentialFormSocket

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-!
  Conditional interface for a canonical boundary-form calculation.

  The form/boundary pullback part is geometric and kernel-checked.  The
  scalar residue socket is explicit input data: this structure intentionally
  does not claim that every differential form has a logarithmic residue.
-/

structure PeirceCanonicalBoundaryFormContract
    (b : PeirceBoundaryCoordinate)
    (path : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (n : ℕ) where
  chartForm : PeirceDifferentialForm n
  chartForm_contDiff : ContDiff ℝ 2 chartForm
  boundaryForm : PeirceBoundaryDifferentialForm n
  boundaryForm_eq_pullback :
    boundaryForm = peirceBoundaryPullback b chartForm
  residueSocket : PeirceBoundaryResidueSocket b path

noncomputable def PeirceCanonicalBoundaryFormContract.ofForm
    (b : PeirceBoundaryCoordinate)
    (path : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    {n : ℕ} (ω : PeirceDifferentialForm n)
    (hω : ContDiff ℝ 2 ω)
    (socket : PeirceBoundaryResidueSocket b path) :
    PeirceCanonicalBoundaryFormContract b path n where
  chartForm := ω
  chartForm_contDiff := hω
  boundaryForm := peirceBoundaryPullback b ω
  boundaryForm_eq_pullback := rfl
  residueSocket := socket

theorem peirceBoundaryContract_boundaryForm_extDeriv
    {b : PeirceBoundaryCoordinate}
    {path : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {n : ℕ} (C : PeirceCanonicalBoundaryFormContract b path n)
    (x : PeirceBoundaryChart) :
    extDeriv C.boundaryForm x =
      (extDeriv C.chartForm
        (peirceBoundaryChartMapCLM b x)).compContinuousLinearMap
        (fderiv ℝ (peirceBoundaryChartMapCLM b) x) := by
  rw [C.boundaryForm_eq_pullback]
  exact peirceBoundaryPullback_extDeriv b C.chartForm
    C.chartForm_contDiff x

theorem peirceBoundaryContract_residue
    {b : PeirceBoundaryCoordinate}
    {path : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {n : ℕ} (C : PeirceCanonicalBoundaryFormContract b path n) :
    PeirceBoundaryResidue C.residueSocket =
      C.residueSocket.regularPart 0 :=
  rfl

theorem peirceBoundaryContract_residue_tendsto
    {b : PeirceBoundaryCoordinate}
    {path : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {n : ℕ} (C : PeirceCanonicalBoundaryFormContract b path n) :
    Filter.Tendsto C.residueSocket.regularPart (_root_.nhds 0)
      (_root_.nhds (PeirceBoundaryResidue C.residueSocket)) :=
  peirceBoundaryResidue_regularPart_tendsto C.residueSocket

end InfoGeometry.Topology
