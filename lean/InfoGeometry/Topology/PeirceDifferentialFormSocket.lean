import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import InfoGeometry.Canonical.PeircePositiveBoundary

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-!
  Finite-dimensional differential-form interface for the Peirce chart.

  This file uses Mathlib's genuine exterior derivative.  It does not identify
  an arbitrary form with a canonical form or assert a boundary residue.
-/

abbrev PeirceChart := EuclideanSpace ℝ (Fin 4)

abbrev PeirceBoundaryChart := EuclideanSpace ℝ (Fin 3)

abbrev PeirceDifferentialForm (n : ℕ) :=
  PeirceChart → PeirceChart [⋀^Fin n]→L[ℝ] ℝ

/-! The boundary chart has coordinates `(a00, a01, a10, a11)`.

The four boundary charts below are bundled continuous linear maps.  This is
deliberately a chart-level construction: it records which coordinate is set
to zero, but does not by itself assert a residue or a canonical-form identity.
-/

noncomputable def peirceBoundarySourceCoordinates :
    PeirceBoundaryChart →L[ℝ] (Fin 3 → ℝ) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap

noncomputable def peirceBoundaryProjection (i : Fin 3) :
    PeirceBoundaryChart →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp
    peirceBoundarySourceCoordinates

noncomputable def peirceBoundaryChartMapCLM
    (b : PeirceBoundaryCoordinate) :
    PeirceBoundaryChart →L[ℝ] PeirceChart :=
  let p0 : PeirceBoundaryChart →L[ℝ] ℝ := peirceBoundaryProjection 0
  let p1 : PeirceBoundaryChart →L[ℝ] ℝ := peirceBoundaryProjection 1
  let p2 : PeirceBoundaryChart →L[ℝ] ℝ := peirceBoundaryProjection 2
  let z : PeirceBoundaryChart →L[ℝ] ℝ := 0
  let coordinates : PeirceBoundaryChart →L[ℝ] (Fin 4 → ℝ) :=
    match b with
    | .a00 => ContinuousLinearMap.pi ![z, p0, p1, p2]
    | .a01 => ContinuousLinearMap.pi ![p0, z, p1, p2]
    | .a10 => ContinuousLinearMap.pi ![p0, p1, z, p2]
    | .a11 => ContinuousLinearMap.pi ![p0, p1, p2, z]
  (EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap.comp coordinates

theorem peirceBoundaryChartMapCLM_contDiff
    (b : PeirceBoundaryCoordinate) :
    ContDiff ℝ 2 (peirceBoundaryChartMapCLM b) := by
  exact (peirceBoundaryChartMapCLM b).contDiff

theorem peirceBoundaryChartMapCLM_a00_zero (x : PeirceBoundaryChart) :
    peirceBoundaryChartMapCLM .a00 x 0 = 0 := by
  simp [peirceBoundaryChartMapCLM, peirceBoundaryProjection,
    peirceBoundarySourceCoordinates]

theorem peirceBoundaryChartMapCLM_a01_zero (x : PeirceBoundaryChart) :
    peirceBoundaryChartMapCLM .a01 x 1 = 0 := by
  simp [peirceBoundaryChartMapCLM, peirceBoundaryProjection,
    peirceBoundarySourceCoordinates]

theorem peirceBoundaryChartMapCLM_a10_zero (x : PeirceBoundaryChart) :
    peirceBoundaryChartMapCLM .a10 x 2 = 0 := by
  simp [peirceBoundaryChartMapCLM, peirceBoundaryProjection,
    peirceBoundarySourceCoordinates]

theorem peirceBoundaryChartMapCLM_a11_zero (x : PeirceBoundaryChart) :
    peirceBoundaryChartMapCLM .a11 x 3 = 0 := by
  simp [peirceBoundaryChartMapCLM, peirceBoundaryProjection,
    peirceBoundarySourceCoordinates]

def peirceChartMatrix (x : PeirceChart) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ![![x 0, x 1], ![x 2, x 3]]

theorem peirceBoundaryChartMapCLM_a00_locus (x : PeirceBoundaryChart) :
    peirceBoundaryValue .a00
        (peirceChartMatrix (peirceBoundaryChartMapCLM .a00 x)) = 0 := by
  simp [peirceBoundaryValue, peirceChartMatrix,
    peirceBoundaryChartMapCLM_a00_zero]

theorem peirceBoundaryChartMapCLM_a01_locus (x : PeirceBoundaryChart) :
    peirceBoundaryValue .a01
        (peirceChartMatrix (peirceBoundaryChartMapCLM .a01 x)) = 0 := by
  simp [peirceBoundaryValue, peirceChartMatrix,
    peirceBoundaryChartMapCLM_a01_zero]

theorem peirceBoundaryChartMapCLM_a10_locus (x : PeirceBoundaryChart) :
    peirceBoundaryValue .a10
        (peirceChartMatrix (peirceBoundaryChartMapCLM .a10 x)) = 0 := by
  simp [peirceBoundaryValue, peirceChartMatrix,
    peirceBoundaryChartMapCLM_a10_zero]

theorem peirceBoundaryChartMapCLM_a11_locus (x : PeirceBoundaryChart) :
    peirceBoundaryValue .a11
        (peirceChartMatrix (peirceBoundaryChartMapCLM .a11 x)) = 0 := by
  simp [peirceBoundaryValue, peirceChartMatrix,
    peirceBoundaryChartMapCLM_a11_zero]

noncomputable def peirceBoundaryPullback
    {n : ℕ} (b : PeirceBoundaryCoordinate)
    (ω : PeirceDifferentialForm n) :
    PeirceBoundaryChart → (PeirceBoundaryChart [⋀^Fin n]→L[ℝ] ℝ) :=
  fun x =>
    (ω (peirceBoundaryChartMapCLM b x)).compContinuousLinearMap
      (fderiv ℝ (peirceBoundaryChartMapCLM b) x)

theorem peirceBoundaryPullback_extDeriv
    {n : ℕ} (b : PeirceBoundaryCoordinate)
    (ω : PeirceDifferentialForm n) (hω : ContDiff ℝ 2 ω)
    (x : PeirceBoundaryChart) :
    extDeriv (peirceBoundaryPullback b ω) x =
      (extDeriv ω (peirceBoundaryChartMapCLM b x)).compContinuousLinearMap
        (fderiv ℝ (peirceBoundaryChartMapCLM b) x) := by
  have hω' : DifferentiableAt ℝ ω
      (peirceBoundaryChartMapCLM b x) :=
    (hω.differentiable (by norm_num)).differentiableAt
  have hf : ContDiffAt ℝ 2 (peirceBoundaryChartMapCLM b) x :=
    (peirceBoundaryChartMapCLM_contDiff b).contDiffAt
  exact extDeriv_pullback (r := (2 : WithTop ℕ∞)) hω' hf (by simp)

noncomputable def peirceExteriorDerivative
    {n : ℕ} (ω : PeirceDifferentialForm n) :
    PeirceDifferentialForm (n + 1) :=
  extDeriv ω

theorem peirceExteriorDerivative_square_zero
    {n : ℕ} (ω : PeirceDifferentialForm n)
    (hω : ContDiff ℝ 2 ω) :
    peirceExteriorDerivative (peirceExteriorDerivative ω) = 0 := by
  exact extDeriv_extDeriv hω (by simp)

theorem peirceExteriorDerivative_square_zero_apply
    {n : ℕ} (ω : PeirceDifferentialForm n)
    (hω : ContDiff ℝ 2 ω) (x : PeirceChart) :
    peirceExteriorDerivative (peirceExteriorDerivative ω) x = 0 := by
  rw [peirceExteriorDerivative_square_zero ω hω]
  rfl

theorem peirceExteriorDerivative_congr_at
    {n : ℕ} {ω₁ ω₂ : PeirceDifferentialForm n}
    {x : PeirceChart} (h : ω₁ =ᶠ[_root_.nhds x] ω₂) :
    peirceExteriorDerivative ω₁ x =
      peirceExteriorDerivative ω₂ x := by
  exact h.extDeriv_eq

end InfoGeometry.Topology
