/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11MetriplecticSymmetry
import InfoGeometry.NCG.KMSStripKleinMonodromy

/-!
# Real matrix pencils in the zeta and KMS coordinate charts

The existing real affine zeta chart supplies the centered coordinate
`centeredSigma z = z.sigma - 1/2`. Evaluating the canonical `Cl11Matrix.gen`
at this coordinate and the chart height transports its three matrix
conjugations to the existing chart reflections. The scalar pencil agrees
with the Clifford pencil exactly on the critical chart line.

The existing map `kmsToZeta β (t, τ) = ⟨1 - τ/β, t/β⟩` then transports this
coincidence locus to `τ = β/2`, for `β > 0`. Every matrix in this file has
real coefficients. The reference to `ZetaDihedral.gamma` uses the existing
coordinate conversion and fixed-locus theorem; no analytic zeta function,
zero-location theorem, or KMS equilibrium assertion is constructed here.
-/

noncomputable section

namespace InfoGeometry.NCG.MetriplecticZetaKMSBridge

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.NCG.KMSStripKleinMonodromy

/-- The canonical Clifford pencil evaluated in centered real chart coordinates. -/
def chartPencil (z : ZetaAffineChart) : Mat2 :=
  gen (centeredSigma z, z.tau)

/-- The scalar multiplication pencil evaluated in the same centered coordinates. -/
def chartScalarPencil (z : ZetaAffineChart) : Mat2 :=
  scalarPencil (centeredSigma z) z.tau

/-- The defect occupies the negative `Eplus` Peirce corner. -/
theorem chartPencil_sub_chartScalarPencil (z : ZetaAffineChart) :
    chartPencil z - chartScalarPencil z =
      (-2 * centeredSigma z) •
        InfoGeometry.Clifford.SplitQ11CausalCone.matrixKreinMinusProjector := by
  exact gen_sub_scalarPencil (centeredSigma z) z.tau

/-- Conjugation by `Eplus` realizes the chart's conjugation reflection. -/
theorem chartPencil_conjugation (z : ZetaAffineChart) :
    Eplus * chartPencil z * Eplus = chartPencil (chartConjugation z) := by
  change Eplus * gen (centeredSigma z, z.tau) * Eplus =
    gen (centeredSigma (chartConjugation z), -z.tau)
  rw [centeredSigma_chartConjugation]
  exact gen_Eplus_conjugate (centeredSigma z) z.tau

/-- Conjugation by `J1` realizes functional duality in the real chart. -/
theorem chartPencil_functionalDual (z : ZetaAffineChart) :
    J1 * chartPencil z * J1 = chartPencil (chartFunctionalDual z) := by
  change J1 * gen (centeredSigma z, z.tau) * J1 =
    gen (centeredSigma (chartFunctionalDual z), -z.tau)
  rw [centeredSigma_chartFunctionalDual]
  exact gen_J1_conjugate (centeredSigma z) z.tau

/-- Since `Eminus⁻¹ = -Eminus`, this conjugation realizes the critical mirror. -/
theorem chartPencil_criticalMirror (z : ZetaAffineChart) :
    (-Eminus) * chartPencil z * Eminus = chartPencil (chartCriticalMirror z) := by
  change (-Eminus) * gen (centeredSigma z, z.tau) * Eminus =
    gen (centeredSigma (chartCriticalMirror z), z.tau)
  rw [centeredSigma_chartCriticalMirror]
  exact gen_Eminus_conjugate (centeredSigma z) z.tau

/-- Coincidence of the two real matrix pencils characterizes the critical chart line. -/
theorem chartPencil_eq_chartScalarPencil_iff (z : ZetaAffineChart) :
    chartPencil z = chartScalarPencil z ↔ chartCriticalLine z := by
  rw [chartPencil, chartScalarPencil, gen_eq_scalarPencil_iff]
  exact (chartCriticalLine_iff_centeredSigma_eq_zero z).symm

/-- The same coincidence locus is the fixed locus of the chart's critical mirror. -/
theorem chartPencil_eq_chartScalarPencil_iff_mirror_fixed (z : ZetaAffineChart) :
    chartPencil z = chartScalarPencil z ↔ chartCriticalMirror z = z := by
  exact (chartPencil_eq_chartScalarPencil_iff z).trans
    (fixed_chartCriticalMirror_iff_criticalLine z).symm

/-- Existing complex chart conversion identifies this locus with `ZetaDihedral.gamma` fixedness. -/
theorem chartPencil_eq_chartScalarPencil_iff_dihedral_fixed (z : ZetaAffineChart) :
    chartPencil z = chartScalarPencil z ↔
      InfoGeometry.Arithmetic.ZetaDihedral.gamma z.toComplex = z.toComplex := by
  rw [chartPencil_eq_chartScalarPencil_iff]
  exact (InfoGeometry.Arithmetic.ZetaDihedral.critical_line_is_invariant_orbit
    z.toComplex).symm

/-- The existing strip coordinate map sends exactly its imaginary-time midline to the critical line. -/
theorem kmsToZeta_criticalLine_iff_midline {β : ℝ} (hβ : 0 < β) (z : StripPoint) :
    chartCriticalLine (kmsToZeta β z) ↔ z.2 = β / 2 := by
  constructor
  · intro hz
    change (kmsToZeta β z).sigma = (1 / 2 : ℝ) at hz
    calc
      z.2 = β * (1 - (kmsToZeta β z).sigma) :=
        kmsToZeta_imaginaryTime_recovery hβ z
      _ = β / 2 := by rw [hz]; ring
  · intro hz
    have hzpair : z = (z.1, β / 2) := Prod.ext rfl hz
    change (kmsToZeta β z).sigma = (1 / 2 : ℝ)
    rw [hzpair]
    exact kmsToZeta_midline hβ z.1

/-- The two real matrix pencils agree exactly on the KMS imaginary-time midline. -/
theorem kms_chartPencil_eq_chartScalarPencil_iff_midline
    {β : ℝ} (hβ : 0 < β) (z : StripPoint) :
    chartPencil (kmsToZeta β z) = chartScalarPencil (kmsToZeta β z) ↔
      z.2 = β / 2 := by
  rw [chartPencil_eq_chartScalarPencil_iff]
  exact kmsToZeta_criticalLine_iff_midline hβ z

/-- Real-time reversal is realized by conjugation with `Eplus`. -/
theorem kms_chartPencil_conjugation (β : ℝ) (z : StripPoint) :
    Eplus * chartPencil (kmsToZeta β z) * Eplus =
      chartPencil (kmsToZeta β (-z.1, z.2)) := by
  rw [chartPencil_conjugation, kms_conjugation_transport]

/-- Reversing real time and exchanging strip edges is realized by `J1`. -/
theorem kms_chartPencil_functionalDual {β : ℝ} (hβ : 0 < β) (z : StripPoint) :
    J1 * chartPencil (kmsToZeta β z) * J1 =
      chartPencil (kmsToZeta β (-z.1, β - z.2)) := by
  rw [chartPencil_functionalDual, kms_functional_reflection_transport hβ]

/-- Exchanging strip edges while preserving real time is realized by `Eminus`. -/
theorem kms_chartPencil_criticalMirror {β : ℝ} (hβ : 0 < β) (z : StripPoint) :
    (-Eminus) * chartPencil (kmsToZeta β z) * Eminus =
      chartPencil (kmsToZeta β (z.1, β - z.2)) := by
  rw [chartPencil_criticalMirror, kms_critical_mirror_transport hβ]

end InfoGeometry.NCG.MetriplecticZetaKMSBridge
