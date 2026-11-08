/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import InfoGeometry.Canonical.KitaevRotorMetricTransport
import InfoGeometry.Canonical.KitaevBoundaryTraceNondegenerate

/-! The transported Dirac trace pairing on the represented two-site boundary
algebra is nondegenerate and remains indefinite. All statements concern the
native boundary image; no classification of the ambient commutant is asserted. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevRotorTracePairing
open KitaevRotorMetricTransport KitaevConcreteBoundary KitaevBoundaryAlgebra
open KitaevBoundaryTraceNormalization KitaevBoundaryTraceNondegenerate
open ReflexiveNilpotentFlows

/-- Pairing after conjugating both boundary operators and transporting the metric. -/
def rotorTracePairing (c s : ℂ) (M N : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace
    ((twoSiteRotor c s * boundaryMatrixHom (by decide) twoSiteOperators M *
      twoSiteRotor c (-s)) *
      (rotorMetricInverse c s *
        (twoSiteRotor c s * boundaryMatrixHom (by decide) twoSiteOperators N *
          twoSiteRotor c (-s)).conjTranspose * rotorMetric c s))

theorem rotorTracePairing_eq (c s : ℂ) (hc : c*c+s*s=1)
    (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    rotorTracePairing c s M N =
      Matrix.trace (boundaryMatrixHom (by decide) twoSiteOperators M *
        twoSiteKreinData.diracAdjoint (boundaryMatrixHom (by decide) twoSiteOperators N)) :=
  rotor_dirac_trace_covariance c s hc _ _

theorem rotorTracePairing_normalization (c s : ℂ) (hc : c*c+s*s=1)
    (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    rotorTracePairing c s M N =
      2 * Matrix.trace (M * (pairDiracMetric * N.conjTranspose * pairDiracMetric)) := by
  rw [rotorTracePairing_eq c s hc, boundaryMatrixHom_dirac_trace]

theorem rotorTracePairing_left_separates (c s : ℂ) (hc : c*c+s*s=1)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ N, rotorTracePairing c s M N = 0) : M = 0 := by
  apply boundary_dirac_trace_left_separates M
  intro N
  simpa only [rotorTracePairing_eq c s hc] using h N

theorem rotorTracePairing_right_separates (c s : ℂ) (hc : c*c+s*s=1)
    (N : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ M, rotorTracePairing c s M N = 0) : N = 0 := by
  apply boundary_dirac_trace_right_separates N
  intro M
  simpa only [rotorTracePairing_eq c s hc] using h M

/-- A negative diagonal value persists for every admissible rotor. -/
theorem rotorTracePairing_negative (c s : ℂ) (hc : c*c+s*s=1) :
    rotorTracePairing c s !![0, 1; 0, 0] !![0, 1; 0, 0] = -2 := by
  rw [rotorTracePairing_eq c s hc]
  exact boundary_dirac_trace_negative

end InfoGeometry.Canonical.KitaevRotorTracePairing
