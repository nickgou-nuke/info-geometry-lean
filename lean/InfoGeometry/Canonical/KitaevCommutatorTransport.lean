/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevRotorCommutator
import InfoGeometry.Canonical.KitaevRotorMetricTransport

/-! Rotor invariance of the native boundary commutator and its trace pairing
under simultaneous metric transport. This is not fixed-metric unitarity. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevCommutatorTransport
open KitaevConcreteBoundary KitaevBoundaryAlgebra KitaevRotorMatrix
open KitaevRotorCommutator KitaevRotorMetricTransport

theorem rotor_commutes_boundaryCommutator (c s u v : ℂ) :
    Commute (twoSiteRotor c s) (boundaryCommutator u v) := by
  change twoSiteRotor c s * boundaryCommutator u v =
    boundaryCommutator u v * twoSiteRotor c s
  unfold twoSiteRotor
  rw [boundary_rotor_eq_matrix, boundaryCommutator_matrix]
  simp only [← map_mul (boundaryMatrixHom (by decide) twoSiteOperators)]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rotor_conjugates_boundaryCommutator (c s u v : ℂ) (hc : c*c+s*s=1) :
    twoSiteRotor c s * boundaryCommutator u v * twoSiteRotor c (-s) =
      boundaryCommutator u v := by
  rw [(rotor_commutes_boundaryCommutator c s u v).eq, mul_assoc,
    twoSiteRotor_inverse c s hc, mul_one]

theorem transported_boundaryCommutator_trace (c s u v : ℂ) (hc : c*c+s*s=1) :
    Matrix.trace (boundaryCommutator u v *
      (rotorMetricInverse c s * (boundaryCommutator u v).conjTranspose * rotorMetric c s)) =
      -4 * (u*v) * star (u*v) := by
  have ht := rotor_dirac_trace_covariance c s hc
    (boundaryCommutator u v) (boundaryCommutator u v)
  rw [rotor_conjugates_boundaryCommutator c s u v hc] at ht
  exact ht.trans (boundaryCommutator_dirac_trace u v)

end InfoGeometry.Canonical.KitaevCommutatorTransport
