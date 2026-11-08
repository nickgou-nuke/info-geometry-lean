/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import InfoGeometry.Canonical.KitaevRotorMatrix
import InfoGeometry.Canonical.KitaevBoundaryTracePairing
import InfoGeometry.CliffordWeyl.DiracPeirceTransport

/-! Transported metric and inverse for the actual two-site boundary rotor.
The new metric need not be an involution. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevRotorMetricTransport
open Matrix CARMajoranaFiniteBridge KitaevConcreteBoundary KitaevBoundaryDiracPair
open KitaevBoundaryTracePairing PeirceRotorAction ReflexiveNilpotentFlows
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

def twoSiteRotor (c s : ℂ) : ChainOp :=
  ReflexiveNilpotentFlows.rotor c s (boundaryAnnihilation (by decide) twoSiteOperators)
    (boundaryCreation (by decide) twoSiteOperators)

def rotorMetric (c s : ℂ) : ChainOp :=
  (twoSiteRotor c (-s)).conjTranspose * twoSiteKreinData.eta * twoSiteRotor c (-s)

def rotorMetricInverse (c s : ℂ) : ChainOp :=
  twoSiteRotor c s * twoSiteKreinData.eta * (twoSiteRotor c s).conjTranspose

theorem twoSiteRotor_inverse (c s : ℂ) (hc : c*c+s*s=1) :
    twoSiteRotor c s * twoSiteRotor c (-s) = 1 :=
  rotor_inverse (boundaryAnnihilation_sq (by decide) twoSiteOperators)
    (boundaryCreation_sq (by decide) twoSiteOperators)
    (boundary_reflexive (by decide) twoSiteOperators).1
    (boundary_reflexive (by decide) twoSiteOperators).2 c s hc

theorem rotorMetric_hermitian (c s : ℂ) :
    (rotorMetric c s).conjTranspose = rotorMetric c s :=
  transported_metric_hermitian _ _ twoSiteKreinData.2.2.1

theorem rotorMetric_mul_inverse (c s : ℂ) (hc : c*c+s*s=1) :
    rotorMetric c s * rotorMetricInverse c s = 1 := by
  exact transported_metric_inverse _ _ _ _
    (by simpa using twoSiteRotor_inverse c (-s) (by simpa using hc))
    (twoSiteRotor_inverse c s hc) twoSiteKreinData.2.1

theorem rotorMetric_inverse_mul (c s : ℂ) (hc : c*c+s*s=1) :
    rotorMetricInverse c s * rotorMetric c s = 1 := by
  exact transported_metric_left_inverse _ _ _ _
    (by simpa using twoSiteRotor_inverse c (-s) (by simpa using hc))
    (twoSiteRotor_inverse c s hc) twoSiteKreinData.2.1

theorem movingPlus_transported_dirac_fixed (c s : ℂ) (hc : c*c+s*s=1) :
    rotorMetricInverse c s *
      (movingPlus c s (boundaryAnnihilation (by decide) twoSiteOperators)
        (boundaryCreation (by decide) twoSiteOperators)).conjTranspose * rotorMetric c s =
      movingPlus c s (boundaryAnnihilation (by decide) twoSiteOperators)
        (boundaryCreation (by decide) twoSiteOperators) := by
  exact metric_adjoint_fixed_change_basis (twoSiteRotor c s) (twoSiteRotor c (-s))
    twoSiteKreinData.eta twoSiteKreinData.eta boundaryOccupation
    (by simpa using twoSiteRotor_inverse c (-s) (by simpa using hc))
    boundaryOccupation_dirac_fixed

theorem rotor_dirac_trace_covariance (c s : ℂ) (hc : c*c+s*s=1) (X Y : ChainOp) :
    Matrix.trace ((twoSiteRotor c s * X * twoSiteRotor c (-s)) *
      (rotorMetricInverse c s * (twoSiteRotor c s * Y * twoSiteRotor c (-s)).conjTranspose *
        rotorMetric c s)) = Matrix.trace (X * twoSiteKreinData.diracAdjoint Y) := by
  exact dirac_trace_pairing_change_basis (twoSiteRotor c s) (twoSiteRotor c (-s))
    twoSiteKreinData.eta twoSiteKreinData.eta X Y
    (by simpa using twoSiteRotor_inverse c (-s) (by simpa using hc))

/-- The bra changes by the inverse rotor when the ket changes by the rotor. -/
theorem rotor_diracRow_transport (c s : ℂ) (hc : c*c+s*s=1)
    (r : (Fin 2 × Fin 2) → ℂ) :
    diracRow (rotorMetric c s) (twoSiteRotor c s *ᵥ r) =
      diracRow twoSiteKreinData.eta r ᵥ* twoSiteRotor c (-s) := by
  exact diracRow_change_basis (twoSiteRotor c s) (twoSiteRotor c (-s))
    twoSiteKreinData.eta
    (by simpa using twoSiteRotor_inverse c (-s) (by simpa using hc)) r

/-- Ket-bra covariance uses the transported Dirac metric. -/
theorem rotor_solder_transport (c s : ℂ) (hc : c*c+s*s=1)
    (l r : (Fin 2 × Fin 2) → ℂ) :
    solder (rotorMetric c s) (twoSiteRotor c s *ᵥ l) (twoSiteRotor c s *ᵥ r) =
      twoSiteRotor c s * solder twoSiteKreinData.eta l r * twoSiteRotor c (-s) := by
  exact solder_change_basis (twoSiteRotor c s) (twoSiteRotor c (-s))
    twoSiteKreinData.eta
    (by simpa using twoSiteRotor_inverse c (-s) (by simpa using hc)) l r

end InfoGeometry.Canonical.KitaevRotorMetricTransport
