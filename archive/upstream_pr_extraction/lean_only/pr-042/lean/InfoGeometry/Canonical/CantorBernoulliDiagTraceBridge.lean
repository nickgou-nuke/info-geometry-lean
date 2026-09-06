import Mathlib.Tactic
import InfoGeometry.Canonical.CantorKMSState
import InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure

/-!
# Finite diagonal trace and Bernoulli cylinder mass

This is a finite consumer bridge only.  It identifies the normalized diagonal
trace of a cylinder indicator with the real Bernoulli mass of the corresponding
Cantor cylinder.  It does not construct a positive functional on the full
Cuntz `C*`-algebra or assert a KMS/GNS theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge

open scoped ENNReal
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
open InfoGeometry.Canonical.CantorKMSState
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Analysis.FractalMeasure.Basic

theorem diagTrace_cylinderIndicator_eq_fractalMeasure_toReal
    (n : ℕ) (w : BitWord n) :
    DiagTrace n (cylinderIndicator n w) =
      ((fractalMeasure
          (InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.cylinderSet n w)).toReal : ℂ) := by
  rw [DiagTrace_cylinderIndicator, fractalMeasure_topologyCylinderSet]
  norm_num [ENNReal.toReal_ofNat]

theorem diagTrace_cylinderIndicator_eq_projectivePrefixFiber_toReal
    (n : ℕ) (w : BitWord n) :
    DiagTrace n (cylinderIndicator n w) =
      ((projectiveLimitMeasure
          {q : PrefixProjectiveLimit |
            π n q = w}).toReal : ℂ) := by
  rw [DiagTrace_cylinderIndicator,
    projectiveLimitMeasure_apply_prefix_fiber]
  norm_num [ENNReal.toReal_ofNat]

end InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge
