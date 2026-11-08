import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauBregman
import InfoGeometry.Canonical.PrimonThermodynamicZetaBridge
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

/-!
# Souriau/zeta calibration readouts on the Hestenes--Krein colimit

This owner translates the real part of the complex Souriau Massieu channel
into compatible Hestenes stage/limit readouts.  The zeta-regularized
determinant identity remains the explicit calibration premise supplied by
`PrimonThermodynamicZetaCalibration`; no regularization or analytic
continuation is reconstructed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinSouriauCalibrationColimit

open InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauBregman
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.PrimonZetaRegularization
open InfoGeometry.Canonical.PrimonThermodynamicZetaBridge
open InfoGeometry.Krein

variable {C : HestenesKreinCone}

def stageMassieuReal
    (massieu : ∀ n, DoubledSpace (C.Base n) → ℂ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  (massieu n x).re

def limitMassieuReal
    (massieu : DoubledSpace C.LimitBase → ℂ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  (massieu x).re

theorem stageMassieuReal_eq_limit
    (stageMassieu : ∀ n, DoubledSpace (C.Base n) → ℂ)
    (limitMassieu : DoubledSpace C.LimitBase → ℂ)
    (hreadout : ∀ n x, stageMassieu n x = limitMassieu (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageMassieuReal stageMassieu n x =
      limitMassieuReal limitMassieu (C.ι n x) := by
  unfold stageMassieuReal limitMassieuReal
  exact congrArg Complex.re (hreadout n x)

theorem stageMassieuReal_bondIterate_eq
    (stageMassieu : ∀ n, DoubledSpace (C.Base n) → ℂ)
    (hreadout : ∀ n m x,
      stageMassieu (n + m)
          (C.toFilteredPhaseCone.bondIterate n m x) =
        stageMassieu n x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageMassieuReal stageMassieu (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) =
      stageMassieuReal stageMassieu n x := by
  unfold stageMassieuReal
  exact congrArg Complex.re (hreadout n m x)

theorem realMassieu_invariant_of_thermal_symmetry
    {G : Type*} [Group G]
    (actOnBeta : G → ℂ → ℂ)
    (partition massieu : ℂ → ℂ)
    (isThermalSymmetry : G → Prop)
    (massieu_eq_log_partition : ∀ β, massieu β = Complex.log (partition β))
    (partition_invariant :
      ∀ g β, isThermalSymmetry g → partition (actOnBeta g β) = partition β)
    (g : G) (β : ℂ)
    (hg : isThermalSymmetry g) :
    (massieu (actOnBeta g β)).re = (massieu β).re := by
  rw [massieu_eq_log_partition, massieu_eq_log_partition, partition_invariant g β hg]

theorem zetaCalibration_real_readout
    (zetaTarget : ℂ → ℂ)
    (hdet : ∀ s : ℂ, zetaRegularizedDetPrimon s = zetaTarget s)
    (s : ℂ) :
    (zetaRegularizedDetPrimon s).re = (zetaTarget s).re := by
  exact congrArg Complex.re (hdet s)

end InfoGeometry.Canonical.HestenesKreinSouriauCalibrationColimit

end noncomputable section
