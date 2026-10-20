import Mathlib.Tactic
import InfoGeometry.Canonical.ParaKahlerLagrangianDimension
import InfoGeometry.SuperGrassmannian.SuperGrassmannianProjectorTransportClosure
import InfoGeometry.InformationGeometry.BKMMetricModularBridge

/-!
# Constructive para-polarization and finite BKM dissipation

General reciprocal scaling is proved from the existing para-Kahler isotropic
sheets, not postulated through a new metric or projector carrier.

The finite BKM metric gives a non-positive quadratic dissipation readout.
This is an explicit metric-level constitutive choice, not a theorem asserting
that arbitrary Onsager maps equal the BKM metric.
-/

noncomputable section

namespace InfoGeometry.Canonical.ModularParaBKMIntegration

open InfoGeometry.Canonical.SuperGrassmannianManifold
open InfoGeometry.Canonical.ParaKahlerLagrangianDimension
open InfoGeometry.InformationGeometry.BKM

section ParaPolarization

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
variable {K : V →ₗ[ℝ] V}

/-- Scalar reciprocal scaling preserves the neutral metric across two
isotropic para-Kahler eigensheets. -/
theorem reciprocal_cross_pairing
    (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K)
    {x₊ x₋ y₊ y₋ : V}
    (hx₊ : InTPlus K x₊) (hx₋ : InTMinus K x₋)
    (hy₊ : InTPlus K y₊) (hy₋ : InTMinus K y₋)
    (a b : ℝ) (hab : a * b = 1) :
    g (a • x₊ + b • x₋) (a • y₊ + b • y₋) =
      g (x₊ + x₋) (y₊ + y₋) := by
  have hpp := tplus_isotropic hK hPK hx₊ hy₊
  have hmm := tminus_isotropic hK hPK hx₋ hy₋
  simp only [map_add, map_smul]
  simp only [LinearMap.add_apply] at *
  simp only [map_add, map_smul]
  rw [hpp, hmm]
  have hba : b * a = 1 := by simpa [mul_comm] using hab
  simp [smul_eq_mul, hab, hba]
  ring

/-- Specialize the generic neutral-metric invariance to a modular rapidity. -/
theorem exponential_cross_pairing
    (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K)
    {x₊ x₋ y₊ y₋ : V}
    (hx₊ : InTPlus K x₊) (hx₋ : InTMinus K x₋)
    (hy₊ : InTPlus K y₊) (hy₋ : InTMinus K y₋)
    (η : ℝ) :
    g (Real.exp η • x₊ + Real.exp (-η) • x₋)
        (Real.exp η • y₊ + Real.exp (-η) • y₋) =
      g (x₊ + x₋) (y₊ + y₋) := by
  apply reciprocal_cross_pairing hK hPK hx₊ hx₋ hy₊ hy₋
  rw [← Real.exp_add]
  simp

end ParaPolarization

section FiniteBKM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The negative BKM quadratic form is a concrete dissipative readout. -/
def finiteBKMDissipation (energies : ι → ℝ)
    (X : Matrix ι ι ℂ) : ℝ :=
  -(bkmInnerProduct energies X X).re

theorem finiteBKMDissipation_nonpos (energies : ι → ℝ)
    (X : Matrix ι ι ℂ) :
    finiteBKMDissipation energies X ≤ 0 := by
  exact neg_nonpos.mpr (bkmInnerProduct_self_nonneg energies X)

/-- The zero tangent perturbation has no BKM dissipation. -/
theorem finiteBKMDissipation_zero (energies : ι → ℝ) :
    finiteBKMDissipation energies (0 : Matrix ι ι ℂ) = 0 := by
  simp [finiteBKMDissipation, bkmInnerProduct]

end FiniteBKM

end InfoGeometry.Canonical.ModularParaBKMIntegration
