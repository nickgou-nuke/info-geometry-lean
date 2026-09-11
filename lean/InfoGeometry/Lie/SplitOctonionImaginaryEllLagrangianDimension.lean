import InfoGeometry.Lie.SplitOctonionImaginaryEllSupportDimension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Intrinsic dimensions of the imaginary ell eigenspaces

The two eigenspaces of the intrinsic support involution are already proved
complementary and isotropic.  This owner uses only the nondegenerate mixed
polar pairing to show that they have equal dimension, hence dimension three.
No coordinate root embedding or identification with the diagonal axial Zorn
support is introduced.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionImaginaryEllLagrangianDimension

open InfoGeometry.Lie.SplitOctonionImaginaryEllSupport
open InfoGeometry.Lie.SplitOctonionImaginaryEllSupportDimension
open InfoGeometry.Lie.SplitOctonionImaginaryAction

abbrev Support := SplitOctonionImaginaryEllSupport.Support
abbrev Plus := SplitOctonionImaginaryEllSupport.SupportPlus
abbrev Minus := SplitOctonionImaginaryEllSupport.SupportMinus

local instance : AddCommGroup Plus := SupportPlus.addCommGroup
local instance : AddCommGroup Minus := SupportMinus.addCommGroup

local instance : FiniteDimensional ℝ
    SplitOctonionImaginaryAction.Imaginary :=
  LinearEquiv.finiteDimensional imaginaryCoordLinearEquiv.symm

local instance : FiniteDimensional ℝ Support :=
  FiniteDimensional.of_injective (Submodule.subtype Support) (by
    intro X Y h
    exact Subtype.ext h)

local instance : FiniteDimensional ℝ Plus :=
  FiniteDimensional.of_injective (Submodule.subtype Plus) (by
    intro X Y h
    exact Subtype.ext h)

local instance : FiniteDimensional ℝ Minus :=
  FiniteDimensional.of_injective (Submodule.subtype Minus) (by
    intro X Y h
    exact Subtype.ext h)

local instance : Module.Finite ℝ (Module.Dual ℝ Plus) :=
  (Module.finite_dual_iff ℝ).2 inferInstance

local instance : Module.Finite ℝ (Module.Dual ℝ Minus) :=
  (Module.finite_dual_iff ℝ).2 inferInstance

/-- Pair a positive eigenvector against the negative eigenspace. -/
def plusToMinusDual : Plus →ₗ[ℝ] Module.Dual ℝ Minus where
  toFun X := (imaginaryPolarBilin X.1.1).comp
    ((Submodule.subtype Support).comp (Submodule.subtype Minus))
  map_add' := by
    intro X Y
    ext Z
    change imaginaryPolarBilin (X.1.1 + Y.1.1) Z.1.1 =
      imaginaryPolarBilin X.1.1 Z.1.1 + imaginaryPolarBilin Y.1.1 Z.1.1
    rw [map_add]
    rfl
  map_smul' := by
    intro r X
    ext Y
    change imaginaryPolarBilin (r • X.1.1) Y.1.1 =
      r • imaginaryPolarBilin X.1.1 Y.1.1
    rw [map_smul]
    rfl

theorem plusToMinusDual_injective : Function.Injective plusToMinusDual := by
  intro X Y hXY
  have hX : plusToMinusDual (X - Y) = 0 := by
    calc
      plusToMinusDual (X - Y) = plusToMinusDual X - plusToMinusDual Y :=
        LinearMap.map_sub plusToMinusDual X Y
      _ = 0 := sub_eq_zero.mpr hXY
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply supportMetric_nondegenerate (X.1 - Y.1)
  intro Z
  rw [support_eq_plus_add_minus Z]
  have hPlus := supportMetric_plus_isotropic (X.1 - Y.1) (supportPPlus Z)
    (Submodule.sub_mem Plus X.2 Y.2) (supportPPlus_mem Z)
  have hMinus : supportMetric (X.1 - Y.1) (supportPMinus Z) = 0 := by
    have hfun := LinearMap.congr_fun hX ⟨supportPMinus Z, supportPMinus_mem Z⟩
    simpa [plusToMinusDual, supportMetric] using hfun
  calc
    supportMetric (X.1 - Y.1) (supportPPlus Z + supportPMinus Z) =
        supportMetric (X.1 - Y.1) (supportPPlus Z) +
          supportMetric (X.1 - Y.1) (supportPMinus Z) := by
      unfold supportMetric
      exact LinearMap.map_add _ _ _
    _ = 0 := by rw [hPlus, hMinus, add_zero]

/-- Pair a negative eigenvector against the positive eigenspace. -/
def minusToPlusDual : Minus →ₗ[ℝ] Module.Dual ℝ Plus where
  toFun X := (imaginaryPolarBilin X.1.1).comp
    ((Submodule.subtype Support).comp (Submodule.subtype Plus))
  map_add' := by
    intro X Y
    ext Z
    change imaginaryPolarBilin (X.1.1 + Y.1.1) Z.1.1 =
      imaginaryPolarBilin X.1.1 Z.1.1 + imaginaryPolarBilin Y.1.1 Z.1.1
    rw [map_add]
    rfl
  map_smul' := by
    intro r X
    ext Y
    change imaginaryPolarBilin (r • X.1.1) Y.1.1 =
      r • imaginaryPolarBilin X.1.1 Y.1.1
    rw [map_smul]
    rfl

theorem minusToPlusDual_injective : Function.Injective minusToPlusDual := by
  intro X Y hXY
  have hX : minusToPlusDual (X - Y) = 0 := by
    calc
      minusToPlusDual (X - Y) = minusToPlusDual X - minusToPlusDual Y :=
        LinearMap.map_sub minusToPlusDual X Y
      _ = 0 := sub_eq_zero.mpr hXY
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply supportMetric_nondegenerate (X.1 - Y.1)
  intro Z
  rw [support_eq_plus_add_minus Z]
  have hPlus : supportMetric (X.1 - Y.1) (supportPPlus Z) = 0 := by
    have hfun := LinearMap.congr_fun hX ⟨supportPPlus Z, supportPPlus_mem Z⟩
    simpa [minusToPlusDual, supportMetric] using hfun
  have hMinus := supportMetric_minus_isotropic (X.1 - Y.1) (supportPMinus Z)
    (Submodule.sub_mem Minus X.2 Y.2) (supportPMinus_mem Z)
  calc
    supportMetric (X.1 - Y.1) (supportPPlus Z + supportPMinus Z) =
        supportMetric (X.1 - Y.1) (supportPPlus Z) +
          supportMetric (X.1 - Y.1) (supportPMinus Z) := by
      unfold supportMetric
      exact LinearMap.map_add _ _ _
    _ = 0 := by rw [hPlus, hMinus, add_zero]

theorem finrank_supportPlus_eq_supportMinus :
    Module.finrank ℝ Plus = Module.finrank ℝ Minus := by
  apply le_antisymm
  · calc
      Module.finrank ℝ Plus ≤ Module.finrank ℝ (Module.Dual ℝ Minus) :=
        LinearMap.finrank_le_finrank_of_injective plusToMinusDual_injective
      _ = Module.finrank ℝ Minus :=
        Subspace.dual_finrank_eq (K := ℝ) (V := Minus)
  · calc
      Module.finrank ℝ Minus ≤ Module.finrank ℝ (Module.Dual ℝ Plus) :=
        LinearMap.finrank_le_finrank_of_injective minusToPlusDual_injective
      _ = Module.finrank ℝ Plus :=
        Subspace.dual_finrank_eq (K := ℝ) (V := Plus)

theorem finrank_supportPlus_add_supportMinus :
    Module.finrank ℝ Plus + Module.finrank ℝ Minus = 6 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq Plus Minus
  rw [supportPlus_sup_minus_eq_top, supportPlus_inf_minus_eq_bot,
    finrank_top, finrank_bot, finrank_activeSupport] at h
  simpa [add_zero, zero_add] using h.symm

theorem finrank_supportPlus : Module.finrank ℝ Plus = 3 := by
  have hsum := finrank_supportPlus_add_supportMinus
  rw [← finrank_supportPlus_eq_supportMinus] at hsum
  omega

theorem finrank_supportMinus : Module.finrank ℝ Minus = 3 := by
  rw [← finrank_supportPlus_eq_supportMinus]
  exact finrank_supportPlus

end InfoGeometry.Lie.SplitOctonionImaginaryEllLagrangianDimension
