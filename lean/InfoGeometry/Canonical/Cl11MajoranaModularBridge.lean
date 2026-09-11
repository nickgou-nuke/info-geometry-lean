import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.MajoranaPHSZeroMode

/-!
# Native `Cl(1,1)`/Majorana modular bridge

This file records the identifications between the existing concrete doubled
Majorana core and the existing Tomita--Krein operators.  It introduces no
new carrier: the bridge is between the native owners already used by both
subsystems.
-/

namespace InfoGeometry.Quantum.RealMajoranaCategory

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.MajoranaPHSZeroMode

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

@[simp] theorem cl11DoubledCore_J_eq_modular_j :
    (cl11DoubledCore E).J = (modular_j (E := E)).toLinearMap := rfl

@[simp] theorem cl11DoubledCore_eps_eq_spectral_epsilon :
    (cl11DoubledCore E).eps = (spectral_epsilon (E := E)).toLinearMap := rfl

@[simp] theorem cl11DoubledCore_Pi_eq_spectral_epsilon :
    (cl11DoubledCore E).Pi = (spectral_epsilon (E := E)).toLinearMap := rfl

theorem cl11DoubledCore_K_eq_J_comp_eps :
    (cl11DoubledCore E).K =
      (cl11DoubledCore E).J.comp (cl11DoubledCore E).eps := by
  rfl

theorem cl11DoubledCore_K_eq_modular_j_comp_spectral_epsilon :
    (cl11DoubledCore E).K =
      (modular_j (E := E)).toLinearMap.comp
        (spectral_epsilon (E := E)).toLinearMap := by
  rfl

theorem concrete_majorana_swap_eq_cl11DoubledCore_J :
    (InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARCreation (E := E) +
      InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARAnnihilation (E := E)).toLinearMap =
      (cl11DoubledCore E).J := by
  rw [concrete_majorana_swap_eq_modular_j (E := E)]
  rfl

theorem concrete_majorana_swap_is_phs_invariant_and_is_core_J :
    IsPHSInvariant (E := E)
      (InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARCreation (E := E) +
        InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARAnnihilation (E := E)) ∧
    (InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARCreation (E := E) +
      InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARAnnihilation (E := E)).toLinearMap =
      (cl11DoubledCore E).J := by
  constructor
  exact concrete_majorana_swap_is_phs_invariant (E := E)
  exact concrete_majorana_swap_eq_cl11DoubledCore_J (E := E)

theorem cl11CanonicalPolarization_involution_eq_spectral_epsilon :
    (cl11CanonicalPolarization (E := E)).involution =
      (spectral_epsilon (E := E)).toLinearMap := by
  ext v
  change (spectralPlusProj (E := E)).toLinearMap v -
      (spectralMinusProj (E := E)).toLinearMap v =
    (spectral_epsilon (E := E)).toLinearMap v
  have hhalf (z : E) :
      (2 : ℝ)⁻¹ • z + (2 : ℝ)⁻¹ • z = z := by
    rw [← add_smul]
    norm_num
  apply DoubledSpace.ext
  · simp only [spectral_epsilon]
    simp [spectralPlusProj, spectralMinusProj, sub_eq_add_neg]
    convert hhalf _ using 1 <;> norm_num
  · simp only [spectral_epsilon]
    simp [spectralPlusProj, spectralMinusProj, sub_eq_add_neg]
    rw [← neg_add]
    convert congrArg Neg.neg (hhalf _) using 1 <;> norm_num

theorem cl11Majorana_modular_bridge :
    (cl11DoubledCore E).J = (modular_j (E := E)).toLinearMap ∧
    (cl11DoubledCore E).eps = (spectral_epsilon (E := E)).toLinearMap ∧
    (cl11DoubledCore E).Pi = (spectral_epsilon (E := E)).toLinearMap ∧
    (cl11DoubledCore E).K =
      (modular_j (E := E)).toLinearMap.comp
        (spectral_epsilon (E := E)).toLinearMap ∧
    (cl11CanonicalPolarization (E := E)).involution =
      (spectral_epsilon (E := E)).toLinearMap ∧
    IsPHSInvariant (E := E)
      (InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARCreation (E := E) +
        InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARAnnihilation (E := E)) := by
  exact ⟨cl11DoubledCore_J_eq_modular_j (E := E),
    cl11DoubledCore_eps_eq_spectral_epsilon (E := E),
    cl11DoubledCore_Pi_eq_spectral_epsilon (E := E),
    cl11DoubledCore_K_eq_modular_j_comp_spectral_epsilon (E := E),
    cl11CanonicalPolarization_involution_eq_spectral_epsilon (E := E),
    (concrete_majorana_swap_is_phs_invariant_and_is_core_J (E := E)).1⟩

end InfoGeometry.Quantum.RealMajoranaCategory
