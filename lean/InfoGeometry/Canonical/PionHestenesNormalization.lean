import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.FiniteSpinAlgebra

import InfoGeometry.Canonical.PionChiralGoldstoneNative
import InfoGeometry.Canonical.BogoliubovClosedForms

/-!
# Pion/Hestenes normalization bridge

This file is a semantic normalization layer over the repository-owned real
split-null CAR operators.  It introduces no new carrier and no new CAR
construction.  The pion names are aliases for the concrete doubled-space
creation/annihilation operators; the Hestenes formulae are proved equalities.

The TKK Cartan involution is deliberately absent here.  This owner only
records the coordinate change between the Hestenes axes
`(modular_j, spectral_epsilon, complex_i)` and the existing null pair.
-/

noncomputable section

namespace InfoGeometry.Canonical.PionHestenesNormalization

open InfoGeometry.Krein
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.PionChiralGoldstoneNative
open InfoGeometry.Canonical.TomitaKreinNilpotentAtom
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovClosedForms

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- The `+1` null lane, using the existing concrete CAR owner. -/
noncomputable abbrev pionPlus : EndH :=
  concreteCARCreation (E := E)

/-- The `-1` null lane, using the existing concrete CAR owner. -/
noncomputable abbrev pionMinus : EndH :=
  concreteCARAnnihilation (E := E)

/-- The neutral grading direction. -/
noncomputable def pionZero : EndH :=
  (1 / 2 : ℝ) • spectral_epsilon (E := E)

omit [CompleteSpace E] in
@[simp] theorem two_smul_pionZero :
    (2 : ℝ) • pionZero (E := E) = spectral_epsilon (E := E) := by
  simp [pionZero, smul_smul]

/-- The concrete `+1` lane is the Hestenes formula `½ (H - K)`. -/
theorem pionPlus_eq_half_H_sub_K :
    pionPlus (E := E) =
      (1 / 2 : ℝ) •
        (modular_j (E := E) - complex_i (E := E)) :=
  hestenesPionPlus_eq_doubledSpace_formula (E := E)

/-- The concrete `-1` lane is the Hestenes formula `½ (H + K)`. -/
theorem pionMinus_eq_half_H_add_K :
    pionMinus (E := E) =
      (1 / 2 : ℝ) •
        (modular_j (E := E) + complex_i (E := E)) :=
  hestenesPionMinus_eq_doubledSpace_formula (E := E)

theorem modular_j_eq_pionPlus_add_pionMinus :
    modular_j (E := E) =
      pionPlus (E := E) + pionMinus (E := E) := by
  rw [pionPlus_eq_half_H_sub_K (E := E),
    pionMinus_eq_half_H_add_K (E := E)]
  module

theorem complex_i_eq_pionMinus_sub_pionPlus :
    complex_i (E := E) =
      pionMinus (E := E) - pionPlus (E := E) := by
  rw [pionPlus_eq_half_H_sub_K (E := E),
    pionMinus_eq_half_H_add_K (E := E)]
  module

@[simp] theorem pionPlus_sq :
    (pionPlus (E := E)).comp (pionPlus (E := E)) = 0 :=
  concrete_creation_square_zero (E := E)

@[simp] theorem pionMinus_sq :
    (pionMinus (E := E)).comp (pionMinus (E := E)) = 0 :=
  concrete_annihilation_square_zero (E := E)

theorem pion_CAR :
    CARBracket (E := E) (pionMinus (E := E)) (pionPlus (E := E)) =
      ContinuousLinearMap.id ℝ H₂ :=
  concrete_car_minus_plus (E := E)

theorem pion_raise_lower_lie :
    ⁅pionPlus (E := E), pionMinus (E := E)⁆ =
      (2 : ℝ) • pionZero (E := E) := by
  rw [LieRing.of_associative_ring_bracket]
  simpa [pionZero, CCRBracket, fockCommutator_eq] using
    (concrete_car_creation_annihilation_ccrBracket_eq_spectral_epsilon
      (E := E))

/-- The neutral grading has weight `+1` on the positive null lane. -/
theorem pionZero_pionPlus_lie :
    ⁅pionZero (E := E), pionPlus (E := E)⁆ = pionPlus (E := E) := by
  rw [LieRing.of_associative_ring_bracket]
  have hhalf : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
  apply ContinuousLinearMap.ext
  intro v
  have hv :
      InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hv]
  apply DoubledSpace.ext <;>
    simp [pionZero, pionPlus, spectral_epsilon,
      concreteCARCreation, cliffordConcreteCreation_apply_to_doubled,
      ← add_smul, hhalf]

/-- The neutral grading has weight `-1` on the negative null lane. -/
theorem pionZero_pionMinus_lie :
    ⁅pionZero (E := E), pionMinus (E := E)⁆ = -(pionMinus (E := E)) := by
  rw [LieRing.of_associative_ring_bracket]
  have hhalf : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
  apply ContinuousLinearMap.ext
  intro v
  have hv :
      InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hv]
  apply DoubledSpace.ext
  · simp [pionZero, pionMinus, spectral_epsilon,
      concreteCARAnnihilation, cliffordConcreteAnnihilation_apply_to_doubled]
  · simp [pionZero, pionMinus, spectral_epsilon,
      concreteCARAnnihilation, cliffordConcreteAnnihilation_apply_to_doubled]
    rw [sub_eq_add_neg, ← neg_add, ← add_smul, hhalf, one_smul]

/-- The complete finite real pion atom: CAR plus the `sl₂` ladder weights. -/
theorem pion_real_atom :
    (pionPlus (E := E)).comp (pionPlus (E := E)) = 0 ∧
    (pionMinus (E := E)).comp (pionMinus (E := E)) = 0 ∧
    CARBracket (E := E) (pionMinus (E := E)) (pionPlus (E := E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) ∧
    ⁅pionPlus (E := E), pionMinus (E := E)⁆ =
      (2 : ℝ) • pionZero (E := E) ∧
    ⁅pionZero (E := E), pionPlus (E := E)⁆ = pionPlus (E := E) ∧
    ⁅pionZero (E := E), pionMinus (E := E)⁆ = -(pionMinus (E := E)) := by
  exact ⟨pionPlus_sq (E := E),
    pionMinus_sq (E := E),
    pion_CAR (E := E),
    pion_raise_lower_lie (E := E),
    pionZero_pionPlus_lie (E := E),
    pionZero_pionMinus_lie (E := E)⟩

/-! The internal phase axis is exposed only through the existing rotor owner. -/

noncomputable def pionPhaseRotor (θ : ℝ) : EndH :=
  KRotation (E := E) (θ / 2)

theorem pionPhaseRotor_closed_form (θ : ℝ) :
    pionPhaseRotor (E := E) θ =
      Real.cos (θ / 2) • (1 : EndH) +
        Real.sin (θ / 2) • complex_i (E := E) := by
  exact KRotation_eq_cos_add_sin_K (E := E) (θ / 2)

end InfoGeometry.Canonical.PionHestenesNormalization
