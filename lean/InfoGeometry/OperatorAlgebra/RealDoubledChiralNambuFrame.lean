/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinReal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.TomitaKreinNilpotentAtom
import InfoGeometry.Krein.MajoranaSheetConnectors

/-!
# Nambu-style frame on the doubled real chiral carrier

This file records the exact matrix-index part of the Nambu dictionary.  The
two sheets are the two matrix-unit sectors; the spin/internal factor is left
inside the coefficient carrier `E`.  No particle-hole anti-linearity or BdG
Hamiltonian condition is claimed on the real carrier.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralNambuFrame

open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.TomitaKreinNilpotentAtom

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev NambuEnd := DoubledSpace E →L[ℝ] DoubledSpace E

/-- Nambu sheet grading (`τ₃`) on the real carrier. -/
abbrev nambuChirality : NambuEnd (E := E) := gamma5 (E := E)

/-- Linear sheet exchange (`τ₁`), before adding any complex conjugation. -/
abbrev nambuSheetFlip : NambuEnd (E := E) := etaChiral (E := E)

/-- The two matrix-unit projectors (`P₊`, `P₋`). -/
abbrev nambuProjectorPlus : NambuEnd (E := E) :=
  leftChiralProjector (E := E)

abbrev nambuProjectorMinus : NambuEnd (E := E) :=
  rightChiralProjector (E := E)

/-- The real operator analogue of `i τ₂ = τ₃ τ₁`. -/
abbrev nambuComplexStructure : NambuEnd (E := E) :=
  chiralComplexStructure (E := E)

@[simp] theorem nambuChirality_sq :
    (nambuChirality (E := E)).comp (nambuChirality (E := E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  gamma5_involution (E := E)

@[simp] theorem nambuSheetFlip_sq :
    (nambuSheetFlip (E := E)).comp (nambuSheetFlip (E := E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  etaChiral_involution (E := E)

theorem nambuChirality_sheetFlip_anticommute :
    (nambuSheetFlip (E := E)).comp (nambuChirality (E := E)) =
      -((nambuChirality (E := E)).comp (nambuSheetFlip (E := E))) :=
  etaChiral_gamma5_anticommute (E := E)

@[simp] theorem nambuComplexStructure_sq :
    (nambuComplexStructure (E := E)).comp
        (nambuComplexStructure (E := E)) =
      -(ContinuousLinearMap.id ℝ (DoubledSpace E)) :=
  chiralComplexStructure_sq (E := E)

theorem nambuSheetFlip_swaps_projectors :
    (nambuSheetFlip (E := E)).comp (nambuProjectorPlus (E := E)) =
      (nambuProjectorMinus (E := E)).comp (nambuSheetFlip (E := E)) :=
  etaChiral_comp_left_projector (E := E)

theorem nambuSheetFlip_swaps_projectors' :
    (nambuSheetFlip (E := E)).comp (nambuProjectorMinus (E := E)) =
      (nambuProjectorPlus (E := E)).comp (nambuSheetFlip (E := E)) :=
  etaChiral_comp_right_projector (E := E)

/-- Conjugating by the sheet flip transports the positive chiral projector to
the negative one. -/
theorem nambuSheetFlip_conjugates_projectorPlus :
    (nambuSheetFlip (E := E)).comp
        ((nambuProjectorPlus (E := E)).comp (nambuSheetFlip (E := E))) =
      nambuProjectorMinus (E := E) :=
  etaChiral_comp_leftChiralProjector_comp_etaChiral (E := E)

theorem nambuSheetFlip_conjugates_projectorMinus :
    (nambuSheetFlip (E := E)).comp
        ((nambuProjectorMinus (E := E)).comp (nambuSheetFlip (E := E))) =
      nambuProjectorPlus (E := E) :=
  etaChiral_comp_rightChiralProjector_comp_etaChiral (E := E)

theorem nambuProjectors_complementary :
    nambuProjectorPlus (E := E) + nambuProjectorMinus (E := E) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  exact leftChiralProjector_add_rightChiralProjector (E := E)

theorem nambuProjectors_mutually_annihilate :
    (nambuProjectorPlus (E := E)).comp (nambuProjectorMinus (E := E)) = 0 ∧
    (nambuProjectorMinus (E := E)).comp (nambuProjectorPlus (E := E)) = 0 := by
  exact ⟨leftChiralProjector_comp_rightChiralProjector (E := E),
    rightChiralProjector_comp_leftChiralProjector (E := E)⟩

@[simp] theorem nambuProjectorPlus_idempotent :
    (nambuProjectorPlus (E := E)).comp (nambuProjectorPlus (E := E)) =
      nambuProjectorPlus (E := E) :=
  leftChiralProjector_idempotent (E := E)

@[simp] theorem nambuProjectorMinus_idempotent :
    (nambuProjectorMinus (E := E)).comp (nambuProjectorMinus (E := E)) =
      nambuProjectorMinus (E := E) :=
  rightChiralProjector_idempotent (E := E)

/-- A finite real Nambu/BdG-shaped operator packet: normal plus pairing part.

`normal` is sheet-preserving and `pairing` is sheet-exchanging.  This is an
operator decomposition, not yet a physical BdG Hamiltonian or a
particle-hole symmetry theorem.
-/
structure ChiralNambuFrame where
  normal : NambuEnd (E := E)
  normal_block : normal ∈ blockDiagonalSubmodule (E := E)
  pairing : NambuEnd (E := E)
  pairing_off_block : pairing ∈ offBlockSubmodule (E := E)

namespace ChiralNambuFrame

abbrev operator (F : ChiralNambuFrame (E := E)) : NambuEnd (E := E) :=
  F.normal + F.pairing

theorem normal_isBlock (F : ChiralNambuFrame (E := E)) :
    IsBlockDiagonal F.normal := F.normal_block

theorem pairing_isOffBlock (F : ChiralNambuFrame (E := E)) :
    IsOffBlockDiagonal F.pairing := F.pairing_off_block

theorem square_pairing_isBlock (F : ChiralNambuFrame (E := E)) :
    F.pairing.comp F.pairing ∈ blockDiagonalSubmodule (E := E) :=
  offSubmodule_comp_off F.pairing_off_block F.pairing_off_block

/-- A normal block followed by a pairing block remains off-diagonal. -/
theorem normal_comp_pairing_isOffBlock (F : ChiralNambuFrame (E := E)) :
    F.normal.comp F.pairing ∈ offBlockSubmodule (E := E) :=
  blockSubmodule_comp_off F.normal_block F.pairing_off_block

/-- A pairing block followed by a normal block remains off-diagonal. -/
theorem pairing_comp_normal_isOffBlock (F : ChiralNambuFrame (E := E)) :
    F.pairing.comp F.normal ∈ offBlockSubmodule (E := E) :=
  offSubmodule_comp_block F.pairing_off_block F.normal_block

/-- The square of a Nambu frame is the four-term block expansion. -/
theorem operator_comp_operator_expansion (F : ChiralNambuFrame (E := E)) :
    F.operator.comp F.operator =
      F.normal.comp F.normal + F.normal.comp F.pairing +
        F.pairing.comp F.normal + F.pairing.comp F.pairing := by
  change (F.normal + F.pairing).comp (F.normal + F.pairing) = _
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  abel

/-- The diagonal terms in the square of a Nambu frame preserve the two
chiral sheets. -/
theorem operator_comp_operator_block_part_isBlock
    (F : ChiralNambuFrame (E := E)) :
    IsBlockDiagonal
      (F.normal.comp F.normal + F.pairing.comp F.pairing) := by
  apply IsBlockDiagonal.add
  · exact IsBlockDiagonal.comp F.normal_block F.normal_block
  · exact IsOffBlockDiagonal.comp F.pairing_off_block F.pairing_off_block

/-- The mixed terms in the square of a Nambu frame exchange the two chiral
sheets. -/
theorem operator_comp_operator_off_part_isOffBlock
    (F : ChiralNambuFrame (E := E)) :
    IsOffBlockDiagonal
      (F.normal.comp F.pairing + F.pairing.comp F.normal) := by
  apply IsOffBlockDiagonal.add
  · exact IsBlockDiagonal.comp_off F.normal_block F.pairing_off_block
  · exact IsOffBlockDiagonal.comp_block F.pairing_off_block F.normal_block

end ChiralNambuFrame

/-! ## Canonical CAR ladder compatibility

The generic Nambu frame is defined on arbitrary universes.  The concrete
split-CAR ladders live on the canonical `Type 0` doubled carrier, so this
bridge is stated at exactly that owner-aligned universe rather than silently
coercing between carriers. -/

section CanonicalCAR

variable {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem concreteCARCreation_eq_nambuProjectorPlus_comp_nambuSheetFlip :
    concreteCARCreation (E := E) =
      (nambuProjectorPlus (E := E)).comp
        (nambuSheetFlip (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : DoubledSpace E) = u := by
    exact DoubledSpace.ext rfl rfl
  rw [← hu]
  apply DoubledSpace.ext <;>
    simp [nambuProjectorPlus, nambuSheetFlip, leftChiralProjector,
      etaChiral, gamma5, spectral_epsilon, modular_j, one_div,
      concreteCARCreation,
      cliffordConcreteCreation_apply_to_doubled] <;> module

theorem concreteCARAnnihilation_eq_nambuProjectorMinus_comp_nambuSheetFlip :
    concreteCARAnnihilation (E := E) =
      (nambuProjectorMinus (E := E)).comp
        (nambuSheetFlip (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : DoubledSpace E) = u := by
    exact DoubledSpace.ext rfl rfl
  rw [← hu]
  apply DoubledSpace.ext <;>
    simp [nambuProjectorMinus, nambuSheetFlip, rightChiralProjector,
      etaChiral, gamma5, spectral_epsilon, modular_j, one_div,
      concreteCARAnnihilation,
      cliffordConcreteAnnihilation_apply_to_doubled] <;> module

theorem nambuCreation_square_zero :
    ((nambuProjectorPlus (E := E)).comp (nambuSheetFlip (E := E))).comp
        ((nambuProjectorPlus (E := E)).comp (nambuSheetFlip (E := E))) = 0 := by
  rw [← concreteCARCreation_eq_nambuProjectorPlus_comp_nambuSheetFlip (E := E)]
  exact concrete_creation_square_zero (E := E)

theorem nambuAnnihilation_square_zero :
    ((nambuProjectorMinus (E := E)).comp (nambuSheetFlip (E := E))).comp
        ((nambuProjectorMinus (E := E)).comp (nambuSheetFlip (E := E))) = 0 := by
  rw [← concreteCARAnnihilation_eq_nambuProjectorMinus_comp_nambuSheetFlip (E := E)]
  exact concrete_annihilation_square_zero (E := E)

theorem nambuCreation_comp_nambuAnnihilation_eq_spectralPlusProj :
    ((nambuProjectorPlus (E := E)).comp (nambuSheetFlip (E := E))).comp
        ((nambuProjectorMinus (E := E)).comp (nambuSheetFlip (E := E))) =
      spectralPlusProj (E := E) := by
  rw [← concreteCARCreation_eq_nambuProjectorPlus_comp_nambuSheetFlip (E := E),
    ← concreteCARAnnihilation_eq_nambuProjectorMinus_comp_nambuSheetFlip (E := E)]
  exact concrete_creation_comp_annihilation_eq_spectralPlusProj (E := E)

theorem nambuAnnihilation_comp_nambuCreation_eq_spectralMinusProj :
    ((nambuProjectorMinus (E := E)).comp (nambuSheetFlip (E := E))).comp
        ((nambuProjectorPlus (E := E)).comp (nambuSheetFlip (E := E))) =
      spectralMinusProj (E := E) := by
  rw [← concreteCARAnnihilation_eq_nambuProjectorMinus_comp_nambuSheetFlip (E := E),
    ← concreteCARCreation_eq_nambuProjectorPlus_comp_nambuSheetFlip (E := E)]
  exact concrete_annihilation_comp_creation_eq_spectralMinusProj (E := E)

theorem nambuCreation_kernel_iff_plusSheet (u : DoubledSpace E) :
    ((nambuProjectorPlus (E := E)).comp (nambuSheetFlip (E := E))) u = 0 ↔
      u ∈ plusSheet (E := E) := by
  rw [← concreteCARCreation_eq_nambuProjectorPlus_comp_nambuSheetFlip (E := E)]
  exact InfoGeometry.Krein.MajoranaSheetConnectors.creation_kernel_iff_plusSheet u

theorem nambuAnnihilation_kernel_iff_minusSheet (u : DoubledSpace E) :
    ((nambuProjectorMinus (E := E)).comp (nambuSheetFlip (E := E))) u = 0 ↔
      u ∈ minusSheet (E := E) := by
  rw [← concreteCARAnnihilation_eq_nambuProjectorMinus_comp_nambuSheetFlip (E := E)]
  exact InfoGeometry.Krein.MajoranaSheetConnectors.annihilation_kernel_iff_minusSheet u

theorem nambuCreation_range_iff_plusSheet (u : DoubledSpace E) :
    (∃ v : DoubledSpace E,
      ((nambuProjectorPlus (E := E)).comp (nambuSheetFlip (E := E))) v = u) ↔
      u ∈ plusSheet (E := E) := by
  rw [← concreteCARCreation_eq_nambuProjectorPlus_comp_nambuSheetFlip (E := E)]
  exact InfoGeometry.Krein.MajoranaSheetConnectors.creation_range_iff_plusSheet u

theorem nambuAnnihilation_range_iff_minusSheet (u : DoubledSpace E) :
    (∃ v : DoubledSpace E,
      ((nambuProjectorMinus (E := E)).comp (nambuSheetFlip (E := E))) v = u) ↔
      u ∈ minusSheet (E := E) := by
  rw [← concreteCARAnnihilation_eq_nambuProjectorMinus_comp_nambuSheetFlip (E := E)]
  exact InfoGeometry.Krein.MajoranaSheetConnectors.annihilation_range_iff_minusSheet u

theorem nambuMajoranaSwap_eq_modular_j :
    (nambuProjectorPlus (E := E)).comp (nambuSheetFlip (E := E)) +
        (nambuProjectorMinus (E := E)).comp (nambuSheetFlip (E := E)) =
      modular_j (E := E) := by
  rw [← concreteCARCreation_eq_nambuProjectorPlus_comp_nambuSheetFlip (E := E),
    ← concreteCARAnnihilation_eq_nambuProjectorMinus_comp_nambuSheetFlip (E := E)]
  exact InfoGeometry.Canonical.MajoranaPHSZeroMode.concrete_majorana_swap_eq_modular_j
    (E := E)

theorem nambuMajoranaCreation_tomita_swap :
    tomitaConjOp (E := E)
        ((nambuProjectorPlus (E := E)).comp (nambuSheetFlip (E := E))) =
      (nambuProjectorMinus (E := E)).comp (nambuSheetFlip (E := E)) := by
  rw [← concreteCARCreation_eq_nambuProjectorPlus_comp_nambuSheetFlip (E := E),
    ← concreteCARAnnihilation_eq_nambuProjectorMinus_comp_nambuSheetFlip (E := E)]
  exact InfoGeometry.Canonical.MajoranaPHSZeroMode.concrete_majorana_creation_swap
    (E := E)

theorem nambuMajoranaAnnihilation_tomita_swap :
    tomitaConjOp (E := E)
        ((nambuProjectorMinus (E := E)).comp (nambuSheetFlip (E := E))) =
      (nambuProjectorPlus (E := E)).comp (nambuSheetFlip (E := E)) := by
  rw [← concreteCARAnnihilation_eq_nambuProjectorMinus_comp_nambuSheetFlip (E := E),
    ← concreteCARCreation_eq_nambuProjectorPlus_comp_nambuSheetFlip (E := E)]
  exact InfoGeometry.Canonical.MajoranaPHSZeroMode.concrete_majorana_annihilation_swap
    (E := E)

end CanonicalCAR

end InfoGeometry.OperatorAlgebra.RealDoubledChiralNambuFrame
