import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinReal
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements

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
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements

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

end ChiralNambuFrame

end InfoGeometry.OperatorAlgebra.RealDoubledChiralNambuFrame
