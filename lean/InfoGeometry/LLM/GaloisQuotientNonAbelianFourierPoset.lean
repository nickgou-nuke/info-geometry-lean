/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.LanguageSymmetryGalois
import InfoGeometry.LLM.LanguageSymmetryDihedral
import InfoGeometry.LLM.LanguageSymmetryQuotient
import InfoGeometry.LLM.LanguageSymmetryWalsh
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Galois actions, quotient variance, and dihedral character blocks

This module connects the three owner branches by actual compatibility theorems.
Galois automorphisms act entrywise on the constructed dihedral blocks. The
existing Walsh coordinate signs instantiate the subgroup variance theorem when
the averaging subgroup contains the corresponding bit flip.

The dependency graph is branching: no linear order on the concepts, arbitrary
identification `G/H ≃ D_N`, full Peter--Weyl classification, or BKM metric
interpretation is claimed by the historical `Poset` filename.
-/

noncomputable section

namespace InfoGeometry.LLM.LanguageSymmetry

open scoped BigOperators

section GaloisBlocks

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {N} ℚ K]

/-- Field automorphisms permute the frequency label of the actual nonabelian
matrix representation; reflection's rational entries remain fixed. -/
theorem galois_dihedralCharacterMatrix (σ : Gal(K / ℚ)) {ζ : K}
    (hζ : ζ ^ N = 1) (k : ZMod N) (g : DihedralGroup N) :
    (dihedralCharacterMatrix ((AddChar.zmodChar N hζ).mulShift k) g).map σ =
      dihedralCharacterMatrix ((AddChar.zmodChar N hζ).mulShift
        ((IsCyclotomicExtension.Rat.galEquivZMod N K σ : ZMod N) * k)) g := by
  cases g <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [dihedralCharacterMatrix, pairedRotation, InfoGeometry.Clifford.J_mat,
      galois_zmodChar_action, mul_assoc]

end GaloisBlocks

section DihedralQuotient

/-- A dihedral quotient obtained by forgetting an independent binary
coordinate. The inverse uses the explicit section `g ↦ (g,1)`. -/
def dihedralBinaryQuotientEquiv (N : ℕ) :
    ((DihedralGroup N × Multiplicative (ZMod 2)) ⧸
      (MonoidHom.fst (DihedralGroup N) (Multiplicative (ZMod 2))).ker) ≃*
        DihedralGroup N :=
  QuotientGroup.quotientKerEquivOfRightInverse
    (MonoidHom.fst (DihedralGroup N) (Multiplicative (ZMod 2)))
    (fun g => (g, 1)) (fun _ => rfl)

/-- The quotient equivalence is literally the first coordinate on representatives. -/
theorem dihedralBinaryQuotientEquiv_mk (N : ℕ)
    (g : DihedralGroup N) (b : Multiplicative (ZMod 2)) :
    dihedralBinaryQuotientEquiv N (QuotientGroup.mk (g, b)) = g := rfl

/-- The matrix representation on the constructed quotient pulls back to the
dihedral action on the first factor of the product group. -/
theorem dihedral_binary_quotient_matrix_action {N : ℕ} {K : Type*} [CommRing K]
    (χ : AddChar (ZMod N) K) (g : DihedralGroup N) (b : Multiplicative (ZMod 2)) :
    ((dihedralCharacterMatrix χ).comp
      (dihedralBinaryQuotientEquiv N).toMonoidHom) (QuotientGroup.mk (g, b)) =
        dihedralCharacterMatrix χ g := rfl

end DihedralQuotient

section WalshQuotient

variable (d : ℕ) (r : Fin d)
  (H : Subgroup (Multiplicative (Fin d → ZMod 2)))

/-- A subgroup containing a coordinate bit flip detects that coordinate's
existing Walsh sign as a nontrivial restricted character. -/
theorem coordinateSign_subgroup_nontrivial
    (hflip : Multiplicative.ofAdd (Pi.single r (1 : ZMod 2)) ∈ H) :
    ∃ h : H, (coordinateSign d r).toMonoidHom h.val ≠ 1 := by
  refine ⟨⟨Multiplicative.ofAdd (Pi.single r (1 : ZMod 2)), hflip⟩, ?_⟩
  norm_num [coordinateSign, AddChar.zmodChar_apply, ZMod.val_one_eq_one_mod]

variable [Fintype H] [Invertible (Fintype.card H : ℝ)]

/-- The exact quotient variance theorem instantiated by a concrete Walsh
coordinate and an actual subgroup containing its bit flip. -/
theorem quotient_walsh_coordinate_surprisal_defect
    (hflip : Multiplicative.ofAdd (Pi.single r (1 : ZMod 2)) ∈ H)
    {s : ℝ} (hs : |s| < 1) :
    let χ := (coordinateSign d r).toMonoidHom
    let P := Representation.averageMap ((TannakaDuality.FiniteGroup.rightRegular (k := ℝ)
      (G := Multiplicative (Fin d → ZMod 2))).comp H.subtype)
    let L := binarySurprisalOperator s (characterMultiplier χ)
    P * (L * L) * P - (P * L * P) * (P * L * P) = (Real.artanh s) ^ 2 • P := by
  apply quotient_binary_surprisal_defect H (coordinateSign d r).toMonoidHom
  · intro x
    exact coordinateSign_sq d r x.toAdd
  · exact coordinateSign_subgroup_nontrivial d r H hflip
  · exact hs

/-- The surviving variance is nonzero exactly at nonzero coupling. -/
theorem quotient_walsh_coordinate_surprisal_defect_ne_zero_iff
    (hflip : Multiplicative.ofAdd (Pi.single r (1 : ZMod 2)) ∈ H)
    {s : ℝ} (hs : |s| < 1) :
    let χ := (coordinateSign d r).toMonoidHom
    let P := Representation.averageMap ((TannakaDuality.FiniteGroup.rightRegular (k := ℝ)
      (G := Multiplicative (Fin d → ZMod 2))).comp H.subtype)
    let L := binarySurprisalOperator s (characterMultiplier χ)
    P * (L * L) * P - (P * L * P) * (P * L * P) ≠ 0 ↔ s ≠ 0 := by
  apply quotient_binary_surprisal_defect_ne_zero_iff H (coordinateSign d r).toMonoidHom
  · intro x
    exact coordinateSign_sq d r x.toAdd
  · exact coordinateSign_subgroup_nontrivial d r H hflip
  · exact hs

end WalshQuotient

end InfoGeometry.LLM.LanguageSymmetry
