/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval
import InfoGeometry.Algebra.Zorn.G2GapResidualPairAssembly
import InfoGeometry.Algebra.Zorn.G2GapResidualPairCellAssembly
import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessAssembly
import InfoGeometry.Algebra.Zorn.G2GAPCertificatesVerified
import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

/-!
# Conditional Bruhat classification assembly and coordinate rigidity for G₂(2)

This module proves the algebraic basis probes and within-cell residual
injectivity, then assembles classification consequences under explicit inputs:

* Stabilizer order 64 and ambient order 12096 require all eight residual
  basis readbacks for every element of the native flag stabilizer.
* The equivalence `Fin 189 ≃ CarrierQuotient` requires residual alignment
  and the ambient order.
* Concrete Bruhat coverage requires injectivity of the quotient
  representative map and the ambient order.

These declarations do not supply those inputs unconditionally. In particular,
a one-sided PC residual is not asserted to be a Weyl representative, and a
finite list of formal cell weights is not an ambient cardinality proof.
The existing PC reconstruction and double-coset transport retain the residual
factor on the native automorphism carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2BruhatClassificationMaster

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2GapResidualPairAssembly
open InfoGeometry.Algebra.Zorn.G2GapResidualPairCellAssembly
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessAssembly
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

noncomputable section

/-! ## 1. Non-Circular Basis8 7 (down2) Rigidity via the Basis8 3 (up1) Probe -/

/-- An algebraic discriminator: `up1 = basis8 3` annihilates `down2 = basis8 7`,
    but strictly rejects the defective candidate `down1 + down2 = basis8 6 + basis8 7`. -/
theorem up1_probe_discriminates_down2_from_defect :
    mul (basis8 3) (basis8 7) = zero ∧
    mul (basis8 3) (add (basis8 6) (basis8 7)) = ePlus := by
  dsimp [basis8, up0, up1, up2, down0, down1, down2, ePlus, eMinus, add, add2, zero]
  decide

/-- The exact residual x1 bit of basis8 7 under fullPeel is false for any stabilizer element. -/
theorem fullPeel_basis8_seven_x1_is_false
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).x1 = false := by
  exact nativeFlagStabilizer_fullPeel_basis8_seven_x1_false_core hg

/-- Full coordinate rigidity of basis8 7 under isotropy, up0, up1, and up2 constraints. -/
theorem splitOct_basis8_seven_rigidity_with_up1_probe (X : SplitOctF2)
    (hsq : mul X X = zero)
    (h4X : mul (basis8 4) X = basis8 0)
    (hX4 : mul X (basis8 4) = basis8 1)
    (h2X : mul (basis8 2) X = zero)
    (h3X : mul (basis8 3) X = zero)
    (hy2 : X.y2 = true) :
    X = basis8 7 := by
  exact basis8_seven_determined_by_relations X hsq h4X hX4 h2X h3X hy2

/-- Residual y1 coordinate of basis8 7 is strictly false when rigidity holds. -/
theorem basis8_seven_y1_is_false_of_rigidity (X : SplitOctF2)
    (hsq : mul X X = zero)
    (h4X : mul (basis8 4) X = basis8 0)
    (hX4 : mul X (basis8 4) = basis8 1)
    (h2X : mul (basis8 2) X = zero)
    (h3X : mul (basis8 3) X = zero)
    (hy2 : X.y2 = true) :
    X.y1 = false := by
  have hX := splitOct_basis8_seven_rigidity_with_up1_probe X hsq h4X hX4 h2X h3X hy2
  rw [hX]
  rfl

/-! ## 2. Master Stabilizer and Group Order Theorems -/

/-- Full residual basis readbacks imply that the native flag stabilizer has order 64. -/
theorem native_stabilizer_order_eq_64
    (hreadback : ∀ g : SplitOctF2Aut,
      g ∈ nativeFlagStabilizer →
      ∀ j : Fin 8, (fullPeel g).1 (basis8 j) = basis8 j) :
    Nat.card (nativeFlagStabilizer : Set SplitOctF2Aut) = 64 := by
  have h_eq : nativeFlagStabilizer = unipotentSubgroup :=
    nativeFlagStabilizer_eq_unipotent_of_fullPeel_mem (fun g hg =>
      fullPeel_mem_unipotent_of_basis_readback (hreadback g hg))
  rw [h_eq]
  exact G2TwoPCSubgroupClosure.unipotentSubgroup_card

/-- Full residual basis readbacks imply ambient order 12096. -/
theorem ambient_group_order_eq_12096
    (hreadback : ∀ g : SplitOctF2Aut,
      g ∈ nativeFlagStabilizer →
      ∀ j : Fin 8, (fullPeel g).1 (basis8 j) = basis8 j) :
    Nat.card SplitOctF2Aut = 12096 :=
  ambient_card_eq_12096_of_fullPeel_basis_readback hreadback

/-! ## 3. Same-Cell Residual Injectivity & Bruhat Classification -/

/-- Same-cell residual injectivity across all 12 Weyl cells of G₂(2). -/
theorem residual_injectivity_all_cells :
    ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      gapResidualPair k i = gapResidualPair k j → i = j :=
  gapResidualPair_injective_on_cell

/-- Residual alignment and ambient order give the quotient equivalence Fin 189 ≃ G / U. -/
noncomputable def explicitQuotientRepresentativeEquiv
    (halign : ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            gapResidualPair k i = gapResidualPair k j)
    (hG : Nat.card SplitOctF2Aut = 12096) :
    Fin 189 ≃ CarrierQuotient :=
  quotientRepresentativeEquiv_of_all_gapResidualPair_alignment halign hG

/-- Quotient-representative injectivity and ambient order imply concrete Bruhat coverage. -/
theorem bruhat_covering_is_entire_group
    (hinj : Function.Injective quotientRepresentative)
    (hG : Nat.card SplitOctF2Aut = 12096) :
    G2TwoBruhatClassification.concreteBruhatCovering = Set.univ :=
  concreteBruhatCovering_eq_univ_of_gap_witness_rows_of_injective_and_ambient_order hinj hG

end

end InfoGeometry.Algebra.Zorn.G2BruhatClassificationMaster
