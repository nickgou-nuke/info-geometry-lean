/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2CorrectedQuotientCertificate
import InfoGeometry.Algebra.Zorn.G2NativeFlagResidualClosure

/-! Native flag signatures descend to right-subgroup cosets. The imported word
table needs inversion under the repository's reversed composition convention. -/
namespace InfoGeometry.Algebra.Zorn.G2CorrectedCosetSignature

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2CorrectedQuotientCertificate G2TwoPCRecovery G2TwoPCSubgroupClosure
open G2NativeFlagStabilizerTransport G2NativeFlagLineCoordinateConstraints

def companionPair : Finset SplitOctF2 :=
  {basis8 5, add (basis8 4) (basis8 5)}

noncomputable def cosetSignature (g : SplitOctF2Aut) :
    SplitOctF2 × Finset SplitOctF2 :=
  ((g⁻¹).1 (basis8 4), companionPair.image (g⁻¹).1)

theorem companionPair_image_inv {u : SplitOctF2Aut}
    (hu : u ∈ unipotentSubgroup) :
    companionPair.image (u⁻¹).1 = companionPair := by
  have hs := unipotentSubgroup_le_nativeFlagStabilizer hu
  have h4 := nativeFlagStabilizer_inv_basis8_four hs
  have h5 := nativeFlagStabilizer_inv_basis8_fifth_cases hs
  simp only [companionPair, Finset.image_insert, Finset.image_singleton]
  rw [(u⁻¹).2.2.1, h4]
  rcases h5 with h5 | h5
  · rw [h5]
  · rw [h5, G2NativeFlagStabilizerClosureReadback.add_self_cancel]
    exact Finset.pair_comm _ _

theorem cosetSignature_mul_right (g : SplitOctF2Aut)
    {u : SplitOctF2Aut} (hu : u ∈ unipotentSubgroup) :
    cosetSignature (g * u) = cosetSignature g := by
  have hs := unipotentSubgroup_le_nativeFlagStabilizer hu
  have h4 := nativeFlagStabilizer_inv_basis8_four hs
  have hp := companionPair_image_inv hu
  apply Prod.ext
  · change ((g * u)⁻¹).1 (basis8 4) = (g⁻¹).1 (basis8 4)
    rw [mul_inv_rev, automorphism_mul_apply, h4]
  · change companionPair.image ((g * u)⁻¹).1 = companionPair.image (g⁻¹).1
    rw [mul_inv_rev]
    change companionPair.image (fun X => (g⁻¹).1 ((u⁻¹).1 X)) = _
    exact (Finset.image_image (s := companionPair)
      (f := fun X => (u⁻¹).1 X) (g := fun X => (g⁻¹).1 X)).symm.trans
        (congrArg (fun s : Finset SplitOctF2 => s.image (g⁻¹).1) hp)

theorem cosetSignature_eq_of_quotient_eq {g h : SplitOctF2Aut}
    (hq : (QuotientGroup.mk g : SplitOctF2Aut ⧸ unipotentSubgroup) =
      QuotientGroup.mk h) : cosetSignature g = cosetSignature h := by
  have hu : g⁻¹ * h ∈ unipotentSubgroup := by
    rwa [QuotientGroup.eq] at hq
  have hfactor : g * (g⁻¹ * h) = h := by simp [← mul_assoc]
  exact (cosetSignature_mul_right g hu).symm.trans (congrArg cosetSignature hfactor)

/-- Inverse evaluations correct the table's quotient orientation. -/
noncomputable def correctedCoset (i : Fin 189) :
    SplitOctF2Aut ⧸ unipotentSubgroup :=
  QuotientGroup.mk ((correctedQuotientRepresentative i)⁻¹)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem inverse_representative_signatures_nodup :
    (List.ofFn (fun i : Fin 189 =>
      cosetSignature ((correctedQuotientRepresentative i)⁻¹))).Nodup := by
  decide

theorem correctedCoset_injective : Function.Injective correctedCoset := by
  intro i j h
  apply (List.nodup_ofFn.mp inverse_representative_signatures_nodup)
  exact cosetSignature_eq_of_quotient_eq h

/-- Signature separation and the independently proved quotient cardinality give coverage. -/
theorem correctedCoset_bijective : Function.Bijective correctedCoset := by
  apply (Nat.bijective_iff_injective_and_card correctedCoset).2
  refine ⟨correctedCoset_injective, ?_⟩
  simpa using G2NativeFlagResidualClosure.quotient_card_eq_189.symm

/-- The corrected inverse word evaluations enumerate the native quotient. -/
noncomputable def correctedCosetEquiv :
    Fin 189 ≃ (SplitOctF2Aut ⧸ unipotentSubgroup) :=
  Equiv.ofBijective correctedCoset correctedCoset_bijective

theorem correctedCosetEquiv_apply (i : Fin 189) :
    correctedCosetEquiv i = QuotientGroup.mk ((correctedQuotientRepresentative i)⁻¹) := rfl

end InfoGeometry.Algebra.Zorn.G2CorrectedCosetSignature
