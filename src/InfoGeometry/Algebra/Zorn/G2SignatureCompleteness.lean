/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2CorrectedCosetSignature

/-! The native flag signature is a complete invariant of the existing quotient. -/
namespace InfoGeometry.Algebra.Zorn.G2SignatureCompleteness

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2CorrectedCosetSignature G2TwoPCSubgroupClosure

theorem quotient_eq_of_cosetSignature_eq {g h : SplitOctF2Aut}
    (hs : cosetSignature g = cosetSignature h) :
    (QuotientGroup.mk g : SplitOctF2Aut ⧸ unipotentSubgroup) =
      QuotientGroup.mk h := by
  obtain ⟨i, hi⟩ := correctedCoset_bijective.2 (QuotientGroup.mk g)
  obtain ⟨j, hj⟩ := correctedCoset_bijective.2 (QuotientGroup.mk h)
  have hij : i = j := by
    apply (List.nodup_ofFn.mp inverse_representative_signatures_nodup)
    exact (cosetSignature_eq_of_quotient_eq hi).trans
      (hs.trans (cosetSignature_eq_of_quotient_eq hj).symm)
  exact hi.symm.trans ((congrArg correctedCoset hij).trans hj)

theorem cosetSignature_eq_iff {g h : SplitOctF2Aut} :
    cosetSignature g = cosetSignature h ↔
      (QuotientGroup.mk g : SplitOctF2Aut ⧸ unipotentSubgroup) =
        QuotientGroup.mk h :=
  ⟨quotient_eq_of_cosetSignature_eq, cosetSignature_eq_of_quotient_eq⟩

theorem cosetSignature_eq_iff_inv_mul_mem {g h : SplitOctF2Aut} :
    cosetSignature g = cosetSignature h ↔ g⁻¹ * h ∈ unipotentSubgroup := by
  rw [cosetSignature_eq_iff, QuotientGroup.eq]

end InfoGeometry.Algebra.Zorn.G2SignatureCompleteness
