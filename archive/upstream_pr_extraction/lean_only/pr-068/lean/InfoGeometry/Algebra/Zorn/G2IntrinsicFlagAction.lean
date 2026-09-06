import InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Intrinsic full-flag action

The intrinsic Zorn incidence relation is already proved equivariant in
`G2InvariantIncidenceCandidates`.  This file packages that result as an
honest action on the dependent sum of isotropic points and intrinsic lines.
It deliberately does not identify this carrier with the exported 189-flag
certificate.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates

abbrev IntrinsicFlag := Σ p : OctImIsotropicPoint, IntrinsicLine p

private theorem intrinsicLine_transport_val
    {a a' : OctImIsotropicPoint} (h : a = a')
    (x : IntrinsicLine a) :
    (cast (congrArg IntrinsicLine h) x).val = x.val := by
  cases h
  rfl

private theorem intrinsicLine_eqRec_val
    {p q : OctImIsotropicPoint} (h : p = q)
    (x : IntrinsicLine p) :
    (h ▸ x).val = x.val := by
  cases h
  rfl

noncomputable def intrinsicFlagMap (g : SplitOctF2Aut) (F : IntrinsicFlag) : IntrinsicFlag :=
  ⟨octImPointPerm g F.1, intrinsicLineMap g F.2⟩

theorem intrinsicFlagMap_one (F : IntrinsicFlag) :
    intrinsicFlagMap (1 : SplitOctF2Aut) F = F := by
  cases F with
  | mk p L =>
    cases L with
    | mk l hl =>
      simp only [intrinsicFlagMap]
      have hp : octImPointPerm (1 : SplitOctF2Aut) p = p := by
        simp [octImPointPerm_one]
      apply Sigma.ext_iff.mpr
      constructor
      · exact hp
      · have htransport :=
          (eqRec_heq hp (intrinsicLineMap (1 : SplitOctF2Aut)
            ⟨l, hl⟩)).symm
        exact htransport.trans (by
          apply heq_of_eq
          apply Subtype.ext
          have hval := intrinsicLine_eqRec_val hp
            (intrinsicLineMap (1 : SplitOctF2Aut) ⟨l, hl⟩)
          simpa [intrinsicLineMap_val, zornZeroTripleMap_one] using hval)

theorem intrinsicFlagMap_mul (g h : SplitOctF2Aut) (F : IntrinsicFlag) :
    intrinsicFlagMap (g * h) F = intrinsicFlagMap g (intrinsicFlagMap h F) := by
  cases F with
  | mk p L =>
    cases L with
    | mk l hl =>
      simp only [intrinsicFlagMap]
      have hp : octImPointPerm (g * h) p =
          octImPointPerm g (octImPointPerm h p) := by
        simp [octImPointPerm_mul]
      apply Sigma.ext_iff.mpr
      constructor
      · exact hp
      · have htransport :=
          (eqRec_heq hp (intrinsicLineMap (g * h) ⟨l, hl⟩)).symm
        exact htransport.trans (by
          apply heq_of_eq
          apply Subtype.ext
          have hval := intrinsicLine_eqRec_val hp
            (intrinsicLineMap (g * h) ⟨l, hl⟩)
          simpa [intrinsicLineMap_val, zornZeroTripleMap_mul] using hval)

noncomputable instance : MulAction SplitOctF2Aut IntrinsicFlag where
  smul := intrinsicFlagMap
  one_smul := intrinsicFlagMap_one
  mul_smul := intrinsicFlagMap_mul

@[simp] theorem smul_intrinsicFlag (g : SplitOctF2Aut) (F : IntrinsicFlag) :
    g • F = intrinsicFlagMap g F := rfl

end InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
