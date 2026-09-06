import InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
import InfoGeometry.Algebra.Zorn.G2NativePointTransitivity

/-!
# Equivariant transport of intrinsic incidence fibres

The native intrinsic incidence relation has an honest action.  This owner
records the corresponding fibre equivalence, without identifying the
intrinsic fibre with the exported finite flag certificate.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2NativePointTransitivity
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable instance (priority := 2000) intrinsicLineFintype (p : OctImIsotropicPoint) :
    Fintype (IntrinsicLine p) := by
  apply Fintype.subtype (intrinsicLines p)
  intro s
  constructor
  · intro hs
    have hs' := (mem_intrinsicLines_iff p s).mp hs
    refine ⟨hs'.2, hs'.1.1, ?_⟩
    intro u hu v hv huv
    exact @hs'.1.2 u v hu hv huv
  · rintro ⟨hp, hcard, hrel⟩
    apply (mem_intrinsicLines_iff p s).mpr
    refine ⟨⟨hcard, ?_⟩, hp⟩
    intro u hu v hv huv
    exact @hrel u v hu hv huv

private theorem cast_intrinsicLine_val
    {p q : OctImIsotropicPoint} (h : p = q)
    (x : IntrinsicLine p) :
    (cast (congrArg IntrinsicLine h) x).val = x.val := by
  cases h
  rfl

private theorem cast_intrinsicLine_val_right
    {p q : OctImIsotropicPoint} (h : q = p)
    (x : IntrinsicLine q) :
    (cast (congrArg IntrinsicLine h) x).val = x.val := by
  cases h
  rfl

noncomputable def intrinsicLineMapEquiv
    (g : SplitOctF2Aut) (p : OctImIsotropicPoint) :
    IntrinsicLine p ≃ IntrinsicLine (octImPointPerm g p) where
  toFun := intrinsicLineMap g
  invFun := fun L =>
    cast (by
      exact congrArg IntrinsicLine (octImPointPerm_inv_apply g p))
      (intrinsicLineMap g⁻¹ L)
  left_inv := by
    intro L
    apply Subtype.ext
    have hInv := octImPointPerm_inv_apply g p
    have hcast := cast_intrinsicLine_val
      hInv
      (intrinsicLineMap g⁻¹ (intrinsicLineMap g L))
    simpa [intrinsicLineMap] using
      hcast.trans (zornZeroTripleMap_inv g L.1)
  right_inv := by
    intro L
    apply Subtype.ext
    have hInv := octImPointPerm_inv_apply g p
    have hcast := cast_intrinsicLine_val_right
      hInv
      (intrinsicLineMap g⁻¹ L)
    have hmap := congrArg (zornZeroTripleMap g) hcast
    simpa [intrinsicLineMap, inv_inv] using
      hmap.trans (zornZeroTripleMap_inv g⁻¹ L.1)

theorem intrinsicLineFiber_card_transport
    (g : SplitOctF2Aut) (p : OctImIsotropicPoint) :
    Fintype.card (IntrinsicLine p) =
      Fintype.card (IntrinsicLine (octImPointPerm g p)) := by
  exact Fintype.card_congr (intrinsicLineMapEquiv g p)

theorem intrinsicLineFiber_card_eq_base
    (p : OctImIsotropicPoint)
    (hpoint : ∃ g : SplitOctF2Aut,
      octImPointPerm g nativeBaseIsotropicPoint = p) :
    Fintype.card (IntrinsicLine p) =
      Fintype.card (IntrinsicLine nativeBaseIsotropicPoint) := by
  obtain ⟨g, hg⟩ := hpoint
  have hcard := intrinsicLineFiber_card_transport g nativeBaseIsotropicPoint
  rw [hg] at hcard
  exact hcard.symm

theorem intrinsicLineFiber_card_eq_base_of_point_transitive
    (p : OctImIsotropicPoint) :
    Fintype.card (IntrinsicLine p) =
      Fintype.card (IntrinsicLine nativeBaseIsotropicPoint) := by
  exact intrinsicLineFiber_card_eq_base p
    (by
      obtain ⟨g, hg⟩ := octImPointPerm_base_surjective p
      exact ⟨g, hg⟩)

end InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport
