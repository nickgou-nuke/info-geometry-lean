import InfoGeometry.Algebra.Zorn.G2NativeLineFiber
import InfoGeometry.Algebra.Zorn.G2NativePointTransitivity

namespace InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativePointFoundation
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2NativePointTransitivity

private theorem nativeCandidateAt_map
    (g : SplitOctF2Aut) (x y : OctImF2)
    (hy : nativeCandidateAt x y) :
    nativeCandidateAt (octImAction g x) (octImAction g y) := by
  rcases hy with ⟨hy0, hyx, hmul⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply hy0
    apply octImAction_injective g
    simpa [octImAction_zero] using hzero
  · intro heq
    apply hyx
    apply octImAction_injective g
    exact heq
  · exact (native_multiplication_zero_iff g x y).mpr hmul

private theorem nativeLineSetAt_map
    (g : SplitOctF2Aut) (x y : OctImF2) :
    nativeLineSetAt (octImAction g x) (octImAction g y) =
      (nativeLineSetAt x y).image (octImAction g) := by
  simp only [nativeLineSetAt, Finset.image_insert, Finset.image_singleton]
  rw [octImAction_add]

private theorem nativeLine_image_mem
    (g : SplitOctF2Aut) (x : OctImF2)
    {L : Finset OctImF2} (hL : L ∈ nativeLinesAt x) :
    L.image (octImAction g) ∈ nativeLinesAt (octImAction g x) := by
  rcases Finset.mem_image.mp hL with ⟨y, hy, hLy⟩
  refine Finset.mem_image.mpr ⟨octImAction g y, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, nativeCandidateAt_map g x y
      (Finset.mem_filter.mp hy).2⟩
  · rw [← hLy, nativeLineSetAt_map]

private theorem nativeLine_inverse_image_mem
    (g : SplitOctF2Aut) (x : OctImF2)
    {L : Finset OctImF2}
    (hL : L ∈ nativeLinesAt (octImAction g x)) :
    L.image (octImAction g⁻¹) ∈ nativeLinesAt x := by
  rcases Finset.mem_image.mp hL with ⟨y, hy, hLy⟩
  refine Finset.mem_image.mpr ⟨octImAction g⁻¹ y, ?_, ?_⟩
  · have hmap := nativeCandidateAt_map g⁻¹ (octImAction g x) y
      (Finset.mem_filter.mp hy).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [← octImAction_mul, inv_mul_cancel, octImAction_one] using hmap⟩
  · have hmap := nativeLineSetAt_map g⁻¹ (octImAction g x) y
    calc
      nativeLineSetAt x (octImAction g⁻¹ y) =
          (nativeLineSetAt (octImAction g x) y).image (octImAction g⁻¹) := by
        simpa [← octImAction_mul, inv_mul_cancel, octImAction_one] using hmap
      _ = L.image (octImAction g⁻¹) := by rw [hLy]

private theorem image_action_left_inverse
    (g : SplitOctF2Aut) (s : Finset OctImF2) :
    (s.image (octImAction g)).image (octImAction g⁻¹) = s := by
  rw [Finset.image_image]
  simp [Function.comp_def, ← octImAction_mul, inv_mul_cancel, octImAction_one]

private theorem image_action_right_inverse
    (g : SplitOctF2Aut) (s : Finset OctImF2) :
    (s.image (octImAction g⁻¹)).image (octImAction g) = s := by
  rw [Finset.image_image]
  simp [Function.comp_def, ← octImAction_mul, mul_inv_cancel, octImAction_one]

noncomputable def nativeLineFiberMap
    (g : SplitOctF2Aut) (x : OctImF2) :
    NativeLinesThroughPoint x ≃ NativeLinesThroughPoint (octImAction g x) where
  toFun L := by
    refine ⟨L.1.image (octImAction g), ?_⟩
    exact nativeLine_image_mem g x L.2
  invFun L := by
    refine ⟨L.1.image (octImAction g⁻¹), ?_⟩
    exact nativeLine_inverse_image_mem g x L.2
  left_inv L := by
    apply Subtype.ext
    exact image_action_left_inverse g L.1
  right_inv L := by
    apply Subtype.ext
    exact image_action_right_inverse g L.1

theorem nativeLineFiber_card_transport
    (g : SplitOctF2Aut) (x : OctImF2) :
    Fintype.card (NativeLinesThroughPoint x) =
      Fintype.card (NativeLinesThroughPoint (octImAction g x)) := by
  exact Fintype.card_congr (nativeLineFiberMap g x)

theorem nativeLineFiber_card_eq_base
    (p : OctImIsotropicPoint)
    (hpoint : ∃ g : SplitOctF2Aut,
      octImAction g nativeBasePoint = p.1) :
    Fintype.card (NativeLinesThroughPoint p.1) = 3 := by
  obtain ⟨g, hg⟩ := hpoint
  have hcard := nativeLineFiber_card_transport g nativeBasePoint
  rw [hg] at hcard
  have hbase : Fintype.card (NativeLinesThroughPoint nativeBasePoint) = 3 := by
    simpa [NativeLine] using
      InfoGeometry.Algebra.Zorn.G2NativeLineFiber.nativeBaseLine_card
  calc
    Fintype.card (NativeLinesThroughPoint p.1) =
        Fintype.card (NativeLinesThroughPoint nativeBasePoint) := hcard.symm
    _ = 3 := hbase

theorem nativeLineFiber_card_eq_three
    (p : OctImIsotropicPoint) :
    Fintype.card (NativeLinesThroughPoint p.1) = 3 := by
  apply nativeLineFiber_card_eq_base p
  obtain ⟨g, hg⟩ := octImPointPerm_base_surjective p
  refine ⟨g, ?_⟩
  have hg' := congrArg Subtype.val hg
  simpa [octImPointPerm_apply, octImAction] using hg'

end InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
