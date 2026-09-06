import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFiberBounds
import Mathlib.Data.Finset.Card

/-!
# The finite admissible-pair carrier for the intrinsic base fibre

The points away from the base point form a neighbour set.  An intrinsic line
through the base point is exactly an admissible two-point subset of that set:
the two points must also be related to one another.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus

open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFiberBounds

abbrev Point :=
  InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint

instance intrinsicLineFinite (p : Point) : Finite (IntrinsicLine p) :=
  Finite.of_injective (fun L : IntrinsicLine p => L.1) Subtype.val_injective

noncomputable instance intrinsicLineFintype (p : Point) : Fintype (IntrinsicLine p) :=
  Fintype.ofFinite (IntrinsicLine p)

def admissiblePair (s : Finset Point) : Prop :=
  s.card = 2 ∧
    s ⊆ zornZeroNeighborSet nativeBaseIsotropicPoint ∧
    ∀ ⦃u v : Point⦄, u ∈ s → v ∈ s → u ≠ v → ZornZeroRelated u v

instance : DecidablePred admissiblePair := by
  intro s
  unfold admissiblePair
  infer_instance

def admissiblePairs : Finset (Finset Point) :=
  (zornZeroNeighborSet nativeBaseIsotropicPoint).powerset.filter admissiblePair

theorem admissiblePairs_card : admissiblePairs.card = 3 := by
  native_decide

theorem intrinsicLine_erase_mem_admissiblePairs
    (L : IntrinsicLine nativeBaseIsotropicPoint) :
    L.1.erase nativeBaseIsotropicPoint ∈ admissiblePairs := by
  simp only [admissiblePairs, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨intrinsicLine_subset_zornZeroNeighborSet L, ?_⟩
  refine ⟨intrinsicLine_erase_card L, intrinsicLine_subset_zornZeroNeighborSet L, ?_⟩
  intro u v hu hv huv
  exact L.2.2.2 ((Finset.mem_erase.mp hu).2)
    ((Finset.mem_erase.mp hv).2) huv

def admissiblePairToLine
    (s : {s : Finset Point // s ∈ admissiblePairs}) :
    IntrinsicLine nativeBaseIsotropicPoint := by
  have hs := (Finset.mem_filter.mp s.2).2
  have hsub : s.1 ⊆ zornZeroNeighborSet nativeBaseIsotropicPoint :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp s.2).1
  have hcard : s.1.card = 2 := hs.1
  have hbase : nativeBaseIsotropicPoint ∉ s.1 := by
    intro hmem
    have hrel :=
      (mem_zornZeroNeighborSet_iff nativeBaseIsotropicPoint nativeBaseIsotropicPoint).mp
        (hsub hmem)
    exact zornZeroRelated_irreflexive nativeBaseIsotropicPoint hrel
  refine ⟨insert nativeBaseIsotropicPoint s.1, ?_, ?_, ?_⟩
  · simp
  · simp [hbase, hcard]
  · intro u v hu hv huv
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact False.elim (huv rfl)
      · exact (mem_zornZeroNeighborSet_iff nativeBaseIsotropicPoint v).mp (hsub hv)
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact zornZeroRelated_symmetric u nativeBaseIsotropicPoint |>.mpr
          ((mem_zornZeroNeighborSet_iff nativeBaseIsotropicPoint u).mp (hsub hu))
      · exact hs.2.2 hu hv huv

def intrinsicLineToAdmissiblePair :
    IntrinsicLine nativeBaseIsotropicPoint ≃
      {s : Finset Point // s ∈ admissiblePairs} where
  toFun L := ⟨L.1.erase nativeBaseIsotropicPoint,
    intrinsicLine_erase_mem_admissiblePairs L⟩
  invFun := admissiblePairToLine
  left_inv L := by
    apply intrinsicLine_ext_of_erase_eq
    simp [admissiblePairToLine]
  right_inv s := by
    apply Subtype.ext
    have hbase : nativeBaseIsotropicPoint ∉ s.1 := by
      intro hmem
      have hrel :=
        (mem_zornZeroNeighborSet_iff nativeBaseIsotropicPoint nativeBaseIsotropicPoint).mp
          ((Finset.mem_powerset.mp (Finset.mem_filter.mp s.2).1) hmem)
      exact zornZeroRelated_irreflexive nativeBaseIsotropicPoint hrel
    simp [admissiblePairToLine, hbase]

theorem intrinsicLine_base_card :
    Fintype.card (IntrinsicLine nativeBaseIsotropicPoint) = 3 := by
  rw [Fintype.card_congr intrinsicLineToAdmissiblePair]
  simpa only [Fintype.card_coe] using admissiblePairs_card

end InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus
