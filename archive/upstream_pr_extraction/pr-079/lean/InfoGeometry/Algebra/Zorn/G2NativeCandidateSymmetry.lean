import InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus
import InfoGeometry.Algebra.Zorn.G2NativeLineSetQuotient

namespace InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry

open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier
open InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus
open InfoGeometry.Algebra.Zorn.G2NativeLineSetQuotient

theorem nativeBasePoint_eq_canonicalBasePoint :
    (nativeBasePoint : G2ParabolicLineCarrier.OctImF2) =
      G2ParabolicLineCarrier.canonicalBasePoint := by
  rfl

theorem octImPointPerm_val_eq_octImAction
    (g : SplitOctF2Aut) (v : OctImIsotropicPoint) :
    (octImPointPerm g v).1 = octImAction g v.1 := by
  rw [octImPointPerm_apply]
  rfl

theorem octImPointPerm_inv_val_eq_octImAction_inv
    (g : SplitOctF2Aut) (v : OctImIsotropicPoint) :
    (octImPointPerm g⁻¹ v).1 = octImAction g⁻¹ v.1 := by
  exact octImPointPerm_val_eq_octImAction g⁻¹ v

theorem intrinsicLineMap_underlying_eq_map
    (g : SplitOctF2Aut) (L : IntrinsicLine nativeBaseIsotropicPoint) :
    (intrinsicLineMap g L).1 =
      L.1.map (octImPointPerm g).toEmbedding := by
  rfl

theorem zornZeroTripleMap_val_image
    (g : SplitOctF2Aut) (s : Finset OctImIsotropicPoint) :
    (zornZeroTripleMap g s).image Subtype.val =
      s.image (fun v => octImAction g v.1) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨u, hu, hux⟩
    rcases Finset.mem_map.mp hu with ⟨v, hv, huv⟩
    have huv' : octImPointPerm g v = u := huv
    refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
    · calc
        octImAction g v.1 = (octImPointPerm g v).1 :=
          (octImPointPerm_val_eq_octImAction g v).symm
        _ = u.1 := congrArg Subtype.val huv'
        _ = x := hux
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, hax⟩
    refine Finset.mem_image.mpr ⟨octImPointPerm g a, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
    · calc
        (octImPointPerm g a).1 = octImAction g a.1 :=
          octImPointPerm_val_eq_octImAction g a
        _ = x := hax

theorem finset_image_eq_image_erase_insert
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (a : α) (f : α → β)
    (ha : a ∈ s) :
    s.image f = insert (f a) ((s.erase a).image f) := by
  rw [← Finset.image_insert, Finset.insert_erase ha]

theorem finset_subtype_val_image_injective
    {α : Type*} [DecidableEq α]
    {s t : Finset {x : α // True}}
    (h : s.image Subtype.val = t.image Subtype.val) :
    s = t := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hx' : (x : α) ∈ t.image Subtype.val := by
      rw [← h]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hx' with ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy
  · intro hx
    have hx' : (x : α) ∈ s.image Subtype.val := by
      rw [h]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hx' with ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy

theorem nativeCandidateAt_isotropic
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    splitQuad y = 0 := by
  native_decide +revert

theorem nativeCandidateAt_reverse_zero
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    mul (embed y) (embed nativeBasePoint) = zero := by
  native_decide +revert

theorem nativeCandidateAt_to_zornZeroRelated
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    (hyquad : splitQuad y = 0) :
    ZornZeroRelated nativeBaseIsotropicPoint
      (⟨y, hyquad, hy.1⟩ : OctImIsotropicPoint) := by
  have hback : mul (embed y) (embed nativeBasePoint) = zero :=
    nativeCandidateAt_reverse_zero y hy
  refine ⟨?_, ?_, ?_⟩
  · exact hy.2.1.symm
  · simpa [nativeBaseIsotropicPoint] using hy.2.2
  · simpa [nativeBaseIsotropicPoint] using hback

theorem nativeCandidateAt_sum_isotropic
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    splitQuad (nativeBasePoint + y) = 0 := by
  native_decide +revert

theorem nativeCandidateAt_sum_to_zornZeroRelated
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    ZornZeroRelated nativeBaseIsotropicPoint
      (⟨nativeBasePoint + y,
        nativeCandidateAt_sum_isotropic y hy,
        by native_decide +revert⟩ : OctImIsotropicPoint) := by
  native_decide +revert

theorem nativeCandidateAt_pair_to_zornZeroRelated
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    (hyquad : splitQuad y = 0) :
    ZornZeroRelated
      (⟨y, hyquad, hy.1⟩ : OctImIsotropicPoint)
      (⟨nativeBasePoint + y,
        nativeCandidateAt_sum_isotropic y hy,
        by native_decide +revert⟩ : OctImIsotropicPoint) := by
  native_decide +revert


noncomputable def intrinsicLineOfCandidate
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    (hyquad : splitQuad y = 0) :
    IntrinsicLine nativeBaseIsotropicPoint := by
  let py : OctImIsotropicPoint := ⟨y, hyquad, hy.1⟩
  let ps : OctImIsotropicPoint := ⟨nativeBasePoint + y,
    nativeCandidateAt_sum_isotropic y hy, by native_decide +revert⟩
  have h0y : nativeBaseIsotropicPoint ≠ py := by
    intro h
    apply hy.2.1
    exact (congrArg Subtype.val h).symm
  have h0s : nativeBaseIsotropicPoint ≠ ps := by
    native_decide +revert
  have hys : py ≠ ps := by
    native_decide +revert
  have hcard : ({nativeBaseIsotropicPoint, py, ps} :
      Finset OctImIsotropicPoint).card = 3 := by
    simp [h0y, h0s, hys]
  refine ⟨{nativeBaseIsotropicPoint, py, ps}, ?_, hcard, ?_⟩
  · simp
  · intro u v hu hv huv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact False.elim (huv rfl)
    · exact nativeCandidateAt_to_zornZeroRelated y hy hyquad
    · exact nativeCandidateAt_sum_to_zornZeroRelated y hy
    · exact (zornZeroRelated_symmetric _ _).mp
        (nativeCandidateAt_to_zornZeroRelated y hy hyquad)
    · exact False.elim (huv rfl)
    · exact nativeCandidateAt_pair_to_zornZeroRelated y hy hyquad
    · exact (zornZeroRelated_symmetric _ _).mp
        (nativeCandidateAt_sum_to_zornZeroRelated y hy)
    · exact (zornZeroRelated_symmetric _ _).mp
        (nativeCandidateAt_pair_to_zornZeroRelated y hy hyquad)
    · exact False.elim (huv rfl)

noncomputable def intrinsicLineOfNativeCandidate
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    IntrinsicLine nativeBaseIsotropicPoint :=
  intrinsicLineOfCandidate y hy (nativeCandidateAt_isotropic y hy)

theorem intrinsicLineOfNativeCandidate_proof_irrel
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy hz : nativeCandidateAt nativeBasePoint y) :
    intrinsicLineOfNativeCandidate y hy =
      intrinsicLineOfNativeCandidate y hz := by
  rfl

theorem intrinsicLineOfNativeCandidate_eq_of_lineSet_eq
    (y z : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    (hz : nativeCandidateAt nativeBasePoint z)
    (hline : lineSet y = lineSet z) :
    intrinsicLineOfNativeCandidate y hy =
      intrinsicLineOfNativeCandidate z hz := by
  have hy' : y ∈ candidates := by
    simpa [candidates, kernelCandidate] using hy
  have hz' : z ∈ candidates := by
    simpa [candidates, kernelCandidate] using hz
  have hcases := (lineSet_eq_lineSet_iff hy' hz').mp hline
  rcases hcases with hzy | hzy
  · have hyz : y = z := hzy.symm
    cases hyz
    exact intrinsicLineOfNativeCandidate_proof_irrel y hy hz
  · have hz' : z = nativeBasePoint + y := hzy
    cases hz'
    have hsum :
        (⟨nativeBasePoint + (nativeBasePoint + y),
          nativeCandidateAt_sum_isotropic (nativeBasePoint + y) hz,
          by native_decide +revert⟩ : OctImIsotropicPoint) =
          ⟨y, nativeCandidateAt_isotropic y hy, hy.1⟩ := by
      apply Subtype.ext
      calc
        nativeBasePoint + (nativeBasePoint + y) =
            (nativeBasePoint + nativeBasePoint) + y :=
          (_root_.add_assoc nativeBasePoint nativeBasePoint y).symm
        _ = y := by rw [nativeBasePoint_add_self, _root_.zero_add]
    apply Subtype.ext
    simp only [intrinsicLineOfNativeCandidate, intrinsicLineOfCandidate]
    rw [hsum]
    ext z
    simp [or_comm]

theorem intrinsicLineOfCandidate_mem_base
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    (hyquad : splitQuad y = 0) :
    nativeBaseIsotropicPoint ∈
      (intrinsicLineOfCandidate y hy hyquad).1 := by
  exact (intrinsicLineOfCandidate y hy hyquad).2.1

theorem intrinsicLineOfCandidate_card
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    (hyquad : splitQuad y = 0) :
    (intrinsicLineOfCandidate y hy hyquad).1.card = 3 :=
  (intrinsicLineOfCandidate y hy hyquad).2.2.1

theorem intrinsicLineOfCandidate_erase_mem_admissiblePairs
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    (hyquad : splitQuad y = 0) :
    (intrinsicLineOfCandidate y hy hyquad).1.erase
        nativeBaseIsotropicPoint ∈ admissiblePairs := by
  exact intrinsicLine_erase_mem_admissiblePairs
    (intrinsicLineOfCandidate y hy hyquad)

theorem admissiblePairToLine_erase_intrinsicLineOfCandidate
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    (hyquad : splitQuad y = 0) :
    admissiblePairToLine
        ⟨(intrinsicLineOfCandidate y hy hyquad).1.erase
            nativeBaseIsotropicPoint,
          intrinsicLineOfCandidate_erase_mem_admissiblePairs y hy hyquad⟩ =
      intrinsicLineOfCandidate y hy hyquad := by
  exact (intrinsicLineToAdmissiblePair).left_inv
    (intrinsicLineOfCandidate y hy hyquad)

theorem intrinsicLineOfCandidate_erase_eq_pair
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    (hyquad : splitQuad y = 0) :
    (intrinsicLineOfCandidate y hy hyquad).1.erase
        nativeBaseIsotropicPoint =
      {⟨y, hyquad, hy.1⟩,
        ⟨nativeBasePoint + y,
          nativeCandidateAt_sum_isotropic y hy,
          by native_decide +revert⟩} := by
  apply Finset.ext
  intro z
  constructor
  · intro hz
    have hz' : z ∈ (intrinsicLineOfCandidate y hy hyquad).1 :=
      (Finset.mem_erase.mp hz).2
    have hz0 : z ≠ nativeBaseIsotropicPoint :=
      (Finset.mem_erase.mp hz).1
    simp only [intrinsicLineOfCandidate] at hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
    rcases hz' with rfl | rfl | rfl
    · exact False.elim (hz0 rfl)
    · simp
    · simp
  · intro hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · have hne :
          (⟨y, hyquad, hy.1⟩ : OctImIsotropicPoint) ≠
            nativeBaseIsotropicPoint := by
        intro h
        apply hy.2.1
        exact congrArg Subtype.val h
      simp only [intrinsicLineOfCandidate, Finset.mem_erase,
        Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hne, Or.inr (Or.inl True.intro)⟩
    · have hne :
          (⟨nativeBasePoint + y,
            nativeCandidateAt_sum_isotropic y hy,
            by native_decide +revert⟩ : OctImIsotropicPoint) ≠
            nativeBaseIsotropicPoint := by
        native_decide +revert
      simp only [intrinsicLineOfCandidate, Finset.mem_erase,
        Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hne, Or.inr (Or.inr True.intro)⟩

theorem intrinsicLineOfNativeCandidate_mem_base
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    nativeBaseIsotropicPoint ∈
      (intrinsicLineOfNativeCandidate y hy).1 := by
  exact intrinsicLineOfCandidate_mem_base y hy
    (nativeCandidateAt_isotropic y hy)

theorem intrinsicLineOfNativeCandidate_card
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    (intrinsicLineOfNativeCandidate y hy).1.card = 3 := by
  exact intrinsicLineOfCandidate_card y hy
    (nativeCandidateAt_isotropic y hy)

theorem intrinsicLineOfNativeCandidate_erase_eq_pair
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    (intrinsicLineOfNativeCandidate y hy).1.erase
        nativeBaseIsotropicPoint =
      {⟨y, nativeCandidateAt_isotropic y hy, hy.1⟩,
        ⟨nativeBasePoint + y,
          nativeCandidateAt_sum_isotropic y hy,
          by native_decide +revert⟩} := by
  exact intrinsicLineOfCandidate_erase_eq_pair y hy
    (nativeCandidateAt_isotropic y hy)

theorem exists_intrinsicLine_of_nativeCandidate
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    ∃ L : IntrinsicLine nativeBaseIsotropicPoint,
      L.1.erase nativeBaseIsotropicPoint =
        {⟨y, nativeCandidateAt_isotropic y hy, hy.1⟩,
          ⟨nativeBasePoint + y,
            nativeCandidateAt_sum_isotropic y hy,
            by native_decide +revert⟩} := by
  refine ⟨intrinsicLineOfNativeCandidate y hy, ?_⟩
  exact intrinsicLineOfNativeCandidate_erase_eq_pair y hy

theorem intrinsicLineOfNativeCandidate_val_image_eq_lineSet
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y) :
    (intrinsicLineOfNativeCandidate y hy).1.image Subtype.val =
      lineSet y := by
  let L := intrinsicLineOfNativeCandidate y hy
  have hdecomp := finset_image_eq_image_erase_insert
    L.1 nativeBaseIsotropicPoint Subtype.val L.2.1
  rw [hdecomp]
  rw [intrinsicLineOfNativeCandidate_erase_eq_pair y hy]
  simp [lineSet, nativeLineSetAt, nativeBasePoint_eq_canonicalBasePoint,
    nativeBaseIsotropicPoint]

theorem lineSet_eq_of_intrinsicLineOfNativeCandidate_eq
    (y z : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    (hz : nativeCandidateAt nativeBasePoint z)
    (hline : intrinsicLineOfNativeCandidate y hy =
      intrinsicLineOfNativeCandidate z hz) :
    lineSet y = lineSet z := by
  rw [← intrinsicLineOfNativeCandidate_val_image_eq_lineSet y hy,
    ← intrinsicLineOfNativeCandidate_val_image_eq_lineSet z hz]
  exact congrArg (fun L : IntrinsicLine nativeBaseIsotropicPoint =>
    L.1.image Subtype.val) hline

theorem intrinsicLineOfNativeCandidate_eq_iff_lineSet_eq
    (y z : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    (hz : nativeCandidateAt nativeBasePoint z) :
    intrinsicLineOfNativeCandidate y hy =
      intrinsicLineOfNativeCandidate z hz ↔
    lineSet y = lineSet z := by
  constructor
  · exact lineSet_eq_of_intrinsicLineOfNativeCandidate_eq y z hy hz
  · intro h
    exact intrinsicLineOfNativeCandidate_eq_of_lineSet_eq y z hy hz h

noncomputable def nativeLineQuotientToIntrinsicLine :
    nativeLineQuotient → IntrinsicLine nativeBaseIsotropicPoint :=
  Quotient.lift
    (fun y : NativeCandidate =>
      intrinsicLineOfNativeCandidate y.1
        ((Finset.mem_filter.mp y.2).2))
    (by
      intro y z h
      exact intrinsicLineOfNativeCandidate_eq_of_lineSet_eq
        y.1 z.1 (Finset.mem_filter.mp y.2).2
        (Finset.mem_filter.mp z.2).2 h)

theorem nativeLineQuotientToIntrinsicLine_mk
    (y : NativeCandidate) :
    nativeLineQuotientToIntrinsicLine (Quotient.mk' y) =
      intrinsicLineOfNativeCandidate y.1
        ((Finset.mem_filter.mp y.2).2) := by
  rfl

theorem nativeLineQuotientToIntrinsicLine_injective :
    Function.Injective nativeLineQuotientToIntrinsicLine := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | h y =>
    induction r using Quotient.inductionOn with
    | h z =>
      apply Quotient.sound
      exact lineSet_eq_of_intrinsicLineOfNativeCandidate_eq
        y.1 z.1 (Finset.mem_filter.mp y.2).2
        (Finset.mem_filter.mp z.2).2 hqr

theorem nativeLineQuotientToIntrinsicLine_bijective :
    Function.Bijective nativeLineQuotientToIntrinsicLine := by
  letI : Fintype nativeLineQuotient :=
    Fintype.ofEquiv NativeLine lineSetQuotientToNativeLines.symm
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact nativeLineQuotientToIntrinsicLine_injective
  · calc
      Fintype.card nativeLineQuotient = Fintype.card NativeLine :=
        Fintype.card_congr lineSetQuotientToNativeLines
      _ = 3 := by
        simpa using G2NativeLineFiber.nativeBaseLine_card
      _ = Fintype.card (IntrinsicLine nativeBaseIsotropicPoint) := by
        symm
        exact intrinsicLine_base_card

noncomputable def nativeLineQuotientIntrinsicLineEquiv :
    nativeLineQuotient ≃ IntrinsicLine nativeBaseIsotropicPoint :=
  Equiv.ofBijective nativeLineQuotientToIntrinsicLine
    nativeLineQuotientToIntrinsicLine_bijective

theorem nativeLineQuotientToIntrinsicLine_surjective :
    Function.Surjective nativeLineQuotientToIntrinsicLine :=
  nativeLineQuotientToIntrinsicLine_bijective.2

def nativeCandidateAction
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint) :
    NativeCandidate → NativeCandidate :=
  fun y => ⟨octImAction g y.1,
    kernelCandidate_action_of_fix g hg y.1 y.2⟩

theorem nativeCandidateAction_lineSet
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (y : NativeCandidate) :
    lineSet (nativeCandidateAction g hg y).1 =
      (lineSet y.1).image (octImAction g) := by
  exact lineSet_action g hg y.1

def nativeLineQuotientAction
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint) :
    nativeLineQuotient → nativeLineQuotient :=
  Quotient.lift
    (fun y => Quotient.mk' (nativeCandidateAction g hg y))
    (by
      intro y z h
      apply Quotient.sound
      change lineSet (octImAction g y.1) = lineSet (octImAction g z.1)
      rw [lineSet_action g hg, lineSet_action g hg]
      exact congrArg (Finset.image (octImAction g)) h)

theorem nativeLineQuotientAction_mk
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (y : NativeCandidate) :
    nativeLineQuotientAction g hg (Quotient.mk' y) =
      Quotient.mk' (nativeCandidateAction g hg y) := by
  rfl

end InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry
