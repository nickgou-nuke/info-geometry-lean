import InfoGeometry.Algebra.Zorn.G2NativeLineFiber

/-!
# Intrinsic incidence candidates

The old `octCross` relation is not equivariant.  This file tests the native
split-Zorn multiplication relation on the actual isotropic-point carrier.
Only statements proved below are promoted as interface.
-/

namespace InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates

noncomputable section

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def ZornZeroRelated (u v : OctImIsotropicPoint) : Prop :=
  u.1 ≠ v.1 ∧
    (mul (embed u.1) (embed v.1) = 0 ∧
      mul (embed v.1) (embed u.1) = 0)

instance (u : OctImIsotropicPoint) :
    DecidablePred (ZornZeroRelated u) := by
  intro v
  unfold ZornZeroRelated
  infer_instance

theorem zornZeroRelated_irreflexive (u : OctImIsotropicPoint) :
    ¬ ZornZeroRelated u u := by
  intro h
  exact h.1 rfl

theorem zornZeroRelated_symmetric (u v : OctImIsotropicPoint) :
    ZornZeroRelated u v ↔ ZornZeroRelated v u := by
  constructor <;> intro h
  · exact ⟨h.1.symm, h.2.2, h.2.1⟩
  · exact ⟨h.1.symm, h.2.2, h.2.1⟩

theorem zornZeroRelated_aut_iff
    (g : SplitOctF2Aut) (u v : OctImIsotropicPoint) :
    ZornZeroRelated (octImPointPerm g u) (octImPointPerm g v) ↔
      ZornZeroRelated u v := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro huv
      apply h.1
      have hmap : octImPointPerm g u = octImPointPerm g v :=
        congrArg (octImPointPerm g) (Subtype.ext huv)
      exact congrArg Subtype.val hmap
    · simpa [octImPointPerm_apply] using
        (native_multiplication_zero_iff g u.1 v.1).mp h.2.1
    · simpa [octImPointPerm_apply] using
        (native_multiplication_zero_iff g v.1 u.1).mp h.2.2
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro huv
      apply h.1
      have hmap : octImPointPerm g u = octImPointPerm g v :=
        Subtype.ext huv
      exact congrArg Subtype.val ((octImPointPerm g).injective hmap)
    · simpa [octImPointPerm_apply] using
        (native_multiplication_zero_iff g u.1 v.1).mpr h.2.1
    · simpa [octImPointPerm_apply] using
        (native_multiplication_zero_iff g v.1 u.1).mpr h.2.2

def zornZeroNeighborSet (u : OctImIsotropicPoint) :
  Finset OctImIsotropicPoint :=
  Finset.univ.filter (ZornZeroRelated u)

@[simp] theorem mem_zornZeroNeighborSet_iff
    (u v : OctImIsotropicPoint) :
    v ∈ zornZeroNeighborSet u ↔ ZornZeroRelated u v := by
  simp [zornZeroNeighborSet]

def zornZeroTriple (s : Finset OctImIsotropicPoint) : Prop :=
  s.card = 3 ∧
    ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ZornZeroRelated u v

instance : DecidablePred zornZeroTriple := by
  intro s
  unfold zornZeroTriple
  infer_instance

def zornZeroTripleMap (g : SplitOctF2Aut)
    (s : Finset OctImIsotropicPoint) : Finset OctImIsotropicPoint :=
  s.map (octImPointPerm g).toEmbedding

theorem zornZeroTripleMap_one (s : Finset OctImIsotropicPoint) :
    zornZeroTripleMap (1 : SplitOctF2Aut) s = s := by
  have he : (octImPointPerm (1 : SplitOctF2Aut)).toEmbedding =
      Function.Embedding.refl _ := by
    ext x
    simp [octImPointPerm_one]
  simp [zornZeroTripleMap, he, Finset.map_refl]

@[simp] theorem mem_zornZeroTripleMap_iff (g : SplitOctF2Aut)
    (s : Finset OctImIsotropicPoint) (u : OctImIsotropicPoint) :
    u ∈ zornZeroTripleMap g s ↔
      (octImPointPerm g).symm u ∈ s := by
  simp [zornZeroTripleMap]

theorem zornZeroNeighborSet_map (g : SplitOctF2Aut)
    (u : OctImIsotropicPoint) :
    zornZeroNeighborSet (octImPointPerm g u) =
      zornZeroTripleMap g (zornZeroNeighborSet u) := by
  ext v
  simp only [zornZeroNeighborSet, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_zornZeroTripleMap_iff]
  constructor
  · intro hv
    exact (zornZeroRelated_aut_iff g u ((octImPointPerm g).symm v)).mp
      (by simpa using hv)
  · intro hv
    simpa using
      (zornZeroRelated_aut_iff g u ((octImPointPerm g).symm v)).mpr
        (by simpa using hv)

theorem zornZeroTripleMap_card (g : SplitOctF2Aut)
    (s : Finset OctImIsotropicPoint) :
    (zornZeroTripleMap g s).card = s.card := by
  simp [zornZeroTripleMap]

theorem zornZeroNeighborSet_card_map (g : SplitOctF2Aut)
    (u : OctImIsotropicPoint) :
    (zornZeroNeighborSet (octImPointPerm g u)).card =
      (zornZeroNeighborSet u).card := by
  rw [zornZeroNeighborSet_map, zornZeroTripleMap_card]

theorem octImPointPerm_inv_apply (g : SplitOctF2Aut)
    (u : OctImIsotropicPoint) :
    octImPointPerm g⁻¹ (octImPointPerm g u) = u := by
  change (octImPointPerm g⁻¹ * octImPointPerm g) u = u
  rw [← octImPointPerm_mul, inv_mul_cancel, octImPointPerm_one]
  rfl

theorem zornZeroTriple_map_iff (g : SplitOctF2Aut)
    (s : Finset OctImIsotropicPoint) :
    zornZeroTriple (zornZeroTripleMap g s) ↔ zornZeroTriple s := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [zornZeroTripleMap] using h.1
    · intro u hu v hv huv
      have hu' : octImPointPerm g u ∈ zornZeroTripleMap g s := by
        simp [zornZeroTripleMap, hu]
      have hv' : octImPointPerm g v ∈ zornZeroTripleMap g s := by
        simp [zornZeroTripleMap, hv]
      exact (zornZeroRelated_aut_iff g u v).mp
        (h.2 _ hu' _ hv' (by simpa using huv))
  · intro h
    refine ⟨?_, ?_⟩
    · simp [zornZeroTripleMap, h.1]
    · intro u hu v hv huv
      have hu' : (octImPointPerm g).symm u ∈ s := by
        simpa [zornZeroTripleMap] using hu
      have hv' : (octImPointPerm g).symm v ∈ s := by
        simpa [zornZeroTripleMap] using hv
      have huv' : (octImPointPerm g).symm u ≠ (octImPointPerm g).symm v := by
        intro hEq
        apply huv
        simpa using congrArg (octImPointPerm g) hEq
      have hpre := (zornZeroRelated_aut_iff g ((octImPointPerm g).symm u)
        ((octImPointPerm g).symm v)).mpr
        (h.2 _ hu' _ hv' huv')
      simpa using hpre

def zornZeroTriples : Finset (Finset OctImIsotropicPoint) :=
  Finset.univ.filter zornZeroTriple

@[simp] theorem mem_zornZeroTriples_map_iff (g : SplitOctF2Aut)
    (s : Finset OctImIsotropicPoint) :
    zornZeroTripleMap g s ∈ zornZeroTriples ↔ s ∈ zornZeroTriples := by
  simp only [zornZeroTriples, Finset.mem_filter, Finset.mem_univ, true_and]
  exact zornZeroTriple_map_iff g s

def IntrinsicLine (p : OctImIsotropicPoint) :=
  {s : Finset OctImIsotropicPoint //
    p ∈ s ∧ s.card = 3 ∧
      ∀ ⦃u v : OctImIsotropicPoint⦄,
        u ∈ s → v ∈ s → u ≠ v → ZornZeroRelated u v}

def intrinsicLines (p : OctImIsotropicPoint) :
  Finset (Finset OctImIsotropicPoint) :=
  zornZeroTriples.filter (fun s => p ∈ s)

def intrinsicLineMap (g : SplitOctF2Aut) {p : OctImIsotropicPoint}
    (L : IntrinsicLine p) : IntrinsicLine (octImPointPerm g p) := by
  let s' := zornZeroTripleMap g L.1
  have htr : zornZeroTriple s' := by
    apply (zornZeroTriple_map_iff g L.1).mpr
    refine ⟨L.2.2.1, ?_⟩
    intro u hu v hv huv
    exact L.2.2.2 hu hv huv
  have hmem : octImPointPerm g p ∈ s' := by
    simp [s', zornZeroTripleMap, L.2.1]
  refine ⟨s', hmem, htr.1, ?_⟩
  exact fun {u} {v} hu hv huv => htr.2 u hu v hv huv

@[simp] theorem intrinsicLineMap_val (g : SplitOctF2Aut)
    {p : OctImIsotropicPoint} (L : IntrinsicLine p) :
    (intrinsicLineMap g L).1 = zornZeroTripleMap g L.1 := by
  rfl

theorem zornZeroTripleMap_mul (g h : SplitOctF2Aut)
    (s : Finset OctImIsotropicPoint) :
    zornZeroTripleMap (g * h) s =
      zornZeroTripleMap g (zornZeroTripleMap h s) := by
  ext u
  simp only [zornZeroTripleMap, Finset.mem_map]
  rw [octImPointPerm_mul]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨octImPointPerm h a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, rfl⟩

theorem zornZeroTripleMap_inv (g : SplitOctF2Aut)
    (s : Finset OctImIsotropicPoint) :
    zornZeroTripleMap g⁻¹ (zornZeroTripleMap g s) = s := by
  rw [← zornZeroTripleMap_mul, inv_mul_cancel, zornZeroTripleMap_one]

theorem intrinsicLineMap_injective (g : SplitOctF2Aut)
    {p : OctImIsotropicPoint} :
    Function.Injective (intrinsicLineMap g (p := p)) := by
  intro L M hLM
  apply Subtype.ext
  apply Finset.map_injective (octImPointPerm g).toEmbedding
  exact congrArg Subtype.val hLM

@[simp] theorem mem_intrinsicLines_iff
    (p : OctImIsotropicPoint) (s : Finset OctImIsotropicPoint) :
    s ∈ intrinsicLines p ↔ zornZeroTriple s ∧ p ∈ s := by
  simp only [intrinsicLines, Finset.mem_filter, zornZeroTriples,
    Finset.mem_univ, true_and]

theorem intrinsicLineMap_mem_intrinsicLines
    (g : SplitOctF2Aut) {p : OctImIsotropicPoint}
    (L : IntrinsicLine p) :
    (intrinsicLineMap g L).1 ∈ intrinsicLines (octImPointPerm g p) := by
  rw [mem_intrinsicLines_iff]
  have hLtr : zornZeroTriple L.1 := by
    refine ⟨L.2.2.1, ?_⟩
    intro u hu v hv huv
    exact L.2.2.2 hu hv huv
  have htr : zornZeroTriple (zornZeroTripleMap g L.1) :=
    (zornZeroTriple_map_iff g L.1).mpr hLtr
  rw [intrinsicLineMap_val]
  exact ⟨htr, (intrinsicLineMap g L).2.1⟩

/-
The symmetric relation above is retained as an equivariant candidate.  Its
finite census and identification with the exported hexagon incidence remain
open; no flag carrier is promoted here.
-/

end

end InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
