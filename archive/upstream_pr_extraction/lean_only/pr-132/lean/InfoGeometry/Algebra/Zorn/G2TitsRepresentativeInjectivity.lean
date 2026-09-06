import InfoGeometry.Algebra.Zorn.G2BNPair
import InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation
import InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
import InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge

namespace InfoGeometry.Algebra.Zorn.G2TitsRepresentativeInjectivity

open InfoGeometry.Algebra.Zorn.G2BNPair
open InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative

theorem quotientOrbit_mem_of_witness
    {k : Fin 12} {i : Fin 189}
    (hcell : ∃ b : SplitOctF2Aut,
      b ∈ G2TwoPCSubgroupClosure.unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk (orbitWeylRepresentative k) :
            SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup)) :
    orbitEnum i ∈
      quotientOrbit G2TwoPCSubgroupClosure.unipotentSubgroup
        (orbitWeylRepresentative k) := by
  obtain ⟨b, hb, hq⟩ := hcell
  exact ⟨b, hb, hq.symm⟩

theorem orbitEnum_mem_quotientOrbit_of_factorization
    {k : Fin 12} {i : Fin 189}
    (hfac : ∃ b₁ b₂ : SplitOctF2Aut,
      b₁ ∈ G2TwoPCSubgroupClosure.unipotentSubgroup ∧
      b₂ ∈ G2TwoPCSubgroupClosure.unipotentSubgroup ∧
      flagRepresentative i =
        b₁ * orbitWeylRepresentative k * b₂) :
    orbitEnum i ∈
      quotientOrbit G2TwoPCSubgroupClosure.unipotentSubgroup
        (orbitWeylRepresentative k) := by
  obtain ⟨b₁, b₂, hb₁, hb₂, hfac⟩ := hfac
  have hq := quotientRepresentative_eq_left_smul_of_factorization
      i b₁ b₂ (orbitWeylRepresentative k) hb₂ hfac
  exact quotientOrbit_mem_of_witness ⟨b₁, hb₁, hq⟩

theorem flagRepresentative_eq_of_autMatrix_factorization
    {k : Fin 12} {i : Fin 189}
    {b₁ b₂ : SplitOctF2Aut}
    (hmat : autMatrix (flagRepresentative i) =
      autMatrix (b₁ * orbitWeylRepresentative k * b₂)) :
    flagRepresentative i = b₁ * orbitWeylRepresentative k * b₂ := by
  exact autMatrix_injective hmat

theorem orbitEnum_mem_quotientOrbit_cell_one
    {i : Fin 189} (hi : i ∈ orbitCells 1) :
    orbitEnum i ∈
      quotientOrbit G2TwoPCSubgroupClosure.unipotentSubgroup
        (orbitWeylRepresentative 1) := by
  obtain ⟨b, hb, hq⟩ :=
    InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness.hcell_one i hi
  exact quotientOrbit_mem_of_witness ⟨b, hb, hq⟩

theorem orbitEnum_mem_quotientOrbit_cell_zero
    {i : Fin 189} (hi : i ∈ orbitCells 0) :
    orbitEnum i ∈
      quotientOrbit G2TwoPCSubgroupClosure.unipotentSubgroup
        (orbitWeylRepresentative 0) := by
  have hi0 : i = orbitCellAnchor 0 := by
    simpa [orbitCells, flagCells, orbitCellAnchor] using hi
  subst i
  obtain ⟨b, hb, hq⟩ :=
    InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness.hcell_anchor 0
  exact quotientOrbit_mem_of_witness ⟨b, hb, hq⟩

theorem orbitWeylRepresentative_doubleCoset_injective_of_quotientOrbit_separation
    (hsep : ∀ {k l : Fin 12}, k ≠ l →
      Disjoint
        (quotientOrbit unipotentSubgroup (orbitWeylRepresentative k))
        (quotientOrbit unipotentSubgroup (orbitWeylRepresentative l))) :
    Function.Injective (fun k : Fin 12 =>
      doubleCoset unipotentSubgroup (orbitWeylRepresentative k)) := by
  intro k l heq
  by_contra hkl
  have hdisj :=
    disjoint_doubleCoset_of_disjoint_quotientOrbit
      unipotentSubgroup
      (orbitWeylRepresentative k)
      (orbitWeylRepresentative l)
      (hsep hkl)
  have h₁ : orbitWeylRepresentative k ∈
      doubleCoset unipotentSubgroup (orbitWeylRepresentative k) :=
    ⟨1, unipotentSubgroup.one_mem, 1, unipotentSubgroup.one_mem, by simp⟩
  have h₂ : orbitWeylRepresentative k ∈
      doubleCoset unipotentSubgroup (orbitWeylRepresentative l) := by
    have hcell :
        doubleCoset unipotentSubgroup (orbitWeylRepresentative k) =
          doubleCoset unipotentSubgroup (orbitWeylRepresentative l) := heq
    rw [← hcell]
    exact h₁
  exact Set.disjoint_iff.mp hdisj ⟨h₁, h₂⟩

theorem orbitWeylRepresentative_injective :
    Function.Injective orbitWeylRepresentative := by
  intro k l h
  have hparam : orbitWeyl k = orbitWeyl l := by
    apply weylNF_injective
    exact h
  exact (show Function.Injective orbitWeyl from by decide) hparam

theorem orbitWeyl_bijective :
    Function.Bijective orbitWeyl := by
  exact by decide

/-! Surjectivity of the 189-entry quotient table is not a consequence of the
    table alone.  This lemma records the non-circular finite-cardinality
    reduction: once the ambient group order is supplied independently, the
    already certified injection forces surjectivity. -/

theorem quotientRepresentative_surjective_of_quotient_card
    (hinj : Function.Injective quotientRepresentative)
    (hcard :
      Nat.card
          (SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup) = 189) :
    Function.Surjective quotientRepresentative := by
  have hbij : Function.Bijective quotientRepresentative := by
    apply (Nat.bijective_iff_injective_and_card quotientRepresentative).2
    constructor
    · exact hinj
    · have hcard' :
          Nat.card (Fin 189) =
            Nat.card
              (SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup) := by
        simpa using hcard.symm
      exact hcard'
  exact hbij.2

/-! The carrier-aligned finite certificate has two independent directions:
    the existing table gives membership of its entries in quotient orbits;
    the missing reverse direction says that every point of each orbit is one
    of those entries.  This assembly lemma records exactly how that reverse
    certificate closes quotient exhaustion. -/

theorem quotientRepresentative_surjective_of_quotientOrbit_cover_and_reverse_witness
    (horbit : ∀ q :
      SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup,
      ∃ k : Fin 12, ∃ b : SplitOctF2Aut,
        b ∈ G2TwoPCSubgroupClosure.unipotentSubgroup ∧
        q = b •
          (QuotientGroup.mk (orbitWeylRepresentative k) :
            SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup))
    (hreverse : ∀ (k : Fin 12) (b : SplitOctF2Aut),
      b ∈ G2TwoPCSubgroupClosure.unipotentSubgroup →
      ∃ i : Fin 189,
        i ∈ orbitCells k ∧
        quotientRepresentative i = b •
          (QuotientGroup.mk (orbitWeylRepresentative k) :
            SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup)) :
    Function.Surjective quotientRepresentative := by
  intro q
  obtain ⟨k, b, hb, hq⟩ := horbit q
  obtain ⟨i, _, hi⟩ := hreverse k b hb
  exact ⟨i, hi.trans hq.symm⟩

/-! A finite-cardinality reduction for the reverse witness.  The forward
    certificate and global quotient injectivity make the representative map
    injective on each cell.  Equality of the two finite cardinalities then
    upgrades it to a bijection onto the corresponding quotient orbit. -/

noncomputable instance quotientOrbitSubtypeFintype (k : Fin 12) :
    Fintype
      {q : SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup //
        q ∈ quotientOrbit G2TwoPCSubgroupClosure.unipotentSubgroup
          (orbitWeylRepresentative k)} :=
  Fintype.ofFinite _

theorem orbitCellSubtype_card (k : Fin 12) :
    Fintype.card {i : Fin 189 // i ∈ orbitCells k} = flagCellCard k := by
  classical
  simpa [orbitCells] using flagCells_card k

theorem quotientOrbit_reverse_witness_of_cell_card_eq
    (hinj : Function.Injective quotientRepresentative)
    (hforward : ∀ (k : Fin 12) (i : Fin 189),
      i ∈ orbitCells k →
      quotientRepresentative i ∈
        quotientOrbit G2TwoPCSubgroupClosure.unipotentSubgroup
          (orbitWeylRepresentative k))
    (k : Fin 12)
    (hcard :
      Fintype.card {i : Fin 189 // i ∈ orbitCells k} =
        Fintype.card
          {q : SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup //
            q ∈ quotientOrbit G2TwoPCSubgroupClosure.unipotentSubgroup
              (orbitWeylRepresentative k)}) :
    ∀ (b : SplitOctF2Aut),
      b ∈ G2TwoPCSubgroupClosure.unipotentSubgroup →
      ∃ i : Fin 189,
        i ∈ orbitCells k ∧
        quotientRepresentative i = b •
          (QuotientGroup.mk (orbitWeylRepresentative k) :
            SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup) := by
  let f : {i : Fin 189 // i ∈ orbitCells k} →
      {q : SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup //
        q ∈ quotientOrbit G2TwoPCSubgroupClosure.unipotentSubgroup
          (orbitWeylRepresentative k)} := fun i =>
    ⟨quotientRepresentative i.1, hforward k i.1 i.2⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hij
  have hf_bij : Function.Bijective f := by
    apply (Fintype.bijective_iff_injective_and_card f).2
    exact ⟨hf_inj, hcard⟩
  intro b hb
  have hqmem :
      b • (QuotientGroup.mk (orbitWeylRepresentative k) :
        SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup) ∈
        quotientOrbit G2TwoPCSubgroupClosure.unipotentSubgroup
          (orbitWeylRepresentative k) :=
    ⟨b, hb, rfl⟩
  obtain ⟨i, hi⟩ := hf_bij.2 ⟨_, hqmem⟩
  exact ⟨i.1, i.2, congrArg Subtype.val hi⟩

theorem quotientOrbit_reverse_witness_of_quotientOrbit_card_eq_cellCard
    (hinj : Function.Injective quotientRepresentative)
    (hforward : ∀ (k : Fin 12) (i : Fin 189),
      i ∈ orbitCells k →
      quotientRepresentative i ∈
        quotientOrbit G2TwoPCSubgroupClosure.unipotentSubgroup
          (orbitWeylRepresentative k))
    (k : Fin 12)
    (hcard :
      Fintype.card
          {q : SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup //
            q ∈ quotientOrbit G2TwoPCSubgroupClosure.unipotentSubgroup
              (orbitWeylRepresentative k)} = flagCellCard k) :
    ∀ (b : SplitOctF2Aut),
      b ∈ G2TwoPCSubgroupClosure.unipotentSubgroup →
      ∃ i : Fin 189,
        i ∈ orbitCells k ∧
        quotientRepresentative i = b •
          (QuotientGroup.mk (orbitWeylRepresentative k) :
            SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup) := by
  apply quotientOrbit_reverse_witness_of_cell_card_eq hinj hforward k
  rw [orbitCellSubtype_card k, hcard]

theorem quotientRepresentative_surjective_of_ambient_order
    (hinj : Function.Injective quotientRepresentative)
    (hG : Nat.card SplitOctF2Aut = 12096) :
    Function.Surjective quotientRepresentative := by
  have hmul :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup
      G2TwoPCSubgroupClosure.unipotentSubgroup
  rw [hG, G2TwoPCSubgroupClosure.unipotentSubgroup_card] at hmul
  apply quotientRepresentative_surjective_of_quotient_card hinj
  omega

/-!
# Injectivity of representatives from a Tits-system readback

This owner isolates the non-computational bridge needed by the concrete
Bruhat index layer.  It does not construct a concrete Tits system and does
not infer disjointness from distinct middle elements.  Once representatives
are elements of `N` and their `toW` values are read back, the generic
`doubleCoset_eq_iff` theorem gives injectivity of their double cosets.
-/

theorem doubleCoset_representative_injective
    {G : Type*} [Group G]
    (ts : TitsSystem G)
    (rep : ts.W → ts.N)
    (hread : ∀ w : ts.W, ts.toW (rep w) = w) :
    Function.Injective
      (fun w : ts.W =>
        doubleCoset ts.B ((rep w : ts.N) : G)) := by
  intro w₁ w₂ hcell
  have hW : ts.toW (rep w₁) = ts.toW (rep w₂) := by
    exact (ts.doubleCoset_eq_iff (rep w₁) (rep w₂)).mp hcell
  simpa [hread] using hW

theorem doubleCoset_representative_ne_of_ne
    {G : Type*} [Group G]
    (ts : TitsSystem G)
    (rep : ts.W → ts.N)
    (hread : ∀ w : ts.W, ts.toW (rep w) = w)
    {w₁ w₂ : ts.W}
    (hne : w₁ ≠ w₂) :
    Disjoint
      (doubleCoset ts.B ((rep w₁ : ts.N) : G))
      (doubleCoset ts.B ((rep w₂ : ts.N) : G)) := by
  apply ts.cell_disjoint (rep w₁) (rep w₂)
  simpa [hread] using hne

end InfoGeometry.Algebra.Zorn.G2TitsRepresentativeInjectivity
