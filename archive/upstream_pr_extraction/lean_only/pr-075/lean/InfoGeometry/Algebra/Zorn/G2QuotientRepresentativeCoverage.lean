import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.Zorn.G2BNPair
import InfoGeometry.GroupTheory.DoubleCosetOrbit
import InfoGeometry.Algebra.Zorn.G2BruhatCellIntersectionCard
import InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation
import InfoGeometry.Algebra.Zorn.G2BruhatResidual
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
import InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe
import InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
import InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier

/-!
# Native coverage of the quotient representative table

The 189 representatives define a map into the concrete quotient.  This owner
isolates the exact carrier-level statement still needed for exhaustion: every
automorphism has one of the representatives as a left quotient representative.
No ambient cardinality or enumeration theorem is used here.
-/

namespace InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeCoverage

open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2BNPair
open InfoGeometry.GroupTheory.DoubleCoset
open InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoOppositeUnipotent
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.GroupTheory.G2BruhatInversions
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier

def QuotientRepresentativeCover : Prop :=
  ∀ g : SplitOctF2Aut, ∃ i : Fin 189,
    (flagRepresentative i)⁻¹ * g ∈ unipotentSubgroup

theorem quotientOrbit_eq_subtype_mulAction_orbit
    (B : Subgroup SplitOctF2Aut) (w : SplitOctF2Aut) :
    quotientOrbit B w =
      MulAction.orbit B (QuotientGroup.mk w : SplitOctF2Aut ⧸ B) := by
  ext q
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact MulAction.mem_orbit_iff.mpr
      ⟨⟨b, hb⟩, rfl⟩
  · intro hq
    rcases MulAction.mem_orbit_iff.mp hq with ⟨b, rfl⟩
    exact ⟨b.1, b.2, rfl⟩

theorem mem_quotientOrbit_stabilizer_iff
    (B : Subgroup SplitOctF2Aut) (w : SplitOctF2Aut)
    (b : B) :
    b ∈ MulAction.stabilizer B
        (QuotientGroup.mk w : SplitOctF2Aut ⧸ B) ↔
      w⁻¹ * (b : SplitOctF2Aut) * w ∈ B := by
  change (b : SplitOctF2Aut) •
      (QuotientGroup.mk w : SplitOctF2Aut ⧸ B) =
      (QuotientGroup.mk w : SplitOctF2Aut ⧸ B) ↔ _
  change (QuotientGroup.mk ((b : SplitOctF2Aut) * w) :
      SplitOctF2Aut ⧸ B) = QuotientGroup.mk w ↔ _
  rw [QuotientGroup.eq]
  have hinv :
      (w⁻¹ * (b : SplitOctF2Aut) * w ∈ B) ↔
        (w⁻¹ * (b : SplitOctF2Aut) * w)⁻¹ ∈ B := by
    constructor <;> intro h
    · exact B.inv_mem h
    · exact B.inv_mem h
  simpa [mul_assoc] using hinv.symm

def quotientStabilizerEquivIntersection
    (B : Subgroup SplitOctF2Aut) (w : SplitOctF2Aut) :
    MulAction.stabilizer B
        (QuotientGroup.mk w : SplitOctF2Aut ⧸ B) ≃
      intersectionSubgroup B (conjugateSubgroup w B) where
  toFun p :=
    ⟨p.1, p.1.property, by
      change w⁻¹ * (p.1 : SplitOctF2Aut) * w ∈ B
      exact (mem_quotientOrbit_stabilizer_iff B w p.1).1 p.2⟩
  invFun x :=
    ⟨⟨x.1, x.2.1⟩,
      (mem_quotientOrbit_stabilizer_iff B w ⟨x.1, x.2.1⟩).2 x.2.2⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

theorem quotientOrbit_card_mul_intersection_card
    (B : Subgroup SplitOctF2Aut) (w : SplitOctF2Aut)
    [Fintype B]
    [Fintype (MulAction.orbit B
      (QuotientGroup.mk w : SplitOctF2Aut ⧸ B))]
    [Fintype (MulAction.stabilizer B
      (QuotientGroup.mk w : SplitOctF2Aut ⧸ B))]
    [Fintype (intersectionSubgroup B (conjugateSubgroup w B))] :
    Fintype.card (MulAction.orbit B
        (QuotientGroup.mk w : SplitOctF2Aut ⧸ B)) *
      Fintype.card (intersectionSubgroup B (conjugateSubgroup w B)) =
        Fintype.card B := by
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    B (QuotientGroup.mk w : SplitOctF2Aut ⧸ B)
  rw [Fintype.card_congr (quotientStabilizerEquivIntersection B w)] at h
  exact h

noncomputable instance identityOrbitFintype :
    Fintype (MulAction.orbit unipotentSubgroup
      (QuotientGroup.mk (1 : SplitOctF2Aut) :
        SplitOctF2Aut ⧸ unipotentSubgroup)) := Fintype.ofFinite _

theorem identity_quotientOrbit_card :
    Fintype.card (MulAction.orbit unipotentSubgroup
      (QuotientGroup.mk (1 : SplitOctF2Aut) :
        SplitOctF2Aut ⧸ unipotentSubgroup)) = 1 := by
  letI : Fintype unipotentSubgroup := Fintype.ofFinite _
  letI : Fintype (MulAction.orbit unipotentSubgroup
      (QuotientGroup.mk (1 : SplitOctF2Aut) :
        SplitOctF2Aut ⧸ unipotentSubgroup)) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer unipotentSubgroup
      (QuotientGroup.mk (1 : SplitOctF2Aut) :
        SplitOctF2Aut ⧸ unipotentSubgroup)) := Fintype.ofFinite _
  letI : Fintype (intersectionSubgroup unipotentSubgroup
      (conjugateSubgroup (1 : SplitOctF2Aut) unipotentSubgroup)) :=
    Fintype.ofFinite _
  have h := quotientOrbit_card_mul_intersection_card
    unipotentSubgroup (1 : SplitOctF2Aut)
  have hU : Fintype.card unipotentSubgroup = 64 := by
    simpa [Nat.card_eq_fintype_card] using unipotentSubgroup_card
  have hI : Fintype.card (intersectionSubgroup unipotentSubgroup
      (conjugateSubgroup (1 : SplitOctF2Aut) unipotentSubgroup)) = 64 := by
    simpa [Nat.card_eq_fintype_card] using
      InfoGeometry.Algebra.Zorn.G2BruhatCellIntersectionCard.identity_intersection_card
  rw [hU, hI] at h
  norm_num at h
  omega

theorem orbitWeylRepresentative_zero_eq_one :
    orbitWeylRepresentative 0 = (1 : SplitOctF2Aut) := by
  rw [orbitWeylRepresentative, orbitWeyl]
  simpa using weylNF_zero_false

theorem quotientStabilizer_card_eq_residual_card
    (p : WeylG2) :
    Nat.card (MulAction.stabilizer unipotentSubgroup
      (QuotientGroup.mk
        (w0 * weylNF p.1 p.2) :
          SplitOctF2Aut ⧸ unipotentSubgroup)) =
      Nat.card (residualSubgroup p) := by
  calc
    Nat.card (MulAction.stabilizer unipotentSubgroup
        (QuotientGroup.mk
          (w0 * weylNF p.1 p.2) :
            SplitOctF2Aut ⧸ unipotentSubgroup)) =
        Nat.card (intersectionSubgroup unipotentSubgroup
          (conjugateSubgroup (w0 * weylNF p.1 p.2)
            unipotentSubgroup)) := by
      exact Nat.card_congr
        (quotientStabilizerEquivIntersection unipotentSubgroup
          (w0 * weylNF p.1 p.2))
    _ = Nat.card (residualSubgroup p) := by
      rw [← residualSubgroup_eq_doubleCoset_intersection p]

theorem quotientStabilizer_card_eq_pow_of_bruhat_equiv
    (p : WeylG2)
    (e : BruhatResidualExponent p ≃ residualSubgroup p) :
    Nat.card (MulAction.stabilizer unipotentSubgroup
      (QuotientGroup.mk
        (w0 * weylNF p.1 p.2) :
          SplitOctF2Aut ⧸ unipotentSubgroup)) =
      2 ^ dihedralLength p := by
  rw [quotientStabilizer_card_eq_residual_card p]
  exact residualSubgroup_card_eq_pow_of_bruhat_equiv p e

/-! The residual convention uses `w0 * weylNF p`, while the concrete Weyl
    carrier is indexed by a single `weylNF`.  This readback is purely
    algebraic and does not assert quotient coverage or cell uniqueness. -/

theorem residual_conjugator_weylNF_readback
    (p : WeylG2) :
    ∃ q : WeylG2,
      w0 * weylNF p.1 p.2 = weylNF q.1 q.2 := by
  have hw0 : w0 = weylNF 3 false := by
    rw [weylNF_three_false]
    exact c_pow_three_eq_swapCartan
  obtain ⟨m, e, h⟩ := weylNF_mul_exists 3 p.1 false p.2
  refine ⟨(m, e), ?_⟩
  rw [hw0]
  exact h

theorem quotientStabilizer_card_eq_pow_of_weylNF_readback
    (p q : WeylG2)
    (hread : w0 * weylNF p.1 p.2 = weylNF q.1 q.2)
    (e : BruhatResidualExponent p ≃ residualSubgroup p) :
    Nat.card (MulAction.stabilizer unipotentSubgroup
      (QuotientGroup.mk
        (weylNF q.1 q.2) :
          SplitOctF2Aut ⧸ unipotentSubgroup)) =
      2 ^ dihedralLength p := by
  rw [← hread]
  exact quotientStabilizer_card_eq_pow_of_bruhat_equiv p e

theorem quotientRepresentative_surjective_iff_group_cover :
    Function.Surjective quotientRepresentative ↔
      QuotientRepresentativeCover := by
  constructor
  · intro hsurj g
    obtain ⟨i, hi⟩ := hsurj (QuotientGroup.mk g)
    change QuotientGroup.mk (flagRepresentative i) = QuotientGroup.mk g at hi
    rw [QuotientGroup.eq] at hi
    exact ⟨i, hi⟩
  · intro hcover q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨i, hi⟩ := hcover g
    refine ⟨i, ?_⟩
    change QuotientGroup.mk (flagRepresentative i) = QuotientGroup.mk g
    rw [QuotientGroup.eq]
    exact hi

theorem quotientRepresentative_surjective_of_group_cover
    (hcover : QuotientRepresentativeCover) :
    Function.Surjective quotientRepresentative :=
  (quotientRepresentative_surjective_iff_group_cover).2 hcover

theorem group_cover_of_quotientRepresentative_surjective
    (hsurj : Function.Surjective quotientRepresentative) :
    QuotientRepresentativeCover :=
  (quotientRepresentative_surjective_iff_group_cover).1 hsurj

/-! Ordered-product owners naturally produce a right-factor form.  This lemma
    is the direct transport from that form to the quotient coverage target. -/

theorem group_cover_of_right_unipotent_factorization
    (hfactor : ∀ g : SplitOctF2Aut, ∃ i : Fin 189, ∃ u : SplitOctF2Aut,
      u ∈ unipotentSubgroup ∧ g = flagRepresentative i * u) :
    QuotientRepresentativeCover := by
  intro g
  obtain ⟨i, u, hu, hgu⟩ := hfactor g
  refine ⟨i, ?_⟩
  rw [hgu, inv_mul_cancel_left]
  exact hu

/-! A single carrier-aligned matrix witness is exactly the quotient witness
    needed by the finite orbit certificate.  This keeps matrix transport out
    of the coverage theorem itself. -/

theorem quotientRepresentative_eq_left_smul_of_matrix_witness
    (i : Fin 189) (b w : SplitOctF2Aut)
    (h : ∃ e : G2TwoSylowSubgroup.PCWordExp,
      autMatrix ((flagRepresentative i)⁻¹ * (b * w)) =
        autMatrix (G2TwoSylowSubgroup.pcWord e)) :
    quotientRepresentative i =
      b • (QuotientGroup.mk w :
        SplitOctF2Aut ⧸ unipotentSubgroup) := by
  change QuotientGroup.mk (flagRepresentative i) =
    QuotientGroup.mk (b * w)
  rw [QuotientGroup.eq]
  obtain ⟨e, he⟩ := h
  have hgroup :
      (flagRepresentative i)⁻¹ * (b * w) =
        G2TwoSylowSubgroup.pcWord e :=
    autMatrix_injective he
  rw [hgroup]
  exact ⟨e, rfl⟩

theorem quotient_orbit_witness_of_matrix_family
    (hmat : ∀ (k : Fin 12) (i : Fin 189),
      i ∈ orbitCells k →
      ∃ e : G2TwoSylowSubgroup.PCWordExp,
        autMatrix ((flagRepresentative i)⁻¹ *
            (G2TwoSylowSubgroup.pcWord e *
              weylNF (orbitWeyl k).1 (orbitWeyl k).2)) =
          autMatrix (G2TwoSylowSubgroup.pcWord e)) :
    ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      ∃ b : SplitOctF2Aut,
        b ∈ unipotentSubgroup ∧
          quotientRepresentative i =
            b • (QuotientGroup.mk
              (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
                SplitOctF2Aut ⧸ unipotentSubgroup) := by
  intro k i hi
  obtain ⟨e, he⟩ := hmat k i hi
  refine ⟨G2TwoSylowSubgroup.pcWord e, ?_, ?_⟩
  · exact ⟨e, rfl⟩
  · exact quotientRepresentative_eq_left_smul_of_matrix_witness
      i (G2TwoSylowSubgroup.pcWord e)
      (weylNF (orbitWeyl k).1 (orbitWeyl k).2) ⟨e, he⟩

theorem quotient_orbit_witness_of_collected_factorization
    (k : Fin 12) (i : Fin 189)
    (hfac : flagRepresentative i =
      collect (G2CASFactorizationCarrier.leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
        collect (G2CASFactorizationCarrier.rightFactorWord k i)) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        quotientRepresentative i =
          b • (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
              SplitOctF2Aut ⧸ unipotentSubgroup) := by
  refine ⟨collect (G2CASFactorizationCarrier.leftFactorWord k i),
    leftFactorWord_mem_unipotentSubgroup k i, ?_⟩
  change QuotientGroup.mk (flagRepresentative i) =
    QuotientGroup.mk
      (collect (G2CASFactorizationCarrier.leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2)
  rw [hfac, QuotientGroup.eq]
  have hright :
      (collect (G2CASFactorizationCarrier.rightFactorWord k i))⁻¹ ∈
        unipotentSubgroup :=
    unipotentSubgroup.inv_mem
      (rightFactorWord_mem_unipotentSubgroup k i)
  obtain ⟨e, he⟩ := hright
  refine ⟨e, ?_⟩
  simp [mul_assoc]
  rw [← he]

theorem cell_one_45_quotient_witness_from_collected_factorization :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        quotientRepresentative 45 =
          b • (QuotientGroup.mk
            (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) :
              SplitOctF2Aut ⧸ unipotentSubgroup) := by
  exact quotient_orbit_witness_of_collected_factorization
    1 45 cell_one_45_factorization

end InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeCoverage
