import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import InfoGeometry.Algebra.Zorn.G2CASGeneratorSubgroup

/-!
# Concrete generator infrastructure for the `G₂(2)` Bruhat cover

This owner records the closure facts that are already consequences of the
concrete double-coset API.  It deliberately does not assert global coverage
or generation of `SplitOctF2Aut`; those remain separate obligations.
-/

namespace InfoGeometry.Algebra.Zorn.G2ConcreteGeneratorInfrastructure

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2CASGeneratorSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation

theorem concreteBruhatCovering_left_mul_borel
    (b : SplitOctF2Aut) (hb : b ∈ unipotentSubgroup)
    {g : SplitOctF2Aut} (hg : g ∈ concreteBruhatCovering) :
    b * g ∈ concreteBruhatCovering := by
  have hb' : b ∈ G2TwoSylowSubgroup.sylowTwoSubgroup := by
    rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    exact hb
  rcases Set.mem_iUnion.mp hg with ⟨p, hp⟩
  apply Set.mem_iUnion.mpr ⟨p, ?_⟩
  exact concreteBruhatCell_left_mul (weylNF p.1 p.2) b g hb' hp

theorem concreteBruhatCovering_right_mul_borel
    (b : SplitOctF2Aut) (hb : b ∈ unipotentSubgroup)
    {g : SplitOctF2Aut} (hg : g ∈ concreteBruhatCovering) :
    g * b ∈ concreteBruhatCovering := by
  have hb' : b ∈ G2TwoSylowSubgroup.sylowTwoSubgroup := by
    rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    exact hb
  rcases Set.mem_iUnion.mp hg with ⟨p, hp⟩
  apply Set.mem_iUnion.mpr ⟨p, ?_⟩
  exact concreteBruhatCell_right_mul (weylNF p.1 p.2) b g hb' hp

theorem unipotentSubgroup_le_flagGeneratedSubgroup :
    unipotentSubgroup ≤
      InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator.flagGeneratedSubgroup := by
  have hle : unipotentSubgroup ≤ casGeneratedSubgroup := by
    intro g hg
    rcases hg with ⟨e, rfl⟩
    have h0 : G2TwoSylowPCAutomorphisms.pcGenerator 0 ∈
        casGeneratedSubgroup := pcGenerator_zero_mem_casGeneratedSubgroup
    have h1 : G2TwoSylowPCAutomorphisms.pcGenerator 1 ∈
        casGeneratedSubgroup := pcGenerator_one_mem_casGeneratedSubgroup
    have h2 : G2TwoSylowPCAutomorphisms.pcGenerator 2 ∈
        casGeneratedSubgroup := pcGenerator_two_mem_casGeneratedSubgroup
    have h3 : G2TwoSylowPCAutomorphisms.pcGenerator 3 ∈
        casGeneratedSubgroup := pcGenerator_three_mem_casGeneratedSubgroup
    have h4 : G2TwoSylowPCAutomorphisms.pcGenerator 4 ∈
        casGeneratedSubgroup := pcGenerator_four_mem_casGeneratedSubgroup
    have h5 : G2TwoSylowPCAutomorphisms.pcGenerator 5 ∈
        casGeneratedSubgroup := pcGenerator_five_mem_casGeneratedSubgroup
    have hterm : ∀ i : Fin 6,
        G2TwoSylowSubgroup.pcTerm i (e i) ∈ casGeneratedSubgroup := by
      intro i
      fin_cases i
      · cases h : e 0 <;> simp [G2TwoSylowSubgroup.pcTerm, h, h0]
      · cases h : e 1 <;> simp [G2TwoSylowSubgroup.pcTerm, h, h1]
      · cases h : e 2 <;> simp [G2TwoSylowSubgroup.pcTerm, h, h2]
      · cases h : e 3 <;> simp [G2TwoSylowSubgroup.pcTerm, h, h3]
      · cases h : e 4 <;> simp [G2TwoSylowSubgroup.pcTerm, h, h4]
      · cases h : e 5 <;> simp [G2TwoSylowSubgroup.pcTerm, h, h5]
    dsimp [G2TwoSylowSubgroup.pcWord]
    exact casGeneratedSubgroup.mul_mem
      (casGeneratedSubgroup.mul_mem
        (casGeneratedSubgroup.mul_mem
          (casGeneratedSubgroup.mul_mem
            (casGeneratedSubgroup.mul_mem (hterm 0) (hterm 1))
            (hterm 2))
          (hterm 3))
        (hterm 4))
      (hterm 5)
  rw [← casGeneratedSubgroup_eq_flagGeneratedSubgroup]
  exact hle

theorem simpleWeylGenerators_mem_flagGeneratedSubgroup :
    s ∈ InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator.flagGeneratedSubgroup ∧
      t ∈ InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator.flagGeneratedSubgroup := by
  have hs : s ∈ casGeneratedSubgroup := by
    simpa [s] using swap01Aut_mem_casGeneratedSubgroup
  have ht_word : t = s * correctedT * s := by
    apply automorphism_ext_of_basis
    intro i
    fin_cases i <;> rfl
  have ht : t ∈ casGeneratedSubgroup := by
    rw [ht_word]
    exact casGeneratedSubgroup.mul_mem
      (casGeneratedSubgroup.mul_mem hs correctedT_mem_casGeneratedSubgroup) hs
  rw [← casGeneratedSubgroup_eq_flagGeneratedSubgroup]
  exact ⟨hs, ht⟩

def concreteBNGeneratorSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure
    ((unipotentSubgroup : Set SplitOctF2Aut) ∪ {s, t})

theorem concreteBNGeneratorSubgroup_le_flagGeneratedSubgroup :
    concreteBNGeneratorSubgroup ≤
      InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator.flagGeneratedSubgroup := by
  apply (Subgroup.closure_le _).2
  intro x hx
  rcases hx with hxU | hxS
  · exact unipotentSubgroup_le_flagGeneratedSubgroup hxU
  · rcases hxS with rfl | rfl
    · exact simpleWeylGenerators_mem_flagGeneratedSubgroup.1
    · exact simpleWeylGenerators_mem_flagGeneratedSubgroup.2

/-! The missing simple-reflection step is exposed as an explicit obligation. -/

def ConcreteBN2Transition : Prop :=
  ∀ r ∈ ({s, t} : Set SplitOctF2Aut), ∀ w : WeylG2,
    ∀ g ∈ concreteBruhatCell (weylNF w.1 w.2),
      r * g ∈ concreteBruhatCovering

def ConcreteCanonicalPeelingStep : Prop :=
  ∀ r ∈ ({s, t} : Set SplitOctF2Aut), ∀ w : WeylG2,
    ∀ g ∈ concreteBruhatCell (weylNF w.1 w.2),
      ∃ w' : WeylG2,
        r * g ∈ concreteBruhatCell (weylNF w'.1 w'.2)

theorem concreteBN2Transition_of_canonicalPeeling
    (h : ConcreteCanonicalPeelingStep) :
    ConcreteBN2Transition := by
  intro r hr w g hg
  obtain ⟨w', hw'⟩ := h r hr w g hg
  exact Set.mem_iUnion.mpr ⟨w', hw'⟩

theorem concreteBruhatCovering_left_mul_simple_of_transition
    (h : ConcreteBN2Transition)
    (r : SplitOctF2Aut) (hr : r ∈ ({s, t} : Set SplitOctF2Aut))
    {g : SplitOctF2Aut} (hg : g ∈ concreteBruhatCovering) :
    r * g ∈ concreteBruhatCovering := by
  rcases Set.mem_iUnion.mp hg with ⟨w, hw⟩
  exact h r hr w g hw

theorem concreteBruhatCovering_left_mul_word
    (h : ConcreteBN2Transition)
    (L : List SplitOctF2Aut)
    (hL : ∀ r ∈ L,
      r ∈ (unipotentSubgroup : Set SplitOctF2Aut) ∪
        ({s, t} : Set SplitOctF2Aut))
    {g : SplitOctF2Aut} (hg : g ∈ concreteBruhatCovering) :
    L.prod * g ∈ concreteBruhatCovering := by
  induction L with
  | nil => simpa using hg
  | cons r L ih =>
      rw [List.prod_cons, mul_assoc]
      have htail : L.prod * g ∈ concreteBruhatCovering := by
        apply ih
        intro q hq
        exact hL q (List.mem_cons_of_mem r hq)
      rcases hL r (List.mem_cons_self) with hrU | hrS
      · exact concreteBruhatCovering_left_mul_borel r hrU htail
      · exact concreteBruhatCovering_left_mul_simple_of_transition h r hrS htail

theorem mem_concreteBruhatCovering_of_cell
    (w : WeylG2) {g : SplitOctF2Aut}
    (hg : g ∈ concreteBruhatCell (weylNF w.1 w.2)) :
    g ∈ concreteBruhatCovering := by
  exact Set.mem_iUnion.mpr ⟨w, hg⟩

/-- Elements preserving the concrete Bruhat union in both directions form a
subgroup.  The two-sided formulation is essential for the inverse law. -/
theorem concreteBN2Transition_s_identity
    {g : SplitOctF2Aut}
    (hg : g ∈ concreteBruhatCell (weylNF 0 false)) :
    s * g ∈ concreteBruhatCovering := by
  have hg' : g ∈ G2TwoSylowSubgroup.sylowTwoSubgroup := by
    simpa [weylNF_zero_false, concreteBruhatCell_one_eq_sylow] using hg
  have hs : s * g ∈ concreteBruhatCell s := by
    exact simple_reflection_s_mul_borel g hg'
  exact Set.mem_iUnion.mpr ⟨(0, true), by
    simpa [weylNF, s] using hs⟩

theorem concreteBN2Transition_t_identity
    {g : SplitOctF2Aut}
    (hg : g ∈ concreteBruhatCell (weylNF 0 false)) :
    t * g ∈ concreteBruhatCovering := by
  have hg' : g ∈ G2TwoSylowSubgroup.sylowTwoSubgroup := by
    simpa [weylNF_zero_false, concreteBruhatCell_one_eq_sylow] using hg
  have ht : t * g ∈ concreteBruhatCell t := by
    exact simple_reflection_t_mul_borel g hg'
  exact Set.mem_iUnion.mpr ⟨(1, true), by
    simpa [weylNF, t] using ht⟩

/-- The canonical peeling obligation is provable on the identity cell.
    This records the genuine base case without claiming the missing Weyl-word
    induction for the remaining eleven cells. -/
theorem concreteCanonicalPeelingStep_identity
    {r : SplitOctF2Aut} (hr : r ∈ ({s, t} : Set SplitOctF2Aut))
    {g : SplitOctF2Aut}
    (hg : g ∈ concreteBruhatCell (weylNF 0 false)) :
    ∃ w' : WeylG2,
      r * g ∈ concreteBruhatCell (weylNF w'.1 w'.2) := by
  rcases hr with rfl | rfl
  · have hg' : g ∈ G2TwoSylowSubgroup.sylowTwoSubgroup := by
      simpa [weylNF_zero_false, concreteBruhatCell_one_eq_sylow] using hg
    have hs : s * g ∈ concreteBruhatCell s :=
      simple_reflection_s_mul_borel g hg'
    exact ⟨(0, true), by simpa [weylNF, s] using hs⟩
  · have hg' : g ∈ G2TwoSylowSubgroup.sylowTwoSubgroup := by
      simpa [weylNF_zero_false, concreteBruhatCell_one_eq_sylow] using hg
    have ht : t * g ∈ concreteBruhatCell t :=
      simple_reflection_t_mul_borel g hg'
    exact ⟨(1, true), by simpa [weylNF, t] using ht⟩

theorem concreteBN2Transition_identity_cell
    {r g : SplitOctF2Aut}
    (hr : r ∈ ({s, t} : Set SplitOctF2Aut))
    (hg : g ∈ concreteBruhatCell (weylNF 0 false)) :
    r * g ∈ concreteBruhatCovering := by
  rcases hr with rfl | rfl
  · exact concreteBN2Transition_s_identity hg
  · exact concreteBN2Transition_t_identity hg

theorem concreteBruhatCell_mem_of_pc_factorization
    (r : SplitOctF2Aut) (e a b : PCWordExp)
    (ha : G2TwoSylowSubgroup.pcWord a ∈ unipotentSubgroup)
    (hb : G2TwoSylowSubgroup.pcWord b ∈ unipotentSubgroup)
    (hfac : r * G2TwoSylowSubgroup.pcWord e * r =
      G2TwoSylowSubgroup.pcWord a * r * G2TwoSylowSubgroup.pcWord b) :
    r * G2TwoSylowSubgroup.pcWord e * r ∈ concreteBruhatCell r := by
  rw [concreteBruhatCell_eq_exact_unipotentCell]
  exact ⟨G2TwoSylowSubgroup.pcWord a, ha,
    G2TwoSylowSubgroup.pcWord b, hb, hfac⟩

end InfoGeometry.Algebra.Zorn.G2ConcreteGeneratorInfrastructure
