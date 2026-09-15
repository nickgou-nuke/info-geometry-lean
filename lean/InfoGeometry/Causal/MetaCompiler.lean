import InfoGeometry.Causal.CertifiedDependencyCompiler

namespace InfoGeometry.Causal.MetaCompiler

open Finset
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.ProofCarryingSchedule

/-!
# Finite proof-carrying compilation

The generic scheduler supplies the finite minimal-element argument, executable
topological extraction, and preservation of proof evidence.  This module gives
the compact theorem requested by the causal archetype protocol.
-/

theorem no_circular_hallucination {α : Type*} [PartialOrder α] (a b : α)
    (hab : a < b) (hba : b < a) : False :=
  lt_asymm hab hba

theorem acyclic_three_cycle {α : Type*} [PartialOrder α] (a b c : α)
    (hab : a < b) (hbc : b < c) (hca : c < a) : False := by
  exact lt_asymm (lt_trans hab hbc) hca

theorem exists_minimal_element {Node : Type*} [PartialOrder Node]
    (nodes : Finset Node) (nonempty : nodes.Nonempty) :
    ∃ minimal ∈ nodes, ∀ candidate ∈ nodes, ¬ candidate < minimal := by
  classical
  obtain ⟨minimal, membership, minimal_card⟩ :=
    nodes.exists_min_image (fun candidate => (nodes.filter (· < candidate)).card) nonempty
  refine ⟨minimal, membership, ?_⟩
  intro candidate candidate_mem candidate_lt
  have subset : insert candidate (nodes.filter (· < candidate)) ⊆
      nodes.filter (· < minimal) := by
    intro element element_mem
    simp only [mem_insert, mem_filter] at element_mem ⊢
    rcases element_mem with rfl | ⟨element_mem, element_lt⟩
    · exact ⟨candidate_mem, candidate_lt⟩
    · exact ⟨element_mem, lt_trans element_lt candidate_lt⟩
  have candidate_not_mem : candidate ∉ nodes.filter (· < candidate) := by simp
  have card_lt : (nodes.filter (· < candidate)).card <
      (nodes.filter (· < minimal)).card := by
    calc
      (nodes.filter (· < candidate)).card <
          (insert candidate (nodes.filter (· < candidate))).card := by
        rw [card_insert_of_notMem candidate_not_mem]
        exact Nat.lt_add_one _
      _ ≤ (nodes.filter (· < minimal)).card := card_le_card subset
  exact (not_lt_of_ge (minimal_card candidate candidate_mem)) card_lt

noncomputable def chooseMinimal {Node : Type*} [PartialOrder Node]
    (nodes : Finset Node) (nonempty : nodes.Nonempty) : Node :=
  Classical.choose (exists_minimal_element nodes nonempty)

theorem chooseMinimal_mem {Node : Type*} [PartialOrder Node]
    (nodes : Finset Node) (nonempty : nodes.Nonempty) :
    chooseMinimal nodes nonempty ∈ nodes :=
  (Classical.choose_spec
    (exists_minimal_element nodes nonempty)).1

theorem chooseMinimal_is_minimal {Node : Type*} [PartialOrder Node]
    (nodes : Finset Node) (nonempty : nodes.Nonempty) :
    ∀ candidate ∈ nodes, ¬ candidate < chooseMinimal nodes nonempty :=
  (Classical.choose_spec
    (exists_minimal_element nodes nonempty)).2

noncomputable def topologicalSort {Node : Type*} [PartialOrder Node]
    [DecidableEq Node] (nodes : Finset Node) : List Node :=
  if nonempty : nodes.Nonempty then
    let minimal := chooseMinimal nodes nonempty
    minimal :: topologicalSort (nodes.erase minimal)
  else []
termination_by nodes.card
decreasing_by
  rename_i nonempty minimal
  exact Finset.card_erase_lt_of_mem (chooseMinimal_mem nodes nonempty)

theorem topologicalSort_spec {Node : Type*} [PartialOrder Node]
    [DecidableEq Node] (nodes : Finset Node) :
    (topologicalSort nodes).Nodup ∧
      (topologicalSort nodes).length = nodes.card ∧
      (topologicalSort nodes).toFinset = nodes ∧
      (topologicalSort nodes).Pairwise (fun earlier later => ¬ later ≤ earlier) := by
  generalize card_eq : nodes.card = size
  induction size using Nat.strong_induction_on generalizing nodes with
  | h size induction =>
  by_cases nonempty : nodes.Nonempty
  · let minimal := chooseMinimal nodes nonempty
    let remainder := nodes.erase minimal
    have minimal_mem : minimal ∈ nodes := chooseMinimal_mem nodes nonempty
    have remainder_smaller : remainder.card < size := by
      rw [← card_eq]
      exact Finset.card_erase_lt_of_mem minimal_mem
    have remainder_spec := induction remainder.card remainder_smaller remainder (by rfl)
    have sort_eq : topologicalSort nodes = minimal :: topologicalSort remainder := by
      rw [topologicalSort]
      simp [nonempty, minimal, remainder]
    rw [sort_eq]
    rcases remainder_spec with ⟨nodup, length, covering, causal⟩
    have minimal_not_in_remainder : minimal ∉ topologicalSort remainder := by
      intro membership
      have in_remainder : minimal ∈ remainder := covering ▸ List.mem_toFinset.mpr membership
      exact (Finset.mem_erase.mp in_remainder).1 rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine List.nodup_cons.mpr ⟨?_, nodup⟩
      exact minimal_not_in_remainder
    · calc
        (topologicalSort remainder).length + 1 = remainder.card + 1 := by rw [length]
        _ = nodes.card := Finset.card_erase_add_one minimal_mem
        _ = size := card_eq
    · rw [List.toFinset_cons, covering]
      exact Finset.insert_erase minimal_mem
    · rw [List.pairwise_cons]
      refine ⟨?_, causal⟩
      intro later later_mem
      have later_mem_remainder : later ∈ remainder :=
        covering ▸ List.mem_toFinset.mpr later_mem
      intro later_le
      exact chooseMinimal_is_minimal nodes nonempty later
        (Finset.mem_erase.mp later_mem_remainder).2
        (lt_of_le_of_ne later_le (Finset.mem_erase.mp later_mem_remainder).1)
  · have empty : nodes = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    subst nodes
    have size_zero : size = 0 := by simpa using card_eq.symm
    subst size
    simp [topologicalSort]

theorem validSchedule_of_pairwise_not_le
    {Node : Type*} [PartialOrder Node] [DecidableEq Node]
    (schedule : List Node) (environment : Finset Node)
    (causal : schedule.Pairwise (fun earlier later => ¬ later ≤ earlier))
    (fresh : ∀ target ∈ schedule, target ∉ environment)
    (coverage : ∀ target ∈ schedule, ∀ prerequisite < target,
      prerequisite ∈ environment ∨ prerequisite ∈ schedule) :
    ValidSchedule environment schedule := by
  induction schedule generalizing environment with
  | nil => trivial
  | cons target remaining induction =>
      have remaining_fresh : ∀ candidate ∈ remaining,
          candidate ∉ insert target environment := by
        intro candidate membership
        simp only [Finset.mem_insert, not_or]
        refine ⟨?_, fresh candidate (List.mem_cons_of_mem target membership)⟩
        intro equal
        exact (List.pairwise_cons.mp causal).1 candidate membership
          (equal ▸ le_rfl)
      have remaining_coverage : ∀ later ∈ remaining, ∀ prerequisite < later,
          prerequisite ∈ insert target environment ∨ prerequisite ∈ remaining := by
        intro later later_mem prerequisite precedes
        rcases coverage later (List.mem_cons_of_mem target later_mem) prerequisite precedes with
          present | present
        · exact Or.inl (Finset.mem_insert_of_mem present)
        · rcases List.mem_cons.mp present with rfl | present
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr present
      refine ⟨⟨fresh target List.mem_cons_self, ?_⟩,
        induction (insert target environment) causal.tail remaining_fresh remaining_coverage⟩
      · intro prerequisite precedes
        rcases coverage target (List.mem_cons_self) prerequisite precedes with
          present | present
        · exact present
        · rcases List.mem_cons.mp present with rfl | present
          · exact False.elim (precedes.ne rfl)
          · exact False.elim ((List.pairwise_cons.mp causal).1 prerequisite present precedes.le)

theorem statement_of_validSchedule
    {Node : Type*} [PartialOrder Node] [DecidableEq Node]
    {statement : Node → Prop} (rules : ProofRules statement)
    (environment : Finset Node) (schedule : List Node)
    (valid : ValidSchedule environment schedule)
    (evidence : ∀ target ∈ environment, statement target) :
    ∀ target ∈ schedule, statement target := by
  induction schedule generalizing environment with
  | nil => simp
  | cons target remaining induction =>
      have target_proof : statement target := rules target (fun prerequisite precedes =>
        evidence prerequisite (valid.1.2 prerequisite precedes))
      have extended : ∀ candidate ∈ insert target environment, statement candidate := by
        intro candidate membership
        rcases Finset.mem_insert.mp membership with rfl | membership
        · exact target_proof
        · exact evidence candidate membership
      intro candidate membership
      rcases List.mem_cons.mp membership with rfl | membership
      · exact target_proof
      · exact induction (insert target environment) valid.2 extended candidate membership

theorem finite_certified_compilation
    {Node : Type*} [PartialOrder Node] [DecidableEq Node] [Fintype Node]
    (statement : Node → Prop)
    (rules : ProofRules statement) :
    ∃ schedule : List Node,
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card Node ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, statement target := by
  let schedule := topologicalSort (Finset.univ : Finset Node)
  have specification := topologicalSort_spec (Finset.univ : Finset Node)
  rcases specification with ⟨nodup, length, complete, pairwise⟩
  have coverage : ∀ target ∈ schedule, ∀ prerequisite < target,
      prerequisite ∈ (∅ : Finset Node) ∨ prerequisite ∈ schedule := by
    intro target target_mem prerequisite precedes
    exact Or.inr (by
      have : prerequisite ∈ (Finset.univ : Finset Node) := Finset.mem_univ prerequisite
      rw [← complete] at this
      exact List.mem_toFinset.mp this)
  have fresh : ∀ target ∈ schedule, target ∉ (∅ : Finset Node) := by
    intro target _
    simp
  have valid := validSchedule_of_pairwise_not_le schedule ∅ pairwise fresh coverage
  have proofs : ∀ target, statement target := by
    intro target
    apply statement_of_validSchedule rules ∅ schedule valid
    · intro candidate membership
      simp at membership
    · have target_mem : target ∈ schedule := by
        have : target ∈ (Finset.univ : Finset Node) := Finset.mem_univ target
        rw [← complete] at this
        exact List.mem_toFinset.mp this
      exact target_mem
  have exact_length : schedule.length = Fintype.card Node := by
    rw [length, Finset.card_univ]
  exact ⟨schedule, valid, pairwise, nodup, exact_length, complete, proofs⟩

end InfoGeometry.Causal.MetaCompiler

namespace InfoGeometry.MetaCompiler

open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.ProofCarryingSchedule

theorem finite_certified_compilation
    {Node : Type*} [PartialOrder Node] [DecidableEq Node] [Fintype Node]
    (statement : Node → Prop)
    (rules : ProofRules statement) :
    ∃ schedule : List Node,
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card Node ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, statement target :=
  InfoGeometry.Causal.MetaCompiler.finite_certified_compilation statement rules

end InfoGeometry.MetaCompiler
