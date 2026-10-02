import InfoGeometry.Causal.FiniteDependencySchedule

namespace InfoGeometry.Causal.FiniteDependencyCompiler

open FiniteDependencySchedule

variable {Node : Type*} [PartialOrder Node] [DecidableEq Node]
  [Fintype Node] [DecidableLT Node]

def selectReady (environment : Finset Node) (pending : List Node) : Option Node :=
  pending.find? (fun target => decide (IsReady environment target))

def compileWithFuel : Nat → Finset Node → List Node → Option (List Node)
  | _, _, [] => some []
  | 0, _, _ :: _ => none
  | fuel + 1, environment, pending@(_ :: _) =>
      match selectReady environment pending with
      | none => none
      | some target =>
          (compileWithFuel fuel (insert target environment) (pending.erase target)).map
            (target :: ·)

def compile (environment : Finset Node) (pending : List Node) : Option (List Node) :=
  compileWithFuel pending.length environment pending

theorem selectReady_sound {environment : Finset Node} {pending : List Node} {target : Node}
    (selected : selectReady environment pending = some target) :
    target ∈ pending ∧ IsReady environment target := by
  exact ⟨List.mem_of_find?_eq_some selected, by
    simpa using List.find?_some selected⟩

theorem selectReady_none_iff (environment : Finset Node) (pending : List Node) :
    selectReady environment pending = none ↔
      ∀ target ∈ pending, ¬ IsReady environment target := by
  simp [selectReady, List.find?_eq_none]

theorem compileWithFuel_sound {fuel : Nat} {environment : Finset Node}
    {pending schedule : List Node}
    (compiled : compileWithFuel fuel environment pending = some schedule) :
    ValidSchedule environment schedule ∧ schedule.Perm pending := by
  induction fuel generalizing environment pending schedule with
  | zero =>
    cases pending with
    | nil =>
      simp only [compileWithFuel, Option.some.injEq] at compiled
      subst schedule
      exact ⟨trivial, List.Perm.refl _⟩
    | cons first rest => simp [compileWithFuel] at compiled
  | succ fuel inductionHypothesis =>
    cases pending with
    | nil =>
      simp only [compileWithFuel, Option.some.injEq] at compiled
      subst schedule
      exact ⟨trivial, List.Perm.refl _⟩
    | cons first rest =>
      cases selected : selectReady environment (first :: rest) with
      | none => simp [compileWithFuel, selected] at compiled
      | some target =>
        obtain ⟨remaining, recursive, rfl⟩ := Option.map_eq_some_iff.mp
          (show (compileWithFuel fuel (insert target environment)
            ((first :: rest).erase target)).map (target :: ·) = some schedule from
            by simpa only [compileWithFuel, selected] using compiled)
        obtain ⟨valid, permutation⟩ := inductionHypothesis recursive
        obtain ⟨membership, ready⟩ := selectReady_sound selected
        exact ⟨⟨ready, valid⟩,
          (permutation.cons target).trans (List.perm_cons_erase membership).symm⟩

theorem compile_sound {environment : Finset Node} {pending schedule : List Node}
    (compiled : compile environment pending = some schedule) :
    ValidSchedule environment schedule ∧ schedule.Perm pending :=
  compileWithFuel_sound compiled

theorem selectReady_exists {environment targetSet : Finset Node} {pending : List Node}
    (closed : IsLowerSet (targetSet : Set Node))
    (coverage : pending.toFinset = targetSet \ environment) (nonempty : pending ≠ []) :
    ∃ target, selectReady environment pending = some target := by
  have remaining : (targetSet \ environment).Nonempty := by
    rw [← coverage]
    simpa using nonempty
  obtain ⟨target, membership, ready⟩ := exists_ready_in_remaining closed remaining
  cases selected : selectReady environment pending with
  | some chosen => exact ⟨chosen, rfl⟩
  | none =>
    have inPending : target ∈ pending := by
      simpa only [← coverage, List.mem_toFinset] using membership
    exact False.elim ((selectReady_none_iff _ _).mp selected target inPending ready)

omit [PartialOrder Node] [Fintype Node] [DecidableLT Node] in
theorem erase_covers_remaining {environment targetSet : Finset Node}
    {pending : List Node} (distinct : pending.Nodup)
    (coverage : pending.toFinset = targetSet \ environment) (target : Node) :
    (pending.erase target).toFinset = targetSet \ insert target environment := by
  ext node
  have covered : node ∈ pending ↔ node ∈ targetSet ∧ node ∉ environment := by
    simpa only [List.mem_toFinset, Finset.mem_sdiff] using
      Iff.of_eq (congrArg (fun elements => node ∈ elements) coverage)
  simp only [List.mem_toFinset, distinct.mem_erase_iff, covered, Finset.mem_sdiff,
    Finset.mem_insert]
  tauto

theorem compileWithFuel_complete (fuel : Nat) (environment targetSet : Finset Node)
    (pending : List Node) (closed : IsLowerSet (targetSet : Set Node))
    (distinct : pending.Nodup) (coverage : pending.toFinset = targetSet \ environment)
    (enoughFuel : pending.length ≤ fuel) :
    ∃ schedule, compileWithFuel fuel environment pending = some schedule := by
  induction fuel generalizing environment pending with
  | zero =>
    have empty : pending = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enoughFuel)
    subst pending
    exact ⟨[], rfl⟩
  | succ fuel inductionHypothesis =>
    cases pending with
    | nil => exact ⟨[], rfl⟩
    | cons first rest =>
      obtain ⟨target, selected⟩ := selectReady_exists closed coverage (by simp)
      have membership := (selectReady_sound selected).1
      have remainingFuel : ((first :: rest).erase target).length ≤ fuel := by
        rw [List.length_erase_of_mem membership]
        simp only [List.length_cons] at enoughFuel ⊢
        omega
      obtain ⟨remaining, recursive⟩ := inductionHypothesis
        (insert target environment) ((first :: rest).erase target)
        (distinct.erase target) (erase_covers_remaining distinct coverage target) remainingFuel
      exact ⟨target :: remaining, by simp [compileWithFuel, selected, recursive]⟩

theorem compile_complete (environment targetSet : Finset Node) (pending : List Node)
    (closed : IsLowerSet (targetSet : Set Node)) (distinct : pending.Nodup)
    (coverage : pending.toFinset = targetSet \ environment) :
    ∃ schedule, compile environment pending = some schedule ∧
      ValidSchedule environment schedule ∧ schedule.Perm pending := by
  obtain ⟨schedule, compiled⟩ := compileWithFuel_complete pending.length environment targetSet
    pending closed distinct coverage le_rfl
  exact ⟨schedule, compiled, compile_sound compiled⟩

theorem compile_full (pending : List Node) (distinct : pending.Nodup)
    (coverage : pending.toFinset = Finset.univ) :
    ∃ schedule, compile ∅ pending = some schedule ∧
      ValidSchedule ∅ schedule ∧ schedule.Nodup ∧
      schedule.toFinset = Finset.univ ∧ schedule.length = Fintype.card Node := by
  obtain ⟨schedule, compiled, valid, permutation⟩ :=
    compile_complete ∅ Finset.univ pending (by
      intro later earlier precedes membership
      exact Finset.mem_univ earlier) distinct (by simpa using coverage)
  have complete : schedule.toFinset = Finset.univ := by
    rw [← coverage]
    ext node
    simpa using permutation.mem_iff (a := node)
  refine ⟨schedule, compiled, valid, validSchedule_nodup valid, complete, ?_⟩
  simpa [complete] using (validSchedule_card valid).symm

theorem compileWithFuel_of_valid (fuel : Nat) {environment : Finset Node}
    {schedule : List Node} (valid : ValidSchedule environment schedule)
    (enoughFuel : schedule.length ≤ fuel) :
    compileWithFuel fuel environment schedule = some schedule := by
  induction fuel generalizing environment schedule with
  | zero =>
    have empty : schedule = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enoughFuel)
    subst schedule
    rfl
  | succ fuel inductionHypothesis =>
    cases schedule with
    | nil => rfl
    | cons first remaining =>
      have selected : selectReady environment (first :: remaining) = some first := by
        simp [selectReady, valid.1]
      have recursive := inductionHypothesis valid.2
        (Nat.le_of_succ_le_succ enoughFuel)
      simp [compileWithFuel, selected, recursive]

theorem compile_of_valid {environment : Finset Node} {schedule : List Node}
    (valid : ValidSchedule environment schedule) :
    compile environment schedule = some schedule :=
  compileWithFuel_of_valid schedule.length valid le_rfl

theorem compile_output_fixed {environment : Finset Node} {pending schedule : List Node}
    (computed : compile environment pending = some schedule) :
    compile environment schedule = some schedule :=
  compile_of_valid (compile_sound computed).1

theorem compile_succeeds_iff (environment : Finset Node) (pending : List Node)
    (initialClosed : IsLowerSet (environment : Set Node)) :
    (∃ schedule, compile environment pending = some schedule) ↔
      pending.Nodup ∧ (∀ target ∈ pending, target ∉ environment) ∧
      IsLowerSet (↑(environment ∪ pending.toFinset) : Set Node) := by
  constructor
  · rintro ⟨schedule, computed⟩
    obtain ⟨valid, permutation⟩ := compile_sound computed
    refine ⟨permutation.nodup_iff.mp (validSchedule_nodup valid), ?_, ?_⟩
    · intro target membership
      exact validSchedule_fresh valid target (permutation.mem_iff.mpr membership)
    · have closed := validSchedule_isLowerSet initialClosed valid
      rwa [List.toFinset_eq_of_perm _ _ permutation] at closed
  · rintro ⟨distinct, fresh, closed⟩
    have coverage : pending.toFinset = (environment ∪ pending.toFinset) \ environment := by
      ext target
      simp only [List.mem_toFinset, Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro membership
        exact ⟨Or.inr membership, fresh target membership⟩
      · rintro ⟨previous | membership, absent⟩
        · exact False.elim (absent previous)
        · exact membership
    obtain ⟨schedule, computed, _⟩ :=
      compile_complete environment (environment ∪ pending.toFinset) pending closed distinct coverage
    exact ⟨schedule, computed⟩

theorem compile_eq_none_iff (environment : Finset Node) (pending : List Node)
    (initialClosed : IsLowerSet (environment : Set Node)) :
    compile environment pending = none ↔
      ¬ (pending.Nodup ∧ (∀ target ∈ pending, target ∉ environment) ∧
        IsLowerSet (↑(environment ∪ pending.toFinset) : Set Node)) := by
  rw [← compile_succeeds_iff environment pending initialClosed]
  cases compile environment pending <;> simp

end InfoGeometry.Causal.FiniteDependencyCompiler
