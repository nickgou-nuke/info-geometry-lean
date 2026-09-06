import proofs.BraidProject.BraidGroup
import proofs.BraidProject.FreeMonoid_mine

theorem List.map_injective (hf : Function.Injective f) (h : List.map f a = List.map f b) :
    a = b := by
  revert b
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons _ _ => simp at h
  | cons head tail ih =>
    intro b h
    cases b with
    | nil => simp at h
    | cons h_b tail_b =>
        simp only [map_cons, cons.injEq] at h
        rw [ih h.2, hf h.1]

theorem foldl_one : ∀ (L : List (FreeMonoid (α × Bool)))
    (a : FreeMonoid (α × Bool)), List.foldl (fun a b => a * b) a L = a * List.foldl (fun a b => a * b) 1 L := by
  intro L
  induction L with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, FreeMonoid'.length_one, FreeMonoid'.eq_one_of_length_eq_zero]
    intro a
    specialize ih (a * head)
    exact List.foldl_assoc

private theorem list_singleton_flatten {α : Type*} (z : Bool) (l : List α) :
    (List.map (fun x : α => [(x, z)]) l).flatten = List.map (fun x => (x, z)) l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem lift_to_pair_map {a b : FreeMonoid α} {z : Bool}
    (h1 : FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) a =
    FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) b) :
    List.map (fun x ↦ (x, z)) a = List.map (fun x ↦ (x, z)) b := by
  have h := congrArg FreeMonoid.toList h1
  simp [FreeMonoid.lift_apply] at h
  change (List.map (fun x : α => [(x, z)]) (FreeMonoid.toList a)).flatten =
    (List.map (fun x : α => [(x, z)]) (FreeMonoid.toList b)).flatten at h
  rw [list_singleton_flatten z (FreeMonoid.toList a),
    list_singleton_flatten z (FreeMonoid.toList b)] at h
  exact h

theorem lift_to_map_inj' {a b : FreeMonoid α} {z : Bool} (h1 : FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) a =
    FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) b) :
    List.map (fun x ↦ FreeMonoid.of (x, z)) a = List.map (fun x ↦ FreeMonoid.of (x, z)) b := by
  have hp := lift_to_pair_map h1
  simpa [List.map_map] using congrArg (List.map (fun p : α × Bool => FreeMonoid.of p)) hp

theorem lift_to_map_inj {a b : FreeMonoid α} {z : Bool} (h1 : FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) a =
    FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) b) :
    List.map (fun x ↦ FreeMonoid.of (x, z)) a = List.map (fun x ↦ FreeMonoid.of (x, z)) b := by
  exact lift_to_map_inj' h1

theorem FreeMonoid.lift_bool {a b : FreeMonoid α} {z : Bool}
    (h1 : FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) a =
    FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) b) : a = b := by
  apply List.map_injective _ (lift_to_map_inj h1)
  intro x x1 h_x
  apply FreeMonoid.of_injective at h_x
  rw [Prod.mk.injEq] at h_x
  exact h_x.1

theorem FreeMonoid.lift_bool_one {a : FreeMonoid α} {b : Bool}
    (h1 : FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, b)) a = 1) :
    a = 1 := by
  have H1 : (FreeMonoid.lift fun x ↦ FreeMonoid.of (x, b)) ([] : List α) = 1 := rfl
  rw [← H1] at h1
  exact FreeMonoid.lift_bool h1

private def tagFalse (xs : List ℕ) : List (ℕ × Bool) :=
  xs.map fun x => (x, false)

private def tagTrue (xs : List ℕ) : List (ℕ × Bool) :=
  xs.map fun x => (x, true)

private theorem tagFalse_injective : Function.Injective tagFalse := by
  intro xs ys h
  exact List.map_injective (fun _ _ hxy => Prod.mk.inj hxy |>.1) h

private theorem tagTrue_injective : Function.Injective tagTrue := by
  intro xs ys h
  exact List.map_injective (fun _ _ hxy => Prod.mk.inj hxy |>.1) h

private theorem tagTrue_eq_tagFalse {b c : List ℕ}
    (h : tagTrue b = tagFalse c) : b = [] ∧ c = [] := by
  cases b with
  | nil =>
      constructor
      · rfl
      · cases c with
        | nil => rfl
        | cons _ _ => simp [tagTrue, tagFalse] at h
  | cons hb tb =>
      cases c with
      | nil => simp [tagTrue, tagFalse] at h
      | cons hc tc =>
          simp [tagTrue, tagFalse] at h

private theorem tagTrue_eq_tagTrue_append_tagFalse {b d c : List ℕ}
    (h : tagTrue b = tagTrue d ++ tagFalse c) : c = [] ∧ b = d := by
  induction d generalizing b with
  | nil =>
      have hc := tagTrue_eq_tagFalse h
      exact ⟨hc.2, hc.1⟩
  | cons hd td ih =>
      cases b with
      | nil => simp [tagTrue] at h
      | cons hb tb =>
          simp only [tagTrue, tagFalse, List.map_cons, List.cons_append, List.cons.injEq] at h
          have hhead : hb = hd := (Prod.mk.inj h.1).1
          have htail := ih h.2
          exact ⟨htail.1, by rw [hhead, htail.2]⟩

private theorem tagFalse_append_tagTrue_eq_tagFalse {a b c : List ℕ}
    (h : tagFalse a ++ tagTrue b = tagFalse c) : b = [] ∧ a = c := by
  induction a generalizing c with
  | nil =>
      simp only [tagFalse, List.map_nil, List.nil_append] at h
      have hb := tagTrue_eq_tagFalse h
      exact ⟨hb.1, hb.2.symm⟩
  | cons ha ta ih =>
      cases c with
      | nil => simp [tagFalse] at h
      | cons hc tc =>
          simp only [tagFalse, tagTrue, List.map_cons, List.cons_append, List.cons.injEq] at h
          have hhead : ha = hc := (Prod.mk.inj h.1).1
          have htail := ih h.2
          exact ⟨htail.1, by rw [hhead, htail.2]⟩

private theorem false_true_blocks {a b c d : List ℕ}
    (h : tagFalse a ++ tagTrue b = tagTrue d ++ tagFalse c) :
    (a = [] ∧ c = [] ∧ b = d) ∨ (b = [] ∧ d = [] ∧ a = c) := by
  cases a with
  | nil =>
      simp only [tagFalse, List.map_nil, List.nil_append] at h
      have hd := tagTrue_eq_tagTrue_append_tagFalse h
      exact Or.inl ⟨rfl, hd.1, hd.2⟩
  | cons ha ta =>
      cases d with
      | nil =>
          simp only [tagTrue, List.map_nil, List.nil_append] at h
          have hb := tagFalse_append_tagTrue_eq_tagFalse h
          exact Or.inr ⟨hb.1, rfl, hb.2⟩
      | cons hd td =>
          simp only [tagFalse, tagTrue, List.map_cons, List.cons_append, List.cons.injEq] at h
          exact False.elim (Bool.noConfusion (Prod.mk.inj h.1).2)

theorem false_true_true_false {a b c d : FreeMonoid' ℕ}
    (h : (FreeMonoid.lift fun x ↦ FreeMonoid.of (x, false)) a.reverse *
    (FreeMonoid.lift fun x ↦ FreeMonoid.of (x, true)) b =
    (FreeMonoid.lift fun x ↦ FreeMonoid.of (x, true)) d *
    (FreeMonoid.lift fun x ↦ FreeMonoid.of (x, false)) c.reverse) : (a = 1 ∧ c = 1 ∧ b = d) ∨
    (b = 1 ∧ d = 1 ∧ a = c) := by
  have hlist := congrArg FreeMonoid.toList h
  simp [FreeMonoid.lift_apply, list_singleton_flatten, Function.comp_def] at hlist
  change tagFalse a.reverse ++ tagTrue b = tagTrue d ++ tagFalse c.reverse at hlist
  rcases false_true_blocks hlist with ⟨ha, hc, hb⟩ | ⟨hb, hd, hac⟩
  · left
    refine ⟨?_, ?_, hb⟩
    · have hrev := congrArg FreeMonoid'.reverse ha
      simpa using hrev
    · have hrev := congrArg FreeMonoid'.reverse hc
      simpa using hrev
  · right
    refine ⟨hb, hd, ?_⟩
    have hrev := congrArg FreeMonoid'.reverse hac
    simpa using hrev
