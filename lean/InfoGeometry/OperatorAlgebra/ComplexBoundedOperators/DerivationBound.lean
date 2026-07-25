import Mathlib.Tactic

/-!
# InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.DerivationBound

Lean-native port of AFP `Jordan_Normal_Form.Derivation_Bound`.

The AFP theory uses Isabelle relations as sets of pairs and relation powers
`r ^^ n`.  In Lean we expose the same exact-length rewriting notion as an
inductive predicate over binary relations:

* `Steps r n a b`: exactly `n` `r`-steps from `a` to `b`,
* `TransSteps r a b`: at least one `r`-step from `a` to `b`,
* `DerivBound r a n`: there is no derivation from `a` of length `n + 1`.

The main AFP lemmas are then available as direct Lean theorems.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.DerivationBound

/-- Exact-length relation power: `Steps r n a b` means `a` rewrites to `b`
in exactly `n` steps. -/
inductive Steps {α : Type*} (r : α → α → Prop) : Nat → α → α → Prop where
  /-- Zero steps stay at the same element. -/
  | refl (a : α) : Steps r 0 a a
  /-- Append one relation step to an exact-length derivation. -/
  | tail {n : Nat} {a b c : α} : Steps r n a b → r b c → Steps r (n + 1) a c

namespace Steps

variable {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}

/-- One relation step is a one-step derivation. -/
theorem single {a b : α} (h : r a b) : Steps r 1 a b := by
  simpa using Steps.tail (Steps.refl (r := r) a) h

/-- Exact derivations concatenate by adding their lengths. -/
theorem append {m n : Nat} {a b c : α}
    (hab : Steps r m a b) (hbc : Steps r n b c) :
    Steps r (m + n) a c := by
  induction hbc with
  | refl b =>
      simpa using hab
  | tail hbc hstep ih =>
      simpa [Nat.add_assoc] using Steps.tail (ih hab) hstep

/-- Every prefix length of an exact derivation has a corresponding endpoint. -/
theorem prefixOf {m k : Nat} {a b : α}
    (h : Steps r m a b) (hk : k ≤ m) :
    ∃ c, Steps r k a c := by
  induction h generalizing k with
  | refl a =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact ⟨a, Steps.refl (r := r) a⟩
  | @tail n a b c hprev hstep ih =>
      by_cases hkTop : k = n + 1
      · subst hkTop
        exact ⟨_, Steps.tail hprev hstep⟩
      · have hkPrev : k ≤ n := by omega
        exact ih hkPrev

/-- A positive-length derivation in the empty relation is impossible. -/
theorem not_empty_of_pos {α : Type*} {n : Nat} {a b : α}
    (hpos : 0 < n) :
    ¬ Steps (fun _ _ : α => False) n a b := by
  intro h
  induction h with
  | refl a =>
      omega
  | tail _ hstep _ =>
      exact hstep

/--
Map an exact source derivation through a function when each source step maps
to at least one target step.
-/
theorem mapTrans {α β : Type*}
    {r : α → α → Prop} {r' : β → β → Prop}
    {f : α → β} {m : Nat} {a b : α}
    (hsteps : Steps r m a b)
    (step : ∀ ⦃x y : α⦄, r x y → ∃ q, 0 < q ∧ Steps r' q (f x) (f y)) :
    ∃ k, m ≤ k ∧ Steps r' k (f a) (f b) := by
  induction hsteps with
  | refl a =>
      exact ⟨0, le_rfl, Steps.refl (r := r') (f a)⟩
  | tail hprev hxy ih =>
      rcases ih with ⟨k, hmk, hk⟩
      rcases step hxy with ⟨q, hqpos, hq⟩
      exact ⟨k + q, by omega, Steps.append hk hq⟩

end Steps

/-- Positive transitive closure represented by an exact positive number of steps. -/
def TransSteps {α : Type*} (r : α → α → Prop) (a b : α) : Prop :=
  ∃ n, 0 < n ∧ Steps r n a b

/-- A single relation step is a positive transitive derivation. -/
theorem transSteps_single {α : Type*} {r : α → α → Prop} {a b : α}
    (h : r a b) : TransSteps r a b :=
  ⟨1, by omega, Steps.single h⟩

/-- Concatenate two positive transitive derivations. -/
theorem TransSteps.trans {α : Type*} {r : α → α → Prop} {a b c : α}
    (hab : TransSteps r a b) (hbc : TransSteps r b c) :
    TransSteps r a c := by
  rcases hab with ⟨m, hmpos, hab⟩
  rcases hbc with ⟨n, hnpos, hbc⟩
  exact ⟨m + n, by omega, Steps.append hab hbc⟩

/-- AFP `deriv_bound`: no derivation of length `n + 1` starts at `a`. -/
def DerivBound {α : Type*} (r : α → α → Prop) (a : α) (n : Nat) : Prop :=
  ¬ ∃ b, Steps r (n + 1) a b

/-- Introduction rule corresponding to AFP `deriv_boundI`. -/
theorem derivBoundI {α : Type*} {r : α → α → Prop} {a : α} {n : Nat}
    (h : ∀ b m, n < m → Steps r m a b → False) :
    DerivBound r a n := by
  intro hb
  rcases hb with ⟨b, hb⟩
  exact h b (n + 1) (by omega) hb

/-- Elimination rule corresponding to AFP `deriv_boundE`. -/
theorem derivBoundE {P : Prop} {α : Type*} {r : α → α → Prop} {a : α} {n : Nat}
    (hb : DerivBound r a n)
    (h : (∀ b m, n < m → Steps r m a b → False) → P) :
    P := by
  apply h
  intro b m hnm hsteps
  have hle : n + 1 ≤ m := by omega
  rcases Steps.prefixOf hsteps hle with ⟨c, hc⟩
  exact hb ⟨c, hc⟩

/-- Characterization of derivation bounds by absence of every longer derivation. -/
theorem derivBound_iff {α : Type*} {r : α → α → Prop} {a : α} {n : Nat} :
    DerivBound r a n ↔ ∀ b m, n < m → ¬ Steps r m a b := by
  constructor
  · intro hb b m hnm hm
    exact derivBoundE hb (fun h => h b m hnm hm)
  · intro h
    exact derivBoundI (fun b m hnm hm => h b m hnm hm)

@[simp]
theorem derivBound_empty {α : Type*} (a : α) (n : Nat) :
    DerivBound (fun _ _ : α => False) a n := by
  intro hb
  rcases hb with ⟨b, hb⟩
  exact Steps.not_empty_of_pos (a := a) (b := b) (n := n + 1) (by omega) hb

/-- Monotonicity of derivation bounds in the numeric bound. -/
theorem derivBound_mono {α : Type*} {r : α → α → Prop} {a : α} {m n : Nat}
    (hmn : m ≤ n) (hb : DerivBound r a m) :
    DerivBound r a n := by
  rw [derivBound_iff] at hb ⊢
  intro b k hnk hk
  exact hb b k (lt_of_le_of_lt hmn hnk) hk

/--
Image lemma corresponding to AFP `deriv_bound_image`.

Each source step must map to a positive target derivation.  Then a target
derivation bound at `f a` bounds source derivations from `a`.
-/
theorem derivBound_image {α β : Type*}
    {r : α → α → Prop} {r' : β → β → Prop}
    {f : α → β} {a : α} {n : Nat}
    (hb : DerivBound r' (f a) n)
    (step : ∀ ⦃x y : α⦄, r x y → TransSteps r' (f x) (f y)) :
    DerivBound r a n := by
  rw [derivBound_iff] at hb ⊢
  intro b m hnm hsteps
  have image_steps :
      ∃ k, m ≤ k ∧ Steps r' k (f a) (f b) :=
    Steps.mapTrans hsteps (by
      intro x y hxy
      exact step hxy)
  rcases image_steps with ⟨k, hmk, hk⟩
  exact hb (f b) k (lt_of_lt_of_le hnm hmk) hk

/-- Subset/closure lemma corresponding to AFP `deriv_bound_subset`. -/
theorem derivBound_subset {α : Type*}
    {r r' : α → α → Prop} {a : α} {n : Nat}
    (hsubset : ∀ ⦃x y : α⦄, r x y → TransSteps r' x y)
    (hb : DerivBound r' a n) :
    DerivBound r a n :=
  derivBound_image (r := r) (r' := r') (f := id) hb (by
    intro x y hxy
    simpa using hsubset hxy)

/-- Strong normalization on a set, expressed as absence of infinite forward chains. -/
def SNOn {α : Type*} (r : α → α → Prop) (s : Set α) : Prop :=
  ¬ ∃ f : Nat → α, f 0 ∈ s ∧ ∀ i, r (f i) (f (i + 1))

/-- Exact derivation extracted from an infinite chain prefix. -/
theorem steps_of_chain {α : Type*} {r : α → α → Prop}
    (f : Nat → α) (hstep : ∀ i, r (f i) (f (i + 1))) :
    ∀ n, Steps r n (f 0) (f n)
  | 0 => by simpa using Steps.refl (r := r) (f 0)
  | n + 1 => by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Steps.tail (steps_of_chain f hstep n) (hstep n)

/-- AFP `deriv_bound_SN_on`: a finite derivation bound implies strong normalization at `a`. -/
theorem derivBound_SNOn {α : Type*} {r : α → α → Prop} {a : α} {n : Nat}
    (hb : DerivBound r a n) :
    SNOn r {a} := by
  intro hchain
  rcases hchain with ⟨f, hf0, hstep⟩
  have h0 : f 0 = a := by simpa using hf0
  have hsteps : Steps r (n + 1) a (f (n + 1)) := by
    simpa [h0] using steps_of_chain f hstep (n + 1)
  exact hb ⟨f (n + 1), hsteps⟩

/-- Any derivation from a bounded start has length at most the bound. -/
theorem derivBound_steps {α : Type*} {r : α → α → Prop}
    {a b : α} {n m : Nat}
    (hsteps : Steps r n a b)
    (hb : DerivBound r a m) :
    n ≤ m := by
  by_contra hnm
  have hlt : m < n := Nat.lt_of_not_ge hnm
  rw [derivBound_iff] at hb
  exact hb b n hlt hsteps

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.DerivationBound
