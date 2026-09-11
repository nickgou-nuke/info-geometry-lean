import InfoGeometry.Causal.ProofDAGRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LogosPartiturePoset

namespace InfoGeometry.Canonical

open InfoGeometry.Causal.ProofDAGRepresentation
open InfoGeometry.Canonical.LogosPartiturePoset

/-!
# Typed context logos streams

Physical language such as a stream of associations or consciousness is
translated here into a finite typed dependency stream.  The carrier is a
list of declarations, and every adjacent transition is justified by the
existing `ProofDAG.le` relation.  No semantic oracle or physical claim is
introduced by this definition.
-/

variable {α : Type*}

/-- Right-associated product of a finite operator word. -/
def operatorWordProduct {R : Type*} [Monoid R] : List R → R
  | [] => 1
  | x :: xs => x * operatorWordProduct xs

@[simp] theorem operatorWordProduct_nil {R : Type*} [Monoid R] :
    operatorWordProduct ([] : List R) = 1 := rfl

@[simp] theorem operatorWordProduct_cons {R : Type*} [Monoid R] (x : R)
    (xs : List R) : operatorWordProduct (x :: xs) =
      x * operatorWordProduct xs := rfl

theorem operatorWordProduct_append {R : Type*} [Monoid R]
    (xs ys : List R) :
    operatorWordProduct (xs ++ ys) =
      operatorWordProduct xs * operatorWordProduct ys := by
  induction xs with
  | nil => simp [operatorWordProduct]
  | cons x xs ih =>
      simp only [List.cons_append, operatorWordProduct_cons, ih, mul_assoc]

theorem operatorWordProduct_map {R S : Type*} [Monoid R] [Monoid S]
    (f : R →* S) (xs : List R) :
    f (operatorWordProduct xs) =
      operatorWordProduct (xs.map f) := by
  induction xs with
  | nil => simp [operatorWordProduct]
  | cons x xs ih =>
      simp only [operatorWordProduct_cons, map_mul, List.map_cons, ih]

theorem operatorWordProduct_eq_zero_of_mem_zero {R : Type*} [MonoidWithZero R]
    {xs : List R} (hzero : 0 ∈ xs) : operatorWordProduct xs = 0 := by
  induction xs with
  | nil => simp at hzero
  | cons x xs ih =>
      simp only [List.mem_cons] at hzero
      rcases hzero with rfl | hzero
      · simp [operatorWordProduct]
      · rw [operatorWordProduct_cons, ih hzero, mul_zero]

theorem operatorWordProduct_replicate_d {n : ℕ} (hn : 0 < n) :
    operatorWordProduct (List.replicate n d) = d := by
  induction n with
  | zero => cases hn
  | succ n ih =>
      rw [List.replicate_succ, operatorWordProduct_cons]
      cases n with
      | zero => simp
      | succ n =>
          rw [ih (Nat.zero_lt_succ n), d_idempotent]

theorem operatorWordProduct_replicate_delta {n : ℕ} (hn : 0 < n) :
    operatorWordProduct (List.replicate n δ) = δ := by
  induction n with
  | zero => cases hn
  | succ n ih =>
      rw [List.replicate_succ, operatorWordProduct_cons]
      cases n with
      | zero => simp
      | succ n =>
          rw [ih (Nat.zero_lt_succ n), δ_idempotent]

/-- Consecutive edge operators selected from a finite node word. -/
def edgeOperatorWord {G : ProofDAG α} (R : CausalRepresentation G) :
    List α → List (Matrix (Fin 2) (Fin 2) ℂ)
  | a :: b :: xs => R.edgeOp a b :: edgeOperatorWord R (b :: xs)
  | _ => []

@[simp] theorem edgeOperatorWord_two {G : ProofDAG α} (R : CausalRepresentation G)
    (a b : α) : edgeOperatorWord R [a, b] = [R.edgeOp a b] := rfl

/-- A finite forward context stream in a proof DAG. -/
inductive IsForwardLogosStream (G : ProofDAG α) : List α → Prop
  | nil : IsForwardLogosStream G []
  | singleton (a : α) : IsForwardLogosStream G [a]
  | cons {a b : α} {tail : List α} :
      G.le a b → IsForwardLogosStream G (b :: tail) →
      IsForwardLogosStream G (a :: b :: tail)

/-- A finite backward context stream, with transitions read in reverse
    dependency orientation. -/
inductive IsBackwardLogosStream (G : ProofDAG α) : List α → Prop
  | nil : IsBackwardLogosStream G []
  | singleton (a : α) : IsBackwardLogosStream G [a]
  | cons {a b : α} {tail : List α} :
      G.le b a → IsBackwardLogosStream G (b :: tail) →
      IsBackwardLogosStream G (a :: b :: tail)

/-- A non-repeating forward path: the explicit carrier for a longer causal
    logos stream whose consecutive operator edges are nontrivial. -/
structure ForwardLogosPath (G : ProofDAG α) where
  nodes : List α
  causal : IsForwardLogosStream G nodes
  nodup : nodes.Nodup

structure BackwardLogosPath (G : ProofDAG α) where
  nodes : List α
  causal : IsBackwardLogosStream G nodes
  nodup : nodes.Nodup

/-! The finite partiture is read as a proof DAG using the native order on
    `Fin 12`, not as a string-labelled semantic interpretation. -/
def partitureProofDAG : ProofDAG ArchetypalNode where
  le := (· ≤ ·)
  refl := fun _ => le_rfl
  trans := fun h₁ h₂ => le_trans h₁ h₂
  antisymm := fun h₁ h₂ => le_antisymm h₁ h₂

theorem partiture_is_forward_logos_stream :
    IsForwardLogosStream partitureProofDAG partiture := by
  change IsForwardLogosStream partitureProofDAG
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  apply IsForwardLogosStream.cons
  · change (0 : ℕ) ≤ 1
    omega
  apply IsForwardLogosStream.cons
  · change (1 : ℕ) ≤ 2
    omega
  apply IsForwardLogosStream.cons
  · change (2 : ℕ) ≤ 3
    omega
  apply IsForwardLogosStream.cons
  · change (3 : ℕ) ≤ 4
    omega
  apply IsForwardLogosStream.cons
  · change (4 : ℕ) ≤ 5
    omega
  apply IsForwardLogosStream.cons
  · change (5 : ℕ) ≤ 6
    omega
  apply IsForwardLogosStream.cons
  · change (6 : ℕ) ≤ 7
    omega
  apply IsForwardLogosStream.cons
  · change (7 : ℕ) ≤ 8
    omega
  apply IsForwardLogosStream.cons
  · change (8 : ℕ) ≤ 9
    omega
  apply IsForwardLogosStream.cons
  · change (9 : ℕ) ≤ 10
    omega
  apply IsForwardLogosStream.cons
  · change (10 : ℕ) ≤ 11
    omega
  exact IsForwardLogosStream.singleton _

def partitureLogosPath : ForwardLogosPath partitureProofDAG :=
  { nodes := partiture
    causal := partiture_is_forward_logos_stream
    nodup := partiture_nodup }

theorem BackwardLogosPath.adjacent_ne {G : ProofDAG α}
    (p : BackwardLogosPath G) {a b : α} {tail : List α}
    (h : p.nodes = a :: b :: tail) : a ≠ b := by
  have hn : (a :: b :: tail).Nodup := h ▸ p.nodup
  have hnot : a ∉ b :: tail := (List.nodup_cons.mp hn).1
  intro hab
  exact hnot (by simp [hab])

def BackwardLogosPath.edgeWord {G : ProofDAG α} (R : CausalRepresentation G)
    (p : BackwardLogosPath G) : List (Matrix (Fin 2) (Fin 2) ℂ) :=
  edgeOperatorWord R p.nodes

theorem BackwardLogosPath.edgeWord_length {G : ProofDAG α}
    (R : CausalRepresentation G) (p : BackwardLogosPath G) :
    (p.edgeWord R).length = p.nodes.length - 1 := by
  have aux : ∀ xs : List α,
      (edgeOperatorWord R xs).length = xs.length - 1 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih =>
        cases rest with
        | nil => rfl
        | cons b tail =>
            simp only [edgeOperatorWord, List.length_cons,
              Nat.add_sub_cancel]
            simpa using ih
  exact aux p.nodes

theorem ForwardLogosPath.adjacent_ne {G : ProofDAG α}
    (p : ForwardLogosPath G) {a b : α} {tail : List α}
    (h : p.nodes = a :: b :: tail) : a ≠ b := by
  have hn : (a :: b :: tail).Nodup := h ▸ p.nodup
  have hnot : a ∉ b :: tail := (List.nodup_cons.mp hn).1
  intro hab
  exact hnot (by simp [hab])

def ForwardLogosPath.edgeWord {G : ProofDAG α} (R : CausalRepresentation G)
    (p : ForwardLogosPath G) : List (Matrix (Fin 2) (Fin 2) ℂ) :=
  edgeOperatorWord R p.nodes

theorem ForwardLogosPath.edgeWord_length {G : ProofDAG α}
    (R : CausalRepresentation G) (p : ForwardLogosPath G) :
    (p.edgeWord R).length = p.nodes.length - 1 := by
  have aux : ∀ xs : List α,
      (edgeOperatorWord R xs).length = xs.length - 1 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih =>
        cases rest with
        | nil => rfl
        | cons b tail =>
            simp only [edgeOperatorWord, List.length_cons,
              Nat.add_sub_cancel]
            simpa using congrArg Nat.succ ih
  exact aux p.nodes

theorem edgeOperatorWord_eq_replicate_d_of_forward
    {G : ProofDAG α} (R : CausalRepresentation G) {xs : List α}
    (h : IsForwardLogosStream G xs) (hn : xs.Nodup) :
    edgeOperatorWord R xs = List.replicate (xs.length - 1) d := by
  induction h with
  | nil => simp [edgeOperatorWord]
  | singleton a => simp [edgeOperatorWord]
  | @cons a b tail hab hs ih =>
      have hnodup : (b :: tail).Nodup := (List.nodup_cons.mp hn).2
      have hnot : a ∉ b :: tail := (List.nodup_cons.mp hn).1
      have hne : a ≠ b := fun hab' => hnot (by simp [hab'])
      simp [edgeOperatorWord, R.edgeOp_forward hab hne, ih hnodup,
        List.replicate_succ]

theorem ForwardLogosPath.edgeWord_product_eq_d
    {G : ProofDAG α} (R : CausalRepresentation G)
    (p : ForwardLogosPath G) (hpositive : 0 < p.nodes.length - 1) :
    operatorWordProduct (p.edgeWord R) = d := by
  unfold ForwardLogosPath.edgeWord
  rw [edgeOperatorWord_eq_replicate_d_of_forward R p.causal p.nodup]
  exact operatorWordProduct_replicate_d hpositive

theorem edgeOperatorWord_eq_replicate_delta_of_backward
    {G : ProofDAG α} (R : CausalRepresentation G) {xs : List α}
    (h : IsBackwardLogosStream G xs) (hn : xs.Nodup) :
    edgeOperatorWord R xs = List.replicate (xs.length - 1) δ := by
  induction h with
  | nil => simp [edgeOperatorWord]
  | singleton a => simp [edgeOperatorWord]
  | @cons a b tail hba hs ih =>
      have hnodup : (b :: tail).Nodup := (List.nodup_cons.mp hn).2
      have hnot : a ∉ b :: tail := (List.nodup_cons.mp hn).1
      have hne : a ≠ b := fun hab' => hnot (by simp [hab'])
      simp [edgeOperatorWord, R.edgeOp_backward hba hne,
        ih hnodup, List.replicate_succ]

theorem BackwardLogosPath.edgeWord_product_eq_delta
    {G : ProofDAG α} (R : CausalRepresentation G)
    (p : BackwardLogosPath G) (hpositive : 0 < p.nodes.length - 1) :
    operatorWordProduct (p.edgeWord R) = δ := by
  unfold BackwardLogosPath.edgeWord
  rw [edgeOperatorWord_eq_replicate_delta_of_backward R p.causal p.nodup]
  exact operatorWordProduct_replicate_delta hpositive

theorem forwardLogosStream_tail {G : ProofDAG α} {a : α} {xs : List α}
    (h : IsForwardLogosStream G (a :: xs)) :
    xs = [] ∨ ∃ b ys, xs = b :: ys ∧ G.le a b ∧
      IsForwardLogosStream G (b :: ys) := by
  cases h with
  | singleton a => exact Or.inl rfl
  | cons hab hs => exact Or.inr ⟨_, _, rfl, hab, hs⟩

theorem forwardLogosStream_step {G : ProofDAG α} {a b : α} {tail : List α}
    (h : IsForwardLogosStream G (a :: b :: tail)) : G.le a b := by
  cases h with
  | cons hab _ => exact hab

theorem edgeOperatorWord_three_forward
    {G : ProofDAG α} (R : CausalRepresentation G) {a b c : α}
    (h : IsForwardLogosStream G [a, b, c])
    (hab : a ≠ b) (hbc : b ≠ c) :
    edgeOperatorWord R [a, b, c] = [d, d] := by
  have hab' : G.le a b := forwardLogosStream_step h
  have hbc' : G.le b c := by
    cases h with
    | cons _ hs => exact forwardLogosStream_step hs
  simp [edgeOperatorWord, R.edgeOp_forward hab' hab,
    R.edgeOp_forward hbc' hbc]

theorem forwardLogosStream_three_operator_product
    {G : ProofDAG α} (R : CausalRepresentation G) {a b c : α}
    (h : IsForwardLogosStream G [a, b, c])
    (hab : a ≠ b) (hbc : b ≠ c) :
    operatorWordProduct (edgeOperatorWord R [a, b, c]) = d := by
  rw [edgeOperatorWord_three_forward R h hab hbc]
  simp [operatorWordProduct, d_idempotent]

theorem edgeOperatorWord_three_backward
    {G : ProofDAG α} (R : CausalRepresentation G) {a b c : α}
    (h : IsBackwardLogosStream G [a, b, c])
    (hab : a ≠ b) (hbc : b ≠ c) :
    edgeOperatorWord R [a, b, c] = [δ, δ] := by
  have hba : G.le b a := by
    cases h with
    | cons hba _ => exact hba
  have hcb : G.le c b := by
    cases h with
    | cons _ hs =>
        cases hs with
        | cons hcb _ => exact hcb
  simp [edgeOperatorWord, R.edgeOp_backward hba hab,
    R.edgeOp_backward hcb hbc]

theorem backwardLogosStream_three_operator_product
    {G : ProofDAG α} (R : CausalRepresentation G) {a b c : α}
    (h : IsBackwardLogosStream G [a, b, c])
    (hab : a ≠ b) (hbc : b ≠ c) :
    operatorWordProduct (edgeOperatorWord R [a, b, c]) = δ := by
  rw [edgeOperatorWord_three_backward R h hab hbc]
  simp [operatorWordProduct, δ_idempotent]

theorem backwardLogosStream_step {G : ProofDAG α} {a b : α} {tail : List α}
    (h : IsBackwardLogosStream G (a :: b :: tail)) : G.le b a := by
  cases h with
  | cons hba _ => exact hba

theorem backwardLogosStream_append_singleton {G : ProofDAG α} {a b : α}
    (hba : G.le b a) : IsBackwardLogosStream G [a, b] := by
  exact .cons hba (.singleton b)

theorem forwardLogosStream_reverse_two_to_backward
    {G : ProofDAG α} {a b : α}
    (h : IsForwardLogosStream G [a, b]) :
    IsBackwardLogosStream G [b, a] := by
  exact .cons (forwardLogosStream_step h) (.singleton a)

theorem backwardLogosStream_no_nontrivial_forward_return
    {G : ProofDAG α} {a b : α}
    (h : IsBackwardLogosStream G [a, b]) (hne : a ≠ b) :
    ¬ G.le a b := by
  intro hab
  exact hne (G.antisymm hab (backwardLogosStream_step h))

theorem backwardLogosStream_map
    {β : Type*} {G : ProofDAG α} {H : ProofDAG β}
    (f : α → β) (hf : ∀ {a b : α}, G.le a b → H.le (f a) (f b))
    {xs : List α}
    (h : IsBackwardLogosStream G xs) :
    IsBackwardLogosStream H (xs.map f) := by
  induction h with
  | nil => exact .nil
  | singleton a => simpa using IsBackwardLogosStream.singleton (G := H) (f a)
  | @cons a b tail hba hs ih =>
      simpa using IsBackwardLogosStream.cons (hf hba) ih

theorem backwardLogosStream_map_comp
    {β γ : Type*} {G : ProofDAG α} {H : ProofDAG β} {K : ProofDAG γ}
    (f : α → β) (hf : ∀ {a b : α}, G.le a b → H.le (f a) (f b))
    (g : β → γ) (hg : ∀ {a b : β}, H.le a b → K.le (g a) (g b))
    {xs : List α} (h : IsBackwardLogosStream G xs) :
    IsBackwardLogosStream K ((xs.map f).map g) := by
  exact backwardLogosStream_map g hg (backwardLogosStream_map f hf h)

theorem backwardLogosStream_head_member_backwardCone
    {G : ProofDAG α} {a : α} {xs : List α}
    (h : IsBackwardLogosStream G (a :: xs)) {b : α} (hb : b ∈ xs) :
    b ∈ backwardCone G a := by
  cases xs with
  | nil => simp at hb
  | cons b tail =>
      cases h with
      | cons hba hs =>
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact hba
          · exact G.trans (backwardLogosStream_head_member_backwardCone hs hb) hba

theorem forwardLogosStream_head_le_member {G : ProofDAG α} {a : α} {xs : List α}
    (h : IsForwardLogosStream G (a :: xs)) {b : α} (hb : b ∈ xs) :
    G.le a b := by
  cases xs with
  | nil => simp at hb
  | cons c tail =>
      cases h with
      | cons hac hs =>
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact hac
          · exact G.trans hac (forwardLogosStream_head_le_member hs hb)

theorem forwardLogosStream_tail_subset_forwardCone
    {G : ProofDAG α} {a : α} {xs : List α}
    (h : IsForwardLogosStream G (a :: xs)) :
    ∀ b ∈ xs, b ∈ forwardCone G a := by
  intro b hb
  exact forwardLogosStream_head_le_member h hb

theorem forwardLogosStream_transitive_readout {G : ProofDAG α} {a b c : α}
    (h : IsForwardLogosStream G [a, b, c]) : G.le a c := by
  exact forwardLogosStream_head_le_member h (by simp)

theorem forwardLogosStream_append_singleton {G : ProofDAG α} {a b : α}
    (hab : G.le a b) : IsForwardLogosStream G [a, b] := by
  exact .cons hab (.singleton b)

/-- The first transition is exactly a membership statement in the existing
    forward cone, so the stream has a canonical graph-theoretic readout. -/
theorem forwardLogosStream_step_mem_forwardCone
    {G : ProofDAG α} {a b : α} {tail : List α}
    (h : IsForwardLogosStream G (a :: b :: tail)) :
    b ∈ forwardCone G a :=
  forwardLogosStream_step h

theorem forwardLogosStream_no_nontrivial_return
    {G : ProofDAG α} {a b : α} (hab : G.le a b) (hba : G.le b a)
    (hne : a ≠ b) : False := by
  exact hne (G.antisymm hab hba)

/-! The operator readout is available exactly when an explicit causal
representation is supplied.  This keeps the graph stream and its matrix
realisation distinct, while transporting the existing orthogonality theorem.
-/
theorem forwardLogosStream_operator_readout
    {G : ProofDAG α} (R : CausalRepresentation G)
    {a b : α} (h : IsForwardLogosStream G [a, b]) (hne : a ≠ b) :
    R.edgeOp a b * R.edgeOp b a = 0 := by
  exact represented_edge_orthogonality G R (forwardLogosStream_step h) hne

theorem forwardLogosStream_operator_readout_rev
    {G : ProofDAG α} (R : CausalRepresentation G)
    {a b : α} (h : IsForwardLogosStream G [a, b]) (hne : a ≠ b) :
    R.edgeOp b a * R.edgeOp a b = 0 := by
  exact represented_edge_orthogonality_rev G R (forwardLogosStream_step h) hne

theorem backwardLogosStream_operator_readout
    {G : ProofDAG α} (R : CausalRepresentation G)
    {a b : α} (h : IsBackwardLogosStream G [a, b]) (hne : a ≠ b) :
    R.edgeOp a b * R.edgeOp b a = 0 := by
  exact represented_edge_orthogonality_rev G R (backwardLogosStream_step h) hne.symm

theorem backwardLogosStream_operator_readout_rev
    {G : ProofDAG α} (R : CausalRepresentation G)
    {a b : α} (h : IsBackwardLogosStream G [a, b]) (hne : a ≠ b) :
    R.edgeOp b a * R.edgeOp a b = 0 := by
  exact represented_edge_orthogonality G R (backwardLogosStream_step h) hne.symm

theorem forwardLogosStream_backtrack_word
    {G : ProofDAG α} (R : CausalRepresentation G)
    {a b : α} (h : IsForwardLogosStream G [a, b]) (hne : a ≠ b) :
    operatorWordProduct [R.edgeOp a b, R.edgeOp b a] = 0 := by
  simp [operatorWordProduct,
    forwardLogosStream_operator_readout R h hne]

/-! A genuine projection theorem: structure-preserving maps transport the
    whole typed stream, not merely an isolated edge. -/
theorem forwardLogosStream_map
    {β : Type*} {G : ProofDAG α} {H : ProofDAG β}
    (f : α → β) (hf : ∀ {a b : α}, G.le a b → H.le (f a) (f b))
    {xs : List α}
    (h : IsForwardLogosStream G xs) :
    IsForwardLogosStream H (xs.map f) := by
  induction h with
  | nil => exact .nil
  | singleton a => simpa using IsForwardLogosStream.singleton (G := H) (f a)
  | @cons a b tail hab hs ih =>
      simpa using IsForwardLogosStream.cons (hf hab) ih

theorem forwardLogosStream_map_step
    {β : Type*} {G : ProofDAG α} {H : ProofDAG β}
    (f : α → β) (hf : ∀ {a b : α}, G.le a b → H.le (f a) (f b))
    {a b : α} (hab : G.le a b) :
    H.le (f a) (f b) :=
  hf hab

theorem forwardLogosStream_map_id
    {G : ProofDAG α} {xs : List α}
    (h : IsForwardLogosStream G xs) :
    IsForwardLogosStream G (xs.map id) := by
  simpa using h

theorem forwardLogosStream_map_comp
    {β γ : Type*} {G : ProofDAG α} {H : ProofDAG β} {K : ProofDAG γ}
    (g : β → γ) (hg : ∀ {a b : β}, H.le a b → K.le (g a) (g b))
    (f : α → β) (hf : ∀ {a b : α}, G.le a b → H.le (f a) (f b))
    {xs : List α}
    (h : IsForwardLogosStream G xs) :
    IsForwardLogosStream K
      ((xs.map f).map g) := by
  exact forwardLogosStream_map g hg (forwardLogosStream_map f hf h)

/-! A structure-preserving projection of a non-repeating stream.  Injectivity is
    explicit because a map preserving only edges can otherwise collapse the
    path and destroy the non-repetition invariant. -/
def ForwardLogosPath.map
    {β : Type*} {G : ProofDAG α} {H : ProofDAG β}
    (p : ForwardLogosPath G) (f : α → β)
    (hf : ∀ {a b : α}, G.le a b → H.le (f a) (f b))
    (hinj : Function.Injective f) : ForwardLogosPath H :=
  { nodes := p.nodes.map f
    causal := forwardLogosStream_map f hf p.causal
    nodup := p.nodup.map hinj }

theorem ForwardLogosPath.map_edgeWord_length
    {β : Type*} {G : ProofDAG α} {H : ProofDAG β}
    (R : CausalRepresentation H) (p : ForwardLogosPath G) (f : α → β)
    (hf : ∀ {a b : α}, G.le a b → H.le (f a) (f b))
    (hinj : Function.Injective f) :
    ((p.map f hf hinj).edgeWord R).length = p.nodes.length - 1 := by
  calc
    ((p.map f hf hinj).edgeWord R).length = (p.nodes.map f).length - 1 :=
      (p.map f hf hinj).edgeWord_length R
    _ = p.nodes.length - 1 := by simp

/-! The same canonical projection for the reverse-oriented stream. -/
def BackwardLogosPath.map
    {β : Type*} {G : ProofDAG α} {H : ProofDAG β}
    (p : BackwardLogosPath G) (f : α → β)
    (hf : ∀ {a b : α}, G.le b a → H.le (f b) (f a))
    (hinj : Function.Injective f) : BackwardLogosPath H :=
  { nodes := p.nodes.map f
    causal := backwardLogosStream_map f hf p.causal
    nodup := p.nodup.map hinj }

theorem BackwardLogosPath.map_edgeWord_length
    {β : Type*} {G : ProofDAG α} {H : ProofDAG β}
    (R : CausalRepresentation H) (p : BackwardLogosPath G) (f : α → β)
    (hf : ∀ {a b : α}, G.le b a → H.le (f b) (f a))
    (hinj : Function.Injective f) :
    ((p.map f hf hinj).edgeWord R).length = p.nodes.length - 1 := by
  rw [(p.map f hf hinj).edgeWord_length R]
  change (p.nodes.map f).length - 1 = p.nodes.length - 1
  simp

theorem BackwardLogosPath.map_edgeWord_product_eq_delta
    {β : Type*} {G : ProofDAG α} {H : ProofDAG β}
    (R : CausalRepresentation H) (p : BackwardLogosPath G) (f : α → β)
    (hf : ∀ {a b : α}, G.le b a → H.le (f b) (f a))
    (hinj : Function.Injective f) (hpositive : 0 < p.nodes.length - 1) :
    operatorWordProduct ((p.map f hf hinj).edgeWord R) = δ := by
  exact BackwardLogosPath.edgeWord_product_eq_delta R (p.map f hf hinj) (by
    simpa [BackwardLogosPath.map] using hpositive)

theorem ForwardLogosPath.map_edgeWord_product_eq_d
    {β : Type*} {G : ProofDAG α} {H : ProofDAG β}
    (R : CausalRepresentation H) (p : ForwardLogosPath G) (f : α → β)
    (hf : ∀ {a b : α}, G.le a b → H.le (f a) (f b))
    (hinj : Function.Injective f) (hpositive : 0 < p.nodes.length - 1) :
    operatorWordProduct ((p.map f hf hinj).edgeWord R) = d := by
  exact ForwardLogosPath.edgeWord_product_eq_d R (p.map f hf hinj) (by
    simpa [ForwardLogosPath.map] using hpositive)

end InfoGeometry.Canonical
