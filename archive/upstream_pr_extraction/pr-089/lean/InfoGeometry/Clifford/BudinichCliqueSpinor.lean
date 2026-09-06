import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Budinich clique-spinor formulation: graph Gram kernel

This module formalizes the first constructive graph-theoretic layer of
Marco and Paolo Budinich's spinorial formulation of the maximum clique
problem.

For a simple graph `G`, we define an explicit complex symmetric diagonal-zero
Gram readout:

* diagonal entries are `0`;
* edge entries are `0`;
* non-edge off-diagonal entries are `1`.

Thus clique membership is exactly the condition that all off-diagonal Gram
entries vanish on the chosen vertex set.  This is the kernel-checked
combinatorial bridge that a later Clifford/pure-spinor factorization can use.
-/

namespace InfoGeometry
namespace Clifford
namespace BudinichCliqueSpinor

variable {α : Type*} [DecidableEq α]

/--
Explicit complex Gram readout for the clique problem.

It records the complement adjacency pattern: off-diagonal edges have value
`0`, off-diagonal non-edges have value `1`, and diagonal entries have value
`0`.
-/
def graphCliqueGram (G : SimpleGraph α) [DecidableRel G.Adj] (v w : α) : ℂ :=
  if v = w then 0 else if G.Adj v w then 0 else 1

@[simp] theorem graphCliqueGram_self (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    graphCliqueGram G v v = 0 := by
  simp [graphCliqueGram]

theorem graphCliqueGram_adj_eq_zero
    (G : SimpleGraph α) [DecidableRel G.Adj] {v w : α} (h : G.Adj v w) :
    graphCliqueGram G v w = 0 := by
  simp [graphCliqueGram, h.ne, h]

theorem graphCliqueGram_eq_one_of_not_adj
    (G : SimpleGraph α) [DecidableRel G.Adj] {v w : α}
    (hne : v ≠ w) (hnot : ¬ G.Adj v w) :
    graphCliqueGram G v w = 1 := by
  simp [graphCliqueGram, hne, hnot]

theorem graphCliqueGram_eq_zero_iff
    (G : SimpleGraph α) [DecidableRel G.Adj] {v w : α} (hne : v ≠ w) :
    graphCliqueGram G v w = 0 ↔ G.Adj v w := by
  constructor
  · intro hzero
    by_contra hnot
    have hone : graphCliqueGram G v w = 1 :=
      graphCliqueGram_eq_one_of_not_adj G hne hnot
    rw [hone] at hzero
    norm_num at hzero
  · intro h
    exact graphCliqueGram_adj_eq_zero G h

theorem graphCliqueGram_symm
    (G : SimpleGraph α) [DecidableRel G.Adj] (v w : α) :
    graphCliqueGram G v w = graphCliqueGram G w v := by
  by_cases heq : v = w
  · subst heq
    simp
  · have hneq : w ≠ v := fun h => heq h.symm
    by_cases hadj : G.Adj v w
    · have hwa : G.Adj w v := hadj.symm
      simp [graphCliqueGram, heq, hneq, hadj, hwa]
    · have hnwa : ¬ G.Adj w v := fun hwa => hadj hwa.symm
      simp [graphCliqueGram, heq, hneq, hadj, hnwa]

/-- Clique condition expressed as vanishing of the explicit Gram readout. -/
def IsGramClique (G : SimpleGraph α) [DecidableRel G.Adj] (s : Set α) : Prop :=
  ∀ v ∈ s, ∀ w ∈ s, v ≠ w → graphCliqueGram G v w = 0

theorem isClique_iff_isGramClique
    (G : SimpleGraph α) [DecidableRel G.Adj] (s : Set α) :
    G.IsClique s ↔ IsGramClique G s := by
  constructor
  · intro hclique v hv w hw hne
    exact graphCliqueGram_adj_eq_zero G (hclique hv hw hne)
  · intro hgram v hv w hw hne
    exact (graphCliqueGram_eq_zero_iff G hne).1 (hgram v hv w hw hne)

/-- Finite-set version of the Gram clique condition. -/
def IsFinsetGramClique (G : SimpleGraph α) [DecidableRel G.Adj] (s : Finset α) : Prop :=
  ∀ v ∈ s, ∀ w ∈ s, v ≠ w → graphCliqueGram G v w = 0

theorem isFinsetGramClique_iff_isGramClique
    (G : SimpleGraph α) [DecidableRel G.Adj] (s : Finset α) :
    IsFinsetGramClique G s ↔ IsGramClique G (s : Set α) := by
  rfl

theorem isClique_finset_iff_isFinsetGramClique
    (G : SimpleGraph α) [DecidableRel G.Adj] (s : Finset α) :
    G.IsClique (s : Set α) ↔ IsFinsetGramClique G s := by
  exact isClique_iff_isGramClique G (s : Set α)

/-- A cardinal `k` is realized by a maximum clique. -/
def IsMaximumCliqueCard (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ s : Finset α,
    s.card = k
      ∧ G.IsClique (s : Set α)
      ∧ ∀ t : Finset α, G.IsClique (t : Set α) → t.card ≤ k

/-- A cardinal `k` is realized by a maximum Gram clique. -/
def IsMaximumGramCliqueCard (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ s : Finset α,
    s.card = k
      ∧ IsFinsetGramClique G s
      ∧ ∀ t : Finset α, IsFinsetGramClique G t → t.card ≤ k

theorem maximumCliqueCard_iff_maximumGramCliqueCard
    (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) :
    IsMaximumCliqueCard G k ↔ IsMaximumGramCliqueCard G k := by
  constructor
  · rintro ⟨s, hcard, hclique, hmax⟩
    refine ⟨s, hcard, (isClique_finset_iff_isFinsetGramClique G s).1 hclique, ?_⟩
    intro t ht
    exact hmax t ((isClique_finset_iff_isFinsetGramClique G t).2 ht)
  · rintro ⟨s, hcard, hgram, hmax⟩
    refine ⟨s, hcard, (isClique_finset_iff_isFinsetGramClique G s).2 hgram, ?_⟩
    intro t ht
    exact hmax t ((isClique_finset_iff_isFinsetGramClique G t).1 ht)

/-! ## Maximal cliques reconstruct the graph -/

/-- A set is a maximal clique when it is clique and cannot be enlarged as a clique. -/
def IsMaximalCliqueSet (G : SimpleGraph α) (s : Set α) : Prop :=
  Maximal G.IsClique s

/-- Two vertices are recovered from the maximal-clique family when some maximal clique contains both. -/
def RecoveredByMaximalCliques (G : SimpleGraph α) (v w : α) : Prop :=
  ∃ s : Set α, IsMaximalCliqueSet G s ∧ v ∈ s ∧ w ∈ s ∧ v ≠ w

omit [DecidableEq α] in
theorem exists_maximalCliqueSet_containing_clique
    (G : SimpleGraph α) [Fintype α] {s₀ : Set α} (hclique : G.IsClique s₀) :
    ∃ s : Set α, IsMaximalCliqueSet G s ∧ s₀ ⊆ s := by
  let family : Set (Set α) := {s | G.IsClique s ∧ s₀ ⊆ s}
  have hfinite : family.Finite := Set.toFinite family
  have hnonempty : family.Nonempty := ⟨s₀, hclique, subset_rfl⟩
  obtain ⟨s, hs, hmax⟩ := hfinite.exists_maximal hnonempty
  refine ⟨s, ?_, hs.2⟩
  refine ⟨hs.1, ?_⟩
  intro t ht hst
  exact hmax ⟨ht, hs.2.trans hst⟩ hst

omit [DecidableEq α] in
theorem exists_maximalCliqueSet_containing_edge
    (G : SimpleGraph α) [Fintype α] {v w : α} (h : G.Adj v w) :
    ∃ s : Set α, IsMaximalCliqueSet G s ∧ v ∈ s ∧ w ∈ s := by
  have hpair : G.IsClique ({v, w} : Set α) := by
    rw [SimpleGraph.isClique_pair]
    intro _
    exact h
  obtain ⟨s, hsmax, hsub⟩ := exists_maximalCliqueSet_containing_clique G hpair
  exact ⟨s, hsmax, hsub (by simp), hsub (by simp)⟩

/-
Appendix Proposition 7, in reconstruction form: for a finite graph, adjacency
is equivalent to co-membership in at least one maximal clique, with the
off-diagonal condition made explicit.
-/
omit [DecidableEq α] in
theorem adj_iff_recoveredByMaximalCliques
    (G : SimpleGraph α) [Fintype α] {v w : α} :
    G.Adj v w ↔ RecoveredByMaximalCliques G v w := by
  constructor
  · intro h
    obtain ⟨s, hsmax, hv, hw⟩ := exists_maximalCliqueSet_containing_edge G h
    exact ⟨s, hsmax, hv, hw, h.ne⟩
  · rintro ⟨s, hsmax, hv, hw, hne⟩
    exact hsmax.1 hv hw hne

omit [DecidableEq α] in
theorem same_maximalClique_recovery_ext
    {G H : SimpleGraph α} [Fintype α]
    (h :
      ∀ s : Set α, IsMaximalCliqueSet G s ↔ IsMaximalCliqueSet H s) :
    G = H := by
  ext v w
  rw [adj_iff_recoveredByMaximalCliques G, adj_iff_recoveredByMaximalCliques H]
  constructor
  · rintro ⟨s, hs, hv, hw, hne⟩
    exact ⟨s, (h s).1 hs, hv, hw, hne⟩
  · rintro ⟨s, hs, hv, hw, hne⟩
    exact ⟨s, (h s).2 hs, hv, hw, hne⟩

/-! ## Explicit Witt-coordinate model of the graph vectors -/

/-- The explicit `P ⊕ Q` Witt coordinate carrier used in the graph construction. -/
abbrev WittGraphSpace (n : ℕ) : Type :=
  (Fin n → ℂ) × (Fin n → ℂ)

/-- The `p_i` coordinate vector. -/
def wittP {n : ℕ} (i : Fin n) : WittGraphSpace n :=
  (fun k => if k = i then 1 else 0, fun _ => 0)

/-- The `q_i` coordinate vector. -/
def wittQ {n : ℕ} (i : Fin n) : WittGraphSpace n :=
  (fun _ => 0, fun k => if k = i then 1 else 0)

/--
The directed Witt pairing.  This is the coordinate pairing for which
`p_i` paired with `q_j` is `δᵢⱼ`; it is the explicit matrix entry readout
used below for `z_i` against `z_j`.
-/
def wittPairing {n : ℕ} (x y : WittGraphSpace n) : ℂ :=
  ∑ i : Fin n, x.1 i * y.2 i

@[simp] theorem wittPairing_p_p {n : ℕ} (i j : Fin n) :
    wittPairing (wittP i) (wittP j) = 0 := by
  simp [wittPairing, wittP]

@[simp] theorem wittPairing_q_q {n : ℕ} (i j : Fin n) :
    wittPairing (wittQ i) (wittQ j) = 0 := by
  simp [wittPairing, wittQ]

@[simp] theorem wittPairing_p_q {n : ℕ} (i j : Fin n) :
    wittPairing (wittP i) (wittQ j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [wittPairing, wittP, wittQ]
  · simp [wittPairing, wittP, wittQ, h, eq_comm]

@[simp] theorem wittPairing_q_p {n : ℕ} (i j : Fin n) :
    wittPairing (wittQ i) (wittP j) = 0 := by
  simp [wittPairing, wittP, wittQ]

/-- Complement adjacency entry as a complex scalar. -/
def complementAdjacencyEntry {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i j : Fin n) : ℂ :=
  if i = j then 0 else if G.Adj i j then 0 else 1

@[simp] theorem complementAdjacencyEntry_self
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    complementAdjacencyEntry G i i = 0 := by
  simp [complementAdjacencyEntry]

theorem complementAdjacencyEntry_symm
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    complementAdjacencyEntry G i j = complementAdjacencyEntry G j i := by
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    by_cases hadj : G.Adj i j
    · have hadj' : G.Adj j i := hadj.symm
      simp [complementAdjacencyEntry, hij, hji, hadj, hadj']
    · have hadj' : ¬ G.Adj j i := fun h => hadj h.symm
      simp [complementAdjacencyEntry, hij, hji, hadj, hadj']

/--
The explicit Budinich graph vector
`z_i = p_i + Σ_j āᵢⱼ q_j`, represented directly in Witt coordinates.
-/
def budinichGraphVector {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i : Fin n) : WittGraphSpace n :=
  (fun k => if k = i then 1 else 0, fun j => complementAdjacencyEntry G i j)

@[simp] theorem budinichGraphVector_pCoord
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i k : Fin n) :
    (budinichGraphVector G i).1 k = if k = i then 1 else 0 := by
  rfl

@[simp] theorem budinichGraphVector_qCoord
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    (budinichGraphVector G i).2 j = complementAdjacencyEntry G i j := by
  rfl

/-- The graph vectors have zero length in the directed Witt readout. -/
theorem budinichGraphVector_null
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    wittPairing (budinichGraphVector G i) (budinichGraphVector G i) = 0 := by
  simp [wittPairing, budinichGraphVector]

/-- The graph-vector pairing recovers the complement adjacency entry. -/
theorem budinichGraphVector_pairing
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    wittPairing (budinichGraphVector G i) (budinichGraphVector G j)
      = complementAdjacencyEntry G j i := by
  simp [wittPairing, budinichGraphVector]

/--
Using symmetry of the graph, the same pairing recovers the ordinary
`i,j` complement adjacency entry.
-/
theorem budinichGraphVector_pairing_symmEntry
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    wittPairing (budinichGraphVector G i) (budinichGraphVector G j)
      = complementAdjacencyEntry G i j := by
  rw [budinichGraphVector_pairing, complementAdjacencyEntry_symm]

/-- A set of graph vectors is totally null exactly when its vertices form a clique. -/
theorem finsetClique_iff_budinichVectors_pairwise_null
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : Finset (Fin n)) :
    G.IsClique (s : Set (Fin n)) ↔
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        wittPairing (budinichGraphVector G i) (budinichGraphVector G j) = 0 := by
  constructor
  · intro hclique i hi j hj hne
    rw [budinichGraphVector_pairing_symmEntry]
    exact graphCliqueGram_adj_eq_zero G (hclique hi hj hne)
  · intro hpair i hi j hj hne
    have hzero := hpair i hi j hj hne
    rw [budinichGraphVector_pairing_symmEntry] at hzero
    exact (graphCliqueGram_eq_zero_iff G hne).1 hzero

end BudinichCliqueSpinor
end Clifford
end InfoGeometry
