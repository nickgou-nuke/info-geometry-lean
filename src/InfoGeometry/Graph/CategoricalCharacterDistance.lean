/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Data.String.Basic
import Mathlib.Tactic

/-!
# Categorical character distance

This models the equal-weight categorical mismatch fraction used by
`tools/repository_evolution/dna_character_tree.py`. Digest values are treated
as categorical states: their bit or hexadecimal distance is irrelevant. This
finite metric does not encode Git ancestry or identify its profiles with
operators in a noncommutative ring.
-/

namespace InfoGeometry.Graph.CategoricalCharacterDistance

variable {n : ℕ} {State : Type*} [DecidableEq State]

/-- Number of retained markers at which two complete profiles disagree. -/
def mismatchCount (x y : Fin n → State) : ℕ :=
  ∑ i : Fin n, if x i = y i then 0 else 1

/-- Equal-weight mismatch fraction, represented exactly in `ℚ`. -/
def mismatchFraction (x y : Fin n → State) : ℚ :=
  (mismatchCount x y : ℚ) / (n : ℚ)

theorem mismatchCount_symm (x y : Fin n → State) :
    mismatchCount x y = mismatchCount y x := by
  unfold mismatchCount
  congr 1
  funext i
  simp [eq_comm]

/-- Reindexing the retained markers by a permutation leaves the mismatch
count unchanged. This is a statement about the distance input only; it does
not assert equivariance of Neighbor-Joining tie-breaking or exported IDs. -/
theorem mismatchCount_reindex (σ : Equiv (Fin n) (Fin n))
    (x y : Fin n → State) :
    mismatchCount (fun i => x (σ i)) (fun i => y (σ i)) =
      mismatchCount x y := by
  unfold mismatchCount
  simpa only [Function.comp_apply] using
    (Equiv.sum_comp σ (fun i => if x i = y i then 0 else 1))

/-- The exact rational mismatch fraction is also independent of the order in
which retained markers are presented. -/
theorem mismatchFraction_reindex (σ : Equiv (Fin n) (Fin n))
    (x y : Fin n → State) :
    mismatchFraction (fun i => x (σ i)) (fun i => y (σ i)) =
      mismatchFraction x y := by
  unfold mismatchFraction
  rw [mismatchCount_reindex]

theorem mismatchCount_eq_zero_iff (x y : Fin n → State) :
    mismatchCount x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hEach := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Nat.zero_le _)).mp h
    funext i
    have hi := hEach i (Finset.mem_univ i)
    by_cases hxy : x i = y i
    · exact hxy
    · simp [hxy] at hi
  · rintro rfl
    simp [mismatchCount]

theorem mismatchCount_triangle (x y z : Fin n → State) :
    mismatchCount x z ≤ mismatchCount x y + mismatchCount y z := by
  unfold mismatchCount
  calc
    (∑ i : Fin n, if x i = z i then 0 else 1) ≤
        ∑ i : Fin n,
          ((if x i = y i then 0 else 1) + (if y i = z i then 0 else 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hxy : x i = y i
      · by_cases hyz : y i = z i
        · simp [hxy, hyz]
        · have hxz : x i ≠ z i := by
            intro hxz
            apply hyz
            calc
              y i = x i := hxy.symm
              _ = z i := hxz
          simp [hxy, hyz]
      · by_cases hyz : y i = z i
        · have hxz : x i ≠ z i := by
            intro hxz
            apply hxy
            calc
              x i = z i := hxz
              _ = y i := hyz.symm
          simp [hyz, hxz]
        · by_cases hxz : x i = z i <;> simp [hxy, hyz, hxz]
    _ = (∑ i : Fin n, if x i = y i then 0 else 1) +
        ∑ i : Fin n, if y i = z i then 0 else 1 := Finset.sum_add_distrib

theorem mismatchCount_le_markerCount (x y : Fin n → State) :
    mismatchCount x y ≤ n := by
  unfold mismatchCount
  calc
    (∑ i : Fin n, if x i = y i then 0 else 1) ≤
        ∑ _i : Fin n, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      split <;> omega
    _ = n := by simp

theorem mismatchFraction_symm (x y : Fin n → State) :
    mismatchFraction x y = mismatchFraction y x := by
  exact congrArg (fun count : ℕ => (count : ℚ) / (n : ℚ))
    (mismatchCount_symm x y)

theorem mismatchFraction_nonneg (x y : Fin n → State) :
    0 ≤ mismatchFraction x y := by
  unfold mismatchFraction
  positivity

/-- With at least one retained marker, zero mismatch fraction is equivalent
to equality of the aligned categorical profiles. -/
theorem mismatchFraction_eq_zero_iff (hn : 0 < n)
    (x y : Fin n → State) :
    mismatchFraction x y = 0 ↔ x = y := by
  unfold mismatchFraction
  have hDen : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  rw [div_eq_zero_iff]
  simp [hDen, mismatchCount_eq_zero_iff]

/-- Equal categorical profiles always have zero mismatch fraction, including
the zero-marker case where the denominator is zero. -/
theorem mismatchFraction_eq_zero_of_eq (x y : Fin n → State) (hxy : x = y) :
    mismatchFraction x y = 0 := by
  unfold mismatchFraction
  rw [(mismatchCount_eq_zero_iff x y).2 hxy]
  simp

theorem mismatchFraction_le_one (hn : 0 < n)
    (x y : Fin n → State) :
    mismatchFraction x y ≤ 1 := by
  have hNum : (mismatchCount x y : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast mismatchCount_le_markerCount x y
  have hDen : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  unfold mismatchFraction
  apply (div_le_iff₀ hDen).2
  simpa using hNum

theorem mismatchFraction_triangle (hn : 0 < n)
    (x y z : Fin n → State) :
    mismatchFraction x z ≤ mismatchFraction x y + mismatchFraction y z := by
  have hCount := mismatchCount_triangle x y z
  have hDen : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  unfold mismatchFraction
  rw [← add_div]
  apply (div_le_div_iff_of_pos_right hDen).2
  exact_mod_cast hCount

/-! ### Four-point additivity diagnostic for one quartet -/

/-- Largest of the three paired-distance sums for a four-taxon quartet. -/
def fourPointLargest (s₁ s₂ s₃ : ℚ) : ℚ := max s₁ (max s₂ s₃)

/-- Second-largest of the three paired-distance sums. -/
def fourPointSecondLargest (s₁ s₂ s₃ : ℚ) : ℚ :=
  max (min s₁ s₂) (min (max s₁ s₂) s₃)

/-- Largest minus second-largest paired-distance sum, matching the per-quartet
residual used by the exporter's four-point diagnostic. -/
def fourPointResidual (s₁ s₂ s₃ : ℚ) : ℚ :=
  fourPointLargest s₁ s₂ s₃ - fourPointSecondLargest s₁ s₂ s₃

theorem fourPointSecondLargest_le_largest (s₁ s₂ s₃ : ℚ) :
    fourPointSecondLargest s₁ s₂ s₃ ≤ fourPointLargest s₁ s₂ s₃ := by
  unfold fourPointSecondLargest fourPointLargest
  have hMax : max s₁ s₂ ≤ max s₁ (max s₂ s₃) := by
    apply max_le
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
  apply max_le
  · exact le_trans (min_le_left _ _) (le_max_left _ _)
  · exact le_trans (min_le_left _ _) hMax

/-- The four-point residual of a quartet is nonnegative. -/
theorem fourPointResidual_nonneg (s₁ s₂ s₃ : ℚ) :
    0 ≤ fourPointResidual s₁ s₂ s₃ := by
  unfold fourPointResidual
  exact sub_nonneg.mpr (fourPointSecondLargest_le_largest s₁ s₂ s₃)

/-- A zero four-point residual means the two largest paired-distance sums
agree, the quartet additivity condition checked by the exporter. -/
theorem fourPointResidual_eq_zero_iff (s₁ s₂ s₃ : ℚ) :
    fourPointResidual s₁ s₂ s₃ = 0 ↔
      fourPointLargest s₁ s₂ s₃ = fourPointSecondLargest s₁ s₂ s₃ := by
  unfold fourPointResidual
  exact sub_eq_zero

/-! ### Exact-rational Neighbor-Joining step

The source algorithm selects a pair minimizing
`(activeCount - 2) * d(i,j) - rowSum(i) - rowSum(j)`, then replaces its
distances to each remaining taxon by `(d(i,k) + d(j,k) - d(i,j))/2`.
These definitions formalize the exact-rational candidate selection and one
contraction step. The state below iterates that contraction, accumulates
undirected branch edges, and appends the terminal three-taxon star. The module
does not formalize Python input validation, taxon-ID preprocessing, or JSON
serialization. -/

/-! ### Evolving NJ state with persistent internal-node identities -/

/-- Taxon leaves and generated internal nodes share one linearly ordered node
space. Leaves retain their original finite indices; internal nodes use a
monotone natural-number identifier. -/
abbrev NJNode (n : ℕ) := Fin n ⊕ₗ ℕ

def njLeaf {n : ℕ} (i : Fin n) : NJNode n := toLex (Sum.inl i)

def njInternal {n : ℕ} (k : ℕ) : NJNode n := toLex (Sum.inr k)

/-- String identifier used by `dna_character_tree.py` when ordering NJ ties. -/
def njNodeIdentifier {n : ℕ} (node : NJNode n) : String :=
  match ofLex node with
  | Sum.inl i => "leaf:" ++ toString i.val
  | Sum.inr k => "internal:" ++ toString k

theorem njInternal_injective {n : ℕ} : Function.Injective (@njInternal n) := by
  intro a b h
  have hs : (Sum.inr a : Fin n ⊕ ℕ) = Sum.inr b := toLex.injective h
  exact Sum.inr.inj hs

/-- One undirected NJ branch with an exact rational length. -/
structure NJEdge (n : ℕ) where
  left : NJNode n
  right : NJNode n
  length : ℚ

/-- A concrete non-loop edge between the first two generated node identities.
The leaf parameter is irrelevant because the internal-node summand is always
inhabited. -/
instance {n : ℕ} : Inhabited (NJEdge n) :=
  ⟨⟨njInternal 0, njInternal 1, 0⟩⟩

/-- Canonical endpoint ordering for an undirected exported edge. -/
def njEdgeCanonical {n : ℕ} (edge : NJEdge n) : Prop :=
  njNodeIdentifier edge.left ≤ njNodeIdentifier edge.right

/-- An exported branch is loop-free when its endpoints differ. -/
def njEdgeNoLoop {n : ℕ} (edge : NJEdge n) : Prop := edge.left ≠ edge.right

/-- The default edge witness has distinct endpoints for every leaf count. -/
theorem njEdge_default_noLoop {n : ℕ} :
    njEdgeNoLoop (default : NJEdge n) := by
  intro h
  have h' := njInternal_injective h
  exact Nat.zero_ne_one h'

/-- Every serialized edge in the accumulated branch list has canonical
endpoint order. -/
def njEdgesCanonical {n : ℕ} (edges : List (NJEdge n)) : Prop :=
  edges.Forall njEdgeCanonical

/-- Every serialized edge has distinct endpoints. -/
def njEdgesNoLoop {n : ℕ} (edges : List (NJEdge n)) : Prop :=
  edges.Forall njEdgeNoLoop

/-- Every branch in an edge list has zero rational length. -/
def njEdgesZeroLength {n : ℕ} (edges : List (NJEdge n)) : Prop :=
  edges.Forall (fun edge => edge.length = 0)

/-- Canonicalize an undirected edge by the exporter's lexical node-ID order. -/
def njUndirectedEdge {n : ℕ} (a b : NJNode n) (length : ℚ) : NJEdge n :=
  if njNodeIdentifier a ≤ njNodeIdentifier b then ⟨a, b, length⟩
  else ⟨b, a, length⟩

@[simp] theorem njUndirectedEdge_length {n : ℕ} (a b : NJNode n) (length : ℚ) :
    (njUndirectedEdge a b length).length = length := by
  by_cases h : njNodeIdentifier a ≤ njNodeIdentifier b <;>
    simp [njUndirectedEdge, h]

theorem njUndirectedEdge_canonical {n : ℕ} (a b : NJNode n) (length : ℚ) :
    njEdgeCanonical (njUndirectedEdge a b length) := by
  by_cases h : njNodeIdentifier a ≤ njNodeIdentifier b
  · simp [njUndirectedEdge, njEdgeCanonical, h]
  · have h' : njNodeIdentifier b ≤ njNodeIdentifier a :=
      (le_total (njNodeIdentifier a) (njNodeIdentifier b)).resolve_left h
    simp [njUndirectedEdge, njEdgeCanonical, h]
    exact h'

theorem njUndirectedEdge_noLoop {n : ℕ} (a b : NJNode n) (length : ℚ)
    (hne : a ≠ b) : njEdgeNoLoop (njUndirectedEdge a b length) := by
  by_cases h : njNodeIdentifier a ≤ njNodeIdentifier b <;>
    simp [njUndirectedEdge, njEdgeNoLoop, h, hne, hne.symm]

/-- The exact rational reduction distance from a newly joined node to an
existing active node. -/
def njReducedDistance {n : ℕ} (d : NJNode n → NJNode n → ℚ)
    (i j k : NJNode n) : ℚ :=
  (d i k + d j k - d i j) / 2

/-- Exact-rational limb lengths for the final three-taxon Neighbor-Joining
star, matching the exporter’s unrooted terminal join. -/
def njFinalLimbA (dAB dAC dBC : ℚ) : ℚ := (dAB + dAC - dBC) / 2
def njFinalLimbB (dAB dAC dBC : ℚ) : ℚ := (dAB + dBC - dAC) / 2
def njFinalLimbC (dAB dAC dBC : ℚ) : ℚ := (dAC + dBC - dAB) / 2

/-- The terminal three limbs reconstruct all three pairwise input distances. -/
theorem njFinalLimb_pairwise_reconstruction (dAB dAC dBC : ℚ) :
    njFinalLimbA dAB dAC dBC + njFinalLimbB dAB dAC dBC = dAB ∧
    njFinalLimbA dAB dAC dBC + njFinalLimbC dAB dAC dBC = dAC ∧
    njFinalLimbB dAB dAC dBC + njFinalLimbC dAB dAC dBC = dBC := by
  unfold njFinalLimbA njFinalLimbB njFinalLimbC
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- Distance matrix after introducing one internal node. Distances between
existing nodes are retained; the new node receives the NJ reduction distances
and has zero self-distance. -/
def njContractDistance {n : ℕ} (d : NJNode n → NJNode n → ℚ)
    (i j fresh a b : NJNode n) : ℚ :=
  if a = fresh then
    if b = fresh then 0 else njReducedDistance d i j b
  else if b = fresh then njReducedDistance d i j a
  else d a b

theorem njContractDistance_symm {n : ℕ} (d : NJNode n → NJNode n → ℚ)
    (hSymm : ∀ a b, d a b = d b a) (i j fresh a b : NJNode n) :
    njContractDistance d i j fresh a b = njContractDistance d i j fresh b a := by
  by_cases ha : a = fresh <;> by_cases hb : b = fresh <;>
    simp [njContractDistance, ha, hb, njReducedDistance, hSymm]

theorem njContractDistance_diag {n : ℕ} (d : NJNode n → NJNode n → ℚ)
    (hDiag : ∀ a, d a a = 0)
    (i j fresh a : NJNode n) :
    njContractDistance d i j fresh a a = 0 := by
  by_cases ha : a = fresh
  · simp [njContractDistance, ha]
  · simp [njContractDistance, ha, hDiag]

/-- Neighbor-Joining reduction preserves the zero distance function. -/
theorem njContractDistance_eq_zero_of_eq_zero {n : ℕ}
    (d : NJNode n → NJNode n → ℚ) (hZero : ∀ a b, d a b = 0)
    (i j fresh a b : NJNode n) :
    njContractDistance d i j fresh a b = 0 := by
  by_cases ha : a = fresh <;> by_cases hb : b = fresh <;>
    simp [njContractDistance, njReducedDistance, ha, hb, hZero]

/-- A single algorithm state: currently active leaves/internal nodes, the
current exact-rational distance matrix, and the next internal-node identifier. -/
structure NJState (n : ℕ) where
  active : Finset (NJNode n)
  distance : NJNode n → NJNode n → ℚ
  nextInternal : ℕ
  edges : List (NJEdge n)
deriving Inhabited

/-- Initial NJ state on the indexed leaves, with the supplied exact-rational
distance function and internal-node counter starting at one. -/
def njInitialState {n : ℕ} (d : NJNode n → NJNode n → ℚ) : NJState n :=
  ⟨Finset.univ.image njLeaf, d, 1, []⟩

/-- Lift an input distance matrix on the indexed leaves to the dynamic node
carrier. Newly allocated internal-node distances start at zero and are then
overwritten by the Neighbor-Joining reduction rule when the node is created. -/
def njInitialDistance {n : ℕ} (d : Fin n → Fin n → ℚ)
    (a b : NJNode n) : ℚ :=
  match ofLex a, ofLex b with
  | Sum.inl i, Sum.inl j => d i j
  | _, _ => 0

/-- Well-formed exact distance matrix contract checked by the Python NJ
entrypoint: square dimensions are encoded by `Fin n`, with zero diagonal,
symmetry, and nonnegative entries. -/
def njDistanceMatrixValid {n : ℕ} (d : Fin n → Fin n → ℚ) : Prop :=
  (∀ i, d i i = 0) ∧
  (∀ i j, d i j = d j i) ∧
  (∀ i j, 0 ≤ d i j)

/-- Initial NJ state directly from a finite input distance matrix. -/
def njInitialStateFromMatrix {n : ℕ} (d : Fin n → Fin n → ℚ) : NJState n :=
  njInitialState (njInitialDistance d)

/-- Equal exact-rational input matrices initialize identical NJ states. -/
theorem njInitialStateFromMatrix_eq_of_eq {n : ℕ}
    {d₁ d₂ : Fin n → Fin n → ℚ} (h : d₁ = d₂) :
    njInitialStateFromMatrix d₁ = njInitialStateFromMatrix d₂ := by
  rw [h]

/-- Reordering retained markers by one permutation for every profile leaves
the initialized exact NJ state unchanged, not only its pairwise distances. -/
theorem njInitialStateFromMatrix_eq_of_marker_reindex
    {taxaCount markerCount : ℕ} {State : Type*} [DecidableEq State]
    (σ : Equiv (Fin markerCount) (Fin markerCount))
    (profiles : Fin taxaCount → Fin markerCount → State) :
    njInitialStateFromMatrix
      (fun i j => mismatchFraction
        (fun k => profiles i (σ k)) (fun k => profiles j (σ k))) =
    njInitialStateFromMatrix
      (fun i j => mismatchFraction (profiles i) (profiles j)) := by
  apply njInitialStateFromMatrix_eq_of_eq
  funext i j
  exact mismatchFraction_reindex σ (profiles i) (profiles j)

/-- Symmetric zero-diagonal input matrices induce symmetric zero-diagonal
initial distances on the complete dynamic node carrier. -/
theorem njInitialStateFromMatrix_distance_laws {n : ℕ}
    (d : Fin n → Fin n → ℚ)
    (hSymm : ∀ i j, d i j = d j i) (hDiag : ∀ i, d i i = 0) :
    (∀ a b, (njInitialStateFromMatrix d).distance a b =
      (njInitialStateFromMatrix d).distance b a) ∧
    (∀ a, (njInitialStateFromMatrix d).distance a a = 0) := by
  constructor
  · intro a b
    change njInitialDistance d a b = njInitialDistance d b a
    cases ha : ofLex a with
    | inl i =>
        cases hb : ofLex b with
        | inl j => simp [njInitialDistance, ha, hb, hSymm i j]
        | inr k => simp [njInitialDistance, ha, hb]
    | inr k =>
        cases hb : ofLex b with
        | inl j => simp [njInitialDistance, ha, hb]
        | inr l => simp [njInitialDistance, ha, hb]
  · intro a
    change njInitialDistance d a a = 0
    cases ha : ofLex a with
    | inl i => simp [njInitialDistance, ha, hDiag i]
    | inr k => simp [njInitialDistance, ha]

/-- A validated input matrix gives nonnegative initial distances on all
dynamic nodes; newly allocated internal-node slots begin at zero. -/
theorem njInitialStateFromMatrix_distance_nonneg {n : ℕ}
    (d : Fin n → Fin n → ℚ) (hValid : njDistanceMatrixValid d) :
    ∀ a b, 0 ≤ (njInitialStateFromMatrix d).distance a b := by
  rcases hValid with ⟨_, _, hNonneg⟩
  intro a b
  change 0 ≤ njInitialDistance d a b
  cases ha : ofLex a with
  | inl i =>
      cases hb : ofLex b with
      | inl j => simpa [njInitialDistance, ha, hb] using hNonneg i j
      | inr k => simp [njInitialDistance, ha, hb]
  | inr k => simp [njInitialDistance, ha]

theorem njLeaf_injective {n : ℕ} : Function.Injective (@njLeaf n) := by
  intro i j hij
  exact Sum.inl.inj (toLex.injective hij)

/-- The initialized active set contains exactly the indexed input taxa. -/
theorem njInitialState_active_card {n : ℕ}
    (d : NJNode n → NJNode n → ℚ) :
    (njInitialState d).active.card = n := by
  change (Finset.univ.image njLeaf).card = n
  rw [Finset.card_image_iff.mpr (by
    intro i hi j hj hij
    exact njLeaf_injective hij)]
  simp

/-- Active-set row sum and Q score, recomputed at every recursive state. -/
def njRowSum {n : ℕ} (s : NJState n) (i : NJNode n) : ℚ :=
  ∑ j ∈ s.active, if i = j then 0 else s.distance i j

def njQScore {n : ℕ} (s : NJState n) (i j : NJNode n) : ℚ :=
  ((s.active.card : ℚ) - 2) * s.distance i j - njRowSum s i - njRowSum s j

/-- If every pair of active nodes has zero distance, each active node has
zero NJ row sum. -/
theorem njRowSum_eq_zero_of_active_zero_distances {n : ℕ}
    (s : NJState n)
    (hZero : ∀ i ∈ s.active, ∀ j ∈ s.active, s.distance i j = 0)
    {i : NJNode n} (hi : i ∈ s.active) :
    njRowSum s i = 0 := by
  unfold njRowSum
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, hZero i hi j hj]

/-- Zero distances on the active set force every eligible Neighbor-Joining
pair to have score zero. Consequently, the score criterion itself cannot
distinguish those pairs; any further choice comes from the secondary key. -/
theorem njQScore_eq_zero_of_active_zero_distances {n : ℕ}
    (s : NJState n)
    (hZero : ∀ i ∈ s.active, ∀ j ∈ s.active, s.distance i j = 0)
    {i j : NJNode n} (hi : i ∈ s.active) (hj : j ∈ s.active) :
    njQScore s i j = 0 := by
  unfold njQScore
  rw [hZero i hi j hj,
    njRowSum_eq_zero_of_active_zero_distances s hZero hi,
    njRowSum_eq_zero_of_active_zero_distances s hZero hj]
  ring

/-- If the input character profiles are all identical, then every active
Neighbor-Joining pair in the initialized mismatch-distance matrix has score
zero. This formalizes score indeterminacy of the unrooted input, not a unique
tree topology. -/
theorem njInitialQScore_eq_zero_of_identical_profiles
    {taxaCount markerCount : ℕ} {State : Type*} [DecidableEq State]
    (profiles : Fin taxaCount → Fin markerCount → State)
    (hProfiles : ∀ i j, profiles i = profiles j)
    {i j : NJNode taxaCount}
    (hi : i ∈ (njInitialStateFromMatrix
      (fun a b => mismatchFraction (profiles a) (profiles b))).active)
    (hj : j ∈ (njInitialStateFromMatrix
      (fun a b => mismatchFraction (profiles a) (profiles b))).active) :
    njQScore (njInitialStateFromMatrix
      (fun a b => mismatchFraction (profiles a) (profiles b))) i j = 0 := by
  apply njQScore_eq_zero_of_active_zero_distances
    (njInitialStateFromMatrix
      (fun a b => mismatchFraction (profiles a) (profiles b))) ?_ hi hj
  intro a ha b hb
  change a ∈ Finset.univ.image njLeaf at ha
  change b ∈ Finset.univ.image njLeaf at hb
  obtain ⟨a₀, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b₀, _, rfl⟩ := Finset.mem_image.mp hb
  change njInitialDistance (fun a b => mismatchFraction (profiles a) (profiles b))
    (njLeaf a₀) (njLeaf b₀) = 0
  simp [njInitialDistance, njLeaf, mismatchFraction_eq_zero_of_eq,
    hProfiles a₀ b₀]

/-- Identical declaration profiles induce the zero distance function on the
entire dynamic NJ node carrier. Internal-node slots are initialized to zero
as well as the pairwise leaf distances. -/
theorem njInitialStateFromMatrix_distance_eq_zero_of_identical_profiles
    {taxaCount markerCount : ℕ} {State : Type*} [DecidableEq State]
    (profiles : Fin taxaCount → Fin markerCount → State)
    (hProfiles : ∀ i j, profiles i = profiles j) :
    ∀ a b, (njInitialStateFromMatrix
      (fun i j => mismatchFraction (profiles i) (profiles j))).distance a b = 0 := by
  intro a b
  change njInitialDistance (fun i j => mismatchFraction (profiles i) (profiles j)) a b = 0
  cases ha : ofLex a with
  | inl i =>
      cases hb : ofLex b with
      | inl j =>
          simpa [njInitialDistance, ha, hb] using
            mismatchFraction_eq_zero_of_eq (profiles i) (profiles j) (hProfiles i j)
      | inr k => simp [njInitialDistance, ha, hb]
  | inr k => simp [njInitialDistance, ha]

/-- NJ limb lengths for the two taxa joined at this state. -/
def njFirstLimb {n : ℕ} (s : NJState n) (i j : NJNode n) : ℚ :=
  (s.distance i j + (njRowSum s i - njRowSum s j) /
    ((s.active.card : ℚ) - 2)) / 2

def njSecondLimb {n : ℕ} (s : NJState n) (i j : NJNode n) : ℚ :=
  s.distance i j - njFirstLimb s i j

/-- If the state distance matrix is globally zero, every active-pair first
limb computed by the NJ formula is zero. -/
theorem njFirstLimb_eq_zero_of_eq_zero_distances {n : ℕ}
    (s : NJState n) (hZero : ∀ a b, s.distance a b = 0)
    {i j : NJNode n} (hi : i ∈ s.active) (hj : j ∈ s.active) :
    njFirstLimb s i j = 0 := by
  unfold njFirstLimb
  rw [hZero i j,
    njRowSum_eq_zero_of_active_zero_distances s
      (by intro a ha b hb; exact hZero a b) hi,
    njRowSum_eq_zero_of_active_zero_distances s
      (by intro a ha b hb; exact hZero a b) hj]
  simp

/-- If the state distance matrix is globally zero, every active-pair second
limb computed by the NJ formula is zero as well. -/
theorem njSecondLimb_eq_zero_of_eq_zero_distances {n : ℕ}
    (s : NJState n) (hZero : ∀ a b, s.distance a b = 0)
    {i j : NJNode n} (hi : i ∈ s.active) (hj : j ∈ s.active) :
    njSecondLimb s i j = 0 := by
  unfold njSecondLimb
  rw [hZero i j, njFirstLimb_eq_zero_of_eq_zero_distances s hZero hi hj]
  simp

/-- The two new limbs reconstruct the selected pair's current distance. -/
theorem njSelected_limbs_reconstruct_distance {n : ℕ} (s : NJState n)
    (i j : NJNode n) :
    njFirstLimb s i j + njSecondLimb s i j = s.distance i j := by
  unfold njSecondLimb
  ring

/-- The final three-taxon star: append its center-to-tip limbs to all edges
recorded by the recursive contractions. -/
def njFinishThree {n : ℕ} (s : NJState n)
    (a b c : NJNode n) : List (NJEdge n) :=
  let dAB := s.distance a b
  let dAC := s.distance a c
  let dBC := s.distance b c
  s.edges ++
    [njUndirectedEdge (njInternal s.nextInternal) a (njFinalLimbA dAB dAC dBC),
     njUndirectedEdge (njInternal s.nextInternal) b (njFinalLimbB dAB dAC dBC),
     njUndirectedEdge (njInternal s.nextInternal) c (njFinalLimbC dAB dAC dBC)]

theorem njFinishThree_edgesCanonical {n : ℕ} (s : NJState n)
    (a b c : NJNode n) (hEdges : njEdgesCanonical s.edges) :
    njEdgesCanonical (njFinishThree s a b c) := by
  simp only [njFinishThree, njEdgesCanonical, List.forall_append]
  constructor
  · exact hEdges
  · repeat' constructor
    all_goals exact njUndirectedEdge_canonical _ _ _

theorem njFinishThree_edgesNoLoop {n : ℕ} (s : NJState n)
    (a b c : NJNode n) (hEdges : njEdgesNoLoop s.edges)
    (ha : njInternal s.nextInternal ≠ a)
    (hb : njInternal s.nextInternal ≠ b)
    (hc : njInternal s.nextInternal ≠ c) :
    njEdgesNoLoop (njFinishThree s a b c) := by
  simp only [njFinishThree, njEdgesNoLoop, List.forall_append]
  constructor
  · exact hEdges
  · repeat' constructor
    all_goals first
      | exact njUndirectedEdge_noLoop _ _ _ ha
      | exact njUndirectedEdge_noLoop _ _ _ hb
      | exact njUndirectedEdge_noLoop _ _ _ hc


/-- Dynamic candidate keys preserve the source's deterministic ordering by
current Q score, then first node identifier, then second node identifier. -/
def njCandidateKey {n : ℕ} (s : NJState n) (i j : NJNode n) :
    ℚ ×ₗ (String ×ₗ (String ×ₗ (NJNode n ×ₗ NJNode n))) :=
  if njNodeIdentifier i ≤ njNodeIdentifier j then
    toLex (njQScore s i j,
      toLex (njNodeIdentifier i,
        toLex (njNodeIdentifier j, toLex (i, j))))
  else
    toLex (njQScore s i j,
      toLex (njNodeIdentifier j,
        toLex (njNodeIdentifier i, toLex (i, j))))

theorem njCandidateKey_score {n : ℕ} (s : NJState n) (i j : NJNode n) :
    (ofLex (njCandidateKey s i j)).1 = njQScore s i j := by
  unfold njCandidateKey
  split <;> rfl

theorem njQScore_swap_of_distance_symm {n : ℕ} (s : NJState n)
    (hSymm : ∀ a b, s.distance a b = s.distance b a) (i j : NJNode n) :
    njQScore s i j = njQScore s j i := by
  unfold njQScore
  rw [hSymm i j]
  ring

def njCandidateKeys {n : ℕ} (s : NJState n) :
    Finset (ℚ ×ₗ (String ×ₗ (String ×ₗ (NJNode n ×ₗ NJNode n)))) :=
  ((s.active.product s.active).filter fun p : NJNode n × NJNode n =>
      p.1 < p.2).image
    (fun p => njCandidateKey s p.1 p.2)

/-- A state with at least two active nodes always has a candidate pair. -/
theorem njCandidateKeys_nonempty {n : ℕ} (s : NJState n)
    (hCard : 1 < s.active.card) : (njCandidateKeys s).Nonempty := by
  rcases Finset.one_lt_card.mp hCard with ⟨a, ha, b, hb, hab⟩
  have hPair : ∃ i j, i ∈ s.active ∧ j ∈ s.active ∧ i < j := by
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact ⟨a, b, ha, hb, hlt⟩
    · exact ⟨b, a, hb, ha, hgt⟩
  rcases hPair with ⟨i, j, hi, hj, hij⟩
  refine ⟨njCandidateKey s i j, ?_⟩
  unfold njCandidateKeys
  apply Finset.mem_image.mpr
  refine ⟨(i, j), Finset.mem_filter.mpr ?_, rfl⟩
  exact ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hij⟩

/-- The exact finite minimum key selected at one recursive NJ state. -/
def njSelectedKey {n : ℕ} (s : NJState n)
    (hCard : 1 < s.active.card) :
      ℚ ×ₗ (String ×ₗ (String ×ₗ (NJNode n ×ₗ NJNode n))) :=
  (njCandidateKeys s).min' (njCandidateKeys_nonempty s hCard)

theorem njSelectedKey_mem {n : ℕ} (s : NJState n)
    (hCard : 1 < s.active.card) : njSelectedKey s hCard ∈ njCandidateKeys s :=
  Finset.min'_mem _ _

/-- The selected dynamic key is no larger than every eligible active pair key. -/
theorem njSelectedKey_minimal {n : ℕ} (s : NJState n)
    (hCard : 1 < s.active.card)
    (key : ℚ ×ₗ (String ×ₗ (String ×ₗ (NJNode n ×ₗ NJNode n))))
    (hKey : key ∈ njCandidateKeys s) : njSelectedKey s hCard ≤ key :=
  Finset.min'_le _ _ hKey

/-- The minimum key is realized by an actual ordered pair of active nodes. -/
theorem njSelectedKey_attained {n : ℕ} (s : NJState n)
    (hCard : 1 < s.active.card) :
    ∃ i ∈ s.active, ∃ j ∈ s.active, i < j ∧
      njCandidateKey s i j = njSelectedKey s hCard := by
  have hMem := njSelectedKey_mem s hCard
  unfold njCandidateKeys at hMem
  rcases Finset.mem_image.mp hMem with ⟨⟨i, j⟩, hp, hKey⟩
  rcases Finset.mem_filter.mp hp with ⟨hp, hij⟩
  rcases Finset.mem_product.mp hp with ⟨hi, hj⟩
  exact ⟨i, hi, j, hj, hij, hKey⟩

/-- The node-pair payload is retained under the string-ID tie-break fields. -/
theorem njCandidateKey_pair {n : ℕ} (s : NJState n) (i j : NJNode n) :
    ofLex (((ofLex ((ofLex (njCandidateKey s i j)).2)).2).2) = (i, j) := by
  unfold njCandidateKey
  split <;> rfl

/-- The pair stored in the minimum key, after removing the nested lexicographic
order wrappers. -/
def njSelectedPair {n : ℕ} (s : NJState n) (hCard : 1 < s.active.card) :
    NJNode n × NJNode n :=
  ofLex (((ofLex ((ofLex (njSelectedKey s hCard)).2)).2).2)

/-- The selected pair is active, ordered, and realizes the minimum key. -/
theorem njSelectedPair_spec {n : ℕ} (s : NJState n)
    (hCard : 1 < s.active.card) :
    (njSelectedPair s hCard).1 ∈ s.active ∧
    (njSelectedPair s hCard).2 ∈ s.active ∧
    (njSelectedPair s hCard).1 < (njSelectedPair s hCard).2 ∧
    njCandidateKey s (njSelectedPair s hCard).1 (njSelectedPair s hCard).2 =
      njSelectedKey s hCard := by
  obtain ⟨i, hi, j, hj, hij, hKey⟩ := njSelectedKey_attained s hCard
  have hPayload := congrArg
    (fun key : ℚ ×ₗ (String ×ₗ (String ×ₗ (NJNode n ×ₗ NJNode n))) =>
      ofLex (((ofLex ((ofLex key).2)).2).2)) hKey
  rw [njCandidateKey_pair] at hPayload
  have hPair : (i, j) = njSelectedPair s hCard := by
    simpa [njSelectedPair] using hPayload
  rcases Prod.mk.inj hPair with ⟨rfl, rfl⟩
  exact ⟨hi, hj, hij, hKey⟩

/-- The selected pair minimizes the Neighbor-Joining Q criterion over every
unordered pair of active taxa, assuming the state distance is symmetric. -/
theorem njSelectedPair_q_minimal {n : ℕ} (s : NJState n)
    (hCard : 1 < s.active.card)
    (hSymm : ∀ a b, s.distance a b = s.distance b a)
    {i j : NJNode n} (hi : i ∈ s.active) (hj : j ∈ s.active) (hij : i ≠ j) :
    njQScore s (njSelectedPair s hCard).1 (njSelectedPair s hCard).2 ≤
      njQScore s i j := by
  have hSelected := njSelectedPair_spec s hCard
  have hScoreSelected : njQScore s (njSelectedPair s hCard).1
      (njSelectedPair s hCard).2 =
      (ofLex (njSelectedKey s hCard)).1 := by
    rw [← hSelected.2.2.2]
    exact (njCandidateKey_score s _ _).symm
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hMem : njCandidateKey s i j ∈ njCandidateKeys s := by
      unfold njCandidateKeys
      apply Finset.mem_image.mpr
      refine ⟨(i, j), Finset.mem_filter.mpr ?_, rfl⟩
      exact ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hlt⟩
    have hMin := njSelectedKey_minimal s hCard _ hMem
    have hFirst := (Prod.Lex.le_iff'.mp hMin).1
    calc
      njQScore s (njSelectedPair s hCard).1 (njSelectedPair s hCard).2 =
          (ofLex (njSelectedKey s hCard)).1 := hScoreSelected
      _ ≤ (ofLex (njCandidateKey s i j)).1 := hFirst
      _ = njQScore s i j := njCandidateKey_score s i j
  · have hMem : njCandidateKey s j i ∈ njCandidateKeys s := by
      unfold njCandidateKeys
      apply Finset.mem_image.mpr
      refine ⟨(j, i), Finset.mem_filter.mpr ?_, rfl⟩
      exact ⟨Finset.mem_product.mpr ⟨hj, hi⟩, hgt⟩
    have hMin := njSelectedKey_minimal s hCard _ hMem
    have hFirst := (Prod.Lex.le_iff'.mp hMin).1
    calc
      njQScore s (njSelectedPair s hCard).1 (njSelectedPair s hCard).2 =
          (ofLex (njSelectedKey s hCard)).1 := hScoreSelected
      _ ≤ (ofLex (njCandidateKey s j i)).1 := hFirst
      _ = njQScore s j i := njCandidateKey_score s j i
      _ = njQScore s i j := njQScore_swap_of_distance_symm s hSymm j i

/-- Contract a selected active pair and create the next internal node. -/
def njContractState {n : ℕ} (s : NJState n)
    (i j : NJNode n) : NJState n :=
  ⟨insert (njInternal s.nextInternal) ((s.active.erase i).erase j),
    njContractDistance s.distance i j (njInternal s.nextInternal),
    s.nextInternal + 1, s.edges⟩

/-- A contraction preserves globally zero distances, including distances to
fresh internal-node identifiers and inactive nodes. -/
theorem njContractState_distance_eq_zero_of_eq_zero {n : ℕ}
    (s : NJState n) (i j : NJNode n)
    (hZero : ∀ a b, s.distance a b = 0) :
    ∀ a b, (njContractState s i j).distance a b = 0 := by
  intro a b
  exact njContractDistance_eq_zero_of_eq_zero s.distance hZero i j
    (njInternal s.nextInternal) a b

/-- Contract a pair while appending its two exact-rational limbs to the
undirected tree edge list. -/
def njJoinState {n : ℕ} (s : NJState n) (i j : NJNode n) : NJState n :=
  let contracted := njContractState s i j
  { contracted with edges := s.edges ++
      [njUndirectedEdge (njInternal s.nextInternal) i (njFirstLimb s i j),
       njUndirectedEdge (njInternal s.nextInternal) j (njSecondLimb s i j)] }

theorem njJoinState_edgesCanonical {n : ℕ} (s : NJState n)
    (i j : NJNode n) (hEdges : njEdgesCanonical s.edges) :
    njEdgesCanonical (njJoinState s i j).edges := by
  simp only [njJoinState, njEdgesCanonical, List.forall_append]
  simp
  exact ⟨hEdges, njUndirectedEdge_canonical _ _ _,
    njUndirectedEdge_canonical _ _ _⟩

theorem njJoinState_edgesNoLoop {n : ℕ} (s : NJState n)
    (i j : NJNode n) (hEdges : njEdgesNoLoop s.edges)
    (hi : njInternal s.nextInternal ≠ i) (hj : njInternal s.nextInternal ≠ j) :
    njEdgesNoLoop (njJoinState s i j).edges := by
  simp only [njJoinState, njEdgesNoLoop, List.forall_append]
  simp
  exact ⟨hEdges, njUndirectedEdge_noLoop _ _ _ hi,
    njUndirectedEdge_noLoop _ _ _ hj⟩

/-- Counter invariant: all active internal-node identifiers are below the
next identifier available for allocation. -/
def njFreshInvariant {n : ℕ} (s : NJState n) : Prop :=
  ∀ k, njInternal k ∈ s.active → k < s.nextInternal

/-- The initial state satisfies the freshness invariant because it contains
only leaf nodes and allocates internal identifiers from zero. -/
theorem njInitialState_freshInvariant {n : ℕ}
    (d : NJNode n → NJNode n → ℚ) :
    njFreshInvariant (njInitialState d) := by
  intro k hk
  change njInternal k ∈ Finset.univ.image njLeaf at hk
  rcases Finset.mem_image.mp hk with ⟨i, _, hEq⟩
  simp [njInternal, njLeaf] at hEq

theorem njContractState_next_internal_fresh {n : ℕ} (s : NJState n)
    (hInv : njFreshInvariant s) : njInternal s.nextInternal ∉ s.active := by
  intro hMem
  exact (Nat.lt_irrefl _) (hInv s.nextInternal hMem)

/-- Finishing on active terminal taxa preserves canonical edge ordering and
introduces no self-loops, because the allocated center is fresh. -/
theorem njFinishThree_active_edges_valid {n : ℕ} (s : NJState n)
    (hInv : njFreshInvariant s) (a b c : NJNode n)
    (ha : a ∈ s.active) (hb : b ∈ s.active) (hc : c ∈ s.active)
    (hEdgesC : njEdgesCanonical s.edges) (hEdgesN : njEdgesNoLoop s.edges) :
    njEdgesCanonical (njFinishThree s a b c) ∧
      njEdgesNoLoop (njFinishThree s a b c) := by
  refine ⟨njFinishThree_edgesCanonical s a b c hEdgesC, ?_⟩
  apply njFinishThree_edgesNoLoop s a b c hEdgesN
  · intro heq
    exact njContractState_next_internal_fresh s hInv (heq ▸ ha)
  · intro heq
    exact njContractState_next_internal_fresh s hInv (heq ▸ hb)
  · intro heq
    exact njContractState_next_internal_fresh s hInv (heq ▸ hc)

/-- The counter invariant is preserved by contraction, including the newly
allocated node whose identifier was the old counter value. -/
theorem njContractState_preserves_freshInvariant {n : ℕ} (s : NJState n)
    (hInv : njFreshInvariant s) (i j : NJNode n) :
    njFreshInvariant (njContractState s i j) := by
  intro k hk
  have hk' : njInternal (n := n) k = njInternal (n := n) s.nextInternal ∨
      njInternal k ∈ (s.active.erase i).erase j := by
    change njInternal (n := n) k ∈
      insert (njInternal (n := n) s.nextInternal) ((s.active.erase i).erase j) at hk
    exact Finset.mem_insert.mp hk
  rcases hk' with hNew | hOld
  · have hId : k = s.nextInternal := njInternal_injective hNew
    change k < s.nextInternal + 1
    omega
  · have hOldActive : njInternal k ∈ s.active :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hOld).2).2
    have hBound := hInv k hOldActive
    change k < s.nextInternal + 1
    omega

/-- Contracting two distinct active nodes and inserting a fresh join node
reduces the active count by one. -/
theorem njContractState_card {n : ℕ} (s : NJState n)
    (i j : NJNode n) (hi : i ∈ s.active) (hj : j ∈ s.active) (hij : i ≠ j)
    (hFresh : njInternal s.nextInternal ∉ s.active) :
    (njContractState s i j).active.card + 1 = s.active.card := by
  have hjErase : j ∈ s.active.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hCardTwo : 1 < s.active.card :=
    Finset.one_lt_card.mpr ⟨i, hi, j, hj, hij⟩
  have hFreshErase : njInternal s.nextInternal ∉ (s.active.erase i).erase j := by
    intro hmem
    exact hFresh ((Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).2)
  change (insert (njInternal s.nextInternal) ((s.active.erase i).erase j)).card + 1 =
    s.active.card
  rw [Finset.card_insert_of_notMem hFreshErase,
    Finset.card_erase_of_mem hjErase, Finset.card_erase_of_mem hi]
  omega

/-- Under the counter invariant, the state transition automatically satisfies
the freshness hypothesis needed for the exact cardinality decrease. -/
theorem njContractState_card_of_freshInvariant {n : ℕ} (s : NJState n)
    (hInv : njFreshInvariant s) (i j : NJNode n)
    (hi : i ∈ s.active) (hj : j ∈ s.active) (hij : i ≠ j) :
    (njContractState s i j).active.card + 1 = s.active.card :=
  njContractState_card s i j hi hj hij (njContractState_next_internal_fresh s hInv)

/-- The actual deterministic NJ transition: select the minimum key, append its
two branch limbs, and update the distance state. -/
def njSelectedContractState {n : ℕ} (s : NJState n)
    (hCard : 3 < s.active.card) : NJState n :=
  njJoinState s (njSelectedPair s (by omega)).1 (njSelectedPair s (by omega)).2

/-- The deterministic recursive step lowers the active-set cardinality by one. -/
theorem njSelectedContractState_card {n : ℕ} (s : NJState n)
    (hInv : njFreshInvariant s) (hCard : 3 < s.active.card) :
    (njSelectedContractState s hCard).active.card + 1 = s.active.card := by
  change (njContractState s (njSelectedPair s (by omega)).1
    (njSelectedPair s (by omega)).2).active.card + 1 = s.active.card
  rcases njSelectedPair_spec s (by omega) with ⟨hi, hj, hlt, _⟩
  exact njContractState_card_of_freshInvariant s hInv
    (njSelectedPair s (by omega)).1 (njSelectedPair s (by omega)).2 hi hj (ne_of_lt hlt)

/-- The deterministic recursive step preserves freshness of the internal-node
counter, so it can be iterated without node-identifier collisions. -/
theorem njSelectedContractState_preserves_freshInvariant {n : ℕ}
    (s : NJState n) (hInv : njFreshInvariant s) (hCard : 3 < s.active.card) :
    njFreshInvariant (njSelectedContractState s hCard) := by
  change njFreshInvariant (njContractState s (njSelectedPair s (by omega)).1
    (njSelectedPair s (by omega)).2)
  rcases njSelectedPair_spec s (by omega) with ⟨_, _, _, _⟩
  exact njContractState_preserves_freshInvariant s hInv
    (njSelectedPair s (by omega)).1 (njSelectedPair s (by omega)).2

/-- Deterministic NJ contractions preserve the canonical endpoint ordering
used by the serialized undirected edge list. -/
theorem njSelectedContractState_edgesCanonical {n : ℕ}
    (s : NJState n) (hCard : 3 < s.active.card)
    (hEdges : njEdgesCanonical s.edges) :
    njEdgesCanonical (njSelectedContractState s hCard).edges := by
  rcases njSelectedPair_spec s (by omega) with ⟨_, _, _, _⟩
  exact njJoinState_edgesCanonical s
    (njSelectedPair s (by omega)).1 (njSelectedPair s (by omega)).2 hEdges

/-- Deterministic NJ contractions never append a self-loop: the newly
allocated internal node is fresh, while the selected endpoints are active. -/
theorem njSelectedContractState_edgesNoLoop {n : ℕ}
    (s : NJState n) (hInv : njFreshInvariant s)
    (hCard : 3 < s.active.card) (hEdges : njEdgesNoLoop s.edges) :
    njEdgesNoLoop (njSelectedContractState s hCard).edges := by
  rcases njSelectedPair_spec s (by omega) with ⟨hi, hj, _, _⟩
  apply njJoinState_edgesNoLoop s
    (njSelectedPair s (by omega)).1 (njSelectedPair s (by omega)).2 hEdges
  · intro hEq
    exact njContractState_next_internal_fresh s hInv (hEq ▸ hi)
  · intro hEq
    exact njContractState_next_internal_fresh s hInv (hEq ▸ hj)

/-- A selected join appends only zero-length limbs when all distances in the
state are zero, and retains the zero-length property of earlier edges. -/
theorem njSelectedContractState_edgesZeroLength {n : ℕ}
    (s : NJState n) (hCard : 3 < s.active.card)
    (hZero : ∀ a b, s.distance a b = 0)
    (hEdges : njEdgesZeroLength s.edges) :
    njEdgesZeroLength (njSelectedContractState s hCard).edges := by
  rcases njSelectedPair_spec s (by omega) with ⟨hi, hj, _, _⟩
  unfold njSelectedContractState
  unfold njJoinState
  simp only [njEdgesZeroLength, List.forall_append]
  refine ⟨hEdges, ?_⟩
  simp [njFirstLimb_eq_zero_of_eq_zero_distances s hZero hi hj,
    njSecondLimb_eq_zero_of_eq_zero_distances s hZero hi hj]

/-- Execute a bounded number of deterministic NJ contractions. The fuel bound
is explicit; the source algorithm stops contracting at three active taxa. -/
def njRunFuel {n : ℕ} : (fuel : ℕ) → (s : NJState n) →
    njFreshInvariant s → NJState n
  | 0, s, _ => s
  | fuel + 1, s, hInv =>
      if hCard : 3 < s.active.card then
        njRunFuel fuel (njSelectedContractState s (by omega))
          (njSelectedContractState_preserves_freshInvariant s hInv (by omega))
      else s

/-- The deterministic bounded NJ runner respects equality of its full input
state. Freshness proofs are propositions, so proof irrelevance identifies them
after substituting the equal states. -/
theorem njRunFuel_eq_of_state_eq {n : ℕ} (fuel : ℕ)
    {s₁ s₂ : NJState n} (hState : s₁ = s₂)
    (hInv₁ : njFreshInvariant s₁) (hInv₂ : njFreshInvariant s₂) :
    njRunFuel fuel s₁ hInv₁ = njRunFuel fuel s₂ hInv₂ := by
  cases hState
  have hInv : hInv₁ = hInv₂ := Subsingleton.elim _ _
  subst hInv₂
  rfl

/-- Applying one permutation to the retained markers of every profile leaves
the complete bounded NJ execution state unchanged. Taxon IDs and the lexical
tie-break keys are fixed; only marker order changes. -/
theorem njRunFuel_eq_of_marker_reindex
    {taxaCount markerCount : ℕ} {State : Type*} [DecidableEq State]
    (σ : Equiv (Fin markerCount) (Fin markerCount))
    (profiles : Fin taxaCount → Fin markerCount → State) (fuel : ℕ) :
    njRunFuel fuel
      (njInitialStateFromMatrix
        (fun i j => mismatchFraction
          (fun k => profiles i (σ k)) (fun k => profiles j (σ k))))
      (njInitialState_freshInvariant _) =
    njRunFuel fuel
      (njInitialStateFromMatrix
        (fun i j => mismatchFraction (profiles i) (profiles j)))
      (njInitialState_freshInvariant _) := by
  apply njRunFuel_eq_of_state_eq fuel
    (njInitialStateFromMatrix_eq_of_marker_reindex σ profiles)

/-- Number of pair joins performed by the bounded deterministic recursion. -/
def njRunFuelJoinCount {n : ℕ} : (fuel : ℕ) → (s : NJState n) →
    njFreshInvariant s → ℕ
  | 0, _, _ => 0
  | fuel + 1, s, hInv =>
      if hCard : 3 < s.active.card then
        njRunFuelJoinCount fuel (njSelectedContractState s hCard)
          (njSelectedContractState_preserves_freshInvariant s hInv hCard) + 1
      else 0

/-- Every finite prefix of the deterministic contraction run preserves a
globally zero distance function. This is a statement about the distance state,
independent of which tied pair the lexicographic selector chooses. -/
theorem njRunFuel_distance_eq_zero_of_eq_zero {n : ℕ}
    (fuel : ℕ) (s : NJState n) (hInv : njFreshInvariant s)
    (hZero : ∀ a b, s.distance a b = 0) :
    ∀ a b, (njRunFuel fuel s hInv).distance a b = 0 := by
  induction fuel generalizing s with
  | zero =>
      simpa [njRunFuel] using hZero
  | succ fuel ih =>
      simp only [njRunFuel]
      split
      · rename_i hCard
        apply ih (njSelectedContractState s hCard)
          (njSelectedContractState_preserves_freshInvariant s hInv hCard)
        intro a b
        change (njContractState s (njSelectedPair s (by omega)).1
          (njSelectedPair s (by omega)).2).distance a b = 0
        exact njContractState_distance_eq_zero_of_eq_zero s
          (njSelectedPair s (by omega)).1 (njSelectedPair s (by omega)).2
          hZero a b
      · exact hZero

/-- If an initial state has globally zero distances, every active pair at the
end of any bounded run has score zero. Thus the score criterion remains
indeterminate at every contraction depth. -/
theorem njRunFuel_qScore_eq_zero_of_eq_zero_distances {n : ℕ}
    (fuel : ℕ) (s : NJState n) (hInv : njFreshInvariant s)
    (hZero : ∀ a b, s.distance a b = 0)
    {i j : NJNode n}
    (hi : i ∈ (njRunFuel fuel s hInv).active)
    (hj : j ∈ (njRunFuel fuel s hInv).active) :
    njQScore (njRunFuel fuel s hInv) i j = 0 := by
  apply njQScore_eq_zero_of_active_zero_distances
    (njRunFuel fuel s hInv) ?_ hi hj
  intro a _ b _
  exact njRunFuel_distance_eq_zero_of_eq_zero fuel s hInv hZero a b

/-- With identical profiles, every active pair has zero NJ score after any
bounded number of deterministic contractions. The theorem captures persistent
score ambiguity, not uniqueness or correctness of a chosen tree topology. -/
theorem njRunFuel_qScore_eq_zero_of_identical_profiles
    {taxaCount markerCount : ℕ} {State : Type*} [DecidableEq State]
    (profiles : Fin taxaCount → Fin markerCount → State)
    (hProfiles : ∀ i j, profiles i = profiles j)
    (fuel : ℕ) {i j : NJNode taxaCount}
    (hi : i ∈ (njRunFuel fuel
      (njInitialStateFromMatrix
        (fun a b => mismatchFraction (profiles a) (profiles b)))
      (njInitialState_freshInvariant _)).active)
    (hj : j ∈ (njRunFuel fuel
      (njInitialStateFromMatrix
        (fun a b => mismatchFraction (profiles a) (profiles b)))
      (njInitialState_freshInvariant _)).active) :
    njQScore (njRunFuel fuel
      (njInitialStateFromMatrix
        (fun a b => mismatchFraction (profiles a) (profiles b)))
      (njInitialState_freshInvariant _)) i j = 0 := by
  apply njRunFuel_qScore_eq_zero_of_eq_zero_distances fuel _ _ ?_ hi hj
  exact njInitialStateFromMatrix_distance_eq_zero_of_identical_profiles
    profiles hProfiles

/-- Every finite recursive prefix preserves the fact that all accumulated NJ
branches have zero length when the initial distances are globally zero. -/
theorem njRunFuel_edgesZeroLength_of_eq_zero_distances {n : ℕ}
    (fuel : ℕ) (s : NJState n) (hInv : njFreshInvariant s)
    (hZero : ∀ a b, s.distance a b = 0)
    (hEdges : njEdgesZeroLength s.edges) :
    njEdgesZeroLength (njRunFuel fuel s hInv).edges := by
  induction fuel generalizing s hInv hZero hEdges with
  | zero => simpa [njRunFuel] using hEdges
  | succ fuel ih =>
      simp only [njRunFuel]
      split
      · rename_i hCard
        apply ih (njSelectedContractState s hCard)
          (njSelectedContractState_preserves_freshInvariant s hInv hCard)
        · exact njContractState_distance_eq_zero_of_eq_zero s
            (njSelectedPair s (by omega)).1 (njSelectedPair s (by omega)).2
            hZero
        · exact njSelectedContractState_edgesZeroLength s hCard hZero hEdges
      · exact hEdges

/-- The terminal three-taxon finish adds only zero-length branches when the
state has zero pairwise distances. -/
theorem njFinishThree_edgesZeroLength_of_eq_zero_distances {n : ℕ}
    (s : NJState n) (hZero : ∀ a b, s.distance a b = 0)
    (hEdges : njEdgesZeroLength s.edges) (a b c : NJNode n) :
    njEdgesZeroLength (njFinishThree s a b c) := by
  simp only [njFinishThree, njEdgesZeroLength, List.forall_append]
  refine ⟨hEdges, ?_⟩
  simp [njFinalLimbA, njFinalLimbB, njFinalLimbC,
    hZero a b, hZero a c, hZero b c]

/-- Recursive execution preserves canonical lexical endpoint ordering in
every accumulated edge. -/
theorem njRunFuel_edgesCanonical {n : ℕ} (fuel : ℕ) (s : NJState n)
    (hInv : njFreshInvariant s) (hEdges : njEdgesCanonical s.edges) :
    njEdgesCanonical (njRunFuel fuel s hInv).edges := by
  induction fuel generalizing s with
  | zero => simpa [njRunFuel] using hEdges
  | succ fuel ih =>
      simp only [njRunFuel]
      split
      · rename_i hCard
        exact ih (njSelectedContractState s (by omega))
          (njSelectedContractState_preserves_freshInvariant s hInv (by omega))
          (njSelectedContractState_edgesCanonical s (by omega) hEdges)
      · exact hEdges

/-- Recursive execution preserves the absence of self-loops in every
accumulated edge. -/
theorem njRunFuel_edgesNoLoop {n : ℕ} (fuel : ℕ) (s : NJState n)
    (hInv : njFreshInvariant s) (hEdges : njEdgesNoLoop s.edges) :
    njEdgesNoLoop (njRunFuel fuel s hInv).edges := by
  induction fuel generalizing s with
  | zero => simpa [njRunFuel] using hEdges
  | succ fuel ih =>
      simp only [njRunFuel]
      split
      · rename_i hCard
        exact ih (njSelectedContractState s (by omega))
          (njSelectedContractState_preserves_freshInvariant s hInv (by omega))
          (njSelectedContractState_edgesNoLoop s hInv (by omega) hEdges)
      · exact hEdges

theorem njRunFuel_preserves_freshInvariant {n : ℕ} (fuel : ℕ)
    (s : NJState n) (hInv : njFreshInvariant s) :
    njFreshInvariant (njRunFuel fuel s hInv) := by
  induction fuel generalizing s with
  | zero => simpa [njRunFuel] using hInv
  | succ fuel ih =>
      simp only [njRunFuel]
      split
      · rename_i hCard
        exact ih (njSelectedContractState s (by omega))
          (njSelectedContractState_preserves_freshInvariant s hInv (by omega))
      · exact hInv

/-- Every recursive contraction contributes exactly two accumulated edges. -/
theorem njRunFuel_edge_count {n : ℕ} (fuel : ℕ) (s : NJState n)
    (hInv : njFreshInvariant s) :
    (njRunFuel fuel s hInv).edges.length =
      s.edges.length + 2 * njRunFuelJoinCount fuel s hInv := by
  induction fuel generalizing s with
  | zero => simp [njRunFuel, njRunFuelJoinCount]
  | succ fuel ih =>
      simp only [njRunFuel, njRunFuelJoinCount]
      split
      · rename_i hCard
        have hEdge : (njJoinState s
            (njSelectedPair s (by omega)).1 (njSelectedPair s (by omega)).2).edges.length =
              s.edges.length + 2 := by
          simp [njJoinState, njContractState, List.length_append]
        simp only [njSelectedContractState]
        rw [ih]
        rw [hEdge]
        omega
      · simp

/-- If the fuel is at least the number of active nodes, repeated NJ
contraction reaches the three-taxon stage used for the final unrooted join. -/
theorem njRunFuel_terminal {n : ℕ} (fuel : ℕ) (s : NJState n)
    (hInv : njFreshInvariant s) (hFuel : s.active.card ≤ fuel + 3) :
    (njRunFuel fuel s hInv).active.card ≤ 3 := by
  induction fuel generalizing s with
  | zero =>
      simp [njRunFuel]
      omega
  | succ fuel ih =>
      rw [njRunFuel]
      split
      · rename_i hCard
        have hStep := njSelectedContractState_card s hInv (by omega)
        have hInv' := njSelectedContractState_preserves_freshInvariant s hInv (by omega)
        have hFuel' : (njSelectedContractState s (by omega)).active.card ≤ fuel + 3 := by
          have hFuelBound := hFuel
          omega
        exact ih (njSelectedContractState s (by omega)) hInv' hFuel'
      · omega

/-- Contraction never passes below the three-taxon stopping threshold. -/
theorem njRunFuel_lower_bound {n : ℕ} (fuel : ℕ) (s : NJState n)
    (hInv : njFreshInvariant s) (hLower : 3 ≤ s.active.card) :
    3 ≤ (njRunFuel fuel s hInv).active.card := by
  induction fuel generalizing s with
  | zero => simpa [njRunFuel] using hLower
  | succ fuel ih =>
      rw [njRunFuel]
      split
      · rename_i hCard
        have hStep := njSelectedContractState_card s hInv (by omega)
        have hInv' := njSelectedContractState_preserves_freshInvariant s hInv (by omega)
        have hLower' : 3 ≤ (njSelectedContractState s (by omega)).active.card := by
          omega
        exact ih (njSelectedContractState s (by omega)) hInv' hLower'
      · omega

/-- With enough fuel and at least three initial taxa, recursion stops at
exactly three active nodes, matching the source Neighbor-Joining loop. -/
theorem njRunFuel_active_card_three {n : ℕ} (fuel : ℕ) (s : NJState n)
    (hInv : njFreshInvariant s) (hLower : 3 ≤ s.active.card)
    (hFuel : s.active.card ≤ fuel + 3) :
    (njRunFuel fuel s hInv).active.card = 3 := by
  exact Nat.le_antisymm
    (njRunFuel_terminal fuel s hInv hFuel)
    (njRunFuel_lower_bound fuel s hInv hLower)

/-- Under the same stopping bounds, the number of binary joins is exactly the
initial excess number of taxa above the terminal three. -/
theorem njRunFuel_join_count {n : ℕ} (fuel : ℕ) (s : NJState n)
    (hInv : njFreshInvariant s) (hLower : 3 ≤ s.active.card)
    (hFuel : s.active.card ≤ fuel + 3) :
    njRunFuelJoinCount fuel s hInv + 3 = s.active.card := by
  induction fuel generalizing s with
  | zero =>
      simp only [njRunFuelJoinCount, Nat.zero_add]
      have hUpper : s.active.card ≤ 3 := by simpa using hFuel
      have hCard : s.active.card = 3 := Nat.le_antisymm hUpper hLower
      exact hCard.symm
  | succ fuel ih =>
      simp only [njRunFuelJoinCount]
      split
      · rename_i hCard
        have hStep := njSelectedContractState_card s hInv (by omega)
        have hInv' := njSelectedContractState_preserves_freshInvariant s hInv (by omega)
        have hLower' : 3 ≤ (njSelectedContractState s (by omega)).active.card := by
          omega
        have hFuel' : (njSelectedContractState s (by omega)).active.card ≤ fuel + 3 := by
          omega
        have hCount := ih (njSelectedContractState s (by omega)) hInv' hLower' hFuel'
        omega
      · omega

/-- After appending the terminal three-taxon star, the accumulated edge count
is the prior count plus two edges per recursive join and three terminal edges. -/
theorem njRunFuel_finished_edge_count {n : ℕ} (fuel : ℕ) (s : NJState n)
    (hInv : njFreshInvariant s) (a b c : NJNode n) :
    (njFinishThree (njRunFuel fuel s hInv) a b c).length =
      s.edges.length + 2 * njRunFuelJoinCount fuel s hInv + 3 := by
  simp only [njFinishThree, List.length_append, List.length_cons, List.length_nil]
  rw [njRunFuel_edge_count]

/-- Given enough fuel and at least three active taxa, finishing the run uses
exactly two edges per contraction plus the three terminal-star edges. -/
theorem njRunFuel_tree_edge_count {n : ℕ} (fuel : ℕ) (s : NJState n)
    (hInv : njFreshInvariant s) (hLower : 3 ≤ s.active.card)
    (hFuel : s.active.card ≤ fuel + 3) (a b c : NJNode n) :
    (njFinishThree (njRunFuel fuel s hInv) a b c).length =
      s.edges.length + 2 * (s.active.card - 3) + 3 := by
  rw [njRunFuel_finished_edge_count]
  have hJoins := njRunFuel_join_count fuel s hInv hLower hFuel
  omega

/-- For `n ≥ 3` input leaves and an empty initial edge list, appending three
terminal branches gives `2n - 3` edges. The following existence theorem
chooses three distinct nodes from the actual terminal active set. -/
theorem njInitialState_finished_edge_count {n : ℕ}
    (d : NJNode n → NJNode n → ℚ) (hn : 3 ≤ n)
    (a b c : NJNode n) :
    (njFinishThree
      (njRunFuel n (njInitialState d) (njInitialState_freshInvariant d)) a b c).length =
        2 * n - 3 := by
  have hCard := njInitialState_active_card d
  have hLower : 3 ≤ (njInitialState d).active.card := by
    rw [njInitialState_active_card]
    exact hn
  have hFuel : (njInitialState d).active.card ≤ n + 3 := by omega
  rw [njRunFuel_tree_edge_count n (njInitialState d)
    (njInitialState_freshInvariant d) hLower hFuel a b c]
  rw [njInitialState_active_card]
  simp only [njInitialState, List.length_nil, Nat.zero_add]
  omega

/-- The recursively produced terminal state supplies three distinct active
taxa, and finishing on those taxa yields the expected unrooted edge count. -/
theorem njInitialState_finishes_on_terminal_taxa {n : ℕ}
    (d : NJNode n → NJNode n → ℚ) (hn : 3 ≤ n) :
    ∃ a b c : NJNode n,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a ∈ (njRunFuel n (njInitialState d) (njInitialState_freshInvariant d)).active ∧
      b ∈ (njRunFuel n (njInitialState d) (njInitialState_freshInvariant d)).active ∧
      c ∈ (njRunFuel n (njInitialState d) (njInitialState_freshInvariant d)).active ∧
      (njFinishThree
        (njRunFuel n (njInitialState d) (njInitialState_freshInvariant d)) a b c).length =
          2 * n - 3 := by
  have hLower : 3 ≤ (njInitialState d).active.card := by
    rw [njInitialState_active_card]
    exact hn
  have hFuel : (njInitialState d).active.card ≤ n + 3 := by
    rw [njInitialState_active_card]
    omega
  have hFinalCard := njRunFuel_active_card_three n (njInitialState d)
    (njInitialState_freshInvariant d) hLower hFuel
  rcases Finset.card_eq_three.mp hFinalCard with
    ⟨a, b, c, hab, hac, hbc, hActive⟩
  refine ⟨a, b, c, hab, hac, hbc, ?_, ?_, ?_, ?_⟩
  · rw [hActive]
    simp
  · rw [hActive]
    simp
  · rw [hActive]
    simp
  · exact njInitialState_finished_edge_count d hn a b c

/-- The actual recursive export, finished on its terminal active taxa, has
canonically ordered undirected edges and no self-loops. -/
theorem njInitialState_terminal_edges_valid {n : ℕ}
    (d : NJNode n → NJNode n → ℚ) (hn : 3 ≤ n) :
    ∃ a b c : NJNode n,
      a ∈ (njRunFuel n (njInitialState d) (njInitialState_freshInvariant d)).active ∧
      b ∈ (njRunFuel n (njInitialState d) (njInitialState_freshInvariant d)).active ∧
      c ∈ (njRunFuel n (njInitialState d) (njInitialState_freshInvariant d)).active ∧
      njEdgesCanonical (njFinishThree
        (njRunFuel n (njInitialState d) (njInitialState_freshInvariant d)) a b c) ∧
      njEdgesNoLoop (njFinishThree
        (njRunFuel n (njInitialState d) (njInitialState_freshInvariant d)) a b c) := by
  have hLower : 3 ≤ (njInitialState d).active.card := by
    rw [njInitialState_active_card]
    exact hn
  have hFuel : (njInitialState d).active.card ≤ n + 3 := by
    rw [njInitialState_active_card]
    omega
  have hFinalCard := njRunFuel_active_card_three n (njInitialState d)
    (njInitialState_freshInvariant d) hLower hFuel
  rcases Finset.card_eq_three.mp hFinalCard with
    ⟨a, b, c, _, _, _, hActive⟩
  have hInv := njRunFuel_preserves_freshInvariant n (njInitialState d)
    (njInitialState_freshInvariant d)
  have hEdgesC := njRunFuel_edgesCanonical n (njInitialState d)
    (njInitialState_freshInvariant d) (by simp [njInitialState, njEdgesCanonical])
  have hEdgesN := njRunFuel_edgesNoLoop n (njInitialState d)
    (njInitialState_freshInvariant d) (by simp [njInitialState, njEdgesNoLoop])
  refine ⟨a, b, c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hActive]
    simp
  · rw [hActive]
    simp
  · rw [hActive]
    simp
  · exact (njFinishThree_active_edges_valid _ hInv a b c
      (by rw [hActive]; simp) (by rw [hActive]; simp) (by rw [hActive]; simp)
      hEdgesC hEdgesN).1
  · exact (njFinishThree_active_edges_valid _ hInv a b c
      (by rw [hActive]; simp) (by rw [hActive]; simp) (by rw [hActive]; simp)
      hEdgesC hEdgesN).2

/-- If all declaration profiles coincide, the Neighbor-Joining export on at
least three taxa has terminal active taxa and every emitted branch has zero
length. This is the exact finite output consequence of identical input
characters; it makes no claim about uniqueness of the resulting topology. -/
theorem njInitialState_identical_profiles_zero_length_export
    {taxaCount markerCount : ℕ} {State : Type*} [DecidableEq State]
    (profiles : Fin taxaCount → Fin markerCount → State)
    (hProfiles : ∀ i j, profiles i = profiles j) (hTaxa : 3 ≤ taxaCount) :
    ∃ a b c : NJNode taxaCount,
      a ∈ (njRunFuel taxaCount
        (njInitialStateFromMatrix
          (fun i j => mismatchFraction (profiles i) (profiles j)))
        (njInitialState_freshInvariant _)).active ∧
      b ∈ (njRunFuel taxaCount
        (njInitialStateFromMatrix
          (fun i j => mismatchFraction (profiles i) (profiles j)))
        (njInitialState_freshInvariant _)).active ∧
      c ∈ (njRunFuel taxaCount
        (njInitialStateFromMatrix
          (fun i j => mismatchFraction (profiles i) (profiles j)))
        (njInitialState_freshInvariant _)).active ∧
      njEdgesZeroLength (njFinishThree
        (njRunFuel taxaCount
          (njInitialStateFromMatrix
            (fun i j => mismatchFraction (profiles i) (profiles j)))
          (njInitialState_freshInvariant _)) a b c) := by
  let d : Fin taxaCount → Fin taxaCount → ℚ :=
    fun i j => mismatchFraction (profiles i) (profiles j)
  let s : NJState taxaCount := njInitialStateFromMatrix d
  have hZero : ∀ a b, s.distance a b = 0 := by
    exact njInitialStateFromMatrix_distance_eq_zero_of_identical_profiles
      profiles hProfiles
  obtain ⟨a, b, c, _, _, _, ha, hb, hc, _⟩ :=
    njInitialState_finishes_on_terminal_taxa (njInitialDistance d) hTaxa
  have ha' : a ∈ (njRunFuel taxaCount s
      (njInitialState_freshInvariant (njInitialDistance d))).active := by
    simpa [s, njInitialStateFromMatrix] using ha
  have hb' : b ∈ (njRunFuel taxaCount s
      (njInitialState_freshInvariant (njInitialDistance d))).active := by
    simpa [s, njInitialStateFromMatrix] using hb
  have hc' : c ∈ (njRunFuel taxaCount s
      (njInitialState_freshInvariant (njInitialDistance d))).active := by
    simpa [s, njInitialStateFromMatrix] using hc
  have hRunZero := njRunFuel_distance_eq_zero_of_eq_zero taxaCount s
    (njInitialState_freshInvariant (njInitialDistance d)) hZero
  have hRunEdges := njRunFuel_edgesZeroLength_of_eq_zero_distances taxaCount s
    (njInitialState_freshInvariant (njInitialDistance d)) hZero (by
      change njEdgesZeroLength (njInitialState (njInitialDistance d)).edges
      simp [njEdgesZeroLength, njInitialState])
  have hFinished := njFinishThree_edgesZeroLength_of_eq_zero_distances
    (njRunFuel taxaCount s (njInitialState_freshInvariant (njInitialDistance d)))
    hRunZero hRunEdges a b c
  exact ⟨a, b, c, ha', hb', hc', hFinished⟩

/-- The state contraction carries forward symmetry of the distance matrix. -/
theorem njContractState_distance_symm {n : ℕ} (s : NJState n)
    (hSymm : ∀ a b, s.distance a b = s.distance b a)
    (i j : NJNode n) :
    ∀ a b, (njContractState s i j).distance a b =
      (njContractState s i j).distance b a := by
  intro a b
  exact njContractDistance_symm s.distance hSymm i j
    (njInternal s.nextInternal) a b

/-- A deterministic pair join preserves symmetry of the active distance
matrix, so the recursive Neighbor-Joining run remains unrooted at every step. -/
theorem njSelectedContractState_distance_symm {n : ℕ} (s : NJState n)
    (hSymm : ∀ a b, s.distance a b = s.distance b a)
    (hCard : 3 < s.active.card) :
    ∀ a b,
      (njSelectedContractState s hCard).distance a b =
        (njSelectedContractState s hCard).distance b a := by
  intro a b
  exact njContractDistance_symm s.distance hSymm
    (njSelectedPair s (by omega)).1 (njSelectedPair s (by omega)).2
    (njInternal s.nextInternal) a b

/-- The distance update retains a zero diagonal. -/
theorem njContractState_distance_diag {n : ℕ} (s : NJState n)
    (hDiag : ∀ a, s.distance a a = 0) (i j : NJNode n) :
    ∀ a, (njContractState s i j).distance a a = 0 := by
  intro a
  exact njContractDistance_diag s.distance hDiag i j
    (njInternal s.nextInternal) a

/-- Deterministic contractions preserve the zero-diagonal distance invariant. -/
theorem njSelectedContractState_distance_diag {n : ℕ} (s : NJState n)
    (hDiag : ∀ a, s.distance a a = 0) (hCard : 3 < s.active.card) :
    ∀ a, (njSelectedContractState s hCard).distance a a = 0 := by
  intro a
  exact njContractDistance_diag s.distance hDiag
    (njSelectedPair s (by omega)).1 (njSelectedPair s (by omega)).2
    (njInternal s.nextInternal) a

/-- The recursive run preserves symmetry and the zero diagonal of its exact
rational distance matrix. Negative reduced distances remain permitted. -/
theorem njRunFuel_preserves_distance_laws {n : ℕ} (fuel : ℕ)
    (s : NJState n) (hInv : njFreshInvariant s)
    (hSymm : ∀ a b, s.distance a b = s.distance b a)
    (hDiag : ∀ a, s.distance a a = 0) :
    (∀ a b, (njRunFuel fuel s hInv).distance a b =
      (njRunFuel fuel s hInv).distance b a) ∧
    (∀ a, (njRunFuel fuel s hInv).distance a a = 0) := by
  induction fuel generalizing s hInv with
  | zero => simpa [njRunFuel] using And.intro hSymm hDiag
  | succ fuel ih =>
      rw [njRunFuel]
      split
      · rename_i hCard
        have hInv' := njSelectedContractState_preserves_freshInvariant s hInv hCard
        have hSymm' := njSelectedContractState_distance_symm s hSymm hCard
        have hDiag' := njSelectedContractState_distance_diag s hDiag hCard
        exact ih (njSelectedContractState s hCard) hInv' hSymm' hDiag'
      · exact ⟨hSymm, hDiag⟩

end InfoGeometry.Graph.CategoricalCharacterDistance
