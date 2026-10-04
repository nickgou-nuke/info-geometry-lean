import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Tactic

/-!
# E8 Root Lattice Decomposition

Following the Colimit Continuum Mandate, we define the purely algebraic root
decomposition of the E8 lattice in $\mathbb{Q}^8$. The 240 roots decompose cleanly into:
1. 112 roots of the D8 sublattice (norm 2, permutations of (±1, ±1, 0, 0, 0, 0, 0, 0)).
2. 128 spinor roots (norm 2, coordinates ±1/2 with an even number of minus signs).

No physical rhetoric or analytical continuations are used.

This file proves the finite coordinate-set facts (cardinality, disjointness,
and squared norm). It does not construct a Clifford module or identify these
roots with a Clifford-algebra basis. In the usual `D₈` branching, the 128
half-integral roots are weights of a half-spin representation of `Spin(16)`;
the relevant Clifford algebra for that representation is on a 16-dimensional
quadratic space, not `Cl(8)`.
-/

namespace InfoGeometry.Canonical.E8RootDecomposition

open scoped BigOperators

/-- Canonical dot product in 8D rational space. -/
def e8Dot (u v : Fin 8 → ℚ) : ℚ := ∑ i, u i * v i

/-- Canonical squared norm in 8D rational space. -/
def e8NormSq (v : Fin 8 → ℚ) : ℚ := e8Dot v v

/-- Base coordinate choices for D8 roots. -/
def D8Base : Finset ℚ := {-1, 0, 1}

/-- The ambient bounding space for D8 roots. -/
def D8Candidates : Finset (Fin 8 → ℚ) := Fintype.piFinset (fun _ => D8Base)

/-- The 112 roots of the D8 sublattice. Formally defined as all vectors
    in the candidate space that satisfy the exact squared norm of 2. -/
def D8Roots : Finset (Fin 8 → ℚ) := D8Candidates.filter (fun v => e8NormSq v = 2)

/-- Base coordinate choices for the Spinor roots. -/
def SpinorBase : Finset ℚ := {1/2, -1/2}

/-- The ambient bounding space for Spinor roots (size 256). -/
def SpinorCandidates : Finset (Fin 8 → ℚ) := Fintype.piFinset (fun _ => SpinorBase)

/-- The 128 spinor roots. Formally defined by the parity chiral condition:
    an even number of minus signs exactly corresponds to their product being positive. -/
def SpinorRoots : Finset (Fin 8 → ℚ) := SpinorCandidates.filter (fun v => (∏ i, v i) > 0)

/-- The complete finite combinatorial E8 root set (112 + 128 = 240). -/
def E8Roots : Finset (Fin 8 → ℚ) := D8Roots ∪ SpinorRoots

/-- Prove that all spinor roots have exactly squared norm 2. -/
theorem spinor_roots_norm (v : Fin 8 → ℚ) (hv : v ∈ SpinorRoots) : e8NormSq v = 2 := by
  have h_cand : v ∈ SpinorCandidates := Finset.mem_of_mem_filter v hv
  dsimp [e8NormSq, e8Dot]
  have h_sq : ∀ i, v i * v i = 1/4 := by
    intro i
    have h1 : v ∈ Fintype.piFinset (fun _ => SpinorBase) := h_cand
    have hi : v i ∈ SpinorBase := Fintype.mem_piFinset.mp h1 i
    dsimp [SpinorBase] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    cases hi with
    | inl h => rw [h]; norm_num
    | inr h => rw [h]; norm_num
  have h_sum : (∑ i : Fin 8, v i * v i) = ∑ i : Fin 8, (1/4 : ℚ) := Finset.sum_congr rfl (fun i _ => h_sq i)
  rw [h_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- Every vector in the filtered `D₈` set has squared norm two. -/
theorem d8_roots_norm (v : Fin 8 → ℚ) (hv : v ∈ D8Roots) :
    e8NormSq v = 2 := by
  exact Finset.mem_filter.mp hv |>.2

/-- The coordinate-root sector has the expected cardinality.  The finite
computation is over the explicit `3^8` candidate box, not an assumed count. -/
theorem d8_roots_card : D8Roots.card = 112 := by
  native_decide

/-- The positive-chirality half-integral sector has 128 elements. -/
theorem spinor_roots_card : SpinorRoots.card = 128 := by
  native_decide

/-- The two coordinate descriptions of roots are disjoint: integral
coordinates cannot equal half-integral coordinates. -/
theorem d8Roots_disjoint_spinorRoots : Disjoint D8Roots SpinorRoots := by
  native_decide

/-- The explicit rational-coordinate root set has 240 elements, split into
112 `D₈` roots and 128 positive-chirality spinor roots. -/
theorem e8_roots_card : E8Roots.card = 240 := by
  rw [E8Roots, Finset.card_union_of_disjoint d8Roots_disjoint_spinorRoots,
    d8_roots_card, spinor_roots_card]

/-- Every element of the explicitly constructed root set has squared norm 2. -/
theorem e8_roots_norm (v : Fin 8 → ℚ) (hv : v ∈ E8Roots) :
    e8NormSq v = 2 := by
  rw [E8Roots, Finset.mem_union] at hv
  rcases hv with hD | hS
  · exact d8_roots_norm v hD
  · exact spinor_roots_norm v hS

/-! ### Rational Weyl reflections -/

/-- The reflection in a vector `α` of squared norm two. -/
def e8Reflection (α v : Fin 8 → ℚ) : Fin 8 → ℚ :=
  v - (e8Dot v α) • α

theorem e8Dot_comm (u v : Fin 8 → ℚ) : e8Dot u v = e8Dot v u := by
  simp [e8Dot, mul_comm]

theorem e8Dot_add_left (u v w : Fin 8 → ℚ) :
    e8Dot (u + v) w = e8Dot u w + e8Dot v w := by
  simp [e8Dot, add_mul, Finset.sum_add_distrib]

theorem e8Dot_sub_left (u v w : Fin 8 → ℚ) :
    e8Dot (u - v) w = e8Dot u w - e8Dot v w := by
  simp [e8Dot, sub_mul, Finset.sum_sub_distrib]

theorem e8Dot_smul_left (c : ℚ) (u v : Fin 8 → ℚ) :
    e8Dot (c • u) v = c * e8Dot u v := by
  simp [e8Dot, Finset.mul_sum, mul_assoc]

theorem e8Dot_smul_right (c : ℚ) (u v : Fin 8 → ℚ) :
    e8Dot u (c • v) = c * e8Dot u v := by
  rw [e8Dot_comm, e8Dot_smul_left, e8Dot_comm]

theorem e8Dot_sub_right (u v w : Fin 8 → ℚ) :
    e8Dot u (v - w) = e8Dot u v - e8Dot u w := by
  rw [e8Dot_comm, e8Dot_sub_left, e8Dot_comm v u, e8Dot_comm w u]

theorem e8Dot_reflection_root (α v : Fin 8 → ℚ)
    (hα : e8NormSq α = 2) :
    e8Dot (e8Reflection α v) α = -e8Dot v α := by
  rw [e8Reflection, e8Dot_sub_left, e8Dot_smul_left]
  dsimp [e8NormSq] at hα
  rw [hα]
  ring

/-- A norm-two reflection is an involution on the ambient rational space. -/
theorem e8Reflection_involutive (α v : Fin 8 → ℚ)
    (hα : e8NormSq α = 2) :
    e8Reflection α (e8Reflection α v) = v := by
  rw [e8Reflection, e8Dot_reflection_root α v hα]
  simp only [neg_smul, sub_neg_eq_add]
  ext i
  simp [e8Reflection, Pi.smul_apply]

/-- A norm-two reflection preserves the rational Euclidean pairing. -/
theorem e8Reflection_isometry (α u v : Fin 8 → ℚ)
    (hα : e8NormSq α = 2) :
    e8Dot (e8Reflection α u) (e8Reflection α v) = e8Dot u v := by
  rw [e8Reflection, e8Dot_sub_left, e8Dot_sub_right,
    e8Dot_sub_right, e8Dot_smul_left, e8Dot_smul_right,
    e8Dot_smul_left, e8Dot_smul_right,
    e8Dot_comm α u, e8Dot_comm α v]
  dsimp [e8NormSq] at hα
  rw [hα]
  ring

theorem e8Reflection_preserves_norm (α v : Fin 8 → ℚ)
    (hα : e8NormSq α = 2) :
    e8NormSq (e8Reflection α v) = e8NormSq v := by
  exact e8Reflection_isometry α v v hα

/-- The finite set of all pairings of explicit `E₈` roots. -/
def E8RootPairings : Finset ℚ :=
  E8Roots.biUnion fun α => E8Roots.image (e8Dot α)

/-- All root pairings in the coordinate model are among the five Cartan values. -/
theorem e8_rootPairings_subset_cartanValues :
    E8RootPairings ⊆ ({-2, -1, 0, 1, 2} : Finset ℚ) := by
  native_decide

/-- Pairings between roots of this explicit set are integral Cartan values. -/
theorem e8_roots_pairing_mem (α β : Fin 8 → ℚ)
    (hα : α ∈ E8Roots) (hβ : β ∈ E8Roots) :
    e8Dot α β ∈ ({-2, -1, 0, 1, 2} : Finset ℚ) := by
  apply e8_rootPairings_subset_cartanValues
  simp only [E8RootPairings, Finset.mem_biUnion, Finset.mem_image]
  exact ⟨α, hα, β, hβ, rfl⟩

/-- The finite set of vectors obtained by reflecting roots in roots. -/
def E8RootReflections : Finset (Fin 8 → ℚ) :=
  E8Roots.biUnion fun α => E8Roots.image (e8Reflection α)

/-- The explicit 240-vector set is closed under reflections in each of its
roots; this is the key root-system axiom beyond having norm-two vectors. -/
theorem e8_rootReflections_subset_roots : E8RootReflections ⊆ E8Roots := by
  native_decide

theorem e8_roots_reflection_closed (α β : Fin 8 → ℚ)
    (hα : α ∈ E8Roots) (hβ : β ∈ E8Roots) :
    e8Reflection α β ∈ E8Roots := by
  apply e8_rootReflections_subset_roots
  simp only [E8RootReflections, Finset.mem_biUnion, Finset.mem_image]
  exact ⟨α, hα, β, hβ, rfl⟩

/-! ### The finite reflection action and its generated subgroup

The finite set above gives an actual permutation representation of the
reflection-generated group. This construction is deliberately stated on the
root subtype: it records the action on the 240 roots, without identifying it
with an independently constructed abstract Coxeter presentation.
-/

/-- The carrier of the explicitly enumerated 240 E₈ roots. -/
abbrev E8Root := {v : Fin 8 → ℚ // v ∈ E8Roots}

/-- Reflection in a root, restricted to the finite E₈ root subtype. -/
def e8RootReflection (α : E8Root) : Equiv.Perm E8Root where
  toFun β := ⟨e8Reflection α.1 β.1,
    e8_roots_reflection_closed α.1 β.1 α.2 β.2⟩
  invFun := toFun
  left_inv β := Subtype.ext (e8Reflection_involutive α.1 β.1
    (e8_roots_norm α.1 α.2))
  right_inv β := Subtype.ext (e8Reflection_involutive α.1 β.1
    (e8_roots_norm α.1 α.2))

/-- Each root reflection is an involution as a permutation of the root set. -/
theorem e8RootReflection_sq (α : E8Root) : e8RootReflection α ^ 2 = 1 := by
  ext β
  exact Subtype.ext (e8Reflection_involutive α.1 β.1
    (e8_roots_norm α.1 α.2))

/-- The concrete Weyl action on the E₈ roots: the subgroup of root
permutations generated by all root reflections. -/
def e8WeylGroup : Subgroup (Equiv.Perm E8Root) :=
  Subgroup.closure (Set.range e8RootReflection)

/-- Every root reflection belongs to the concrete reflection-generated group. -/
theorem e8RootReflection_mem_e8WeylGroup (α : E8Root) :
    e8RootReflection α ∈ e8WeylGroup :=
  Subgroup.subset_closure ⟨α, rfl⟩

end InfoGeometry.Canonical.E8RootDecomposition
