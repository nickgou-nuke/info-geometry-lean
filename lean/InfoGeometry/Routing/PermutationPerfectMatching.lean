import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! A finite, graph-level realization of permutation routing.

This owner stops at the exact matching boundary: a permutation graph is shown
to be a perfect matching.  It does not identify arbitrary graph morphisms with
permutations or add a stochastic interpretation.
-/

namespace InfoGeometry.Routing.PermutationPerfectMatching

abbrev Vertex (n : ℕ) := Fin n
abbrev Edge (n : ℕ) := Vertex n × Vertex n

def permutationEdges {n : ℕ} (σ : Equiv.Perm (Vertex n)) : Set (Edge n) :=
  {e | e.2 = σ e.1}

def IsPerfectMatching {n : ℕ} (E : Set (Edge n)) : Prop :=
  (∀ i : Vertex n, ∃! j : Vertex n, (i, j) ∈ E) ∧
  (∀ j : Vertex n, ∃! i : Vertex n, (i, j) ∈ E)

def matrixSupport {n : ℕ} (P : Matrix (Vertex n) (Vertex n) ℝ) : Set (Edge n) :=
  {e | P e.1 e.2 ≠ 0}

theorem permMatrix_support_eq_permutationEdges {n : ℕ}
    (σ : Equiv.Perm (Vertex n)) :
    matrixSupport (σ.permMatrix ℝ) = permutationEdges σ := by
  ext e
  rcases e with ⟨i, j⟩
  simp [matrixSupport, permutationEdges]
  exact eq_comm

theorem permutationEdges_iff_permMatrix_ne_zero {n : ℕ}
    (σ : Equiv.Perm (Vertex n)) (i j : Vertex n) :
    (i, j) ∈ permutationEdges σ ↔ (σ.permMatrix ℝ) i j ≠ 0 := by
  rw [← permMatrix_support_eq_permutationEdges σ]
  rfl

theorem permutationEdges_left_unique {n : ℕ} (σ : Equiv.Perm (Vertex n)) (i : Vertex n)
    {j k : Vertex n} (hj : (i, j) ∈ permutationEdges σ)
    (hk : (i, k) ∈ permutationEdges σ) : j = k := by
  change j = σ i at hj
  change k = σ i at hk
  exact hj.trans hk.symm

theorem permutationEdges_right_unique {n : ℕ} (σ : Equiv.Perm (Vertex n)) (j : Vertex n)
    {i k : Vertex n} (hi : (i, j) ∈ permutationEdges σ)
    (hk : (k, j) ∈ permutationEdges σ) : i = k := by
  change j = σ i at hi
  change j = σ k at hk
  exact σ.injective (hi.symm.trans hk)

theorem permutationEdges_isPerfectMatching {n : ℕ} (σ : Equiv.Perm (Vertex n)) :
    IsPerfectMatching (permutationEdges σ) := by
  constructor
  · intro i
    refine ⟨σ i, ?_, ?_⟩
    · change σ i = σ i
      simp
    · intro j hj
      exact permutationEdges_left_unique σ i hj
        (by change σ i = σ i; simp)
  · intro j
    refine ⟨σ.symm j, ?_, ?_⟩
    · change j = σ (σ.symm j)
      simp
    · intro i hi
      exact permutationEdges_right_unique σ j hi
        (by change j = σ (σ.symm j); simp)

theorem permMatrix_support_isPerfectMatching {n : ℕ}
    (σ : Equiv.Perm (Vertex n)) :
    IsPerfectMatching (matrixSupport (σ.permMatrix ℝ)) := by
  rw [permMatrix_support_eq_permutationEdges σ]
  exact permutationEdges_isPerfectMatching σ

/-! A typed finite routing morphism layer.  This is a permutation category
interface, not yet a declaration-DAG morphism. -/
structure RoutingMorphism (n : ℕ) where
  map : Vertex n ≃ Vertex n

def identityRouting (n : ℕ) : RoutingMorphism n :=
  ⟨Equiv.refl (Vertex n)⟩

def composeRouting {n : ℕ} (g f : RoutingMorphism n) : RoutingMorphism n :=
  ⟨f.map.trans g.map⟩

def routingMatrix {n : ℕ} (f : RoutingMorphism n) :
    Matrix (Vertex n) (Vertex n) ℝ :=
  Equiv.Perm.permMatrix ℝ f.map

@[simp] theorem identityRouting_apply {n : ℕ} (i : Vertex n) :
    (identityRouting n).map i = i := by
  rfl

@[simp] theorem composeRouting_apply {n : ℕ}
    (g f : RoutingMorphism n) (i : Vertex n) :
    (composeRouting g f).map i = g.map (f.map i) := by
  rfl

theorem composeRouting_assoc {n : ℕ}
    (h g f : RoutingMorphism n) :
    composeRouting h (composeRouting g f) =
      composeRouting (composeRouting h g) f := by
  cases h
  cases g
  cases f
  rfl

theorem composeRouting_identity_left {n : ℕ} (f : RoutingMorphism n) :
    composeRouting (identityRouting n) f = f := by
  cases f
  rfl

theorem composeRouting_identity_right {n : ℕ} (f : RoutingMorphism n) :
    composeRouting f (identityRouting n) = f := by
  cases f
  rfl

theorem routingMatrix_support_isPerfectMatching {n : ℕ}
    (f : RoutingMorphism n) :
    IsPerfectMatching (matrixSupport (routingMatrix f)) := by
  simpa [routingMatrix] using permMatrix_support_isPerfectMatching f.map

theorem routingMatrix_identity {n : ℕ} :
    routingMatrix (identityRouting n) = (1 : Matrix (Vertex n) (Vertex n) ℝ) := by
  simp [routingMatrix, identityRouting]

theorem permMatrix_mul_transpose {n : ℕ} (σ : Equiv.Perm (Vertex n)) :
    σ.permMatrix ℝ * Matrix.transpose (σ.permMatrix ℝ) = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul,
    inv_mul_cancel, Matrix.permMatrix_one]

theorem routingMatrix_mul_transpose {n : ℕ} (f : RoutingMorphism n) :
    routingMatrix f * Matrix.transpose (routingMatrix f) = 1 := by
  simpa [routingMatrix] using permMatrix_mul_transpose f.map

/-! The matrix representation uses the standard right-to-left convention of
`Equiv.Perm` multiplication.  This theorem records that convention explicitly
for downstream routing code. -/
theorem permMatrix_mul_composition {n : ℕ}
    (σ τ : Equiv.Perm (Vertex n)) :
    (σ * τ).permMatrix ℝ = τ.permMatrix ℝ * σ.permMatrix ℝ := by
  rw [Matrix.permMatrix_mul]

theorem routingMatrix_compose {n : ℕ}
    (g f : RoutingMorphism n) :
    routingMatrix (composeRouting g f) =
      routingMatrix f * routingMatrix g := by
  unfold routingMatrix composeRouting
  rw [← Equiv.Perm.mul_def]
  exact Matrix.permMatrix_mul (R := ℝ) (n := Vertex n)
    (σ := g.map) (τ := f.map)

end InfoGeometry.Routing.PermutationPerfectMatching
