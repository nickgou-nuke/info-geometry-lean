import InfoGeometry.Routing.BirkhoffVonNeumann
import InfoGeometry.Canonical.AttentionPolarizedGibbsBridge
import InfoGeometry.Canonical.SinkhornFoundation

/-!
# Polarized Split Attention and Sinkhorn Balance

This module packages the positive-sheet split attention Gibbs family as a finite
weight matrix and identifies its row-stochastic and doubly-stochastic closures.
-/

namespace InfoGeometry.Canonical.Attention

open InfoGeometry.GrandCanonical
open scoped BigOperators

section Matrix

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance polarizedSinkhornFinNonempty : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩

/-- Row-indexed polarized split attention matrix over a finite family of queries. -/
noncomputable def polarizedPlusAttentionMatrix
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => polarizedPlusAttentionWeights (E := E) (V := V) (queries i) ctx β j

omit [AddCommMonoid V] [Module ℝ V] [Fact (0 < n)] in
@[simp] theorem polarizedPlusAttentionMatrix_apply
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) (i j : Fin n) :
    polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j
      = polarizedPlusAttentionWeights (E := E) (V := V) (queries i) ctx β j := rfl

-- theorem-class: bridge
/-- Each entry of the polarized split attention matrix is a Gibbs weight for the row query. -/
@[simp] theorem polarizedPlusAttentionMatrix_apply_eq_gibbsWeight
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) (i j : Fin n) :
    polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j
      = gibbsWeight (polarizedPlusParams (E := E) (V := V) (queries i) ctx) β j := by
  rw [polarizedPlusAttentionMatrix_apply]
  exact (gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights
    (E := E) (V := V) (q := queries i) (ctx := ctx) (β := β) (i := j)).symm

-- theorem-class: closure
/-- The polarized split attention matrix has nonnegative entries. -/
theorem polarizedPlusAttentionMatrix_nonneg
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) (i j : Fin n) :
    0 ≤ polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j := by
  rw [polarizedPlusAttentionMatrix_apply_eq_gibbsWeight (E := E) (V := V)
    (queries := queries) (ctx := ctx) (β := β) (i := i) (j := j)]
  exact gibbsWeight_nonneg (polarizedPlusParams (E := E) (V := V) (queries i) ctx) β j

-- theorem-class: closure
/-- Every query row of the polarized split attention matrix is normalized. -/
theorem polarizedPlusAttentionMatrix_row_sum_one
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) (i : Fin n) :
    ∑ j : Fin n, polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j = 1 := by
  simpa [polarizedPlusAttentionMatrix] using
    gibbsWeight_sum_one (polarizedPlusParams (E := E) (V := V) (queries i) ctx) β

-- theorem-class: closure
/-- The polarized split attention matrix is row-stochastic by Gibbs normalization. -/
theorem polarizedPlusAttentionMatrix_mem_rowStochastic
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) :
    polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β ∈ Matrix.rowStochastic ℝ (Fin n) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i j
    exact polarizedPlusAttentionMatrix_nonneg (E := E) (V := V) queries ctx β i j
  · intro i
    exact polarizedPlusAttentionMatrix_row_sum_one (E := E) (V := V) queries ctx β i

-- theorem-class: closure
/--
If the polarized split attention matrix also satisfies column balance, then it
is doubly stochastic.
-/
theorem polarizedPlusAttentionMatrix_mem_doublyStochastic
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (hcol : ∀ j : Fin n,
      ∑ i : Fin n, polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j = 1) :
    polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact polarizedPlusAttentionMatrix_nonneg (E := E) (V := V) queries ctx β i j
  · intro i
    exact polarizedPlusAttentionMatrix_row_sum_one (E := E) (V := V) queries ctx β i
  · intro j
    exact hcol j

-- theorem-class: closure
/--
A column-balanced polarized split attention matrix admits a Birkhoff-von Neumann
permutation decomposition.
-/
theorem exists_perm_decomposition_of_bistochastic_polarizedPlusAttention
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (hcol : ∀ j : Fin n,
      ∑ i : Fin n, polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j = 1) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • σ.permMatrix ℝ
        = polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β := by
  exact exists_eq_sum_perm_of_mem_doublyStochastic
    (M := polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_mem_doublyStochastic
      (E := E) (V := V) queries ctx β hcol)

-- theorem-class: closure
omit [Fact (0 < n)] in
/-- Every permutation routing matrix is doubly stochastic. -/
theorem permMatrix_mem_doublyStochastic
    (σ : Equiv.Perm (Fin n)) :
    σ.permMatrix ℝ ∈ doublyStochastic ℝ (Fin n) := by
  simpa using (Matrix.permMatrix_mem_doublyStochastic (R := ℝ) (n := Fin n) (σ := σ))

-- theorem-class: closure
omit [Fact (0 < n)] in
/-- The doubly stochastic routing polytope is the convex hull of permutation matrices. -/
theorem doublyStochastic_eq_convexHull_permMatrix' :
    (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)) =
      convexHull ℝ {x | ∃ σ : Equiv.Perm (Fin n), σ.permMatrix ℝ = x} := by
  simpa using (doublyStochastic_eq_convexHull_permMatrix (R := ℝ) (n := Fin n))

/--
The positive cone generated by permutation matrices, represented as the set of
nonnegative linear combinations of permutation matrices.
-/
abbrev permMatrixCone : Set (Matrix (Fin n) (Fin n) ℝ) :=
  BirkhoffRouting.permMatrixCone

@[simp] theorem mem_permMatrixCone_iff
    (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ permMatrixCone (n := n) ↔
      ∃ w : Equiv.Perm (Fin n) → ℝ,
        (∀ σ, 0 ≤ w σ) ∧
        ∑ σ, w σ • σ.permMatrix ℝ = M := by
  simpa [permMatrixCone] using
    (BirkhoffRouting.mem_permMatrixCone_iff (n := n) M)

/-- Every permutation matrix lies in the generated positive cone. -/
theorem permMatrix_mem_permMatrixCone
    (σ : Equiv.Perm (Fin n)) :
    σ.permMatrix ℝ ∈ permMatrixCone (n := n) := by
  simpa [permMatrixCone] using
    (BirkhoffRouting.permMatrix_mem_permMatrixCone (n := n) σ)

/-- Every doubly stochastic matrix lies in the generated positive cone. -/
theorem doublyStochastic_mem_permMatrixCone
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    M ∈ permMatrixCone (n := n) := by
  simpa [permMatrixCone] using
    (BirkhoffRouting.doublyStochastic_mem_permMatrixCone (n := n) M hM)

end Matrix

end InfoGeometry.Canonical.Attention
