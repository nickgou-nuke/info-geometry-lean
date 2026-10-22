/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DeterministicArgmaxAttention
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Attention as a convex combination of deterministic routes

The carrier is the actual rectangular attention matrix, not its spectrum.
The deterministic matrices are reused from `DeterministicArgmaxAttention`.
Every nonnegative row-normalized matrix belongs to their convex hull.

The explicit coefficients `routeWeight A f = ∏ i, A i (f i)` select the
independent coupling of the rows. They are a canonical choice of convex
coordinates, NOT a unique linear basis expansion. These weights reconstruct
both the matrix and its action on arbitrary real modules. Forbidden mask
entries force all routes using them to have coefficient zero.

There is no assertion that attention is an idempotent projection, that a
row-stochastic matrix is doubly stochastic, or that this exponential-size
formula is an efficient runtime representation.
-/

namespace InfoGeometry.Routing.AttentionPolytope

open Matrix DeterministicArgmaxAttention
open scoped BigOperators

noncomputable section

variable {n m k : ℕ}

/-- Product of the row probability simplices, including rectangular attention. -/
def attentionPolytope (n m : ℕ) : Set (Matrix (Fin n) (Fin m) ℝ) :=
  {A | (∀ i j, 0 ≤ A i j) ∧ ∀ i, ∑ j, A i j = 1}

/-- The independent coupling of all attention rows, indexed by complete routes. -/
def routeWeight (A : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → Fin m) : ℝ :=
  ∏ i, A i (f i)

lemma routeWeight_nonneg (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (f : Fin n → Fin m) :
    0 ≤ routeWeight A f := by
  exact Finset.prod_nonneg (fun i _ => hA i (f i))

/-- Normalization follows from distributivity, not an assumed mixture witness. -/
theorem routeWeight_sum_one (A : Matrix (Fin n) (Fin m) ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) :
    ∑ f : Fin n → Fin m, routeWeight A f = 1 := by
  unfold routeWeight
  rw [← Fintype.prod_sum (fun (i : Fin n) (j : Fin m) => A i j)]
  simp_rw [hrow]
  simp

/-- The row marginals of the product coupling are exactly the original entries. -/
theorem routeWeight_marginal (A : Matrix (Fin n) (Fin m) ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) (i : Fin n) (j : Fin m) :
    (∑ f : Fin n → Fin m,
      routeWeight A f * deterministicAttention f i j) = A i j := by
  classical
  have factor (f : Fin n → Fin m) :
      routeWeight A f * deterministicAttention f i j =
        ∏ r : Fin n, A r (f r) *
          (if r = i then (if j = f r then (1 : ℝ) else 0) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [routeWeight, deterministicAttention]
  have row_factor (r : Fin n) :
      (∑ c : Fin m, A r c *
        (if r = i then (if j = c then (1 : ℝ) else 0) else 1)) =
          if r = i then A i j else 1 := by
    by_cases h : r = i
    · subst r
      simp
    · simp [h, hrow r]
  simp_rw [factor]
  rw [← Fintype.prod_sum (fun (r : Fin n) (c : Fin m) =>
    A r c * (if r = i then (if j = c then (1 : ℝ) else 0) else 1))]
  simp_rw [row_factor]
  simp

/-- Exact matrix reconstruction from the deterministic routing vertices. -/
theorem reconstruct (A : Matrix (Fin n) (Fin m) ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) :
    (∑ f : Fin n → Fin m, routeWeight A f • deterministicAttention f) = A := by
  ext i j
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
    routeWeight_marginal A hrow i j

lemma deterministic_mem (f : Fin n → Fin m) :
    deterministicAttention f ∈ attentionPolytope n m := by
  refine ⟨?_, deterministic_attention_row_sum f⟩
  intro i j
  simp only [deterministicAttention]
  split_ifs <;> norm_num

lemma convex_attentionPolytope : Convex ℝ (attentionPolytope n m) := by
  intro A hA B hB a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro i j
    change 0 ≤ a * A i j + b * B i j
    exact add_nonneg (mul_nonneg ha (hA.1 i j)) (mul_nonneg hb (hB.1 i j))
  · intro i
    change (∑ j, (a * A i j + b * B i j)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hA.2 i, hB.2 i, mul_one, mul_one]
    exact hab

/-- Native convex-hull equality: the whole rectangular row-stochastic polytope. -/
theorem convexHull_deterministic_eq :
    convexHull ℝ (Set.range (deterministicAttention (N := n) (M := m))) =
      attentionPolytope n m := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨f, rfl⟩
      exact deterministic_mem f
    · exact convex_attentionPolytope
  · intro A hA
    rw [← reconstruct A hA.2]
    exact (convex_convexHull ℝ _).sum_mem
      (fun f _ => routeWeight_nonneg A hA.1 f)
      (routeWeight_sum_one A hA.2)
      (fun f _ => subset_convexHull ℝ _ (Set.mem_range_self f))

/-- Square matrices connect directly to Mathlib's existing stochastic monoid. -/
theorem mem_rowStochastic_iff_mem_convexHull (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ Matrix.rowStochastic ℝ (Fin n) ↔
      A ∈ convexHull ℝ (Set.range (deterministicAttention (N := n) (M := n))) := by
  rw [convexHull_deterministic_eq, Matrix.mem_rowStochastic_iff_sum]
  rfl

lemma eq_deterministic_of_off_route_zero (B : Matrix (Fin n) (Fin m) ℝ)
    (hrow : ∀ i, ∑ j, B i j = 1) (f : Fin n → Fin m)
    (hoff : ∀ i j, j ≠ f i → B i j = 0) :
    B = deterministicAttention f := by
  ext i j
  by_cases h : j = f i
  · subst j
    have hs : (∑ c : Fin m, B i c) = B i (f i) := by
      apply Finset.sum_eq_single (f i)
      · intro c _ hc
        exact hoff i c hc
      · simp
    have hselected : B i (f i) = 1 := hs.symm.trans (hrow i)
    simpa [deterministicAttention] using hselected
  · simp [deterministicAttention, h, hoff i j h]

/-- Vertex rigidity: no deterministic route is a nontrivial convex mixture of
other row-normalized nonnegative matrices. This proves the extremality property
without assuming an eigenbasis or choosing a triangulation. -/
theorem deterministic_convex_rigidity (f : Fin n → Fin m)
    {B C : Matrix (Fin n) (Fin m) ℝ}
    (hB : B ∈ attentionPolytope n m) (hC : C ∈ attentionPolytope n m)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmix : a • B + b • C = deterministicAttention f) :
    B = deterministicAttention f ∧ C = deterministicAttention f := by
  have off (i : Fin n) (j : Fin m) (hj : j ≠ f i) :
      B i j = 0 ∧ C i j = 0 := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin m) ℝ => M i j) hmix
    change a * B i j + b * C i j = deterministicAttention f i j at he
    simp only [deterministicAttention, ite_eq_right hj] at he
    have hBn := hB.1 i j
    have hCn := hC.1 i j
    have hBa := mul_nonneg ha.le hBn
    have hCb := mul_nonneg hb.le hCn
    constructor <;> nlinarith
  exact ⟨eq_deterministic_of_off_route_zero B hB.2 f (fun i j hj => (off i j hj).1),
    eq_deterministic_of_off_route_zero C hC.2 f (fun i j hj => (off i j hj).2)⟩

/-- The deterministic routes are native Mathlib extreme points. -/
theorem deterministic_mem_extremePoints (f : Fin n → Fin m) :
    deterministicAttention f ∈ (attentionPolytope n m).extremePoints ℝ := by
  rw [mem_extremePoints]
  refine ⟨deterministic_mem f, ?_⟩
  intro B hB C hC hsegment
  rcases hsegment with ⟨a, b, ha, hb, _hab, hmix⟩
  exact deterministic_convex_rigidity f hB hC ha hb hmix

/-- Full vertex classification: no further extreme points exist. -/
theorem extremePoints_eq_deterministic :
    (attentionPolytope n m).extremePoints ℝ =
      Set.range (deterministicAttention (N := n) (M := m)) := by
  apply Set.Subset.antisymm
  · rw [← convexHull_deterministic_eq]
    exact extremePoints_convexHull_subset
  · rintro _ ⟨f, rfl⟩
    exact deterministic_mem_extremePoints f

/-- Routing composition is contravariant in the token-to-key functions. -/
theorem deterministic_mul (f : Fin n → Fin m) (g : Fin m → Fin k) :
    deterministicAttention f * deterministicAttention g =
      deterministicAttention (g ∘ f) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (f i)]
  · simp [deterministicAttention, Function.comp_def]
  · intro c _ hc
    simp [deterministicAttention, hc]
  · simp

section Values

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A deterministic route reads exactly one value per query. -/
theorem deterministic_readout (f : Fin n → Fin m) (V : Fin m → E) (i : Fin n) :
    (∑ j, deterministicAttention f i j • V j) = V (f i) := by
  simp [deterministicAttention]

/-- The requested token representation: soft attention equals the same convex
mixture of deterministic reads, for values in any real module. -/
theorem token_readout_decomposition (A : Matrix (Fin n) (Fin m) ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) (V : Fin m → E) (i : Fin n) :
    (∑ j, A i j • V j) =
      ∑ f : Fin n → Fin m, routeWeight A f • V (f i) := by
  calc
    (∑ j, A i j • V j) =
        ∑ j, (∑ f : Fin n → Fin m,
          routeWeight A f * deterministicAttention f i j) • V j := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun c : ℝ => c • V j) (routeWeight_marginal A hrow i j).symm
    _ = ∑ f : Fin n → Fin m, routeWeight A f •
        (∑ j, deterministicAttention f i j • V j) := by
      simp_rw [Finset.sum_smul, mul_smul, Finset.smul_sum]
      exact Finset.sum_comm
    _ = ∑ f : Fin n → Fin m, routeWeight A f • V (f i) := by
      simp_rw [deterministic_readout]

/-- Attention supplies barycentric coordinates in the value polytope. -/
theorem token_readout_mem_convexHull (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : A ∈ attentionPolytope n m) (V : Fin m → E) (i : Fin n) :
    (∑ j, A i j • V j) ∈ convexHull ℝ (Set.range V) := by
  exact (convex_convexHull ℝ _).sum_mem (fun j _ => hA.1 i j) (hA.2 i)
    (fun j _ => subset_convexHull ℝ _ (Set.mem_range_self j))

end Values

/-- A one-hot query token extracts its attention row, not an eigenprojection. -/
theorem basis_token_row (A : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    Matrix.vecMul (Pi.single i (1 : ℝ)) A = A i := by
  funext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

/-- Exact reconstruction of the complete matrix-on-values action. -/
theorem matrix_readout_decomposition (A : Matrix (Fin n) (Fin m) ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) (V : Matrix (Fin m) (Fin k) ℝ) :
    A * V = ∑ f : Fin n → Fin m,
      routeWeight A f • (deterministicAttention f * V) := by
  calc
    A * V = (∑ f : Fin n → Fin m,
        routeWeight A f • deterministicAttention f) * V := by
      rw [reconstruct A hrow]
    _ = _ := by
      rw [Matrix.sum_mul]
      simp only [Matrix.smul_mul]

/-- Every route that crosses a forbidden entry has zero coefficient. -/
theorem routeWeight_zero_of_forbidden (A : Matrix (Fin n) (Fin m) ℝ)
    (allowed : Fin n → Fin m → Prop)
    (hmask : ∀ i j, ¬ allowed i j → A i j = 0)
    (f : Fin n → Fin m) (i : Fin n) (hbad : ¬ allowed i (f i)) :
    routeWeight A f = 0 := by
  unfold routeWeight
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hmask i (f i) hbad)

/-- Every nonzero coefficient labels a mask-respecting complete route. -/
theorem nonzero_route_is_allowed (A : Matrix (Fin n) (Fin m) ℝ)
    (allowed : Fin n → Fin m → Prop)
    (hmask : ∀ i j, ¬ allowed i j → A i j = 0)
    (f : Fin n → Fin m) (hf : routeWeight A f ≠ 0) :
    ∀ i, allowed i (f i) := by
  intro i
  by_contra hi
  exact hf (routeWeight_zero_of_forbidden A allowed hmask f i hi)

/-- Causal attention decomposes entirely into causal deterministic routes. -/
theorem nonzero_causal_route (A : Matrix (Fin n) (Fin n) ℝ)
    (hcausal : ∀ i j, i < j → A i j = 0)
    (f : Fin n → Fin n) (hf : routeWeight A f ≠ 0) :
    ∀ i, f i ≤ i := by
  exact nonzero_route_is_allowed A (fun i j => j ≤ i)
    (fun i j h => hcausal i j (lt_of_not_ge h)) f hf

end
end InfoGeometry.Routing.AttentionPolytope
