import Mathlib.Topology.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Convex.StdSimplex
import InfoGeometry.Convex.LogSumExp

open scoped BigOperators

namespace InfoGeometry.Topology

open InfoGeometry.Convex.LogSumExp

variable {X n : Type*} [TopologicalSpace X] [Fintype n] [Nonempty n]

/-- A finite latent-logit field, with one real logit for each token/state. -/
noncomputable def latentSoftmax (logits : X → n → ℝ) : X → n → ℝ :=
  fun x => softmax (logits x)

theorem continuous_latentSoftmax_coordinate
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) (i : n) :
    Continuous (fun x => latentSoftmax logits x i) := by
  have hsum : Continuous (fun x => ∑ j : n, Real.exp (logits x j)) := by
    simpa using
      (continuous_finset_sum (s := (Finset.univ : Finset n))
        (fun j _ => Real.continuous_exp.comp (hlogits j)))
  have hne : ∀ x : X, (∑ j : n, Real.exp (logits x j)) ≠ 0 := by
    intro x
    exact (sumExp_pos (logits x)).ne'
  simpa [latentSoftmax, softmax, sumExp] using
    (Real.continuous_exp.comp (hlogits i)).div hsum hne

theorem continuous_latentSoftmax
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) :
    Continuous (latentSoftmax logits) := by
  exact continuous_pi (fun i => continuous_latentSoftmax_coordinate logits hlogits i)

omit [TopologicalSpace X] in
theorem latentSoftmax_sum_one
    (logits : X → n → ℝ) (x : X) :
    ∑ i : n, latentSoftmax logits x i = 1 := by
  exact sum_softmax_eq_one (logits x)

omit [TopologicalSpace X] in
theorem latentSoftmax_nonneg
    (logits : X → n → ℝ) (x : X) (i : n) :
    0 ≤ latentSoftmax logits x i := by
  exact softmax_nonneg (logits x) i

omit [TopologicalSpace X] in
theorem latentSoftmax_coordinate_pos
    (logits : X → n → ℝ) (x : X) (i : n) :
    0 < latentSoftmax logits x i := by
  unfold latentSoftmax
  exact div_pos (Real.exp_pos _) (sumExp_pos (logits x))

omit [TopologicalSpace X] in
theorem latentSoftmax_mem_stdSimplex
    (logits : X → n → ℝ) (x : X) :
    latentSoftmax logits x ∈ stdSimplex ℝ n := by
  rw [stdSimplex_eq_inter]
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · exact fun i => latentSoftmax_nonneg logits x i
  · exact latentSoftmax_sum_one logits x

/-- The symbolic latent representation, with normalization carried by the
standard-simplex subtype itself. -/
noncomputable def latentSimplexMap
    (logits : X → n → ℝ) : X → stdSimplex ℝ n :=
  fun x => ⟨latentSoftmax logits x, latentSoftmax_mem_stdSimplex logits x⟩

theorem continuous_latentSimplexMap
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) :
    Continuous (latentSimplexMap logits) := by
  exact (continuous_latentSoftmax logits hlogits).subtype_mk
    (fun x => latentSoftmax_mem_stdSimplex logits x)

theorem isCompact_range_latentSimplexMap
    [CompactSpace X]
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) :
    IsCompact (Set.range (latentSimplexMap logits)) :=
  isCompact_range (continuous_latentSimplexMap logits hlogits)

theorem isClosed_range_latentSimplexMap
    [CompactSpace X]
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) :
    IsClosed (Set.range (latentSimplexMap logits)) :=
  (isCompact_range_latentSimplexMap logits hlogits).isClosed

omit [TopologicalSpace X] in
theorem latentSimplexMap_coordinate_pos
    (logits : X → n → ℝ) (x : X) (i : n) :
    0 < (latentSimplexMap logits x : n → ℝ) i :=
  latentSoftmax_coordinate_pos logits x i

theorem latentSoftmax_uniformShift
    (logits : X → n → ℝ) (c : X → ℝ) :
    latentSoftmax (fun x => logits x + c x • uniformShift) =
      latentSoftmax logits := by
  funext x
  exact softmax_add_uniformShift (logits x) (c x)

theorem latentSimplexMap_uniformShift
    (logits : X → n → ℝ) (c : X → ℝ) :
    latentSimplexMap (fun x => logits x + c x • uniformShift) =
      latentSimplexMap logits := by
  funext x
  apply Subtype.ext
  exact congrFun (latentSoftmax_uniformShift logits c) x

theorem latentSoftmax_coordinate_fiber_isClosed
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i))
    (i : n) (c : ℝ) :
    IsClosed {x : X | latentSoftmax logits x i = c} := by
  change IsClosed ((fun x => latentSoftmax logits x i) ⁻¹' ({c} : Set ℝ))
  exact isClosed_singleton.preimage
    (continuous_latentSoftmax_coordinate logits hlogits i)

/-- The finite symbolic latent map is a continuous map into the normalized
probability simplex, expressed by its native nonnegativity and sum-one laws. -/
theorem latentSoftmax_simplex_readout
    (logits : X → n → ℝ)
    (hlogits : ∀ i, Continuous (fun x => logits x i)) :
    Continuous (latentSoftmax logits) ∧
      (∀ x, ∑ i : n, latentSoftmax logits x i = 1) ∧
      (∀ x i, 0 ≤ latentSoftmax logits x i) := by
  exact ⟨continuous_latentSoftmax logits hlogits,
    fun x => latentSoftmax_sum_one logits x,
    fun x i => latentSoftmax_nonneg logits x i⟩

end InfoGeometry.Topology
