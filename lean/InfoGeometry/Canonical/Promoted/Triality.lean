import Architect
import InfoGeometry.Clifford.SplitQ11
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Analysis.SpecialFunctions.Exp

namespace InfoGeometry.Research.Triality

open InfoGeometry.Clifford
open scoped BigOperators

@[blueprint "def:triadic-core"]
structure TriadicCore (Q K V : Type*) where
  interact : Q → K → ℝ
  route    : Q → K → V

@[blueprint "def:metric-triadic-core"]
structure MetricTriadicCore (Q K V : Type*) extends TriadicCore Q K V where
  quadQ : Q → ℝ
  quadK : K → ℝ
  quadV : V → ℝ
  route_norm_compat : ∀ q k, quadV (route q k) = quadQ q + quadK k + 2 * interact q k

/--
A low-dimensional instance of Metric Triadic Core based on the Split signature (1,1).
-/
@[blueprint "def:split-metric-triadic-instance"]
noncomputable def splitMetricTriadicInstance :
    MetricTriadicCore (ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) :=
  { interact := fun q k => splitB11 q k
    route := fun q k => q + k
    quadQ := fun v => splitQ11 v
    quadK := fun v => splitQ11 v
    quadV := fun v => splitQ11 v
    route_norm_compat := fun q k => by
      -- Polarization identity for split(1,1) matches exactly
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using splitQ11_add q k }

@[simp] theorem splitMetricTriadicInstance_route (q k : ℝ × ℝ) :
    splitMetricTriadicInstance.route q k = q + k := rfl

@[simp] theorem splitMetricTriadicInstance_interact (q k : ℝ × ℝ) :
    splitMetricTriadicInstance.interact q k = splitB11 q k := rfl

@[simp] theorem splitMetricTriadicInstance_quadQ (q : ℝ × ℝ) :
    splitMetricTriadicInstance.quadQ q = splitQ11 q := rfl

@[simp] theorem splitMetricTriadicInstance_quadK (k : ℝ × ℝ) :
    splitMetricTriadicInstance.quadK k = splitQ11 k := rfl

@[simp] theorem splitMetricTriadicInstance_quadV (v : ℝ × ℝ) :
    splitMetricTriadicInstance.quadV v = splitQ11 v := rfl

@[simp] theorem splitMetricTriadicInstance_route_norm_compat (q k : ℝ × ℝ) :
    splitMetricTriadicInstance.quadV (splitMetricTriadicInstance.route q k) =
      splitMetricTriadicInstance.quadQ q + splitMetricTriadicInstance.quadK k
        + 2 * splitMetricTriadicInstance.interact q k :=
  splitMetricTriadicInstance.route_norm_compat q k

/--
Formalization of a Geometric Attention Map over a Triadic Core.
This defines how a single Query aggregates an indexed family of Keys and Values.
-/
@[blueprint "def:geometric-attention-map"]
structure GeometricAttentionMap {Q K V : Type*} (core : TriadicCore Q K V)
    (ι : Type*) [DecidableEq ι] [AddCommGroup V] [Module ℝ V] where
  /-- Finite set of indices for keys and values. -/
  I : Finset ι
  /-- Key mapping. -/
  keys : ι → K
  /-- Attention weights for a query q across all indices i ∈ I. -/
  weights : Q → ι → ℝ
  /-- Condition that weights sum to 1 for each query (normalization). -/
  weights_sum_one : ∀ q, ∑ i ∈ I, weights q i = 1

namespace GeometricAttentionMap

variable {Q K V ι : Type*} {core : TriadicCore Q K V}
    [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

/--
The aggregated attention output.
-/
noncomputable def attention (attn : GeometricAttentionMap core ι) (q : Q) : V :=
  ∑ i ∈ attn.I, (attn.weights q i) • (core.route q (attn.keys i))

@[simp] theorem attention_def (attn : GeometricAttentionMap core ι) (q : Q) :
    attn.attention q = ∑ i ∈ attn.I, (attn.weights q i) • (core.route q (attn.keys i)) := rfl

/--
Theorem: If routing decomposes additively into query and key embeddings, the canonical
attention sum decomposes into a residual term plus a weighted key aggregate.
-/
@[blueprint "thm:attention-decomposition-residual"]
theorem attention_decomposition_residual (attn : GeometricAttentionMap core ι)
    (toV : Q → V) (kToV : K → V)
    (h_route : ∀ q k, core.route q k = toV q + kToV k) (q : Q) :
    attn.attention q = toV q + ∑ i ∈ attn.I, (attn.weights q i) • kToV (attn.keys i) := by
  calc
    attn.attention q
        = ∑ i ∈ attn.I, (attn.weights q i) • (core.route q (attn.keys i)) := rfl
    _   = ∑ i ∈ attn.I, (attn.weights q i) • (toV q + kToV (attn.keys i)) := by simp_rw [h_route]
    _   = ∑ i ∈ attn.I, ((attn.weights q i) • toV q + (attn.weights q i) • kToV (attn.keys i)) := by
            apply Finset.sum_congr rfl
            intros i _; rw [smul_add]
    _   = (∑ i ∈ attn.I, (attn.weights q i) • toV q) + ∑ i ∈ attn.I, (attn.weights q i) • kToV (attn.keys i) := by
            rw [Finset.sum_add_distrib]
    _   = ((∑ i ∈ attn.I, attn.weights q i) • toV q) + ∑ i ∈ attn.I, (attn.weights q i) • kToV (attn.keys i) := by
            rw [Finset.sum_smul]
    _   = (1 : ℝ) • toV q + ∑ i ∈ attn.I, (attn.weights q i) • kToV (attn.keys i) := by rw [attn.weights_sum_one]
    _   = toV q + ∑ i ∈ attn.I, (attn.weights q i) • kToV (attn.keys i) := by rw [one_smul]

end GeometricAttentionMap

/--
A Softmax-based Attention Map where weights are derived from exponential interaction scores.
Requires a non-empty index set to ensure the denominator is strictly positive.
-/
@[blueprint "def:softmax-geometric-attention"]
noncomputable def softmaxAttention {Q K V ι : Type*} (core : TriadicCore Q K V)
    [DecidableEq ι] [AddCommGroup V] [Module ℝ V] (I : Finset ι) (hI : I.Nonempty) (keys : ι → K) :
    GeometricAttentionMap core ι where
  I := I
  keys := keys
  weights := fun q i =>
    let Z := ∑ j ∈ I, Real.exp (core.interact q (keys j))
    Real.exp (core.interact q (keys i)) / Z
  weights_sum_one := fun q => by
    let Z := ∑ j ∈ I, Real.exp (core.interact q (keys j))
    have hZ_pos : 0 < Z := by
      dsimp [Z]
      simpa using
        (Finset.sum_pos
          (s := I)
          (f := fun j => Real.exp (core.interact q (keys j)))
          (by
            intro j hj
            exact Real.exp_pos _)
          hI)
    calc
      ∑ i ∈ I, Real.exp (core.interact q (keys i)) / Z
          = (∑ i ∈ I, Real.exp (core.interact q (keys i))) / Z := by
              rw [Finset.sum_div]
      _ = Z / Z := by rfl
      _ = 1 := by exact div_self (ne_of_gt hZ_pos)

/--
Multi-head geometric attention with `n` heads.

Each head has its own triadic core and its own attention map.
The combined head outputs are assembled as a function `Fin n → Vh` and then
projected linearly into `Vout` (abstracting "concatenate + output projection").
-/
@[blueprint "def:multi-head-geometric-attention"]
structure MultiHeadGeometricAttention
    {Q K Vh Vout ι : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout]
    (n : ℕ) where
  cores : Fin n → TriadicCore Q K Vh
  heads : (h : Fin n) → GeometricAttentionMap (cores h) ι
  outProj : (Fin n → Vh) →ₗ[ℝ] Vout

namespace MultiHeadGeometricAttention

variable {Q K Vh Vout ι : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout]
    {n : ℕ} (M : MultiHeadGeometricAttention (Q:=Q) (K:=K) (Vh:=Vh) (Vout:=Vout) (ι:=ι) n)

/-- The tuple of all head outputs, indexed by head. -/
noncomputable def preOutput (q : Q) : Fin n → Vh :=
  fun h => (M.heads h).attention q

/-- The final multi-head output after the output projection. -/
noncomputable def output (q : Q) : Vout :=
  M.outProj (M.preOutput q)

@[simp] theorem preOutput_def (q : Q) :
    M.preOutput q = fun h => (M.heads h).attention q := rfl

@[simp] theorem output_def (q : Q) :
    M.output q = M.outProj (fun h => (M.heads h).attention q) := rfl

/--
Theorem: If each head's routing decomposes additively into a query embedding
and a key embedding, the total multi-head output decomposes into the sum of:
1. The output-projected query embeddings (the global skip connection).
2. The output-projected weighted key aggregates.
-/
@[blueprint "thm:multihead-attention-decomposition-residual"]
theorem output_decomposition_residual
    (toV : Fin n → Q → Vh) (kToV : Fin n → K → Vh)
    (h_route : ∀ h q k, (M.cores h).route q k = toV h q + kToV h k) (q : Q) :
    M.output q =
      M.outProj (fun h => toV h q) +
      M.outProj (fun h => ∑ i ∈ (M.heads h).I, ((M.heads h).weights q i) • kToV h ((M.heads h).keys i)) := by
  rw [output_def]
  have h_pointwise : (fun h => (M.heads h).attention q) =
    (fun h => toV h q + ∑ i ∈ (M.heads h).I, ((M.heads h).weights q i) • kToV h ((M.heads h).keys i)) := by
    funext h
    exact GeometricAttentionMap.attention_decomposition_residual (M.heads h) (toV h) (kToV h) (h_route h) q
  rw [h_pointwise]
  -- Linearity of outProj handles the Pi-vector addition
  exact M.outProj.map_add (fun h => toV h q) (fun h => ∑ i ∈ (M.heads h).I, ((M.heads h).weights q i) • kToV h ((M.heads h).keys i))

end MultiHeadGeometricAttention

end InfoGeometry.Research.Triality
