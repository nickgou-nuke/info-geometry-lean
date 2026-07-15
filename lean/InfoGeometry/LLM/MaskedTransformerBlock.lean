import InfoGeometry.LLM.TransformerBlock

open scoped BigOperators

namespace InfoGeometry.LLM

open Triality

/--
Causal-mask interface over token indices.

`allow q i` is interpreted as "query state `q` may attend to index `i`".
-/
structure CausalMask (Q ι : Type*) where
  allow : Q → ι → Prop

/--
Masked transformer block built on top of the canonical `TransformerBlock` scaffold.

The mask is applied at the per-head attention weight level.
-/
structure MaskedTransformerBlock
    {Q K Vh Vout ι : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout]
    (n : ℕ) where
  base : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n
  causalMask : CausalMask Q ι

namespace MaskedTransformerBlock

variable {Q K Vh Vout ι : Type*} [DecidableEq ι]
variable [AddCommGroup Vh] [Module ℝ Vh]
variable [AddCommGroup Vout] [Module ℝ Vout]
variable {n : ℕ}

/-- Head-level masked weight (`0` when the mask blocks index `i`). -/
noncomputable def maskedHeadWeight
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (h : Fin n) (q : Q) (i : ι) : ℝ := by
  classical
  exact if M.causalMask.allow q i then (M.base.attn.heads h).weights q i else 0

/-- Tuple of masked head outputs before the output projection. -/
noncomputable def maskedPreOutput
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) : Fin n → Vh :=
  fun h =>
    ∑ i ∈ (M.base.attn.heads h).I,
      (M.maskedHeadWeight h q i) • (M.base.attn.cores h).route q ((M.base.attn.heads h).keys i)

/-- Masked attention output after the existing multi-head output projection. -/
noncomputable def maskedAttentionOut
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) : Vout :=
  M.base.attn.outProj (M.maskedPreOutput q)

/-- Masked first residual stage followed by `norm1`. -/
noncomputable def maskedAfterAttention
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) : Vout :=
  M.base.norm1 (M.base.residualLift q + M.maskedAttentionOut q)

/-- Masked second residual stage followed by `norm2`. -/
noncomputable def maskedAfterMLP
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) : Vout :=
  M.base.norm2 (M.maskedAfterAttention q + M.base.mlp (M.maskedAfterAttention q))

/-- Full masked transformer-block forward map. -/
noncomputable def run
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) : Vout :=
  M.maskedAfterMLP q

@[simp] lemma maskedHeadWeight_of_not_allow
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (h : Fin n) (q : Q) (i : ι)
    (hBlock : ¬ M.causalMask.allow q i) :
    M.maskedHeadWeight h q i = 0 := by
  classical
  simp [maskedHeadWeight, hBlock]

@[simp] lemma maskedHeadWeight_of_allow
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (h : Fin n) (q : Q) (i : ι)
    (hAllow : M.causalMask.allow q i) :
    M.maskedHeadWeight h q i = (M.base.attn.heads h).weights q i := by
  classical
  simp [maskedHeadWeight, hAllow]

lemma maskedPreOutput_eq_base_preOutput_of_allows_all
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (hAll : ∀ q i, M.causalMask.allow q i) (q : Q) :
    M.maskedPreOutput q = M.base.attn.preOutput q := by
  funext h
  unfold maskedPreOutput MultiHeadGeometricAttention.preOutput
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [maskedHeadWeight, hAll q i]

lemma maskedAttentionOut_eq_base_attentionOut_of_allows_all
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (hAll : ∀ q i, M.causalMask.allow q i) (q : Q) :
    M.maskedAttentionOut q = M.base.attentionOut q := by
  unfold maskedAttentionOut TransformerBlock.attentionOut
  rw [maskedPreOutput_eq_base_preOutput_of_allows_all (M := M) hAll q]
  simp [MultiHeadGeometricAttention.output_def]

lemma run_eq_base_run_of_allows_all
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (hAll : ∀ q i, M.causalMask.allow q i) (q : Q) :
    M.run q = M.base.run q := by
  unfold run maskedAfterMLP maskedAfterAttention TransformerBlock.run
    TransformerBlock.afterMLP TransformerBlock.afterAttention
  rw [maskedAttentionOut_eq_base_attentionOut_of_allows_all (M := M) hAll q]

end MaskedTransformerBlock

end InfoGeometry.LLM
