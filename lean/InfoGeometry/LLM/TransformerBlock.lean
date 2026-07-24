import InfoGeometry.Canonical.Attention
import InfoGeometry.Canonical.Triality

namespace InfoGeometry.LLM

open InfoGeometry.Canonical.Attention
open InfoGeometry.Canonical.Triality

/-- Context-window alias for LLM-facing APIs. -/
abbrev TokenContext (n : ℕ) (K V : Type*) := InfoGeometry.Canonical.Attention.ContextWindow n K V

/-- Functional identity predicate used for normalization-layer assumptions. -/
def IsIdentityMap {V : Type*} (f : V → V) : Prop :=
  ∀ x, f x = x

/--
Canonical transformer-block interface over the existing geometric multi-head attention core.

Architecture:
1. multi-head attention output
2. residual + first normalization
3. MLP feed-forward update
4. second normalization
-/
structure TransformerBlock
    {Q K Vh Vout ι : Type*} [DecidableEq ι]
    [AddCommGroup Vh] [Module ℝ Vh]
    [AddCommGroup Vout] [Module ℝ Vout]
    (n : ℕ) where
  attn : MultiHeadGeometricAttention (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n
  residualLift : Q → Vout
  norm1 : Vout → Vout
  mlp : Vout →ₗ[ℝ] Vout
  norm2 : Vout → Vout

namespace TransformerBlock

variable {Q K Vh Vout ι : Type*} [DecidableEq ι]
variable [AddCommGroup Vh] [Module ℝ Vh]
variable [AddCommGroup Vout] [Module ℝ Vout]
variable {n : ℕ}

noncomputable def attentionOut
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) : Vout :=
  B.attn.output q

/-- First residual stage (`x + Attn(x)`), then normalized by `norm1`. -/
noncomputable def afterAttention
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) : Vout :=
  B.norm1 (B.residualLift q + B.attentionOut q)

/-- Second residual stage (`h + MLP(h)`), then normalized by `norm2`. -/
noncomputable def afterMLP
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) : Vout :=
  B.norm2 (B.afterAttention q + B.mlp (B.afterAttention q))

/-- Full transformer-block forward map. -/
noncomputable def run
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) : Vout :=
  B.afterMLP q

@[simp] lemma attentionOut_def
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) :
    B.attentionOut q = B.attn.output q := rfl

@[simp] lemma afterAttention_def
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) :
    B.afterAttention q = B.norm1 (B.residualLift q + B.attentionOut q) := rfl

@[simp] lemma afterMLP_def
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) :
    B.afterMLP q = B.norm2 (B.afterAttention q + B.mlp (B.afterAttention q)) := rfl

@[simp] lemma run_def
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (q : Q) :
    B.run q = B.afterMLP q := rfl

lemma attentionOut_decomposition_residual
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (toV : Fin n → Q → Vh) (kToV : Fin n → K → Vh)
    (hRoute : ∀ h q k, (B.attn.cores h).route q k = toV h q + kToV h k) (q : Q) :
    B.attentionOut q =
      B.attn.outProj (fun h => toV h q) +
      B.attn.outProj
        (fun h => ∑ i ∈ (B.attn.heads h).I, ((B.attn.heads h).weights q i) • kToV h ((B.attn.heads h).keys i)) := by
  simpa [attentionOut] using
    (MultiHeadGeometricAttention.output_decomposition_residual
      (M := B.attn) toV kToV hRoute q)

lemma afterAttention_eq_residual_add_attention
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (hNorm1 : IsIdentityMap B.norm1) (q : Q) :
    B.afterAttention q = B.residualLift q + B.attentionOut q := by
  unfold afterAttention
  simpa using hNorm1 (B.residualLift q + B.attentionOut q)

lemma afterMLP_eq_afterAttention_of_zero_mlp
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (hNorm2 : IsIdentityMap B.norm2) (hMLP : B.mlp = 0) (q : Q) :
    B.afterMLP q = B.afterAttention q := by
  unfold afterMLP
  rw [hMLP]
  have hN : B.norm2 (B.afterAttention q) = B.afterAttention q := hNorm2 (B.afterAttention q)
  simpa [hN]

lemma run_eq_residual_add_attention_of_trivial_post
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (hNorm1 : IsIdentityMap B.norm1)
    (hNorm2 : IsIdentityMap B.norm2)
    (hMLP : B.mlp = 0)
    (q : Q) :
    B.run q = B.residualLift q + B.attentionOut q := by
  unfold run
  rw [afterMLP_eq_afterAttention_of_zero_mlp (B := B) hNorm2 hMLP q]
  rw [afterAttention_eq_residual_add_attention (B := B) hNorm1 q]

end TransformerBlock

end InfoGeometry.LLM
