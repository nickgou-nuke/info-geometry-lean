import Mathlib
import InfoGeometry.Neurosymbolic.BornNMFEngine
import InfoGeometry.Canonical.AttentionPolarizedGibbsBridge

open Matrix
open scoped BigOperators
open InfoGeometry.Neurosymbolic.BornNMFEngine
open InfoGeometry.Canonical.Attention

namespace InfoGeometry.Neurosymbolic.LLMAttentionKreinMellinBridge

/-- Structure unifying LLM Attention, Gibbs Thermodynamics, and the Born-NMF Engine -/
structure LLMLatentSpaceUnification (n : ℕ) [Fact (0 < n)] where
  attention_matrix : Matrix (Fin n) (Fin n) ℝ
  attention_nonneg : MatrixNonneg attention_matrix
  has_factorization : Nonempty (NeurosymbolicFactorization (Fin n) (Fin n) (Fin n))

/-- Theorem: Softmax attention probability matrix is elementwise non-negative. -/
theorem softmax_attention_matrix_nonneg {n : ℕ} [Fact (0 < n)] (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    MatrixNonneg (fun i j => Real.exp (β * A i j) / ∑ k, Real.exp (β * A i k)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  intro i j
  dsimp [MatrixNonneg]
  have h_exp_pos : 0 < Real.exp (β * A i j) := Real.exp_pos (β * A i j)
  have h_sum_pos : 0 < ∑ k, Real.exp (β * A i k) := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  exact div_nonneg h_exp_pos.le h_sum_pos.le

/-- Main Theorem: Proof of existence of the Unified LLM Latent Space Geometry Engine. -/
theorem llm_latent_space_unification_exists {n : ℕ} [Fact (0 < n)] (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    Nonempty (LLMLatentSpaceUnification n) := by
  have h_nonneg := softmax_attention_matrix_nonneg A β
  have h_W : MatrixNonneg (1 : Matrix (Fin n) (Fin n) ℝ) := fun i j => by
    dsimp [Matrix.one_apply]
    split_ifs <;> norm_num
  have h_factor := neurosymbolic_engine_exists (m := Fin n) (k := Fin n) (n := Fin n) A 1 1 h_W h_W
  refine ⟨⟨fun i j => Real.exp (β * A i j) / ∑ k, Real.exp (β * A i k), h_nonneg, h_factor⟩⟩

end InfoGeometry.Neurosymbolic.LLMAttentionKreinMellinBridge
