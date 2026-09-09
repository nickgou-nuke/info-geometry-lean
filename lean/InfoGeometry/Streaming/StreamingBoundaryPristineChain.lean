import InfoGeometry.Streaming.CausalMemory
import InfoGeometry.Streaming.PositiveBoundaryConditioning
import InfoGeometry.Streaming.WeakValueBoundary
import InfoGeometry.Streaming.GaugeCovariantRouting
import InfoGeometry.Streaming.BipartiteGraphDirac
import InfoGeometry.Streaming.G2GradedRouter
import InfoGeometry.Streaming.PairingGapSeparation
import InfoGeometry.Streaming.UnipotentMemoryShift

/-!
# Exact boundary-conditioned streaming and explicit geometric structure

The combined statements keep causal recurrence, positive conditioning,
quantum weak ratios, discrete connection transport, and graph Hodge algebra
separate. A complete physical token dynamics or general manifold quantization
is not inferred from their coexistence.
-/

noncomputable section
namespace InfoGeometry.Streaming.StreamingBoundaryPristineChain

open scoped BigOperators
open InfoGeometry.Streaming.PositiveBoundaryConditioning
open InfoGeometry.Streaming.BipartiteGraphDirac
open InfoGeometry.Streaming.CausalMemory
open InfoGeometry.Streaming.GaugeCovariantRouting

/-- A positive attention kernel and nonempty terminal support construct a valid conditioned step. -/
theorem conditioned_attention_packet {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (score : ι → ι → ℝ) (τ : ℝ) (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (i₀ j₀ : ι) (hai : 0 < a i₀) (hbj : 0 < b j₀) :
    let K := attentionKernel score τ
    tiltedKernel K b ∈ Matrix.rowStochastic ℝ ι ∧
      (∑ i, conditioned a (backward K b) i) = 1 ∧
      forward (tiltedKernel K b) (conditioned a (backward K b)) =
        conditioned (forward K a) b := by
  dsimp only
  have hback := backward_attention_pos score τ b hb j₀ hbj
  have hz := overlap_pos a _ ha hback i₀ hai
  exact ⟨tiltedKernel_stochastic _ b
      (fun i j => (InfoGeometry.Routing.FiniteSoftmax.weight_pos (score i) τ j).le)
      hb hback,
    conditioned_sum a _ (ne_of_gt hz),
    InfoGeometry.Streaming.PositiveBoundaryConditioning.conditioned_forward
      _ a b (fun i => ne_of_gt (hback i))⟩

/-- The graph differential construction discharges both nilpotence and oddness obligations. -/
theorem concrete_graph_packet {v e : Type*} [Fintype v] [Fintype e]
    [DecidableEq v] [DecidableEq e] (B : Matrix e v ℝ) :
    differential B * differential B = 0 ∧ codifferential B * codifferential B = 0 ∧
      graphDirac B * graphDirac B =
        InfoGeometry.Canonical.DiscreteDiracHodgeChiral.hodgeLaplacian
          (differential B) (codifferential B) ∧
      graphDirac B * grading = -(grading * graphDirac B) :=
  ⟨differential_sq B, codifferential_sq B, graphDirac_sq B, graphDirac_odd B⟩

/-- A single causal memory state can be processed in arbitrary consecutive chunks. -/
theorem memory_prefix_and_chunks {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V) (u w : ℕ → V) (x : V) (m n : ℕ)
    (h : ∀ k < m + n, u k = w k) :
    state T u x (m + n) = state T w x (m + n) ∧
      state T u x (m + n) = state T (fun k => u (m + k)) (state T u x m) n :=
  ⟨state_prefix T u w x _ h, state_chunks T u x m n⟩

end InfoGeometry.Streaming.StreamingBoundaryPristineChain
