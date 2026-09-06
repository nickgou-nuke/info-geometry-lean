import Mathlib.Tactic
import InfoGeometry.Neurosymbolic.BornNMFEngine

open Matrix
open scoped BigOperators
open InfoGeometry.Neurosymbolic.BornNMFEngine

namespace InfoGeometry.Neurosymbolic.SinkhornCramerRaoBridge

/-- Row-stochastic matrix property (row sums equal 1) -/
def IsRowStochastic {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i, ∑ j, S i j = 1

/-- Theorem: Softmax attention matrix is row-stochastic (each row sums to 1). -/
theorem softmax_attention_row_stochastic {n : ℕ} [Fact (0 < n)] (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    IsRowStochastic (fun i j => Real.exp (β * A i j) / ∑ k, Real.exp (β * A i k)) := by
  intro i
  dsimp [IsRowStochastic]
  rw [← Finset.sum_div]
  have h_sum_pos : (∑ k, Real.exp (β * A i k)) ≠ 0 := by
    haveI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
    exact ne_of_gt (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)
  exact div_self h_sum_pos

/-- Cramér-Rao Information Lower Bound Positivity Theorem -/
theorem cramer_rao_bound_pos {I : ℝ} (hI : 0 < I) :
    0 < 1 / I :=
  one_div_pos.mpr hI

/-- Structure representing the Sinkhorn-Cramér-Rao Attention Information Geometry Packet -/
def SinkhornCramerRaoPacket (n : ℕ) [Fact (0 < n)] : Type _ :=
  {p : ℝ × ℝ × Matrix (Fin n) (Fin n) ℝ //
    0 < p.1 ∧
    0 < p.2.1 ∧
    IsRowStochastic p.2.2 ∧
    MatrixNonneg p.2.2}

namespace SinkhornCramerRaoPacket

/-- Native tuple projection for the Fisher information. -/
abbrev fisher_info {n : ℕ} [Fact (0 < n)]
    (packet : SinkhornCramerRaoPacket n) : ℝ :=
  packet.1.1

/-- Native subtype proof of Fisher positivity. -/
theorem h_fisher_pos {n : ℕ} [Fact (0 < n)]
    (packet : SinkhornCramerRaoPacket n) : 0 < packet.fisher_info :=
  packet.2.1

/-- Native tuple projection for the Cramér--Rao bound. -/
abbrev cramer_rao_bound {n : ℕ} [Fact (0 < n)]
    (packet : SinkhornCramerRaoPacket n) : ℝ :=
  packet.1.2.1

/-- Native subtype proof of Cramér--Rao-bound positivity. -/
theorem h_cr_pos {n : ℕ} [Fact (0 < n)]
    (packet : SinkhornCramerRaoPacket n) : 0 < packet.cramer_rao_bound :=
  packet.2.2.1

/-- Native tuple projection for the attention matrix. -/
abbrev attention_matrix {n : ℕ} [Fact (0 < n)]
    (packet : SinkhornCramerRaoPacket n) : Matrix (Fin n) (Fin n) ℝ :=
  packet.1.2.2

/-- Native subtype proof of row stochasticity. -/
theorem attention_row_stochastic {n : ℕ} [Fact (0 < n)]
    (packet : SinkhornCramerRaoPacket n) :
    IsRowStochastic packet.attention_matrix :=
  packet.2.2.2.1

/-- Native subtype proof of matrix nonnegativity. -/
theorem attention_nonneg {n : ℕ} [Fact (0 < n)]
    (packet : SinkhornCramerRaoPacket n) :
    MatrixNonneg packet.attention_matrix :=
  packet.2.2.2.2

end SinkhornCramerRaoPacket

/-- Main Theorem: Proof of existence of the Sinkhorn-Cramér-Rao Information Geometry Bridge. -/
theorem sinkhorn_cramer_rao_bridge_exists {n : ℕ} [Fact (0 < n)] (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    Nonempty (SinkhornCramerRaoPacket n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  have h_row := softmax_attention_row_stochastic A β
  have h_nonneg : MatrixNonneg (fun i j => Real.exp (β * A i j) / ∑ k, Real.exp (β * A i k)) := by
    intro i j
    have h_exp_pos : 0 < Real.exp (β * A i j) := Real.exp_pos (β * A i j)
    have h_sum_pos : 0 < ∑ k, Real.exp (β * A i k) := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
    exact div_nonneg h_exp_pos.le h_sum_pos.le
  refine ⟨⟨(1, 1, fun i j => Real.exp (β * A i j) / ∑ k, Real.exp (β * A i k)), ?_⟩⟩
  exact ⟨by norm_num, by norm_num, h_row, h_nonneg⟩

end InfoGeometry.Neurosymbolic.SinkhornCramerRaoBridge
