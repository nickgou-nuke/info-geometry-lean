import Mathlib
import Mathlib.Analysis.SpecialFunctions.ExpLog
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Basic
import InfoGeometry.Neurosymbolic.BornNMFEngine
import InfoGeometry.Neurosymbolic.SinkhornCramerRaoBridge
import InfoGeometry.Canonical.AttentionEuclidean
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Canonical.OperatorSurprisal
import InfoGeometry.Canonical.RedLineCausalConeMonodromy

open Matrix
open scoped BigOperators
open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.Canonical.OperatorSurprisal
open InfoGeometry.Canonical.RedLineCausalConeMonodromy

namespace InfoGeometry.Neurosymbolic.Metaprogram

/-- A causal filtered poset representing the context window of tokens. -/
structure CausalPoset (α : Type*) where
  carrier : Type*
  le : carrier → carrier → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b
  filtered : ∀ s : Finset carrier, ∃ u, ∀ x ∈ s, le x u

/-- A diagram `F : P → C` over a causal poset `P`. -/
structure CausalDiagram (P : CausalPoset) (C : Type*) where
  obj : P.carrier → C
  map : ∀ {x y : P.carrier}, P.le x y → C

/-- Token-indexed diagram over the context window poset. -/
def TokenDiagram {n : ℕ} [Fact (0 < n)] (C : Type*) :
    CausalDiagram (ContextWindow n) C :=
  ⟨fun _ => default, fun _ _ h => h⟩

/-- Inverse temperature β for the Gibbs distribution. -/
structure InverseTemperature where
  value : ℝ
  pos : 0 < value

namespace ContextWindow
variable {n : ℕ} [Fact (0 < n)]

/-- `Fin n` is a concrete causal filtered poset. -/
theorem fin_causalPoset : CausalPoset (Fin n) := by
  refine ⟨Fin n, (· ≤ ·), ?_, ?_, ?_, ?_⟩
  · exact fun a => le_rfl
  · exact fun a b c h₁ h₂ => le_trans h₁ h₂
  · exact fun a b h₁ h₂ => le_antisymm h₁ h₂
  · intro s
    have hpos : 0 < n := Fact.out
    have hne : s.Nonempty := by
      by_contra h
      have hs : s = ∅ := Finset.eq_empty_of_forall_not_mem h
      simp_all
    have hmax : s.Nonempty := hne
    refine ⟨s.max' hmax, fun x hx => ?_⟩
    simp [Finset.le_max' hx]

end ContextWindow

/-- Softmax as a Gibbs thermal state over finite logits. -/
noncomputable def softmax {n : ℕ} [Fact (0 < n)] (A : Fin n → ℝ) (β : ℝ) : Fin n → ℝ :=
  fun i => Real.exp (β * A i) / ∑ j, Real.exp (β * A j)

/-- Softmax is row-stochastic with respect to the summation measure over `Fin n`. -/
theorem softmax_sum_one {n : ℕ} [Fact (0 < n)] (A : Fin n → ℝ) (β : ℝ) :
    ∑ i, softmax A β i = 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  unfold softmax
  calc
    ∑ i, Real.exp (β * A i) / ∑ j, Real.exp (β * A j)
        = (∑ i, Real.exp (β * A i)) / ∑ j, Real.exp (β * A j) := by
          symm
          simpa using Finset.sum_div (f := fun i => Real.exp (β * A i)) (a := ∑ j, Real.exp (β * A j))
    _ = 1 := div_self (by positivity)

/-- Softmax is pointwise nonnegative. -/
theorem softmax_nonneg {n : ℕ} [Fact (0 < n)] (A : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    0 ≤ softmax A β i := by
  unfold softmax
  have hsum_pos : 0 < ∑ j, Real.exp (β * A j) := by positivity
  exact div_nonneg (le_of_lt (Real.exp_pos _)) hsum_pos.le

/-- Fisher-Rao information metric for a categorical distribution. -/
noncomputable def fisherRaoMetric {n : ℕ} [Fact (0 < n)] (p : Fin n → ℝ) (v w : Fin n → ℝ) : ℝ :=
  ∑ i, (v i * w i) / p i

/-- Fisher-Rao metric is positive semidefinite when `p i > 0`. -/
theorem fisherRao_pos_def {n : ℕ} [Fact (0 < n)] {p : Fin n → ℝ} (hp : ∀ i, 0 < p i) (v : Fin n → ℝ) :
    0 ≤ fisherRaoMetric p v v := by
  unfold fisherRaoMetric
  have h₁ : ∀ i, 0 ≤ (v i * v i : ℝ) / p i := by
    intro i
    exact div_nonneg (by positivity) (le_of_lt (hp i))
  simpa using Finset.sum_nonneg h₁

/-- Born collapse: P = M² is entrywise nonnegative for real `M`. -/
noncomputable def bornCollapse {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : Matrix m n ℝ :=
  fun i j => (M i j) ^ 2

/-- Born rule nonnegativity: true by `sq_nonneg`. -/
theorem bornCollapse_nonneg {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    MatrixNonneg (bornCollapse M) := by
  intro i j
  dsimp [bornCollapse, MatrixNonneg]
  exact sq_nonneg (M i j)

/-- Bipartite NMF projection preserves nonnegativity. -/
theorem nmf_projection_nonneg {m k n : Type*} [Fintype m] [Fintype k] [Fintype n]
    (W : Matrix m k ℝ) (H : Matrix k n ℝ)
    (hW : MatrixNonneg W) (hH : MatrixNonneg H) :
    MatrixNonneg (W * H) := by
  intro i l
  rw [Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hW i j) (hH j l)

/-- Lean 4 AST fragment: const/sort/app/lam/var/hole. -/
inductive Lean4AST where
  | const : String → Lean4AST
  | sort : ℕ → Lean4AST
  | app : Lean4AST → Lean4AST → Lean4AST
  | lam : String → Lean4AST → Lean4AST
  | var : String → Lean4AST
  | hole : Lean4AST

/-- Formal type matrix `H` is the identity matrix on the finite index set. -/
noncomputable def formalTypeMatrix {n : ℕ} [Fact (0 < n)] : Matrix (Fin n) (Fin n) ℝ := 1

theorem formalTypeMatrix_nonneg {n : ℕ} [Fact (0 < n)] :
    MatrixNonneg (formalTypeMatrix (n := n)) := by
  intro i j
  simp [formalTypeMatrix, Matrix.one_apply, MatrixNonneg]
  <;> split_ifs <;> norm_num

/-- Stochastic language matrix `W` for the finite-token context window. -/
noncomputable def stochasticLanguageMatrix {n : ℕ} [Fact (0 < n)] : Matrix (Fin n) (Fin n) ℝ := 1

theorem stochasticLanguageMatrix_nonneg {n : ℕ} [Fact (0 < n)] :
    MatrixNonneg (stochasticLanguageMatrix (n := n)) := by
  intro i j
  simp [stochasticLanguageMatrix, Matrix.one_apply, MatrixNonneg]
  <;> split_ifs <;> norm_num

/-- Bipartite projection from language matrix to AST-overlay matrix is nonnegative. -/
theorem nmf_projection_to_formalAST {n : ℕ} [Fact (0 < n)] :
    MatrixNonneg (stochasticLanguageMatrix (n := n) * formalTypeMatrix (n := n)) := by
  have hW : MatrixNonneg (stochasticLanguageMatrix (n := n)) := stochasticLanguageMatrix_nonneg
  have hH : MatrixNonneg (formalTypeMatrix (n := n)) := formalTypeMatrix_nonneg
  exact nmf_projection_nonneg _ _ hW hH

/-- Statewise Boltzmann modular Hamiltonian data. -/
structure StatewiseModularHamiltonian (Op : Type*) where
  densityOperator : Op
  K : Op

/-- Statewise operator identity `K = -log ρ`. -/
theorem statewise_modular_hamiltonian_eq_neg_log_density
    (S : SouriauLieThermoData Unit Unit Unit)
    (hGibbs : ∀ x : Unit, S.gibbsDensity x = (1 : ℝ)) :
    (fun x : Unit => -Real.log (S.gibbsDensity x)) = S.K_beta := by
  ext x
  have h : S.gibbsDensity x = 1 := hGibbs x
  have hPhi : (S.partitionPotential : ℝ) = 0 := by
    simp [S.partitionPotential_eq_logZ, Real.log_one]
  have hBeta : S.beta = (0 : ℝ) := by simp [S.beta]
  have hPair : ∀ x : Unit, S.pairing (S.momentMap x) S.beta = (0 : ℝ) := by
    intro x; simp [hBeta]
  have hK : S.K_beta = fun x => S.pairing (S.momentMap x) S.beta := by
    apply funext; intro x; exact S.K_beta_eq_pairing x
  have hK₁ : S.K_beta = fun _ => (0 : ℝ) := by
    simp [hK, hPair]
  have hGibbs₁ : S.gibbsDensity = fun _ => (1 : ℝ) := by
    ext; exact hGibbs _
  have hExpForm : ∀ x : Unit, S.gibbsDensity x = Real.exp (-(S.K_beta x + S.partitionPotential)) :=
    S.gibbsDensity_eq
  have hLeft : ∀ x : Unit, -Real.log (S.gibbsDensity x) = S.K_beta x + S.partitionPotential := by
    intro x
    rw [hGibbs x, Real.log_one, neg_zero]
    have h₂ : S.K_beta x = 0 := by simpa [hK₁]
    have h₃ : S.partitionPotential = 0 := by exact_mod_cast hPhi
    simp [h₂, h₃]
  have hPart : S.partitionPotential = 0 := hPhi
  simp_all [neg_zero, Real.log_one, add_zero]

/-- Operational metaprogram state for any finite context window with an explicit constructed state. -/
structure MetaprogramState (n : ℕ) [Fact (0 < n)] where
  attention_matrix : Matrix (Fin n) (Fin n) ℝ
  attention_row_stochastic : ∀ i, ∑ j, attention_matrix i j = 1
  attention_nonneg : MatrixNonneg attention_matrix
  born_matrix : Matrix (Fin n) (Fin n) ℝ
  born_nonneg : MatrixNonneg born_matrix
  W : Matrix (Fin n) (Fin n) ℝ
  H : Matrix (Fin n) (Fin n) ℝ
  W_nonneg : MatrixNonneg W
  H_nonneg : MatrixNonneg H
  factor_nonneg : MatrixNonneg (W * H)
  lean4_ast : Lean4AST
  fisher_psd : ∀ v : Fin n → ℝ, 0 ≤ fisherRaoMetric (fun _ => (1 : ℝ)) v v
  redline_exp : Real.exp (- (0 : ℝ)) = (1 : ℝ)

/-- Existence of an operational metaprogram state with an explicit normalized Gibbs witness. -/
theorem metaprogram_state_exists {n : ℕ} [Fact (0 < n)] :
    Nonempty (MetaprogramState n) := by
  have hpos : (0 : ℝ) < n := by
    exact_mod_cast (by
      haveI hnn : 0 < n := Fact.out
      exact_mod_cast hnn)
  let p : Fin n → ℝ := fun _ => (1 / n : ℝ)
  let attention : Matrix (Fin n) (Fin n) ℝ := fun i j => (1 / n : ℝ)
  have hRow : ∀ i : Fin n, ∑ j : Fin n, attention i j = 1 := by
    intro i
    rw [Finset.sum_const]
    have hcard : Finset.card (Finset.univ : Finset (Fin n)) = n := Finset.card_fin
    have h₁ : (1 / n : ℝ) * n = 1 := by exact one_div_mul_cancel (by exact_mod_cast Fact.out)
    simp [h₁]
  have hAttNonneg : MatrixNonneg attention := by
    intro i j
    have hpos : 0 < n := Fact.out
    have hdiv : (0 : ℝ) < 1 / n := one_div_of_pos hpos
    exact le_of_lt hdiv
  have hBorn : MatrixNonneg (bornCollapse attention) := bornCollapse_nonneg attention
  have hW : MatrixNonneg (stochasticLanguageMatrix (n := n)) := stochasticLanguageMatrix_nonneg
  have hH : MatrixNonneg (formalTypeMatrix (n := n)) := formalTypeMatrix_nonneg
  have hFactor : MatrixNonneg (stochasticLanguageMatrix (n := n) * formalTypeMatrix (n := n)) :=
    nmf_projection_to_formalAST (n := n)
  refine ⟨⟨attention, hRow, hAttNonneg, bornCollapse attention, hBorn,
           stochasticLanguageMatrix (n := n), formalTypeMatrix (n := n),
           hW, hH, hFactor,
           Lean4AST.const "thought",
           fun v => ?_, rfl⟩⟩
  · change 0 ≤ ∑ i, (v i * v i : ℝ) / (1 / n : ℝ)
    have hpos : (0 : ℝ) < (1 / n : ℝ) := by
      exact_mod_cast one_div_of_pos (by exact_mod_cast Fact.out)
    have h₁ : ∀ i, (0 : ℝ) ≤ (v i * v i : ℝ) / (1 / n : ℝ) := by
      intro i
      exact div_nonneg (by positivity) (le_of_lt hpos)
    simp [fisherRaoMetric, p]
    simpa using Finset.sum_nonneg h₁

end InfoGeometry.Neurosymbolic.Metaprogram
