import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Algebra.StochasticGrammarCuntzKriegerBridge

/-- **Definition**: Row-Stochastic Language Transition Matrix A (n x n).
    A(i, j) ≥ 0, and ∑_{j} A(i, j) = 1 for all states i. -/
structure StochasticTransitionMatrix (n : ℕ) where
  A : Fin n → Fin n → ℝ
  nonneg : ∀ i j, 0 ≤ A i j
  row_sum : ∀ i, (Finset.univ : Finset (Fin n)).sum (fun j => A i j) = 1

namespace StochasticTransitionMatrix

variable {n : ℕ} (M : StochasticTransitionMatrix n)

/-- Square-Root Amplitude Language Transition Matrix Ψ(i, j) = √(A(i, j)). -/
def amplitudeMatrix (i j : Fin n) : ℝ :=
  Real.sqrt (M.A i j)

/-- **Theorem**: Amplitude Matrix Row L2 Normalization on Unit Sphere.
    For each state i, ∑_{j} Ψ(i, j)^2 = 1. -/
theorem amplitude_row_l2_normalization (i : Fin n) :
    (Finset.univ : Finset (Fin n)).sum (fun j => (M.amplitudeMatrix i j)^2) = 1 := by
  dsimp [amplitudeMatrix]
  have h_sq : ∀ j, (Real.sqrt (M.A i j))^2 = M.A i j := fun j => Real.sq_sqrt (M.nonneg i j)
  calc (Finset.univ : Finset (Fin n)).sum (fun j => (Real.sqrt (M.A i j))^2)
    _ = (Finset.univ : Finset (Fin n)).sum (fun j => M.A i j) := by
      congr 1
      ext j
      exact h_sq j
    _ = 1 := M.row_sum i

end StochasticTransitionMatrix

/-- **Definition**: Bhattacharyya Language Transition Fidelity between Models M1 and M2 at State i.
    BC_i(M1, M2) = ∑_{j} √(A1(i, j) * A2(i, j)). -/
def bhattacharyyaLanguageFidelity {n : ℕ} (M1 M2 : StochasticTransitionMatrix n) (i : Fin n) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun j => Real.sqrt (M1.A i j * M2.A i j))

/-- **Theorem**: Bhattacharyya Language Fidelity as Amplitude Inner Product.
    BC_i(M1, M2) = ⟨Ψ1(i, ·), Ψ2(i, ·)⟩. -/
theorem bhattacharyya_language_fidelity_eq_inner_product
    {n : ℕ} (M1 M2 : StochasticTransitionMatrix n) (i : Fin n) :
    bhattacharyyaLanguageFidelity M1 M2 i =
      (Finset.univ : Finset (Fin n)).sum (fun j => M1.amplitudeMatrix i j * M2.amplitudeMatrix i j) := by
  dsimp [bhattacharyyaLanguageFidelity, StochasticTransitionMatrix.amplitudeMatrix]
  congr 1
  ext j
  rw [Real.sqrt_mul (M1.nonneg i j)]

/-- **Theorem**: Master Stochastic Grammar & Cuntz-Krieger Information Synthesis.
    Unifies:
    1. Stochastic transition row sum ∑_{j} A(i, j) = 1.
    2. Amplitude row L2 normalization ∑_{j} Ψ(i, j)^2 = 1.
    3. Bhattacharyya language model overlap as amplitude inner product. -/
theorem master_stochastic_grammar_cuntz_krieger_synthesis
    {n : ℕ} (M1 M2 : StochasticTransitionMatrix n) (i : Fin n) :
    ((Finset.univ : Finset (Fin n)).sum (fun j => M1.A i j) = 1) ∧
    ((Finset.univ : Finset (Fin n)).sum (fun j => (M1.amplitudeMatrix i j)^2) = 1) ∧
    (bhattacharyyaLanguageFidelity M1 M2 i =
      (Finset.univ : Finset (Fin n)).sum (fun j => M1.amplitudeMatrix i j * M2.amplitudeMatrix i j)) := ⟨
  M1.row_sum i,
  M1.amplitude_row_l2_normalization i,
  bhattacharyya_language_fidelity_eq_inner_product M1 M2 i
⟩

end InfoGeometry.Algebra.StochasticGrammarCuntzKriegerBridge
