import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Fibonacci product statistic on a finite list encoding a finite multiset of path lengths. -/
def conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct
    (lengths : List ℕ) : ℕ :=
  (lengths.map fun ell => Nat.fib (ell + 2)).prod

/-- The singleton spectrum `{4}`. -/
def conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum : List ℕ :=
  [4]

/-- The triple spectrum `{1, 1, 1}`. -/
def conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum : List ℕ :=
  [1, 1, 1]

/-- The explicit product collision `F_6 = F_3^3`. -/
def productCollision : Prop :=
  conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum =
    conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct
      conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum ∧
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum ≠
        conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum

/-- The Fibonacci product statistic is not injective on finite spectra. -/
def noninjective : Prop :=
  ∃ A B : List ℕ,
    A ≠ B ∧
      conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct A =
        conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct B

/-- Equal product multiplicity can identify spectra with different internal graph sizes. -/
def losesGraphType : Prop :=
  ∃ A B : List ℕ,
    A ≠ B ∧
      conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct A =
        conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct B ∧
      A.length ≠ B.length

/-- Paper label: `prop:conclusion-fiber-multiplicity-product-noninjective`. -/
theorem paper_conclusion_fiber_multiplicity_product_noninjective
    : productCollision ∧ noninjective ∧ losesGraphType := by
  have hcollision :
      conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct
          conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum =
        conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct
          conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum := by
    norm_num [conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct,
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum,
      conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum, Nat.fib]
  have hne :
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum ≠
        conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum := by
    decide
  refine ⟨⟨hcollision, hne⟩, ?_, ?_⟩
  · exact ⟨
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum,
      conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum,
      hne, hcollision⟩
  · refine ⟨
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum,
      conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum,
      hne, hcollision, ?_⟩
    decide

end Omega.Conclusion
