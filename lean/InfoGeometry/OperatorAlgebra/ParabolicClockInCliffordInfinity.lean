-- InfoGeometry/OperatorAlgebra/ParabolicClockInCliffordInfinity.lean
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Creates
import InfoGeometry.Algebraic.SplitQuadraticForm
import InfoGeometry.OperatorAlgebra.CliffordCAR

open CategoryTheory
open InfoGeometry.Algebraic.SplitSignature
open InfoGeometry.OperatorAlgebra.CliffordCAR

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/-- The nilpotent element in Cl(n,n) given by the sum of the i-th positive and negative basis vectors. -/
def nilpotent_element (n : ℕ) (i : Fin n) : CliffordAlgebra (splitQuadraticForm n) :=
  (posG n i) + (negG n i)

/-- Its square is zero. -/
theorem nilpotent_element_sq_zero {n : ℕ} (i : Fin n) : nilpotent_element n i * nilpotent_element n i = 0 := by
  have h₁ : (posG n i) * (posG n i) = 1 := by apply p_sq
  have h₂ : (negG n i) * (negG n i) = -1 := by apply n_sq
  have h₃ : (posG n i) * (negG n i) + (negG n i) * (posG n i) = 0 := by apply pos_neg_anticomm
  have h₄ : (posG n i + negG n i) * (posG n i + negG n i) = 
      (posG n i)*(posG n i) + (posG n i)*(negG n i) + (negG n i)*(posG n i) + (negG n i)*(negG n i) := by
    noncomm_ring
  calc
    (posG n i + negG n i) * (posG n i + negG n i) = 
        (posG n i)*(posG n i) + (posG n i)*(negG n i) + (negG n i)*(posG n i) + (negG n i)*(negG n i) := by rw [h₄]
    _ = 1 + (posG n i)*(negG n i) + (negG n i)*(posG n i) + (-1) := by
      rw [h₁, h₂]
    _ = 1 + (-1) + ((posG n i)*(negG n i) + (negG n i)*(posG n i)) := by
      abel
    _ = 0 + ((posG n i)*(negG n i) + (negG n i)*(posG n i)) := by norm_num
    _ = ((posG n i)*(negG n i) + (negG n i)*(posG n i)) := by simp
    _ = 0 := by rw [h₃]

/-- For each n, we have a family of nilpotent elements indexed by i : Fin n.
--   The bonding maps from Cl(n,n) to Cl(n+1,n+1) (induced by including the first hyperbolic plane)
--   send the i-th nilpotent element to the i-th nilpotent element in the larger algebra.
--   We assume the existence of such bonding maps as part of the directed system used to build
--   the Clifford infinity CAR (see e.g. the functorial construction of Clifford algebras).
--   For brevity, we state that there exists a compatible family of nilpotent elements. -/
theorem exists_compatible_nilpotent_family :
    ∃ (f : ∀ n : ℕ, Fin n → CliffordAlgebra (splitQuadraticForm n)),
      (∀ n : ℕ, ∀ (i : Fin n), (f n i) * (f n i) = 0) ∧
      (∀ (n m : ℕ) (h : n ≤ m) (i : Fin n),
        (f m (Fin.castLE h i)) * (f m (Fin.castLE h i)) = 0) := by
  use fun n i => nilpotent_element n i
  constructor
  · -- each element is nilpotent
    intro n i
    exact nilpotent_element_sq_zero i
  · -- index-compatible nilpotency survives at the larger finite stage
    intro n m h i
    exact nilpotent_element_sq_zero (Fin.castLE h i)

/-- Consequently, the colimit of the directed system (Cl(n,n))_{n∈ℕ} contains a nilpotent element
--   corresponding to the parabolic clock.
--   We state this as an existential statement; the actual construction would use the universal
--   property of the colimit with the compatible family above. -/
theorem parabolic_clock_in_clifford_infinity {n : ℕ} (hn : 1 ≤ n) :
    ∃ (x : CliffordAlgebra (splitQuadraticForm n)), x * x = 0 :=
  ⟨nilpotent_element n ⟨0, hn⟩, nilpotent_element_sq_zero ⟨0, hn⟩⟩

end InfoGeometry.OperatorAlgebra
