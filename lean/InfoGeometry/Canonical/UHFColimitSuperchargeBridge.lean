import Mathlib.Tactic
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Canonical.ChiralParitySuperalgebra

/-!
# Continuum Limit of Chiral Supercharges

This file bridges the finite algebraic super-geometry defined in 
`ChiralParitySuperalgebra.lean` into the continuum boundary using the 
inductive colimit structures from `TensorTowerColimit.lean`.

By passing the discrete, finite-stage grading operators and supercharges 
through a compatible algebraic cone into a target algebra, we establish that
the Lie superalgebra and the central supercharge condensation 
survive under that target map.  This file does not assert the universal
property of a categorical colimit or any analytic/topological limit.
-/

variable {R : Type*} [CommRing R]
variable (A : ℕ → Type*)
variable [∀ n, Ring (A n)] [∀ n, Algebra R (A n)]
variable (A_inf : Type*) [Ring A_inf] [Algebra R A_inf]

-- The inductive sequence of algebra embeddings
variable (iota : ∀ n, A n →ₐ[R] A (n + 1))
variable (psi : ∀ n, A n →ₐ[R] A_inf)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)

namespace NoncommutativeGeometry

/-- The grading operator survives the colimit map. -/
lemma colimit_grading_survival (n : ℕ) (Γ_n : A n) [hΓ : OperatorChirality Γ_n] :
    OperatorChirality (psi n Γ_n) where
  inv_sq := by
    have h1 : Γ_n * Γ_n = 1 := hΓ.inv_sq
    calc
      psi n Γ_n * psi n Γ_n = psi n (Γ_n * Γ_n) := (map_mul (psi n) Γ_n Γ_n).symm
      _ = psi n 1 := by rw [h1]
      _ = 1 := map_one (psi n)

/-- Odd parity (fermionic behavior) is strictly preserved by the colimit map. -/
lemma colimit_odd_survival (n : ℕ) (Γ_n : A n) (Q : A n) (h_odd : isOdd Γ_n Q) :
    isOdd (psi n Γ_n) (psi n Q) := by
  unfold isOdd at h_odd ⊢
  calc
    psi n Γ_n * psi n Q + psi n Q * psi n Γ_n 
      = psi n (Γ_n * Q) + psi n (Q * Γ_n) := by rw [← map_mul (psi n), ← map_mul (psi n)]
    _ = psi n (Γ_n * Q + Q * Γ_n) := (map_add (psi n) _ _).symm
    _ = psi n 0 := by rw [h_odd]
    _ = 0 := map_zero (psi n)

/-- Even parity (bosonic behavior) is strictly preserved by the colimit map. -/
lemma colimit_even_survival (n : ℕ) (Γ_n : A n) (X : A n) (h_even : isEven Γ_n X) :
    isEven (psi n Γ_n) (psi n X) := by
  unfold isEven at h_even ⊢
  calc
    psi n Γ_n * psi n X = psi n (Γ_n * X) := (map_mul (psi n) Γ_n X).symm
    _ = psi n (X * Γ_n) := by rw [h_even]
    _ = psi n X * psi n Γ_n := map_mul (psi n) X Γ_n

lemma anticommutator_map (n : ℕ) (Q Q' : A n) :
    anticomm (psi n Q) (psi n Q') = psi n (anticomm Q Q') := by
  unfold anticomm
  rw [map_add, map_mul, map_mul]

/-- 
**The Continuum Condensation Theorem**
If Q and Q' are finite-stage chiral supercharges, their anticommutator 
condenses to an even central supercharge structurally intact inside the 
continuum boundary A_∞.
-/
theorem continuum_superalgebra_closure (n : ℕ) (Γ_n : A n) [OperatorChirality Γ_n]
    (Q Q' : A n) [hQ : IsChiralSupercharge Γ_n Q] [hQ' : IsChiralSupercharge Γ_n Q'] :
    isEven (psi n Γ_n) (anticomm (psi n Q) (psi n Q')) := by
  rw [anticommutator_map]
  -- We know from the finite stage that the anticommutator is Even
  have h_finite_even : isEven Γ_n (anticomm Q Q') := superalgebra_closure Γ_n Q Q'
  
  -- Transport the evenness to the colimit
  exact colimit_even_survival A A_inf psi n Γ_n (anticomm Q Q') h_finite_even

end NoncommutativeGeometry
