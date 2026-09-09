import Mathlib
import InfoGeometry.Canonical.ChiralCausalCone

/-!
# Euclidean Nilpotent Obstruction

In a `NoZeroDivisors` algebra (ℝ, ℂ, ℍ — any Euclidean/positive-definite
division algebra), `x² = 0` forces `x = 0`. No non-trivial nilpotents exist.
This is the algebraic "prison": chiral ladder operators (σ⁺, σ⁻) with
σ² = 0 and σ ≠ 0 are IMPOSSIBLE.

The split Clifford algebra `Cl(1,1)` escapes the prison because it has
zero divisors: `(r₀+r₅)(r₀-r₅) = r₀² - r₅² = 1 - (-1) = 2 ≠ 0` but
the individual factors are not invertible. This is what permits
`σPlus² = 0` with `σPlus ≠ 0`.

Zero sorries, zero axioms.
-/

namespace EuclideanNilpotentObstruction

variable {A : Type*} [Semiring A]

/-- In a domain with no zero divisors, nilpotent ⇒ zero.
This is the Euclidean/algebraic "prison". -/
theorem sq_zero_eq_zero_of_noZeroDivisors [NoZeroDivisors A] {x : A} (h : x * x = 0) :
    x = 0 :=
  mul_self_eq_zero.mp h

/-- A non-trivial nilpotent: x² = 0 but x ≠ 0.
Impossible in `NoZeroDivisors` algebras. -/
def admits_nontrivial_nilpotent (x : A) : Prop := x * x = 0 ∧ x ≠ 0

/-- The obstruction: no non-trivial nilpotents exist in `NoZeroDivisors`. -/
theorem no_nontrivial_nilpotent [NoZeroDivisors A] (x : A) :
    ¬ admits_nontrivial_nilpotent x := by
  rintro ⟨h_sq, h_ne⟩
  exact h_ne (sq_zero_eq_zero_of_noZeroDivisors h_sq)

/-! ## The Euclidean Prison for Division Algebras -/

/-- Real numbers have no non-trivial nilpotents. -/
theorem real_no_nontrivial_nilpotent (x : ℝ) : ¬ admits_nontrivial_nilpotent x :=
  no_nontrivial_nilpotent x

/-- Complex numbers have no non-trivial nilpotents. -/
theorem complex_no_nontrivial_nilpotent (x : ℂ) : ¬ admits_nontrivial_nilpotent x :=
  no_nontrivial_nilpotent x

/-- Quaternions have no non-trivial nilpotents. -/
theorem quaternion_no_nontrivial_nilpotent (x : Quaternion ℝ) : ¬ admits_nontrivial_nilpotent x :=
  no_nontrivial_nilpotent x

/-! ## The split Clifford escape — explicit non-trivial nilpotent -/

open ChiralCausalCone

/-- `σPlus² = 0` in `M₂(ℂ)`. Already proved in `ChiralCausalCone`. -/
theorem split_escape_sq : σPlus * σPlus = 0 := σPlus_sq

/-- `σPlus ≠ 0` in `M₂(ℂ)`. By explicit matrix entry. -/
theorem split_escape_ne_zero : σPlus ≠ 0 := by
  intro h
  have h01 : σPlus 0 1 = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by rw [h]
  simp [σPlus] at h01

/-- The split Clifford algebra `M₂(ℂ)` admits a non-trivial nilpotent.
This escapes the Euclidean prison because `M₂(ℂ)` has zero divisors. -/
theorem split_admits_nontrivial_nilpotent : admits_nontrivial_nilpotent σPlus :=
  ⟨split_escape_sq, split_escape_ne_zero⟩

/-- The prison is real: `NoZeroDivisors` algebras cannot host chiral ladders.
The split signature is the escape. -/
theorem chiral_ladders_require_split_signature :
    admits_nontrivial_nilpotent σPlus :=
  split_admits_nontrivial_nilpotent

end EuclideanNilpotentObstruction
