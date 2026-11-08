import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Virasoro.VirasoroAlgebra

/-!
# InfoGeometry.Canonical.VirasoroRecursiveSchema

Recursive/iterative proof schema for Virasoro adjoint dynamics,
using the external Virasoro algebra as boundary data.
-/

namespace InfoGeometry.Canonical.VirasoroRecursiveSchema

open VirasoroProject
open VirasoroProject.VirasoroAlgebra

section

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

/-- Single-step adjoint action by `L_n`. -/
noncomputable def adL (n : ℤ) (X : VirasoroAlgebra 𝕜) : VirasoroAlgebra 𝕜 :=
  ⁅lgen 𝕜 n, X⁆

/-- Recursive iterated adjoint action by `L_n`. -/
noncomputable def adPowL (n : ℤ) : ℕ → VirasoroAlgebra 𝕜 → VirasoroAlgebra 𝕜
  | 0, X => X
  | k + 1, X => adL 𝕜 n (adPowL n k X)

@[simp] theorem adPowL_zero (n : ℤ) (X : VirasoroAlgebra 𝕜) :
    adPowL 𝕜 n 0 X = X := rfl

@[simp] theorem adPowL_succ (n : ℤ) (k : ℕ) (X : VirasoroAlgebra 𝕜) :
    adPowL 𝕜 n (k + 1) X = adL 𝕜 n (adPowL 𝕜 n k X) := rfl

/-- First recursive step on generators is the external Virasoro bracket formula. -/
theorem adPowL_one_lgen (n m : ℤ) :
    adPowL 𝕜 n 1 (lgen 𝕜 m)
      = (n - m : 𝕜) • lgen 𝕜 (n + m)
        + if n + m = 0 then ((n^3 - n : 𝕜) / 12) • cgen 𝕜 else 0 := by
  simp [adPowL, adL, lgen_bracket]

/-- Non-resonant first step (`n+m ≠ 0`): no central correction. -/
theorem adPowL_one_lgen_of_ne_zero (n m : ℤ) (h : n + m ≠ 0) :
    adPowL 𝕜 n 1 (lgen 𝕜 m) = (n - m : 𝕜) • lgen 𝕜 (n + m) := by
  simp [adPowL, adL, lgen_bracket_of_ne_zero, h]

/-- Resonant first step (`n+m = 0`): central correction appears. -/
theorem adPowL_one_lgen_of_add_eq_zero (n m : ℤ) (h : n + m = 0) :
    adPowL 𝕜 n 1 (lgen 𝕜 m) =
      (n - m : 𝕜) • lgen 𝕜 (n + m) + ((n^3 - n : 𝕜) / 12) • cgen 𝕜 := by
  simp [adPowL, adL, lgen_bracket_of_add_eq_zero, h]

/--
Iterative schema theorem:
for every recursion depth `r`, the next step is obtained by one extra `adL`.
-/
theorem adPowL_iterative_schema (n : ℤ) :
    ∀ r : ℕ, ∀ X : VirasoroAlgebra 𝕜,
      adPowL 𝕜 n (r + 1) X = adL 𝕜 n (adPowL 𝕜 n r X) := by
  intro r X
  simp [adPowL]

end

end InfoGeometry.Canonical.VirasoroRecursiveSchema

