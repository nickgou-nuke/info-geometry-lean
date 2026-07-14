import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic

noncomputable section

namespace QCCRCore

/-!
# q-CCR core algebraic surface

This file introduces only the minimal algebraic relation surface for the
$q$-deformed canonical commutation relation:

    a_i^* a_j - q · a_j a_i^* = δ_{ij} · 1

Special limits:
- q = 0   → Cuntz–Toeplitz isometry: a_i^* a_j = δ_{ij} · 1
- q = −1  → CAR anticommutator: {a_i^*, a_j} = δ_{ij} · 1
- q = +1  → CCR commutator: [a_i^*, a_j] = δ_{ij} · 1

The file depends only on basic algebra/star/real imports and has no repository
internal imports.
-/

/--
The q-CCR structure on an operator algebra `Op` with `N` generators.

The relation is: `star(a_i) * a_j = δ_{ij} + q · a_j · star(a_i)`.
-/
structure QCCRAlgebra (N : ℕ) (Op : Type*) [Ring Op] [StarRing Op] [Algebra ℝ Op] where
  a     : Fin N → Op
  q     : ℝ
  q_commutation : ∀ i j : Fin N, star (a i) * (a j) = (if i = j then (1 : Op) else 0) + q • ((a j) * star (a i))

namespace QCCRAlgebra

/-- At q = 0, the q-CCR relation reduces to the Cuntz–Toeplitz isometry condition. -/
theorem q_zero_is_cuntz (N : ℕ) (Op : Type*) [Ring Op] [StarRing Op] [Algebra ℝ Op]
    (A : QCCRAlgebra N Op) (hq0 : A.q = 0) (i j : Fin N) :
    star (A.a i) * (A.a j) = if i = j then (1 : Op) else 0 := by
  have h := A.q_commutation i j
  rw [hq0] at h
  simpa [zero_smul, add_zero] using h

/-- At q = -1, the q-CCR relation enforces the CAR anticommutator. -/
theorem q_neg_one_is_car (N : ℕ) (Op : Type*) [Ring Op] [StarRing Op] [Algebra ℝ Op]
    (A : QCCRAlgebra N Op) (hq_neg1 : A.q = -1) (i j : Fin N) :
    star (A.a i) * (A.a j) + (A.a j) * star (A.a i) = if i = j then (1 : Op) else 0 := by
  have h := A.q_commutation i j
  rw [hq_neg1] at h
  have : (-1 : ℝ) • ((A.a j) * star (A.a i)) + (A.a j) * star (A.a i) = 0 := by simp
  calc
    star (A.a i) * (A.a j) + (A.a j) * star (A.a i)
        = ((if i = j then (1 : Op) else 0) + (-1 : ℝ) • ((A.a j) * star (A.a i))) + (A.a j) * star (A.a i) := by rw [h]
    _ = (if i = j then (1 : Op) else 0) + ((-1 : ℝ) • ((A.a j) * star (A.a i)) + (A.a j) * star (A.a i)) := by
      simp [add_assoc]
    _ = (if i = j then (1 : Op) else 0) := by simp

/-- At q = 1, the q-CCR relation enforces the CCR commutator. -/
theorem q_one_is_ccr (N : ℕ) (Op : Type*) [Ring Op] [StarRing Op] [Algebra ℝ Op]
    (A : QCCRAlgebra N Op) (hq1 : A.q = 1) (i j : Fin N) :
    star (A.a i) * (A.a j) - (A.a j) * star (A.a i) = if i = j then (1 : Op) else 0 := by
  have h := A.q_commutation i j
  rw [hq1] at h
  calc
    star (A.a i) * (A.a j) - (A.a j) * star (A.a i)
        = ((if i = j then (1 : Op) else 0) + (1 : ℝ) • ((A.a j) * star (A.a i))) - (A.a j) * star (A.a i) := by rw [h]
    _ = (if i = j then (1 : Op) else 0) := by simp

end QCCRAlgebra

end QCCRCore
