import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.End

/-!
QMS isolated proof target for `InfoGeometry.Capstone.BenamouBrenierBridge`.

Pure mathematical context:
- `R` is a commutative ring.
- `M` is an additive commutative group and `R`-module.
- `Module.End R M` is the noncommutative ring of `R`-linear endomorphisms of `M`.
- `N : Module.End R M` is the algebraic JKO nilpotent generator.
- The premise `N * N = 0` is square-zero nilpotency: the second-order parabolic direction vanishes exactly.
- The discrete JKO bonding step is `1 + N`.
- Since every product containing two consecutive `N` factors vanishes, the finite power collapses exactly:
  `(1 + N)^n = 1 + n • N`.
- This is an algebraic Hestenes--Krein/direct-colimit finite-stage law, not an analytic convergence theorem.

Existing Lean/mathlib context:
- `Module.End R M` has ring structure with distributivity.
- `nsmul` on endomorphisms is additive repeated sum.
- The helper lemma `(n • N) * N = 0` follows by induction from `N * N = 0`.
- The main theorem follows by induction using distributivity and additive normalization.
-/

namespace InfoGeometry.QMS.BenamouBrenierNilpotentCollapse

variable (R : Type*) [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

def JKO_Endomorphism (N : Module.End R M) : Prop :=
  N * N = 0

lemma nsmul_mul_self_eq_zero
    (N : Module.End R M) (h_nil : JKO_Endomorphism R M N) (n : ℕ) :
    (n • N) * N = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, add_mul, ih, h_nil]
      simp

/-- Exact finite nilpotent collapse for the algebraic JKO step. -/
theorem jko_operator_collapse
    (N : Module.End R M) (h_nil : JKO_Endomorphism R M N) (n : ℕ) :
    (1 + N) ^ n = 1 + n • N := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih]
      rw [mul_add, mul_one]
      rw [add_mul, one_mul, nsmul_mul_self_eq_zero R M N h_nil k]
      change 1 + k • N + (N + 0) = 1 + Nat.succ k • N
      rw [succ_nsmul]
      simp [add_assoc]

end InfoGeometry.QMS.BenamouBrenierNilpotentCollapse
