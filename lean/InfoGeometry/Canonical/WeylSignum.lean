import Mathlib
import InfoGeometry.Arithmetic.MoebiusSignature

/-!
# Weyl Signum

Finite theorem-owned signum layer for the prime `A₁^P` Weyl group.

#### BUCKET 1: CLOSED FINITE THEOREMS
`weylSignum_eq_mobius` identifies the finite Weyl sign with Mathlib's Möbius
function on the square-free product represented by a finite prime subset.
`signum_trace_annihilation` proves trace preservation under an involutive
boundary twist from explicit hypotheses.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`signum_trace_annihilation` requires the explicit premises
`M_parity * M_parity = 1` and `trace Γ_signum = 0`.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not construct an infinite affine Weyl group, an `E₇(₇)`
representation, a Weyl-Kac character formula, or a Riemann-zero theorem.
-/

noncomputable section

namespace WeylSignum

open Matrix
open InfoGeometry.Algebra

/-- Finite Weyl signum for the Boolean Weyl group of a prime `A₁^P` system. -/
def weylSignum {S : PrimeA1RootSystem} (w : S.WeylGroup) : ℤ :=
  S.signature w

/--
Finite Weyl sign equals the arithmetic Möbius value of the represented
square-free prime product.
-/
theorem weylSignum_eq_mobius {S : PrimeA1RootSystem} (w : S.WeylGroup) :
    weylSignum w = ArithmeticFunction.moebius (InfoGeometry.Arithmetic.weylToNat w) := by
  exact InfoGeometry.Arithmetic.weyl_sign_eq_moebius w

/--
Trace-free signum operators remain trace-free after an involutive boundary
twist.

This is the finite matrix trace transport lemma.  The trace-free and
involutive assumptions are explicit hypotheses; no global Weyl geometry is
hidden in a structure field.
-/
theorem signum_trace_annihilation
    (Γ_signum M_parity : Matrix (Fin 32) (Fin 32) ℝ)
    (h_twist : M_parity * M_parity = 1)
    (h_trace : Matrix.trace Γ_signum = 0) :
    Matrix.trace (M_parity * Γ_signum * M_parity) = 0 := by
  have h1 :
      Matrix.trace (M_parity * Γ_signum * M_parity) =
        Matrix.trace (M_parity * (M_parity * Γ_signum)) := by
    rw [Matrix.trace_mul_comm (M_parity * Γ_signum) M_parity]
  have h2 :
      M_parity * (M_parity * Γ_signum) =
        (M_parity * M_parity) * Γ_signum := by
    rw [Matrix.mul_assoc]
  rw [h1, h2, h_twist, Matrix.one_mul]
  exact h_trace

end WeylSignum

