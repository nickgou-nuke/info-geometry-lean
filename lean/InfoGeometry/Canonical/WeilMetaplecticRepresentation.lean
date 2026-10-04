import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.SylvesterIwasawaKAN

/-!
# Algebraic Egorov identities for finite matrix words

This file records the exact algebraic content of the displayed covariance
equations. It does not construct a Weil representation: a matrix `U`, a
two-sided inverse, and the covariance equations are not supplied as fields of
a “representation” structure. Instead, the covariance equations are proved
equivalent to their intertwining forms for any invertible matrix.

The exponent in `displacementWord` is a natural-number encoding. Reduction
modulo a dimension requires an additional root-of-unity theorem and is not
implicit in this definition.
-/

namespace InfoGeometry.Canonical.WeilMetaplecticRepresentation

open InfoGeometry.Canonical.SylvesterIwasawaKAN

variable {R : Type*} [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ordered clock-shift word with its chosen natural exponent convention.
This is not yet a modular displacement operator unless periodicity is proved. -/
def displacementWord (ω : R) (X Z : Matrix n n R)
    (inv2 u v : ℕ) : Matrix n n R :=
  (ω ^ (inv2 * u * v)) • ((X ^ u) * (Z ^ v))

/-- Egorov covariance on the shift is equivalent to its intertwining equation. -/
theorem egorov_X_iff_intertwining
    (ω : R) (X Z U Uinv : Matrix n n R) (inv2 a c : ℕ)
    (hleft : Uinv * U = 1) (hright : U * Uinv = 1) :
    U * X * Uinv = displacementWord ω X Z inv2 a c ↔
      U * X = displacementWord ω X Z inv2 a c * U := by
  constructor
  · intro h
    calc
      U * X = U * X * 1 := by rw [Matrix.mul_one]
      _ = U * X * (Uinv * U) := by rw [hleft]
      _ = (U * X * Uinv) * U := by simp only [Matrix.mul_assoc]
      _ = displacementWord ω X Z inv2 a c * U := by rw [h]
  · intro h
    calc
      U * X * Uinv = (U * X) * Uinv := by simp only [Matrix.mul_assoc]
      _ = (displacementWord ω X Z inv2 a c * U) * Uinv := by rw [h]
      _ = displacementWord ω X Z inv2 a c * (U * Uinv) := by
        simp only [Matrix.mul_assoc]
      _ = displacementWord ω X Z inv2 a c := by rw [hright, Matrix.mul_one]

/-- Egorov covariance on the clock is equivalent to its intertwining equation. -/
theorem egorov_Z_iff_intertwining
    (ω : R) (X Z U Uinv : Matrix n n R) (inv2 b d : ℕ)
    (hleft : Uinv * U = 1) (hright : U * Uinv = 1) :
    U * Z * Uinv = displacementWord ω X Z inv2 b d ↔
      U * Z = displacementWord ω X Z inv2 b d * U := by
  constructor
  · intro h
    calc
      U * Z = U * Z * 1 := by rw [Matrix.mul_one]
      _ = U * Z * (Uinv * U) := by rw [hleft]
      _ = (U * Z * Uinv) * U := by simp only [Matrix.mul_assoc]
      _ = displacementWord ω X Z inv2 b d * U := by rw [h]
  · intro h
    calc
      U * Z * Uinv = (U * Z) * Uinv := by simp only [Matrix.mul_assoc]
      _ = (displacementWord ω X Z inv2 b d * U) * Uinv := by rw [h]
      _ = displacementWord ω X Z inv2 b d * (U * Uinv) := by
        simp only [Matrix.mul_assoc]
      _ = displacementWord ω X Z inv2 b d := by rw [hright, Matrix.mul_one]

/-- Conjugation by a two-sidedly invertible matrix preserves products. This is
the algebraic step needed to extend covariance identities from generators to
ordered words. -/
private theorem conjugate_mul
    (U Uinv A B : Matrix n n R) (hleft : Uinv * U = 1) :
    (U * A * Uinv) * (U * B * Uinv) = U * (A * B) * Uinv := by
  calc
    (U * A * Uinv) * (U * B * Uinv) = U * A * Uinv * U * B * Uinv := by
      simp only [Matrix.mul_assoc]
    _ = U * A * (Uinv * U) * B * Uinv := by
      simp only [Matrix.mul_assoc]
    _ = U * (A * B) * Uinv := by
      rw [hleft]
      simp only [Matrix.one_mul, Matrix.mul_assoc]

/-- Conjugation by an invertible matrix carries every natural power of a
matrix to the corresponding power of its conjugate. -/
private theorem conjugate_pow
    (U Uinv A : Matrix n n R) (hleft : Uinv * U = 1)
    (hright : U * Uinv = 1) (k : ℕ) :
    U * A ^ k * Uinv = (U * A * Uinv) ^ k := by
  induction k with
  | zero => simp [hright]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      calc
        U * (A ^ k * A) * Uinv =
            (U * A ^ k * Uinv) * (U * A * Uinv) :=
              (conjugate_mul U Uinv (A ^ k) A hleft).symm
        _ = (U * A * Uinv) ^ k * (U * A * Uinv) := by rw [ih]

/-- Generator covariance extends to every ordered monomial `X^u * Z^v`.
This is an algebraic Egorov theorem; modular phase reduction and construction
of a Weil operator remain separate obligations. -/
theorem egorov_orderedMonomial
    (X Z U Uinv : Matrix n n R) (u v : ℕ)
    (hleft : Uinv * U = 1) (hright : U * Uinv = 1) :
    U * (X ^ u * Z ^ v) * Uinv =
      (U * X * Uinv) ^ u * (U * Z * Uinv) ^ v := by
  calc
    U * (X ^ u * Z ^ v) * Uinv =
        (U * X ^ u * Uinv) * (U * Z ^ v * Uinv) :=
          (conjugate_mul U Uinv (X ^ u) (Z ^ v) hleft).symm
    _ = (U * X * Uinv) ^ u * (U * Z * Uinv) ^ v := by
      rw [conjugate_pow U Uinv X hleft hright u,
        conjugate_pow U Uinv Z hleft hright v]

end InfoGeometry.Canonical.WeilMetaplecticRepresentation
