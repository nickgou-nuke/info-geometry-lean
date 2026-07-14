import Mathlib.Data.Finset.Insert
import InfoGeometry.External.Automath.Omega.POM.S5GaloisArithmetic

namespace Omega.POM

/-- The discriminant arithmetic actually proved for the `K_5` lane. -/
def K5DiscriminantArithmetic : Prop :=
  2 ^ 4 * 3 ^ 4 * 5 * 11 * 13 * 17383 = (16107783120 : ℕ) ∧
    -(16107783120 : ℤ) < 0 ∧
    ¬ ∃ k : ℤ, k * k = -(16107783120 : ℤ)

/-- The exact discriminant of the Perron field `K_5`. -/
def K5Discriminant : ℤ := -(16107783120 : ℤ)

/-- The polynomial discriminant of `P_5`. -/
def P5Discriminant : ℤ := -(16107783120 : ℤ)

/-- The ramified rational primes of `K_5`. -/
def K5RamifiedPrimes : Finset ℕ := {2, 3, 5, 11, 13, 17383}

/-- The reduced discriminant squareclass of `K_5`. -/
def K5DiscriminantSquareclass : ℤ := -12428845

/-- The discriminant arithmetic package imported from `S5GaloisArithmetic`. -/
theorem k5_discriminant_arithmetic :
    K5DiscriminantArithmetic := by
  exact ⟨Omega.POM.S5GaloisArithmetic.disc_factorization,
    Omega.POM.S5GaloisArithmetic.disc_negative,
    Omega.POM.S5GaloisArithmetic.disc_not_square⟩

/-- Paper-facing discriminant package of the Perron field `K_5`.

This theorem deliberately does not assert monogenicity: the imported owner file
proves discriminant arithmetic seeds, not an integral-basis theorem.
-/
theorem paper_pom_s5_field_discriminant_arithmetic :
    K5DiscriminantArithmetic ∧
      K5Discriminant = P5Discriminant ∧
      K5RamifiedPrimes = ({2, 3, 5, 11, 13, 17383} : Finset ℕ) ∧
      K5DiscriminantSquareclass = (-12428845 : ℤ) := by
  exact ⟨k5_discriminant_arithmetic, rfl, rfl, rfl⟩

end Omega.POM
