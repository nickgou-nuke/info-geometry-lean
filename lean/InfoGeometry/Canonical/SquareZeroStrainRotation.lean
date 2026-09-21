import InfoGeometry.Canonical.MoorePenrose
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Square-zero commutators and their star decomposition

This algebraic core uses the existing Moore–Penrose predicate. It does not
introduce a second anomaly definition or import the fluid operator layer.
-/

namespace InfoGeometry.Canonical.SquareZeroStrainRotation

section Ring

variable {A : Type*} [Ring A] [StarRing A]

/-- The Moore–Penrose range projector fixes every right multiple of `a`. -/
theorem rangeProjector_mul_regularization
    (a b c : A) (h : MoorePenrose.IsMoorePenroseInverse a b) :
    (a * b) * (a * c) = a * c := by
  calc
    (a * b) * (a * c) = (a * b * a) * c := by
      simp only [mul_assoc]
    _ = a * c := by rw [h.aba_eq_a]

/-- The projector commutator factors through the complementary range sector. -/
theorem commutator_factorization
    (a b c : A) (h : MoorePenrose.IsMoorePenroseInverse a b) :
    (a * b) * (a * c) - (a * c) * (a * b) = (a * c) * (1 - a * b) := by
  rw [rangeProjector_mul_regularization a b c h]
  noncomm_ring

/-- The range projector acts as identity on the output of the commutator. -/
theorem rangeProjector_mul_commutator
    (a b c : A) (h : MoorePenrose.IsMoorePenroseInverse a b) :
    (a * b) * ((a * b) * (a * c) - (a * c) * (a * b)) =
        (a * b) * (a * c) - (a * c) * (a * b) := by
  simp only [commutator_factorization a b c h]
  rw [← mul_assoc, rangeProjector_mul_regularization a b c h]

/-- The commutator vanishes on input from the range projector. -/
theorem commutator_mul_rangeProjector
    (a b c : A) (h : MoorePenrose.IsMoorePenroseInverse a b) :
    ((a * b) * (a * c) - (a * c) * (a * b)) * (a * b) = 0 := by
  have hP : (a * b) * (a * b) = a * b :=
    rangeProjector_mul_regularization a b b h
  rw [commutator_factorization a b c h]
  calc
    ((a * c) * (1 - a * b)) * (a * b) =
        (a * c) * ((1 - a * b) * (a * b)) := by rw [mul_assoc]
    _ = 0 := by rw [sub_mul, one_mul, hP, sub_self, mul_zero]

/-- The commutator belongs to the mixed corner `P A (1-P)`. -/
theorem commutator_mixed_peirce_corner
    (a b c : A) (h : MoorePenrose.IsMoorePenroseInverse a b) :
    (a * b) * ((a * b) * (a * c) - (a * c) * (a * b)) * (1 - a * b) =
        (a * b) * (a * c) - (a * c) * (a * b) := by
  rw [rangeProjector_mul_commutator a b c h, mul_sub, mul_one,
    commutator_mul_rangeProjector a b c h, sub_zero]

/-- The commutator is square-zero without imposing a Drazin law on `c`. -/
theorem commutator_mul_self_eq_zero
    (a b c : A) (h : MoorePenrose.IsMoorePenroseInverse a b) :
    ((a * b) * (a * c) - (a * c) * (a * b)) *
        ((a * b) * (a * c) - (a * c) * (a * b)) = 0 := by
  have hkill : (1 - a * b) * (a * c) = 0 := by
    rw [sub_mul, one_mul, rangeProjector_mul_regularization a b c h, sub_self]
  rw [commutator_factorization a b c h]
  calc
    ((a * c) * (1 - a * b)) * ((a * c) * (1 - a * b)) =
        (a * c) * ((1 - a * b) * (a * c)) * (1 - a * b) := by
          simp only [mul_assoc]
    _ = 0 := by rw [hkill]; simp

/-- Self-adjoint spectral regularization makes the range-projector commutator zero. -/
theorem commutator_eq_zero_of_regularization_selfAdjoint
    (a b c : A) (h : MoorePenrose.IsMoorePenroseInverse a b)
    (hc : star (a * c) = a * c) :
    (a * b) * (a * c) - (a * c) * (a * b) = 0 := by
  have hleft := rangeProjector_mul_regularization a b c h
  have hright : (a * c) * (a * b) = a * c := by
    calc
      (a * c) * (a * b) = star (a * c) * star (a * b) := by
        rw [hc, h.ab_star]
      _ = star ((a * b) * (a * c)) := (star_mul (a * b) (a * c)).symm
      _ = star (a * c) := congrArg star hleft
      _ = a * c := hc
  rw [hleft, hright, sub_self]

/-- A square-zero element and its star determine an unnormalized split pair. -/
theorem square_zero_star_pair
    (x : A) (hx : x * x = 0) :
    (x + star x) * (x + star x) = -((x - star x) * (x - star x)) ∧
    (x + star x) * (x - star x) = -((x - star x) * (x + star x)) := by
  have hs : star x * star x = 0 := by
    calc
      star x * star x = star (x * x) := (star_mul x x).symm
      _ = 0 := by rw [hx, star_zero]
  constructor
  · have hsum :
        (x + star x) * (x + star x) + (x - star x) * (x - star x) = 0 := by
      calc
        _ = (x * x + star x * star x) + (x * x + star x * star x) := by
          noncomm_ring
        _ = 0 := by rw [hx, hs]; simp
    exact eq_neg_of_add_eq_zero_left hsum
  · have hsum :
        (x + star x) * (x - star x) + (x - star x) * (x + star x) = 0 := by
      calc
        _ = (x * x - star x * star x) + (x * x - star x * star x) := by
          noncomm_ring
        _ = 0 := by rw [hx, hs]; simp
    exact eq_neg_of_add_eq_zero_left hsum

end Ring

section RealAlgebra

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A]

/-- Equal real scaling preserves both split-pair identities. -/
theorem square_zero_scaled_star_pair
    (x : A) (hx : x * x = 0) (r : ℝ) :
    (r • (x + star x)) * (r • (x + star x)) =
        -((r • (x - star x)) * (r • (x - star x))) ∧
    (r • (x + star x)) * (r • (x - star x)) =
        -((r • (x - star x)) * (r • (x + star x))) := by
  obtain ⟨hsq, hanti⟩ := square_zero_star_pair x hx
  constructor
  · simpa only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, smul_neg]
      using congrArg (fun y : A => (r * r) • y) hsq
  · simpa only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, smul_neg]
      using congrArg (fun y : A => (r * r) • y) hanti

end RealAlgebra

end InfoGeometry.Canonical.SquareZeroStrainRotation
