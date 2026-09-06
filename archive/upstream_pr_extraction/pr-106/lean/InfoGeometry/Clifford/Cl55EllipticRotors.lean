import InfoGeometry.Clifford.Cl55HyperbolicWeights
import InfoGeometry.Clifford.Cl55WittCircularAxes

/-!
# Real elliptic rotors in `Cl(5,5)`

An elliptic CAR axis is a native Cl55 element with square `-1`.  The rotor
packet below is therefore formed in the real algebra itself.  Its product law,
reverse-product norm, and interaction with the hyperbolic axis are all
noncommutative identities; no external complex scalar or diagonal model is
used.
-/

namespace InfoGeometry.Clifford.Clifford55

noncomputable def ellipticRotor55 (i : Fin 5) (a b : ℝ) : Cl55 :=
  a • (1 : Cl55) + b • ellipticAxis55 i

theorem ellipticRotor55_mul
    (i : Fin 5) (a b c d : ℝ) :
    ellipticRotor55 i a b * ellipticRotor55 i c d =
      (a * c - b * d) • (1 : Cl55) +
        (a * d + b * c) • ellipticAxis55 i := by
  unfold ellipticRotor55
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, ellipticAxis55_sq, smul_neg]
  module

theorem ellipticRotor55_mul_reverse
    (i : Fin 5) (a b : ℝ) :
    ellipticRotor55 i a b * ellipticRotor55 i a (-b) =
      (a ^ 2 + b ^ 2) • (1 : Cl55) := by
  rw [ellipticRotor55_mul]
  simp only [mul_neg, sub_neg_eq_add]
  module

theorem ellipticRotor55_reverse_mul
    (i : Fin 5) (a b : ℝ) :
    ellipticRotor55 i a (-b) * ellipticRotor55 i a b =
      (a ^ 2 + b ^ 2) • (1 : Cl55) := by
  rw [ellipticRotor55_mul]
  simp only [neg_mul, sub_neg_eq_add]
  module

theorem hyperbolicAxis55_mul_ellipticRotor55
    (i : Fin 5) (a b : ℝ) :
    hyperbolicAxis55 i * ellipticRotor55 i a b =
      ellipticRotor55 i a (-b) * hyperbolicAxis55 i := by
  unfold ellipticRotor55
  have h := hyperbolicAxis55_ellipticAxis55_anticommute i
  have h' : hyperbolicAxis55 i * ellipticAxis55 i =
      -(ellipticAxis55 i * hyperbolicAxis55 i) :=
    eq_neg_of_add_eq_zero_left h
  have hleft :
      hyperbolicAxis55 i *
          (a • (1 : Cl55) + b • ellipticAxis55 i) =
        a • hyperbolicAxis55 i +
          b • (hyperbolicAxis55 i * ellipticAxis55 i) := by
    rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one]
  have hright :
      (a • (1 : Cl55) + (-b) • ellipticAxis55 i) *
          hyperbolicAxis55 i =
        a • hyperbolicAxis55 i +
          (-b) • (ellipticAxis55 i * hyperbolicAxis55 i) := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  rw [hleft, hright, h']
  module

end InfoGeometry.Clifford.Clifford55
