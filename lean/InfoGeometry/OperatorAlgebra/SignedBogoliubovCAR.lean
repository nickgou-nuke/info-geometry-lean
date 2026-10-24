/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR

/-! # Signed particle–hole coefficients

The creator coefficient is independent of the annihilator coefficient. This
distinguishes circular CAR transport from algebraic hyperbolic transport;
no preservation of the star operation is asserted.
-/

namespace InfoGeometry.OperatorAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The diagonal CAR coefficient with independent pairing signs. -/
theorem particleHole_diagonal (p P q Q : A) (u v w : R)
    (hpP : thermalAnticommutator p P = 1)
    (hqQ : thermalAnticommutator q Q = 1)
    (hpq : thermalAnticommutator p q = 0)
    (hPQ : thermalAnticommutator P Q = 0) :
    thermalAnticommutator (u • p + v • Q) (u • P + w • q) =
      (u * u + v * w) • (1 : A) := by
  have hQP : thermalAnticommutator Q P = 0 := by
    rw [thermalAnticommutator_symm, hPQ]
  have hQq : thermalAnticommutator Q q = 1 := by
    rw [thermalAnticommutator_symm, hqQ]
  rw [thermalAnticommutator_expand, hpP, hpq, hQP, hQq]
  simp only [smul_zero, add_zero, add_smul]

/-- Cross annihilators cancel because the two diagonal CAR constants agree. -/
theorem particleHole_annihilator_cross (p P q Q : A) (u v : R)
    (hpP : thermalAnticommutator p P = 1)
    (hqQ : thermalAnticommutator q Q = 1)
    (hpq : thermalAnticommutator p q = 0)
    (hPQ : thermalAnticommutator P Q = 0) :
    thermalAnticommutator (u • p + v • Q) (u • q - v • P) = 0 := by
  have hQP : thermalAnticommutator Q P = 0 := by
    rw [thermalAnticommutator_symm, hPQ]
  have hQq : thermalAnticommutator Q q = 1 := by
    rw [thermalAnticommutator_symm, hqQ]
  rw [sub_eq_add_neg, ← neg_smul, thermalAnticommutator_expand,
    hpq, hpP, hQq, hQP]
  simp [mul_comm v u]

/-- Circular and hyperbolic choices are covered by a single normalization. -/
theorem particleHole_normalized (p P q Q : A) (u v w : R)
    (hpP : thermalAnticommutator p P = 1)
    (hqQ : thermalAnticommutator q Q = 1)
    (hpq : thermalAnticommutator p q = 0)
    (hPQ : thermalAnticommutator P Q = 0)
    (h : u * u + v * w = 1) :
    thermalAnticommutator (u • p + v • Q) (u • P + w • q) = 1 := by
  rw [particleHole_diagonal p P q Q u v w hpP hqQ hpq hPQ, h, one_smul]

/-- The mixed cross-mode relation uses square-zero of its two factors, not
division of their self-anticommutators by two. -/
theorem particleHole_mixed_cross (p Q : A) (u v w : R)
    (hp : p * p = 0) (hQ : Q * Q = 0)
    (hpQ : thermalAnticommutator p Q = 0) :
    thermalAnticommutator (u • p + v • Q) (u • Q - w • p) = 0 := by
  have hQp : thermalAnticommutator Q p = 0 := by
    rw [thermalAnticommutator_symm, hpQ]
  have hpp : thermalAnticommutator p p = 0 := by
    simp [thermalAnticommutator, hp]
  have hQQ : thermalAnticommutator Q Q = 0 := by
    simp [thermalAnticommutator, hQ]
  rw [sub_eq_add_neg, ← neg_smul, thermalAnticommutator_expand,
    hpQ, hpp, hQQ, hQp]
  simp

end InfoGeometry.OperatorAlgebra
