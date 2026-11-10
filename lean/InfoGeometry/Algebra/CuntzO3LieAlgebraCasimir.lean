/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzO3TriSupersymmetry

noncomputable section

namespace InfoGeometry.Algebra.CuntzO3LieAlgebraCasimir

open InfoGeometry.Algebra.CuntzO3TriSupersymmetry

/-- The Quadratic Casimir Operator C_2 for su(3) in the Cuntz O_3 representation. -/
def casimir2 {R : Type*} [Ring R] [Invertible (2 : R)] [Invertible (6 : R)] (g : CuntzO3Generators R) : R :=
  Q12 g * Q21 g + Q21 g * Q12 g +
  Q23 g * Q32 g + Q32 g * Q23 g +
  Q31 g * Q13 g + Q13 g * Q31 g +
  (⅟(2 : R)) * (Lambda3 g * Lambda3 g) +
  (⅟(6 : R)) * (Lambda8 g * Lambda8 g)

/-- **Theorem**: Off-diagonal root product sum in Cuntz O3 is 2 * 1. -/
theorem cuntz_off_diagonal_root_sum {R : Type*} [Ring R] (g : CuntzO3Generators R) :
    Q12 g * Q21 g + Q21 g * Q12 g +
    Q23 g * Q32 g + Q32 g * Q23 g +
    Q31 g * Q13 g + Q13 g * Q31 g = 2 := by
  dsimp [Q12, Q21, Q23, Q32, Q31, Q13]
  have h11 : g.S1star * g.S1 = 1 := g.S1star_S1
  have h22 : g.S2star * g.S2 = 1 := g.S2star_S2
  have h33 : g.S3star * g.S3 = 1 := g.S3star_S3
  have h_c : g.S1 * g.S1star + g.S2 * g.S2star + g.S3 * g.S3star = 1 := g.completeness
  have t1 : g.S1 * g.S2star * (g.S2 * g.S1star) = g.S1 * g.S1star := by rw [mul_assoc, ← mul_assoc g.S2star, h22, one_mul]
  have t2 : g.S2 * g.S1star * (g.S1 * g.S2star) = g.S2 * g.S2star := by rw [mul_assoc, ← mul_assoc g.S1star, h11, one_mul]
  have t3 : g.S2 * g.S3star * (g.S3 * g.S2star) = g.S2 * g.S2star := by rw [mul_assoc, ← mul_assoc g.S3star, h33, one_mul]
  have t4 : g.S3 * g.S2star * (g.S2 * g.S3star) = g.S3 * g.S3star := by rw [mul_assoc, ← mul_assoc g.S2star, h22, one_mul]
  have t5 : g.S3 * g.S1star * (g.S1 * g.S3star) = g.S3 * g.S3star := by rw [mul_assoc, ← mul_assoc g.S1star, h11, one_mul]
  have t6 : g.S1 * g.S3star * (g.S3 * g.S1star) = g.S1 * g.S1star := by rw [mul_assoc, ← mul_assoc g.S3star, h33, one_mul]
  rw [t1, t2, t3, t4, t5, t6]
  have h_ring : g.S1 * g.S1star + g.S2 * g.S2star + g.S2 * g.S2star + g.S3 * g.S3star + g.S3 * g.S3star + g.S1 * g.S1star = 2 * (g.S1 * g.S1star + g.S2 * g.S2star + g.S3 * g.S3star) := by
    rw [show (2 : R) = 1 + 1 by norm_num]
    noncomm_ring
  rw [h_ring, h_c, mul_one]

/-- **Theorem**: Square of Isospin Cartan Generator λ3^2 = P1 + P2. -/
theorem lambda3_squared {R : Type*} [Ring R] (g : CuntzO3Generators R) :
    Lambda3 g * Lambda3 g = g.S1 * g.S1star + g.S2 * g.S2star := by
  dsimp [Lambda3]
  have h11 : g.S1star * g.S1 = 1 := g.S1star_S1
  have h22 : g.S2star * g.S2 = 1 := g.S2star_S2
  have h12 : g.S1star * g.S2 = 0 := g.S1star_S2
  have h21 : g.S2star * g.S1 = 0 := g.S2star_S1
  have t1 : g.S1 * g.S1star * (g.S1 * g.S1star) = g.S1 * g.S1star := by rw [mul_assoc, ← mul_assoc g.S1star, h11, one_mul]
  have t2 : g.S2 * g.S2star * (g.S2 * g.S2star) = g.S2 * g.S2star := by rw [mul_assoc, ← mul_assoc g.S2star, h22, one_mul]
  have z1 : g.S1 * g.S1star * (g.S2 * g.S2star) = 0 := by rw [mul_assoc, ← mul_assoc g.S1star, h12, zero_mul, mul_zero]
  have z2 : g.S2 * g.S2star * (g.S1 * g.S1star) = 0 := by rw [mul_assoc, ← mul_assoc g.S2star, h21, zero_mul, mul_zero]
  calc (g.S1 * g.S1star - g.S2 * g.S2star) * (g.S1 * g.S1star - g.S2 * g.S2star)
    _ = g.S1 * g.S1star * (g.S1 * g.S1star) - g.S1 * g.S1star * (g.S2 * g.S2star) -
        g.S2 * g.S2star * (g.S1 * g.S1star) + g.S2 * g.S2star * (g.S2 * g.S2star) := by noncomm_ring
    _ = g.S1 * g.S1star - 0 - 0 + g.S2 * g.S2star := by rw [t1, t2, z1, z2]
    _ = g.S1 * g.S1star + g.S2 * g.S2star := by noncomm_ring

/-- **Theorem**: Square of Hypercharge Cartan Generator λ8^2 = P1 + P2 + 4 P3. -/
theorem lambda8_squared {R : Type*} [Ring R] (g : CuntzO3Generators R) :
    Lambda8 g * Lambda8 g = g.S1 * g.S1star + g.S2 * g.S2star + 4 * (g.S3 * g.S3star) := by
  dsimp [Lambda8]
  have h11 : g.S1star * g.S1 = 1 := g.S1star_S1
  have h22 : g.S2star * g.S2 = 1 := g.S2star_S2
  have h33 : g.S3star * g.S3 = 1 := g.S3star_S3
  have h12 : g.S1star * g.S2 = 0 := g.S1star_S2
  have h21 : g.S2star * g.S1 = 0 := g.S2star_S1
  have h13 : g.S1star * g.S3 = 0 := g.S1star_S3
  have h31 : g.S3star * g.S1 = 0 := g.S3star_S1
  have h23 : g.S2star * g.S3 = 0 := g.S2star_S3
  have h32 : g.S3star * g.S2 = 0 := g.S3star_S2
  have t1 : g.S1 * g.S1star * (g.S1 * g.S1star) = g.S1 * g.S1star := by rw [mul_assoc, ← mul_assoc g.S1star, h11, one_mul]
  have t2 : g.S2 * g.S2star * (g.S2 * g.S2star) = g.S2 * g.S2star := by rw [mul_assoc, ← mul_assoc g.S2star, h22, one_mul]
  have t3 : g.S3 * g.S3star * (g.S3 * g.S3star) = g.S3 * g.S3star := by rw [mul_assoc, ← mul_assoc g.S3star, h33, one_mul]
  have z1 : g.S1 * g.S1star * (g.S2 * g.S2star) = 0 := by rw [mul_assoc, ← mul_assoc g.S1star, h12, zero_mul, mul_zero]
  have z2 : g.S2 * g.S2star * (g.S1 * g.S1star) = 0 := by rw [mul_assoc, ← mul_assoc g.S2star, h21, zero_mul, mul_zero]
  have z3 : g.S1 * g.S1star * (g.S3 * g.S3star) = 0 := by rw [mul_assoc, ← mul_assoc g.S1star, h13, zero_mul, mul_zero]
  have z4 : g.S3 * g.S3star * (g.S1 * g.S1star) = 0 := by rw [mul_assoc, ← mul_assoc g.S3star, h31, zero_mul, mul_zero]
  have z5 : g.S2 * g.S2star * (g.S3 * g.S3star) = 0 := by rw [mul_assoc, ← mul_assoc g.S2star, h23, zero_mul, mul_zero]
  have z6 : g.S3 * g.S3star * (g.S2 * g.S2star) = 0 := by rw [mul_assoc, ← mul_assoc g.S3star, h32, zero_mul, mul_zero]
  calc (g.S1 * g.S1star + g.S2 * g.S2star - 2 * (g.S3 * g.S3star)) * (g.S1 * g.S1star + g.S2 * g.S2star - 2 * (g.S3 * g.S3star))
    _ = g.S1 * g.S1star * (g.S1 * g.S1star) + g.S2 * g.S2star * (g.S2 * g.S2star) + 4 * (g.S3 * g.S3star * (g.S3 * g.S3star)) +
        g.S1 * g.S1star * (g.S2 * g.S2star) + g.S2 * g.S2star * (g.S1 * g.S1star) -
        2 * (g.S1 * g.S1star * (g.S3 * g.S3star)) - 2 * (g.S3 * g.S3star * (g.S1 * g.S1star)) -
        2 * (g.S2 * g.S2star * (g.S3 * g.S3star)) - 2 * (g.S3 * g.S3star * (g.S2 * g.S2star)) := by
      rw [show (2 : R) = 1 + 1 by norm_num, show (4 : R) = 1 + 1 + 1 + 1 by norm_num]
      noncomm_ring
    _ = g.S1 * g.S1star + g.S2 * g.S2star + 4 * (g.S3 * g.S3star) := by rw [t1, t2, t3, z1, z2, z3, z4, z5, z6]; noncomm_ring

/-- The displayed quadratic expression reduces to a scalar in the Cuntz
representation. This gives the full centrality statement, not only commutation
with one selected root operator. -/
theorem casimir2_eq_scalar {R : Type*} [Ring R]
    [Invertible (2 : R)] [Invertible (6 : R)] (g : CuntzO3Generators R) :
    casimir2 g = 2 + ⅟(2 : R) + ⅟(6 : R) := by
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self (2 : R)
  have h6 : (6 : R) * ⅟(6 : R) = 1 := mul_invOf_self (6 : R)
  have hcoeff : ⅟(2 : R) + ⅟(6 : R) = 4 * ⅟(6 : R) := by
    have h236 : (2 : R) * 3 = 6 := by norm_num
    have hhalf : ⅟(2 : R) = 3 * ⅟(6 : R) := by
      calc
        ⅟(2 : R) = ⅟(2 : R) * ((2 * 3 : R) * ⅟(6 : R)) := by rw [h236, h6, mul_one]
        _ = (⅟(2 : R) * 2) * (3 * ⅟(6 : R)) := by noncomm_ring
        _ = 3 * ⅟(6 : R) := by rw [h2, one_mul]
    rw [hhalf, show (3 : R) = 1 + 1 + 1 by norm_num, show (4 : R) = 1 + 1 + 1 + 1 by norm_num]
    noncomm_ring
  dsimp [casimir2]
  rw [cuntz_off_diagonal_root_sum, lambda3_squared, lambda8_squared]
  calc
    2 + ⅟(2 : R) * (g.S1 * g.S1star + g.S2 * g.S2star) +
        ⅟(6 : R) * (g.S1 * g.S1star + g.S2 * g.S2star +
          4 * (g.S3 * g.S3star)) =
      2 + (⅟(2 : R) + ⅟(6 : R)) *
          (g.S1 * g.S1star + g.S2 * g.S2star) +
          (4 * ⅟(6 : R)) * (g.S3 * g.S3star) := by
      rw [show (4 : R) = 1 + 1 + 1 + 1 by norm_num]
      noncomm_ring
    _ = 2 + (4 * ⅟(6 : R)) *
          (g.S1 * g.S1star + g.S2 * g.S2star + g.S3 * g.S3star) := by
      rw [hcoeff]
      noncomm_ring
    _ = 2 + 4 * ⅟(6 : R) := by rw [g.completeness, mul_one]
    _ = 2 + ⅟(2 : R) + ⅟(6 : R) := by rw [← hcoeff]; abel

/-- The Cuntz quadratic element commutes with every carrier element because
it is the scalar identified by `casimir2_eq_scalar`. -/
theorem casimir2_commutes {R : Type*} [Ring R]
    [Invertible (2 : R)] [Invertible (6 : R)] (g : CuntzO3Generators R)
    (x : R) :
    lieBracket (casimir2 g) x = 0 := by
  rw [casimir2_eq_scalar]
  dsimp [lieBracket]
  have h2x : (2 : R) * x = x * 2 := by
    rw [show (2 : R) = 1 + 1 by norm_num]; noncomm_ring
  have h6x : (6 : R) * x = x * 6 := by
    rw [show (6 : R) = 1 + 1 + 1 + 1 + 1 + 1 by norm_num]; noncomm_ring
  have hinv2 : (⅟(2 : R)) * x = x * (⅟(2 : R)) := by
    calc
      (⅟(2 : R)) * x = (⅟(2 : R)) * x * ((2 : R) * ⅟(2 : R)) := by rw [mul_invOf_self, mul_one]
      _ = (⅟(2 : R)) * (x * 2) * ⅟(2 : R) := by noncomm_ring
      _ = (⅟(2 : R)) * (2 * x) * ⅟(2 : R) := by rw [← h2x]
      _ = ((⅟(2 : R)) * 2) * x * ⅟(2 : R) := by noncomm_ring
      _ = x * ⅟(2 : R) := by rw [invOf_mul_self, one_mul]
  have hinv6 : (⅟(6 : R)) * x = x * (⅟(6 : R)) := by
    calc
      (⅟(6 : R)) * x = (⅟(6 : R)) * x * ((6 : R) * ⅟(6 : R)) := by rw [mul_invOf_self, mul_one]
      _ = (⅟(6 : R)) * (x * 6) * ⅟(6 : R) := by noncomm_ring
      _ = (⅟(6 : R)) * (6 * x) * ⅟(6 : R) := by rw [← h6x]
      _ = ((⅟(6 : R)) * 6) * x * ⅟(6 : R) := by noncomm_ring
      _ = x * ⅟(6 : R) := by rw [invOf_mul_self, one_mul]
  calc
    (2 + ⅟(2 : R) + ⅟(6 : R)) * x - x * (2 + ⅟(2 : R) + ⅟(6 : R))
      = (2 * x - x * 2) + (⅟(2 : R) * x - x * ⅟(2 : R)) + (⅟(6 : R) * x - x * ⅟(6 : R)) := by noncomm_ring
    _ = 0 := by rw [h2x, hinv2, hinv6]; noncomm_ring

/-- **Theorem**: Projection P3 Orthogonality to Q12 Root Generator.
    P3 Q12 = 0 and Q12 P3 = 0. -/
theorem p3_q12_ortho {R : Type*} [Ring R] (g : CuntzO3Generators R) :
    (g.S3 * g.S3star) * Q12 g = 0 ∧ Q12 g * (g.S3 * g.S3star) = 0 := ⟨
  by dsimp [Q12]; rw [mul_assoc, ← mul_assoc g.S3star, g.S3star_S1, zero_mul, mul_zero],
  by dsimp [Q12]; rw [mul_assoc, ← mul_assoc g.S2star, g.S2star_S3, zero_mul, mul_zero]
⟩

/-- **Theorem**: Casimir Invariance / Schur's Lemma for Cuntz su(3) Representation.
    The Quadratic Casimir Operator C_2 commutes with Q12: [C_2, Q12] = 0. -/
theorem casimir2_commutes_q12 {R : Type*} [Ring R] [Invertible (2 : R)] [Invertible (6 : R)] (g : CuntzO3Generators R) :
    lieBracket (casimir2 g) (Q12 g) = 0 :=
  casimir2_commutes g (Q12 g)

end InfoGeometry.Algebra.CuntzO3LieAlgebraCasimir
