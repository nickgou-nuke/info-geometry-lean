/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge

/-!
# Sharp bound for the finite Peirce commutator-square profile

The imported owner identifies the variance readout with the scalar
`4 * ((u * v) / (u^2 + v^2))^2` times the identity matrix. This file proves
that coefficient is at most one and attains one at both real diagonal
directions `(1,1)` and `(1,-1)`. These are finite real-coordinate statements;
they do not construct a projective quotient or a metric space.
-/

namespace InfoGeometry.Clifford.Cl11ProjectiveVarianceBounds

open InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge

/-- The scalar coefficient in the finite Peirce variance readout is bounded
above by its midpoint value. The totalized inverse convention at `(0,0)` is
included in the statement. -/
theorem varianceProfile_le_one (u v : ℝ) :
    4 * ((u * v) / (u ^ 2 + v ^ 2)) ^ 2 ≤ 1 := by
  by_cases hden : u ^ 2 + v ^ 2 = 0
  · have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    simp [hu, hv]
  · have hpos : 0 < (u ^ 2 + v ^ 2) ^ 2 := by
      have hsum_nonneg : 0 ≤ u ^ 2 + v ^ 2 :=
        add_nonneg (sq_nonneg u) (sq_nonneg v)
      have hsum_pos : 0 < u ^ 2 + v ^ 2 :=
        lt_of_le_of_ne hsum_nonneg (Ne.symm hden)
      exact pow_pos hsum_pos 2
    rw [div_pow]
    calc
      4 * ((u * v) ^ 2 / (u ^ 2 + v ^ 2) ^ 2) =
          (4 * (u * v) ^ 2) / (u ^ 2 + v ^ 2) ^ 2 := by ring
      _ ≤ 1 := (div_le_iff₀ hpos).2 (by
        nlinarith [sq_nonneg (u ^ 2 - v ^ 2)])

/-- The profile reaches one in the positive diagonal direction. -/
theorem varianceProfile_eq_one_positive_diagonal :
    4 * ((1 * 1 : ℝ) / (1 ^ 2 + 1 ^ 2)) ^ 2 = 1 := by
  norm_num

/-- The profile also reaches one in the negative diagonal direction. -/
theorem varianceProfile_eq_one_negative_diagonal :
    4 * ((1 * -1 : ℝ) / (1 ^ 2 + (-1) ^ 2)) ^ 2 = 1 := by
  norm_num

/-- Every entry of the finite `M2R` commutator-square variance readout is
bounded above by the corresponding entry of the identity matrix. This uses
the imported variance identity without imposing an order on `M2R` itself.
-/
theorem normalizedPeircePoint_variance_entrywise_le_identity (u v : ℝ) :
    ∀ i j : Fin 2,
      (-(4 : ℝ) •
        ((Pminus * normalizedPeircePoint u v -
          normalizedPeircePoint u v * Pminus) ^ 2)) i j ≤
      (1 : M2R) i j := by
  rw [normalizedPeircePoint_variance]
  have hcoeff := varianceProfile_le_one u v
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using hcoeff
  · simp [hij]

end InfoGeometry.Clifford.Cl11ProjectiveVarianceBounds
