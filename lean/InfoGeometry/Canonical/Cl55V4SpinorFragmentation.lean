/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ConformalReflection55
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.ConformalProjectiveEmbedding55

/-!
# Cl(5,5) Spinor Fragmentation by the Finite V₄ Action

This file gives explicit `Cl(5,5)` identities for the seed decomposition
`u ± v` against the two order-two sandwich involutions coming from
`J = u - v` and `S = u + v`.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55V4SpinorFragmentation

open InfoGeometry.Clifford.ConformalLift55

/-- Conformal reflection (inversion) element. -/
def J (p : ConformalNullPair) : Cl55 :=
  InfoGeometry.Clifford.ConformalReflection55.J p

/-- Projective inversion element. -/
def S (p : ConformalNullPair) : Cl55 :=
  InfoGeometry.Clifford.ConformalProjectiveEmbedding55.S p

/-- `V₄`-relevant seed vectors. -/
def spinorPlus (p : ConformalNullPair) : Cl55 := p.u + p.v

def spinorMinus (p : ConformalNullPair) : Cl55 := p.u - p.v

private theorem sandwich_mul_of_square_one {R : Type*} [Ring R]
    {s x y : R} (hs : s * s = 1) :
    s * (x * y) * s = (s * x * s) * (s * y * s) := by
  calc
    s * (x * y) * s = s * x * (s * s) * y * s := by
      rw [hs]
      noncomm_ring
    _ = (s * x * s) * (s * y * s) := by noncomm_ring

private theorem sandwich_mul_of_square_neg_one {R : Type*} [Ring R]
    {s x y : R} (hs : s * s = -1) :
    s * (x * y) * s = -((s * x * s) * (s * y * s)) := by
  calc
    s * (x * y) * s = -(s * x * (s * s) * y * s) := by
      rw [hs]
      noncomm_ring
    _ = -((s * x * s) * (s * y * s)) := by noncomm_ring

/-- `J` swaps `u` and `v`. -/
theorem J_sandwich_u (p : ConformalNullPair) : J p * p.u * J p = p.v := by
  simpa [J] using InfoGeometry.Clifford.ConformalReflection55.J_swap_origin p

/-- `J` swaps `v` and `u`. -/
theorem J_sandwich_v (p : ConformalNullPair) : J p * p.v * J p = p.u := by
  simpa [J] using InfoGeometry.Clifford.ConformalReflection55.J_swap_infinity p

/-- `S` swaps `u` and `v`. -/
theorem S_sandwich_u (p : ConformalNullPair) : S p * p.u * S p = p.v := by
  simpa [S] using InfoGeometry.Clifford.ConformalProjectiveEmbedding55.S_u_S p

/-- `S` swaps `v` and `u`. -/
theorem S_sandwich_v (p : ConformalNullPair) : S p * p.v * S p = p.u := by
  simpa [S] using InfoGeometry.Clifford.ConformalProjectiveEmbedding55.S_v_S p

/-- `u + v` is fixed by the `J` sandwich. -/
theorem spinorPlus_fixed_by_J (p : ConformalNullPair) :
    J p * spinorPlus p * J p = spinorPlus p := by
  calc
    J p * spinorPlus p * J p
        = J p * p.u * J p + J p * p.v * J p := by
          rw [spinorPlus, mul_add, add_mul]
    _ = p.v + p.u := by simp [J_sandwich_u p, J_sandwich_v p]
    _ = spinorPlus p := by simp [spinorPlus, add_comm]

/-- `u - v` is anti-fixed by the `J` sandwich. -/
theorem spinorMinus_anti_by_J (p : ConformalNullPair) :
    J p * spinorMinus p * J p = -spinorMinus p := by
  calc
    J p * spinorMinus p * J p
        = J p * p.u * J p + -(J p * p.v * J p) := by
          rw [spinorMinus, sub_eq_add_neg, mul_add, mul_neg, add_mul, neg_mul]
    _ = p.v + -p.u := by simp [J_sandwich_u p, J_sandwich_v p]
    _ = -spinorMinus p := by
      simp [spinorMinus, sub_eq_add_neg]

/-- `u + v` is fixed by the `S` sandwich. -/
theorem spinorPlus_fixed_by_S (p : ConformalNullPair) :
    S p * spinorPlus p * S p = spinorPlus p := by
  calc
    S p * spinorPlus p * S p
        = S p * p.u * S p + S p * p.v * S p := by
            rw [spinorPlus, mul_add, add_mul]
    _ = p.v + p.u := by simp [S_sandwich_u p, S_sandwich_v p]
    _ = spinorPlus p := by simp [spinorPlus, add_comm]

/-- `u - v` is anti-fixed by the `S` sandwich. -/
theorem spinorMinus_anti_by_S (p : ConformalNullPair) :
    S p * spinorMinus p * S p = -spinorMinus p := by
  calc
    S p * spinorMinus p * S p
        = S p * p.u * S p + -(S p * p.v * S p) := by
          rw [spinorMinus, sub_eq_add_neg, mul_add, mul_neg, add_mul, neg_mul]
    _ = p.v + -p.u := by simp [S_sandwich_u p, S_sandwich_v p]
    _ = -spinorMinus p := by
      simp [spinorMinus, sub_eq_add_neg]

/-- The commutator of the conformal null pair is its boundary grading element. -/
def nullPairGrading (p : ConformalNullPair) : Cl55 := p.u * p.v - p.v * p.u

/-- The conformal inversion sandwich fixes the null-pair grading element.
The minus sign in `J^2 = -1` compensates for the exchange of the two null
generators in each product. -/
theorem J_sandwich_nullPairGrading (p : ConformalNullPair) :
    J p * nullPairGrading p * J p = nullPairGrading p := by
  have hJJ : J p * J p = -(1 : Cl55) := by
    simpa [J, pow_two] using InfoGeometry.Clifford.ConformalReflection55.J_sq p
  have hUV : J p * (p.u * p.v) * J p = -(p.v * p.u) := by
    rw [sandwich_mul_of_square_neg_one hJJ, J_sandwich_u, J_sandwich_v]
  have hVU : J p * (p.v * p.u) * J p = -(p.u * p.v) := by
    rw [sandwich_mul_of_square_neg_one hJJ, J_sandwich_v, J_sandwich_u]
  unfold nullPairGrading
  calc
    J p * (p.u * p.v - p.v * p.u) * J p =
        J p * (p.u * p.v) * J p - J p * (p.v * p.u) * J p := by
          noncomm_ring
    _ = -(p.v * p.u) - (-(p.u * p.v)) := by rw [hUV, hVU]
    _ = p.u * p.v - p.v * p.u := by abel

/-- The projective involution has the opposite action on the same grading:
its square is `+1`, so exchanging the two null generators reverses their
commutator. -/
theorem S_sandwich_nullPairGrading (p : ConformalNullPair) :
    S p * nullPairGrading p * S p = -nullPairGrading p := by
  have hSS : S p * S p = 1 := by
    simpa [S] using InfoGeometry.Clifford.ConformalProjectiveEmbedding55.S_sq p
  have hUV : S p * (p.u * p.v) * S p = p.v * p.u := by
    rw [sandwich_mul_of_square_one hSS, S_sandwich_u, S_sandwich_v]
  have hVU : S p * (p.v * p.u) * S p = p.u * p.v := by
    rw [sandwich_mul_of_square_one hSS, S_sandwich_v, S_sandwich_u]
  unfold nullPairGrading
  calc
    S p * (p.u * p.v - p.v * p.u) * S p =
        S p * (p.u * p.v) * S p - S p * (p.v * p.u) * S p := by
          noncomm_ring
    _ = p.v * p.u - p.u * p.v := by rw [hUV, hVU]
    _ = -(p.u * p.v - p.v * p.u) := by abel

/-- The `J`-sandwich involution. -/
theorem J_sandwich_involution (p : ConformalNullPair) (x : Cl55) :
    J p * (J p * x * J p) * J p = x := by
  have hJJ : J p * J p = - (1 : Cl55) := by
    simpa [J, pow_two] using (InfoGeometry.Clifford.ConformalReflection55.J_sq p)
  calc
    J p * (J p * x * J p) * J p = (J p * J p) * x * (J p * J p) := by
      simp [mul_assoc]
    _ = (- (1 : Cl55)) * x * (- (1 : Cl55)) := by simp [hJJ]
    _ = x := by simp

/-- The `S`-sandwich involution. -/
theorem S_sandwich_involution (p : ConformalNullPair) (x : Cl55) :
    S p * (S p * x * S p) * S p = x := by
  have hSS : S p * S p = (1 : Cl55) := by
    simpa [S] using (InfoGeometry.Clifford.ConformalProjectiveEmbedding55.S_sq p)
  calc
    S p * (S p * x * S p) * S p = (S p * S p) * x * (S p * S p) := by
      simp [mul_assoc]
    _ = (1 : Cl55) * x * (1 : Cl55) := by rw [hSS]
    _ = x := by simp

end InfoGeometry.Canonical.Cl55V4SpinorFragmentation
