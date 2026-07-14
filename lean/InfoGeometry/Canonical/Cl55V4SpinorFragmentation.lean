import InfoGeometry.Clifford.ConformalReflection55
import InfoGeometry.Clifford.ConformalProjectiveEmbedding55

/-!
# Cl(5,5) Spinor Fragmentation by the Finite V₄ Action

This file gives explicit `Cl(5,5)` identities for the seed decomposition
`u ± v` against the two order-two sandwich involutions coming from
`J = u - v` and `S = u + v`.
-/

noncomputable section

namespace Cl55V4SpinorFragmentation

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

end Cl55V4SpinorFragmentation
