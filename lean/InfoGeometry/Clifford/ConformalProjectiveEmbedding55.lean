import InfoGeometry.Clifford.ConformalLift55
import Mathlib

/-!
# Conformal Projective Embedding

This file defines the projective embedding $F(x) = x + \frac{1}{2}x^2 n_\infty + n_0$
and the geometric inverse $x^{-1} = x / x^2$.
It establishes the reflection property that maps $F(x)$ to $F(x^{-1})$.
-/

noncomputable section

namespace InfoGeometry.Clifford.ConformalProjectiveEmbedding55

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ConformalLift55
open ConformalNullPair

variable (P : ConformalNullPair)

/-- The standard CGA origin generator. -/
def n_zero : Cl55 := P.u

/-- The standard CGA infinity generator. -/
def n_infty : Cl55 := (-2 : ℝ) • P.v

/-- Projective embedding $F(x)$ for a vector $x$ with square $x^2$. -/
def F (x : Cl55) (x_sq : ℝ) : Cl55 :=
  x + (1 / 2 * x_sq) • n_infty P + n_zero P

/-- Geometric inverse $x^{-1} = x / x^2$. -/
def geoInv (x : Cl55) (x_sq : ℝ) : Cl55 :=
  (1 / x_sq) • x

/-- Geometric inverse squared is $1 / x^2$. -/
theorem geoInv_sq (x : Cl55) (x_sq : ℝ) (hx_sq : x * x = x_sq • (1 : Cl55)) (hx : x_sq ≠ 0) :
    geoInv x x_sq * geoInv x x_sq = (1 / x_sq : ℝ) • (1 : Cl55) := by
  dsimp [geoInv]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  rw [hx_sq, smul_smul]
  congr 1
  calc
    (1 / x_sq) * (1 / x_sq) * x_sq = (1 / x_sq) * ((1 / x_sq) * x_sq) := by rw [mul_assoc]
    _ = (1 / x_sq) * 1 := by rw [div_mul_cancel₀ 1 hx]
    _ = 1 / x_sq := by rw [mul_one]

/-- 
  The inversion operator is the sphere $S = u + v$, which happens to be
  the original `J` defined in `ConformalLift55.lean`.
-/
def S : Cl55 := P.J

/--
Reflection/inversion law for the projective conformal embedding.

If `x` is orthogonal to the conformal null pair, and `q` is the nonzero scalar
representing `x²`, then conjugation by `S = u+v` sends the projective embedding
of `x` to the scaled embedding of the geometric inverse `q⁻¹x`.

This is a finite Clifford-algebra identity. It does not assert analytic
continuation or a completed conformal compactification.
-/
theorem conformal_inversion_maps_to_geoInv (x : Cl55) (q : ℝ)
    (hx_ortho_u : x * P.u = - P.u * x)
    (hx_ortho_v : x * P.v = - P.v * x)
    (_hx_sq : x * x = q • (1 : Cl55))
    (hq : q ≠ 0) :
    - (S P * F P x q * S P) = q • F P (geoInv x q) (1 / q) := by
  dsimp [S, F, geoInv, n_zero, n_infty]
  have h_J_sq : P.J * P.J = 1 := P.J_sq
  have h_J_u_J : P.J * P.u * P.J = P.v := P.J_u_J
  have h_J_v_J : P.J * P.v * P.J = P.u := P.J_v_J
  have h_x_J : x * P.J = - P.J * x := by
    dsimp [ConformalNullPair.J]
    rw [mul_add, hx_ortho_u, hx_ortho_v]
    noncomm_ring
  have h_J_x_J : P.J * x * P.J = - x := by
    calc
      P.J * x * P.J = P.J * (x * P.J) := by rw [mul_assoc]
      _ = P.J * (- P.J * x) := by rw [h_x_J]
      _ = - (P.J * P.J) * x := by noncomm_ring
      _ = - (1 : Cl55) * x := by rw [h_J_sq]
      _ = - x := by noncomm_ring
  have h_inv : q * (1 / q) = 1 := mul_one_div_cancel hq
  have h_eq1 : (1 / 2 * q) • (-2 : ℝ) • P.v = - q • P.v := by
    rw [smul_smul]
    congr 1
    ring
  have h_eq2 : (1 / 2 * (1 / q)) • (-2 : ℝ) • P.v = - (1 / q) • P.v := by
    rw [smul_smul]
    congr 1
    ring
  rw [h_eq1, h_eq2]
  have h_LHS : - (P.J * (x + - q • P.v + P.u) * P.J) = x + q • P.u - P.v := by
    rw [mul_add, add_mul, mul_add, add_mul]
    rw [mul_smul_comm, smul_mul_assoc]
    rw [h_J_x_J, h_J_v_J, h_J_u_J]
    simp only [neg_add, neg_neg, neg_smul]
    abel
  have h_RHS : q • ((1 / q) • x + - (1 / q) • P.v + P.u) = x + q • P.u - P.v := by
    rw [smul_add, smul_add, smul_smul, smul_smul]
    have h_scal : q * -(1 / q) = -1 := by
      calc
        q * -(1 / q) = - (q * (1 / q)) := by ring
        _ = - 1 := by rw [h_inv]
    rw [h_scal, h_inv]
    simp only [one_smul, neg_one_smul]
    abel
  rw [h_LHS, h_RHS]

/--
The projective embedding of a vector in the split null cone lands on the null cone of Cl(5,5).

For any vector `x` that is orthogonal to the conformal null pair `P.u` and `P.v`, 
if `x² = q`, then `F(x, q)² = 0`.
-/
theorem F_sq_zero (x : Cl55) (q : ℝ)
    (hx_ortho_u : x * P.u = - P.u * x)
    (hx_ortho_v : x * P.v = - P.v * x)
    (hx_sq : x * x = q • (1 : Cl55)) :
    F P x q * F P x q = 0 := by
  dsimp [F, n_zero, n_infty]
  have h_eq1 : (1 / 2 * q) • (-2 : ℝ) • P.v = - q • P.v := by
    rw [smul_smul]
    congr 1
    ring
  rw [h_eq1]
  have h_u2 : P.u * P.u = 0 := by
    have h_pow := P.u_square
    rw [pow_two] at h_pow
    exact h_pow
  have h_v2 : P.v * P.v = 0 := by
    have h_pow := P.v_square
    rw [pow_two] at h_pow
    exact h_pow
  have h_x_v_cancel : (- q) • (x * P.v) - q • (P.v * x) = 0 := by
    rw [hx_ortho_v, neg_smul, neg_mul, smul_neg, neg_neg, sub_self]
  have h_x_u_cancel : x * P.u + P.u * x = 0 := by
    rw [hx_ortho_u, neg_mul]
    exact neg_add_cancel (P.u * x)
  have h_uv_cancel : (- q) • (P.v * P.u) - q • (P.u * P.v) = (- q) • (1 : Cl55) := by
    rw [sub_eq_add_neg, ← neg_smul, ← smul_add]
    have h_anticomm : P.v * P.u + P.u * P.v = 1 := by
      rw [add_comm]
      exact P.anticomm
    rw [h_anticomm]
  let qv : Cl55 := q • P.v
  have h_goal_rewrite : (x + -q • P.v + P.u) * (x + -q • P.v + P.u) = (x - qv + P.u) * (x - qv + P.u) := by
    dsimp [qv]
    rw [neg_smul, ← sub_eq_add_neg]
  rw [h_goal_rewrite]
  have h_expand : (x - qv + P.u) * (x - qv + P.u) =
      x * x - x * qv + x * P.u - qv * x + qv * qv - qv * P.u + P.u * x - P.u * qv + P.u * P.u := by
    noncomm_ring
  have h1 : x * qv = q • (x * P.v) := by dsimp [qv]; rw [mul_smul_comm]
  have h2 : qv * x = q • (P.v * x) := by dsimp [qv]; rw [smul_mul_assoc]
  have h3 : qv * qv = (q * q) • (P.v * P.v) := by dsimp [qv]; rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h4 : qv * P.u = q • (P.v * P.u) := by dsimp [qv]; rw [smul_mul_assoc]
  have h5 : P.u * qv = q • (P.u * P.v) := by dsimp [qv]; rw [mul_smul_comm]
  rw [h_expand]
  rw [hx_sq]
  rw [h_u2]
  rw [h1, h2, h3, h4, h5]
  rw [h_v2]
  simp only [smul_zero, add_zero]
  have h_rearrange : q • (1 : Cl55) - q • (x * P.v) + x * P.u - q • (P.v * x) - q • (P.v * P.u) + P.u * x - q • (P.u * P.v) =
      q • (1 : Cl55) + ((- q) • (x * P.v) - q • (P.v * x)) + (x * P.u + P.u * x) + ((- q) • (P.v * P.u) - q • (P.u * P.v)) := by
    rw [neg_smul, neg_smul]
    noncomm_ring
  rw [h_rearrange]
  rw [h_x_v_cancel, h_x_u_cancel, h_uv_cancel]
  simp

end InfoGeometry.Clifford.ConformalProjectiveEmbedding55

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
- `geoInv_sq` : Evaluates the square of the geometric inverse vector $x^{-1}$, proving natively that $(x^{-1})^2 = 1 / x^2$. Verified completely via scalar field arithmetic.
- `conformal_inversion_maps_to_geoInv` : Proves natively that the action of the reflection sphere $S$ on the projective embedding of $x$ maps strictly to the scaled projective embedding of the geometric inverse: $- S * F(x) * S = x^2 F(x^{-1})$. Fully closed with zero remaining dependencies or placeholders.
- `F_sq_zero` : Proves that the projective embedding of any vector in the split null cone lands strictly on the null cone of $Cl(5,5)$, i.e., $F(x,q)^2 = 0$. Fully closed and verified.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- (None) : All definitions and theorems in `ConformalProjectiveEmbedding55.lean` are fully and unconditionally proved over any valid choice of `ConformalNullPair` witness.

#### BUCKET 3: OPEN CLOSURE DEBT
- (None) : Zero open closure debt remains in the `ConformalProjectiveEmbedding55` lane.
-/
