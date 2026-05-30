import InfoGeometry.Clifford.ConformalLift55
import Mathlib
import Mathlib.Tactic.NoncommRing

/-!
# Conformal Projective Embedding

This file defines the projective embedding `F(x) = x + (1/2) x² n∞ + n₀`
and the geometric inverse `x⁻¹ = x / x²`.

It proves the finite Clifford-algebra reflection identity sending `F(x)` to the
scaled embedding of the geometric inverse.
-/

noncomputable section

namespace InfoGeometry.Clifford.ConformalProjectiveEmbedding55

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ConformalLift55

variable (P : ConformalNullPair)

/-- The standard CGA origin generator. -/
def n_zero : Cl55 := P.u

/-- The standard CGA infinity generator. -/
def n_infty : Cl55 := (-2 : ℝ) • P.v

/-- Projective embedding `F(x) = x + (1/2)x² n∞ + n₀`. -/
def F (x : Cl55) (x_sq : ℝ) : Cl55 :=
  x + (1 / 2 * x_sq) • n_infty P + n_zero P

/-- Geometric inverse `x⁻¹ = x / x²`. -/
def geoInv (x : Cl55) (x_sq : ℝ) : Cl55 :=
  (1 / x_sq) • x

/-- Geometric inverse squared is `1 / x²`. -/
theorem geoInv_sq (x : Cl55) (x_sq : ℝ)
    (hx_sq : x * x = x_sq • (1 : Cl55)) (hx : x_sq ≠ 0) :
    geoInv x x_sq * geoInv x x_sq = (1 / x_sq : ℝ) • (1 : Cl55) := by
  dsimp [geoInv]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  rw [hx_sq, smul_smul]
  congr 1
  calc
    (1 / x_sq) * (1 / x_sq) * x_sq
        = (1 / x_sq) * ((1 / x_sq) * x_sq) := by rw [mul_assoc]
    _ = (1 / x_sq) * 1 := by rw [div_mul_cancel₀ 1 hx]
    _ = 1 / x_sq := by rw [mul_one]

/-- The conformal inversion sphere `S = u + v`. -/
def S : Cl55 := P.u + P.v

/-- Null-pair square rule for `u`. -/
theorem u_mul_u : P.u * P.u = 0 := by
  simpa [pow_two] using P.u_square

/-- Null-pair square rule for `v`. -/
theorem v_mul_v : P.v * P.v = 0 := by
  simpa [pow_two] using P.v_square

/-- The inversion sphere squares to the identity. -/
theorem S_sq : S P * S P = 1 := by
  dsimp [S]
  have hu : P.u * P.u = 0 := u_mul_u P
  have hv : P.v * P.v = 0 := v_mul_v P
  calc
    (P.u + P.v) * (P.u + P.v)
        = P.u * P.u + (P.u * P.v + P.v * P.u) + P.v * P.v := by
            noncomm_ring
    _ = 0 + 1 + 0 := by rw [hu, hv, P.anticomm]
    _ = 1 := by noncomm_ring

/-- Conjugation by `S = u + v` sends `u` to `v`. -/
theorem S_u_S : S P * P.u * S P = P.v := by
  dsimp [S]
  have hu : P.u * P.u = 0 := u_mul_u P
  have hv : P.v * P.v = 0 := v_mul_v P
  have hsub : P.u * P.v = 1 - P.v * P.u :=
    eq_sub_of_add_eq P.anticomm
  have hvuv : P.v * P.u * P.v = P.v := by
    calc
      P.v * P.u * P.v = P.v * (P.u * P.v) := by noncomm_ring
      _ = P.v * (1 - P.v * P.u) := by rw [hsub]
      _ = P.v - P.v * P.v * P.u := by noncomm_ring
      _ = P.v := by rw [hv]; noncomm_ring
  calc
    (P.u + P.v) * P.u * (P.u + P.v)
        = P.v * P.u * P.v := by rw [hu]; noncomm_ring
    _ = P.v := hvuv

/-- Conjugation by `S = u + v` sends `v` to `u`. -/
theorem S_v_S : S P * P.v * S P = P.u := by
  dsimp [S]
  have hu : P.u * P.u = 0 := u_mul_u P
  have hv : P.v * P.v = 0 := v_mul_v P
  have hsub : P.v * P.u = 1 - P.u * P.v := by
    have hcomm : P.v * P.u + P.u * P.v = 1 := by
      rw [add_comm]
      exact P.anticomm
    exact eq_sub_of_add_eq hcomm
  have huvu : P.u * P.v * P.u = P.u := by
    calc
      P.u * P.v * P.u = P.u * (P.v * P.u) := by noncomm_ring
      _ = P.u * (1 - P.u * P.v) := by rw [hsub]
      _ = P.u - P.u * P.u * P.v := by noncomm_ring
      _ = P.u := by rw [hu]; noncomm_ring
  calc
    (P.u + P.v) * P.v * (P.u + P.v)
        = P.u * P.v * P.u := by rw [hv]; noncomm_ring
    _ = P.u := huvu

/-- If `x` anticommutes with the null pair, then it anticommutes with `S`. -/
theorem x_mul_S_eq_neg_S_mul_x (x : Cl55)
    (hx_ortho_u : x * P.u = - P.u * x)
    (hx_ortho_v : x * P.v = - P.v * x) :
    x * S P = - S P * x := by
  dsimp [S]
  rw [mul_add, add_mul, hx_ortho_u, hx_ortho_v]
  noncomm_ring

/-- If `x` anticommutes with the null pair, then `S*x*S = -x`. -/
theorem S_x_S_eq_neg_x (x : Cl55)
    (hx_ortho_u : x * P.u = - P.u * x)
    (hx_ortho_v : x * P.v = - P.v * x) :
    S P * x * S P = -x := by
  have hxS : x * S P = - S P * x :=
    x_mul_S_eq_neg_S_mul_x P x hx_ortho_u hx_ortho_v
  have hS2 : S P * S P = 1 := S_sq P
  calc
    S P * x * S P = S P * (x * S P) := by rw [mul_assoc]
    _ = S P * (- S P * x) := by rw [hxS]
    _ = - (S P * S P) * x := by noncomm_ring
    _ = - (1 : Cl55) * x := by rw [hS2]
    _ = -x := by noncomm_ring

/--
Reflection/inversion law for the projective conformal embedding.

If `x` is orthogonal to the conformal null pair, and `q` is the nonzero scalar
representing `x²`, then conjugation by `S = u + v` sends the projective embedding
of `x` to the scaled embedding of the geometric inverse `q⁻¹x`.
-/
theorem conformal_inversion_maps_to_geoInv (x : Cl55) (q : ℝ)
    (hx_ortho_u : x * P.u = - P.u * x)
    (hx_ortho_v : x * P.v = - P.v * x)
    (_hx_sq : x * x = q • (1 : Cl55))
    (hq : q ≠ 0) :
    - (S P * F P x q * S P) = q • F P (geoInv x q) (1 / q) := by
  dsimp [F, geoInv, n_zero, n_infty]
  have h_S_x_S : S P * x * S P = -x :=
    S_x_S_eq_neg_x P x hx_ortho_u hx_ortho_v
  have h_S_u_S : S P * P.u * S P = P.v := S_u_S P
  have h_S_v_S : S P * P.v * S P = P.u := S_v_S P
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
  have h_LHS :
      - (S P * (x + - q • P.v + P.u) * S P) = x + q • P.u - P.v := by
    rw [mul_add, add_mul, mul_add, add_mul]
    rw [mul_smul_comm, smul_mul_assoc]
    rw [h_S_x_S, h_S_v_S, h_S_u_S]
    simp only [neg_add, neg_neg, neg_smul]
    abel
  have h_RHS :
      q • ((1 / q) • x + - (1 / q) • P.v + P.u) = x + q • P.u - P.v := by
    rw [smul_add, smul_add, smul_smul, smul_smul]
    have h_scal : q * -(1 / q) = -1 := by
      calc
        q * -(1 / q) = - (q * (1 / q)) := by ring
        _ = -1 := by rw [h_inv]
    rw [h_scal, h_inv]
    simp only [one_smul, neg_one_smul]
    abel
  rw [h_LHS, h_RHS]

/--
The projective embedding of a vector orthogonal to the conformal null pair lands
on the null cone when `x² = q`.
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
  have h_u2 : P.u * P.u = 0 := u_mul_u P
  have h_v2 : P.v * P.v = 0 := v_mul_v P
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
  have h_goal_rewrite :
      (x + -q • P.v + P.u) * (x + -q • P.v + P.u)
        = (x - qv + P.u) * (x - qv + P.u) := by
    dsimp [qv]
    rw [neg_smul, ← sub_eq_add_neg]
  rw [h_goal_rewrite]
  have h_expand : (x - qv + P.u) * (x - qv + P.u) =
      x * x - x * qv + x * P.u - qv * x + qv * qv - qv * P.u
        + P.u * x - P.u * qv + P.u * P.u := by
    noncomm_ring
  have h1 : x * qv = q • (x * P.v) := by dsimp [qv]; rw [mul_smul_comm]
  have h2 : qv * x = q • (P.v * x) := by dsimp [qv]; rw [smul_mul_assoc]
  have h3 : qv * qv = (q * q) • (P.v * P.v) := by
    dsimp [qv]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h4 : qv * P.u = q • (P.v * P.u) := by dsimp [qv]; rw [smul_mul_assoc]
  have h5 : P.u * qv = q • (P.u * P.v) := by dsimp [qv]; rw [mul_smul_comm]
  rw [h_expand]
  rw [hx_sq]
  rw [h_u2]
  rw [h1, h2, h3, h4, h5]
  rw [h_v2]
  simp only [smul_zero, add_zero]
  have h_rearrange :
      q • (1 : Cl55) - q • (x * P.v) + x * P.u - q • (P.v * x)
          - q • (P.v * P.u) + P.u * x - q • (P.u * P.v)
        = q • (1 : Cl55) + ((- q) • (x * P.v) - q • (P.v * x))
          + (x * P.u + P.u * x) + ((- q) • (P.v * P.u) - q • (P.u * P.v)) := by
    rw [neg_smul, neg_smul]
    noncomm_ring
  rw [h_rearrange]
  rw [h_x_v_cancel, h_x_u_cancel, h_uv_cancel]
  simp

end InfoGeometry.Clifford.ConformalProjectiveEmbedding55

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `geoInv_sq`
- `u_mul_u`
- `v_mul_v`
- `S_sq`
- `S_u_S`
- `S_v_S`
- `x_mul_S_eq_neg_S_mul_x`
- `S_x_S_eq_neg_x`
- `conformal_inversion_maps_to_geoInv`
- `F_sq_zero`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Theorems that compile conditionally based on explicitly named, valid premises or external verified witnesses. No hidden assumptions.]
- All theorems are parameterized by an explicit `ConformalNullPair` witness `P`.
- `conformal_inversion_maps_to_geoInv` and `F_sq_zero` additionally require explicit orthogonality hypotheses.

#### BUCKET 3: OPEN CLOSURE DEBT
[Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]
- No Type III theorem.
- No analytic continuation theorem.
- No global conformal compactification theorem.
-/
