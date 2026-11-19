/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Connes–Lott Yang–Baxter–Kantor Poset (`A₀ ≺ … ≺ A₁₁`, `M₀ ≺ … ≺ M₅`)

Unified, deduplicated noncommutative matrix operator algebra for the
Non-Abelian Yang–Mills–Higgs Connes–Lott Yang–Baxter Attention poset:
1. `Mat2 R` (`End(ℂ²)`) with `toMatrixEquiv : Mat2 R ≃ Matrix (Fin 2) (Fin 2) R`
   and multiplicative bridge `toMatrix_mul`, `toMatrix_add`, `toMatrix_one`,
   plus an explicit noncommuting witness (`connes_lott_yang_baxter_noncommuting`).
2. Stages `A₀ ≺ A₁`, `A₆–A₉`, and Archetypes `M₀–M₁`: `sl₂(R)` Lie connection &
   curvature, Lorentzian signature `(2, 1)` Killing form, Yang–Mills Frobenius–Cartan
   splitting, Connes–Lott boundary-twist Higgs Cayley–Hamilton identity, and finite-group
   BCH Wilson-link decomposition.
3. `Mat4 R` (`V₁ ⊗ V₂`): Stages `A₂–A₅`, `A₁₀`: `physDressedLax = auxDressedLax`,
   `higgsTransfer` intertwining, closed-form transfer matrix, and unconditional
   multi-head transfer commutativity `[τ̃(w₁, η₁), τ̃(w₂, η₂)] = 0`.
4. `AuxMat4 R` (`V₀ ⊗ V₁ ⊗ V₂`): Stage `A₁₁` and Archetypes `M₂–M₅`:
   3-factor equivariant Yang–Baxter RTT braid relation, 2-factor cocycle telescoping,
   corner activation (`m41`, `m14`), shifted Yangian quantum determinant collapse to the
   Kähler–Bergman barrier, and unconditional 2-site gauged transfer commutativity.
-/

namespace InfoGeometry.Algebra.ConnesLottYangBaxterPoset

/-! ### 1. `2 × 2` Algebra `Mat2 R` and Mathlib `Matrix (Fin 2) (Fin 2) R` Bridge -/

/-- Explicit `2 × 2` matrix over a commutative ring `R`. -/
@[ext]
structure Mat2 (R : Type*) where
  a11 : R
  a12 : R
  a21 : R
  a22 : R
  deriving DecidableEq, Repr

namespace Mat2

section Ops
variable {R : Type*} [CommRing R]

def zero : Mat2 R := ⟨0, 0, 0, 0⟩
def one  : Mat2 R := ⟨1, 0, 0, 1⟩

def E00 : Mat2 R := ⟨1, 0, 0, 0⟩
def E01 : Mat2 R := ⟨0, 1, 0, 0⟩
def E10 : Mat2 R := ⟨0, 0, 1, 0⟩
def E11 : Mat2 R := ⟨0, 0, 0, 1⟩

def add (A B : Mat2 R) : Mat2 R :=
  ⟨A.a11 + B.a11, A.a12 + B.a12, A.a21 + B.a21, A.a22 + B.a22⟩

def sub (A B : Mat2 R) : Mat2 R :=
  ⟨A.a11 - B.a11, A.a12 - B.a12, A.a21 - B.a21, A.a22 - B.a22⟩

def neg (A : Mat2 R) : Mat2 R :=
  ⟨-A.a11, -A.a12, -A.a21, -A.a22⟩

def smul (c : R) (A : Mat2 R) : Mat2 R :=
  ⟨c * A.a11, c * A.a12, c * A.a21, c * A.a22⟩

def mul (A B : Mat2 R) : Mat2 R :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21, A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21, A.a21 * B.a12 + A.a22 * B.a22⟩

def comm  (A B : Mat2 R) : Mat2 R := sub (mul A B) (mul B A)
def acomm (A B : Mat2 R) : Mat2 R := add (mul A B) (mul B A)
def tr    (A : Mat2 R)   : R      := A.a11 + A.a22
def det   (A : Mat2 R)   : R      := A.a11 * A.a22 - A.a12 * A.a21
def adj   (G : Mat2 R)   : Mat2 R := ⟨G.a22, -G.a12, -G.a21, G.a11⟩

/-- Non-Abelian Wilson transition link / cocycle `W_{2,1} = G₂ adj(G₁)`. -/
def wilsonLink (G2 G1 : Mat2 R) : Mat2 R := mul G2 (adj G1)

/-- Bridge to Mathlib `Matrix (Fin 2) (Fin 2) R`. -/
def toMatrix (A : Mat2 R) : Matrix (Fin 2) (Fin 2) R := !![A.a11, A.a12; A.a21, A.a22]

/-- Inverse bridge from Mathlib `Matrix (Fin 2) (Fin 2) R`. -/
def ofMatrix (M : Matrix (Fin 2) (Fin 2) R) : Mat2 R := ⟨M 0 0, M 0 1, M 1 0, M 1 1⟩

def toMatrixEquiv : Mat2 R ≃ Matrix (Fin 2) (Fin 2) R where
  toFun := toMatrix
  invFun := ofMatrix
  left_inv A := by ext <;> rfl
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

lemma toMatrix_one : toMatrix (one : Mat2 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, one]

lemma toMatrix_add (A B : Mat2 R) : toMatrix (add A B) = toMatrix A + toMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, add]

lemma toMatrix_mul (A B : Mat2 R) : toMatrix (mul A B) = toMatrix A * toMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, mul, Matrix.mul_apply, Fin.sum_univ_two]

def sigma_x    : Mat2 R := ⟨0, 1,  1,  0⟩
def neg_isig_y : Mat2 R := ⟨0, -1, 1,  0⟩
def sigma_z    : Mat2 R := ⟨1, 0,  0, -1⟩

def Jx (q0 q1 k0 k1 : R) : R := q0 * k1 + q1 * k0
def Jy (q0 q1 k0 k1 : R) : R := q0 * k1 - q1 * k0
def Jz (q0 q1 k0 k1 : R) : R := q0 * k0 - q1 * k1

/-- General traceless element in `sl₂(R)` with coordinates `(ax, ay, az)`. -/
def lieConnection (ax ay az : R) : Mat2 R :=
  add (add (smul ax sigma_x) (smul ay neg_isig_y)) (smul az sigma_z)

/-- Weighted bilinear map `(q, k) ↦ sl₂(R)` with anisotropy parameters `(gx, gy, gz)`. -/
def weightedBilinear (gx gy gz q0 q1 k0 k1 : R) : Mat2 R :=
  lieConnection (gx * Jx q0 q1 k0 k1) (gy * Jy q0 q1 k0 k1) (gz * Jz q0 q1 k0 k1)

/-- Normalized signature `(2, 1)` Killing form `κ(A₁, A₂) = (1/2) tr(A₁ A₂)`. -/
def killingForm (ax1 ay1 az1 ax2 ay2 az2 : R) : R :=
  ax1 * ax2 - ay1 * ay2 + az1 * az2

/-- Cayley–Hamilton group element `c₀ I₂ + s₀ A`. -/
def expSL2 (c0 s0 : R) (A : Mat2 R) : Mat2 R :=
  add (smul c0 one) (smul s0 A)

/-- Connes–Lott boundary-twist Higgs matrix `K(q, w_B, w_C) = [[1, q w_C], [w_B, -q]]`. -/
def higgsK (q wB wC : R) : Mat2 R := ⟨1, q * wC, wB, -q⟩

/-- Frobenius quadratic form `||W - I₂||_F²`. -/
def frobeniusLinkLoss (W : Mat2 R) : R :=
  (W.a11 - 1) * (W.a11 - 1) + W.a12 * W.a12 + W.a21 * W.a21 + (W.a22 - 1) * (W.a22 - 1)

/-- Conjugation-invariant Wilson trace loss `tr((W - I₂)(adj W - I₂))`. -/
def wilsonInvariantLoss (W : Mat2 R) : R :=
  tr (mul (sub W one) (sub (adj W) one))

/-- Cartan boost defect `(w₁₁ - w₂₂)² + (w₁₂ + w₂₁)²`. -/
def cartanBoostLoss (W : Mat2 R) : R :=
  (W.a11 - W.a22) * (W.a11 - W.a22) + (W.a12 + W.a21) * (W.a12 + W.a21)

/-- OpenGauss T16 noncommutativity witness in `Mat2 ℤ`. -/
theorem connes_lott_yang_baxter_noncommuting :
    comm (sigma_x : Mat2 ℤ) (sigma_z : Mat2 ℤ) ≠ zero := by
  intro h
  have h12 : (comm (sigma_x : Mat2 ℤ) (sigma_z : Mat2 ℤ)).a12 = (zero : Mat2 ℤ).a12 := by rw [h]
  dsimp [comm, sub, mul, sigma_x, sigma_z, zero] at h12
  norm_num at h12

/-- OpenGauss T16 matrix shear generators witnessing noncommutativity over any nontrivial ring. -/
def shearGenerator [Zero R] [One R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 0, 0]

def lowerShearGenerator [Zero R] [One R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 1, 0]

/-- The `2×2` matrix algebra is non-commutative over any nontrivial ring. -/
theorem matrix_fin2_noncommutative [Nontrivial R] :
    (shearGenerator : Matrix (Fin 2) (Fin 2) R) *
        (lowerShearGenerator : Matrix (Fin 2) (Fin 2) R) ≠
      lowerShearGenerator * shearGenerator := by
  apply ne_of_apply_ne (fun M => M 0 0)
  simp [shearGenerator, lowerShearGenerator, Matrix.mul_apply, Fin.sum_univ_two]

/-- Explicit real non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ` (OpenGauss T16). -/
def realP0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
def realX : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem real_matrix_two_noncommutative : realP0 * realX ≠ realX * realP0 := by
  intro h
  have h01 : (realP0 * realX) 0 1 = (realX * realP0) 0 1 := by rw [h]
  simp [realP0, realX, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Stages `A₀ ≺ A₁` & Archetype `M₀`: `sl₂(R)` Lie connection, adjugate identity,
    Killing anticommutator, and isotropic nilpotency / elliptic complex structure. -/
theorem stage_A0_A1_nonabelian_lie_connection_and_curvature
    (ax1 ay1 az1 ax2 ay2 az2 : R) (G : Mat2 R) :
    let A1 := lieConnection ax1 ay1 az1
    let A2 := lieConnection ax2 ay2 az2
    let ω_sq := az1 * az1 + ax1 * ax1 - ay1 * ay1
    A1 = ⟨az1, ax1 - ay1, ax1 + ay1, -az1⟩ ∧
    tr A1 = 0 ∧
    mul A1 A1 = smul ω_sq one ∧
    mul G (adj G) = smul (det G) one ∧
    mul (adj G) G = smul (det G) one ∧
    comm A1 A2 = lieConnection
      (2 * (ay1 * az2 - az1 * ay2))
      (2 * (ax1 * az2 - az1 * ax2))
      (2 * (ax1 * ay2 - ay1 * ax2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · (try ext) <;> dsimp [lieConnection, sigma_x, neg_isig_y, sigma_z,
                         comm, mul, add, sub, smul, adj, det, tr, one] <;> ring

/-- Archetype `M₀` rank-1 nilpotency & anisotropic elliptic structure alongside `sl₂` Killing form. -/
theorem archetype_M0_rank1_nilpotency_and_elliptic_structure (q0 q1 k0 k1 : R) :
    let A_iso  := weightedBilinear 1 1 1 q0 q1 k0 k1
    let A_nilp := weightedBilinear 1 1 1 q0 q1 (-q1) q0
    let A_ell  := weightedBilinear 0 1 0 1 0 0 1
    det A_iso = -((q0 * k0 + q1 * k1) * (q0 * k0 + q1 * k1)) ∧
    mul A_nilp A_nilp = zero ∧
    mul A_ell A_ell = smul (-1) one := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · (try ext) <;> dsimp [weightedBilinear, lieConnection, Jx, Jy, Jz,
                         sigma_x, neg_isig_y, sigma_z, mul, add, smul, det, one, zero] <;> ring

/-- Stage `A₆`: Lorentzian signature `(2, 1)` Killing metric and Clifford curvature square. -/
theorem stage_A6_lorentzian_killing_metric_and_clifford_curvature_square
    (ax1 ay1 az1 ax2 ay2 az2 : R) :
    let A1 := lieConnection ax1 ay1 az1
    let A2 := lieConnection ax2 ay2 az2
    let F12 := comm A1 A2
    let k11 := killingForm ax1 ay1 az1 ax1 ay1 az1
    let k22 := killingForm ax2 ay2 az2 ax2 ay2 az2
    let k12 := killingForm ax1 ay1 az1 ax2 ay2 az2
    acomm A1 A2 = smul (2 * k12) one ∧
    tr (mul A1 F12) = 0 ∧
    tr (mul A2 F12) = 0 ∧
    mul F12 F12 = smul (4 * (k12 * k12 - k11 * k22)) one := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · (try ext) <;> dsimp [lieConnection, killingForm, sigma_x, neg_isig_y, sigma_z,
                         comm, acomm, mul, add, sub, smul, tr, one] <;> ring

/-- Stage `A₇` / Archetype `M₁`: Yang–Mills Frobenius–Cartan splitting and gauge invariance. -/
theorem stage_A7_yang_mills_frobenius_cartan_splitting_and_gauge_invariance
    (W H : Mat2 R) (c s : R) :
    let R_so2 : Mat2 R := ⟨c, -s, s, c⟩
    let W_conj := mul (mul H W) (adj H)
    frobeniusLinkLoss W = wilsonInvariantLoss W + cartanBoostLoss W ∧
    wilsonInvariantLoss W = 2 * (1 + det W - tr W) ∧
    tr W_conj = det H * tr W ∧
    det W_conj = det H * det H * det W ∧
    cartanBoostLoss R_so2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp [frobeniusLinkLoss, wilsonInvariantLoss, cartanBoostLoss,
           mul, sub, adj, tr, det, one]; ring

/-- Stage `A₈` / Archetype `M₁`: Connes–Lott Higgs determinant, Cayley–Hamilton identity,
    and scale invariance. -/
theorem stage_A8_connes_lott_higgs_determinant_and_scale_invariance
    (q wB wC lam : R) :
    let K := higgsK q wB wC
    let D_lam : Mat2 R := ⟨1, 0, 0, lam⟩
    tr K = 1 - q ∧
    det K = -q * (1 + wB * wC) ∧
    sub (sub (mul K K) (smul (1 - q) K)) (smul (q * (1 + wB * wC)) one) = zero ∧
    mul (mul D_lam (higgsK q wB (lam * wC))) (adj D_lam) =
      smul lam (higgsK q (lam * wB) wC) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · (try ext) <;> dsimp [higgsK, mul, sub, smul, adj, tr, det, one, zero] <;> ring

/-- Stage `A₉`: Finite-group BCH Wilson-link Killing decomposition. -/
theorem stage_A9_finite_group_bch_wilson_link_killing_decomposition
    (c1 s1 ax1 ay1 az1 c2 s2 ax2 ay2 az2 : R) :
    let A1  := lieConnection ax1 ay1 az1
    let A2  := lieConnection ax2 ay2 az2
    let G1  := expSL2 c1 s1 A1
    let G2  := expSL2 c2 s2 A2
    let W21 := wilsonLink G2 G1
    let W12 := wilsonLink G1 G2
    let k12 := killingForm ax1 ay1 az1 ax2 ay2 az2
    smul 2 W21 =
      add (add (smul (2 * (c1 * c2 - s1 * s2 * k12)) one)
               (sub (smul (2 * c1 * s2) A2) (smul (2 * c2 * s1) A1)))
          (smul (s1 * s2) (comm A1 A2)) ∧
    tr W21 = 2 * (c1 * c2 - s1 * s2 * k12) ∧
    sub (sub W21 W12) (sub (smul (2 * c1 * s2) A2) (smul (2 * c2 * s1) A1)) =
      smul (s1 * s2) (comm A1 A2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · (try ext) <;> dsimp [wilsonLink, expSL2, lieConnection, killingForm,
                         sigma_x, neg_isig_y, sigma_z,
                         comm, mul, add, sub, smul, adj, tr, one] <;> ring

end Ops
end Mat2

/-! ### 2. `4 × 4` Tensor Algebra `Mat4 R` (`V₁ ⊗ V₂`) — Stages `A₂–A₅`, `A₁₀` -/

/-- Explicit `4 × 4` matrix over `R` representing `End(V₁ ⊗ V₂)`. -/
@[ext]
structure Mat4 (R : Type*) where
  m11 : R
  m12 : R
  m13 : R
  m14 : R
  m21 : R
  m22 : R
  m23 : R
  m24 : R
  m31 : R
  m32 : R
  m33 : R
  m34 : R
  m41 : R
  m42 : R
  m43 : R
  m44 : R
  deriving DecidableEq, Repr

namespace Mat4

section Ops
variable {R : Type*} [CommRing R]

def zero : Mat4 R := ⟨0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0⟩
def one  : Mat4 R := ⟨1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1⟩

def add (A B : Mat4 R) : Mat4 R :=
  ⟨A.m11+B.m11, A.m12+B.m12, A.m13+B.m13, A.m14+B.m14,
   A.m21+B.m21, A.m22+B.m22, A.m23+B.m23, A.m24+B.m24,
   A.m31+B.m31, A.m32+B.m32, A.m33+B.m33, A.m34+B.m34,
   A.m41+B.m41, A.m42+B.m42, A.m43+B.m43, A.m44+B.m44⟩

def sub (A B : Mat4 R) : Mat4 R :=
  ⟨A.m11-B.m11, A.m12-B.m12, A.m13-B.m13, A.m14-B.m14,
   A.m21-B.m21, A.m22-B.m22, A.m23-B.m23, A.m24-B.m24,
   A.m31-B.m31, A.m32-B.m32, A.m33-B.m33, A.m34-B.m34,
   A.m41-B.m41, A.m42-B.m42, A.m43-B.m43, A.m44-B.m44⟩

def smul (c : R) (A : Mat4 R) : Mat4 R :=
  ⟨c*A.m11, c*A.m12, c*A.m13, c*A.m14,
   c*A.m21, c*A.m22, c*A.m23, c*A.m24,
   c*A.m31, c*A.m32, c*A.m33, c*A.m34,
   c*A.m41, c*A.m42, c*A.m43, c*A.m44⟩

def mul (A B : Mat4 R) : Mat4 R :=
  ⟨A.m11*B.m11 + A.m12*B.m21 + A.m13*B.m31 + A.m14*B.m41,
   A.m11*B.m12 + A.m12*B.m22 + A.m13*B.m32 + A.m14*B.m42,
   A.m11*B.m13 + A.m12*B.m23 + A.m13*B.m33 + A.m14*B.m43,
   A.m11*B.m14 + A.m12*B.m24 + A.m13*B.m34 + A.m14*B.m44,
   A.m21*B.m11 + A.m22*B.m21 + A.m23*B.m31 + A.m24*B.m41,
   A.m21*B.m12 + A.m22*B.m22 + A.m23*B.m32 + A.m24*B.m42,
   A.m21*B.m13 + A.m22*B.m23 + A.m23*B.m33 + A.m24*B.m43,
   A.m21*B.m14 + A.m22*B.m24 + A.m23*B.m34 + A.m24*B.m44,
   A.m31*B.m11 + A.m32*B.m21 + A.m33*B.m31 + A.m34*B.m41,
   A.m31*B.m12 + A.m32*B.m22 + A.m33*B.m32 + A.m34*B.m42,
   A.m31*B.m13 + A.m32*B.m23 + A.m33*B.m33 + A.m34*B.m43,
   A.m31*B.m14 + A.m32*B.m24 + A.m33*B.m34 + A.m34*B.m44,
   A.m41*B.m11 + A.m42*B.m21 + A.m43*B.m31 + A.m44*B.m41,
   A.m41*B.m12 + A.m42*B.m22 + A.m43*B.m32 + A.m44*B.m42,
   A.m41*B.m13 + A.m42*B.m23 + A.m43*B.m33 + A.m44*B.m43,
   A.m41*B.m14 + A.m42*B.m24 + A.m43*B.m34 + A.m44*B.m44⟩

def comm (A B : Mat4 R) : Mat4 R := sub (mul A B) (mul B A)

def kron (A B : Mat2 R) : Mat4 R :=
  ⟨A.a11 * B.a11, A.a11 * B.a12, A.a12 * B.a11, A.a12 * B.a12,
   A.a11 * B.a21, A.a11 * B.a22, A.a12 * B.a21, A.a12 * B.a22,
   A.a21 * B.a11, A.a21 * B.a12, A.a22 * B.a11, A.a22 * B.a12,
   A.a21 * B.a21, A.a21 * B.a22, A.a22 * B.a21, A.a22 * B.a22⟩

def P_swap : Mat4 R := ⟨1,0,0,0, 0,0,1,0, 0,1,0,0, 0,0,0,1⟩
def Lax (w η : R) : Mat4 R := add (smul w one) (smul η P_swap)

def physDressedLax (w η : R) (G : Mat2 R) : Mat4 R :=
  mul (mul (kron Mat2.one G) (Lax w η)) (kron Mat2.one (Mat2.adj G))

def auxDressedLax (w η : R) (G : Mat2 R) : Mat4 R :=
  mul (mul (kron (Mat2.adj G) Mat2.one) (Lax w η)) (kron G Mat2.one)

def blockA (M : Mat4 R) : Mat2 R := ⟨M.m11, M.m12, M.m21, M.m22⟩
def blockB (M : Mat4 R) : Mat2 R := ⟨M.m13, M.m14, M.m23, M.m24⟩
def blockC (M : Mat4 R) : Mat2 R := ⟨M.m31, M.m32, M.m41, M.m42⟩
def blockD (M : Mat4 R) : Mat2 R := ⟨M.m33, M.m34, M.m43, M.m44⟩

def partialTrace0 (M : Mat4 R) : Mat2 R :=
  Mat2.add (blockA M) (blockD M)

def higgsTransfer (q wB wC : R) (M : Mat4 R) : Mat2 R :=
  Mat2.add
    (Mat2.add (Mat2.sub (blockA M) (Mat2.smul q (blockD M)))
              (Mat2.smul wB (blockB M)))
    (Mat2.smul (q * wC) (blockC M))

private theorem mul_assoc_mat4 (A B C : Mat4 R) :
    mul (mul A B) C = mul A (mul B C) := by
  ext <;> dsimp [mul] <;> ring

private theorem one_mul_mat4 (A : Mat4 R) : mul one A = A := by
  ext <;> dsimp [mul, one] <;> ring

private theorem mul_one_mat4 (A : Mat4 R) : mul A one = A := by
  ext <;> dsimp [mul, one] <;> ring

private theorem zero_mul_mat4 (A : Mat4 R) : mul zero A = zero := by
  ext <;> dsimp [mul, zero] <;> ring

private theorem mul_zero_mat4 (A : Mat4 R) : mul A zero = zero := by
  ext <;> dsimp [mul, zero] <;> ring

private theorem add_assoc_mat4 (A B C : Mat4 R) : add (add A B) C = add A (add B C) := by
  ext <;> dsimp [add] <;> ring

private theorem add_comm_mat4 (A B : Mat4 R) : add A B = add B A := by
  ext <;> dsimp [add] <;> ring

private theorem zero_add_mat4 (A : Mat4 R) : add zero A = A := by
  ext <;> dsimp [add, zero] <;> ring

private theorem add_zero_mat4 (A : Mat4 R) : add A zero = A := by
  ext <;> dsimp [add, zero] <;> ring

private theorem add_mul_mat4 (A B C : Mat4 R) : mul (add A B) C = add (mul A C) (mul B C) := by
  ext <;> dsimp [mul, add] <;> ring

private theorem mul_add_mat4 (A B C : Mat4 R) : mul A (add B C) = add (mul A B) (mul A C) := by
  ext <;> dsimp [mul, add] <;> ring

private theorem smul_add_mat4 (c : R) (A B : Mat4 R) :
    smul c (add A B) = add (smul c A) (smul c B) := by
  ext <;> dsimp [smul, add] <;> ring

private theorem add_smul_mat4 (a b : R) (A : Mat4 R) :
    smul (a + b) A = add (smul a A) (smul b A) := by
  ext <;> dsimp [smul, add] <;> ring

private theorem smul_smul_mat4 (a b : R) (A : Mat4 R) :
    smul a (smul b A) = smul (a * b) A := by
  ext <;> dsimp [smul] <;> ring

private theorem kron_mul_kron (A B C D : Mat2 R) :
    mul (kron A B) (kron C D) = kron (Mat2.mul A C) (Mat2.mul B D) := by
  ext <;> dsimp [kron, mul, Mat2.mul] <;> ring

private theorem mul_smul_mat4 (c : R) (A B : Mat4 R) :
    mul A (smul c B) = smul c (mul A B) := by
  ext <;> dsimp [mul, smul] <;> ring

private theorem smul_mul_mat4 (c : R) (A B : Mat4 R) :
    mul (smul c A) B = smul c (mul A B) := by
  ext <;> dsimp [mul, smul] <;> ring

private theorem smul_sub_mat4 (c : R) (A B : Mat4 R) :
    smul c (sub A B) = sub (smul c A) (smul c B) := by
  ext <;> dsimp [smul, sub] <;> ring

private theorem kron_adj_mul_kron (G1 G2 : Mat2 R) :
    mul (kron (Mat2.adj G1) (Mat2.adj G2)) (kron G1 G2) =
      smul (Mat2.det G1 * Mat2.det G2) one := by
  ext <;> dsimp [kron, mul, smul, one, Mat2.adj, Mat2.det] <;> ring

theorem kron_conj_comm (G1 G2 : Mat2 R) (X Y : Mat4 R) :
    comm (mul (mul (kron G1 G2) X) (kron (Mat2.adj G1) (Mat2.adj G2)))
         (mul (mul (kron G1 G2) Y) (kron (Mat2.adj G1) (Mat2.adj G2))) =
      smul (Mat2.det G1 * Mat2.det G2)
           (mul (mul (kron G1 G2) (comm X Y)) (kron (Mat2.adj G1) (Mat2.adj G2))) := by
  have hprod : ∀ A B : Mat4 R,
      mul (mul (mul (kron G1 G2) A) (kron (Mat2.adj G1) (Mat2.adj G2)))
          (mul (mul (kron G1 G2) B) (kron (Mat2.adj G1) (Mat2.adj G2))) =
        smul (Mat2.det G1 * Mat2.det G2)
             (mul (mul (kron G1 G2) (mul A B)) (kron (Mat2.adj G1) (Mat2.adj G2))) := by
    intro A B
    calc mul (mul (mul (kron G1 G2) A) (kron (Mat2.adj G1) (Mat2.adj G2)))
             (mul (mul (kron G1 G2) B) (kron (Mat2.adj G1) (Mat2.adj G2)))
        = mul (mul (kron G1 G2) A)
              (mul (mul (kron (Mat2.adj G1) (Mat2.adj G2)) (kron G1 G2))
                   (mul B (kron (Mat2.adj G1) (Mat2.adj G2)))) := by
          simp only [mul_assoc_mat4]
      _ = smul (Mat2.det G1 * Mat2.det G2)
               (mul (mul (kron G1 G2) (mul A B)) (kron (Mat2.adj G1) (Mat2.adj G2))) := by
          rw [kron_adj_mul_kron, smul_mul_mat4, mul_smul_mat4, one_mul_mat4]
          simp only [mul_assoc_mat4]
  dsimp [comm]
  rw [hprod X Y, hprod Y X, ← smul_sub_mat4]
  congr 1
  ext <;> dsimp [mul, sub] <;> ring

set_option maxHeartbeats 800000 in
/-- Stages `A₂ ≺ A₃ ≺ A₄`: physical-vs.-auxiliary gauge duality and Higgs-transfer intertwining. -/
theorem stage_A2_A3_A4_duality_and_higgs_transfer_intertwining
    (w η q wB wC : R) (G : Mat2 R) (M : Mat4 R) :
    physDressedLax w η G = auxDressedLax w η G ∧
    partialTrace0 (mul (kron (Mat2.higgsK q wB wC) Mat2.one) M) =
      higgsTransfer q wB wC M ∧
    higgsTransfer q wB wC (auxDressedLax w η G) =
      Mat2.mul (Mat2.mul G (higgsTransfer q wB wC (Lax w η))) (Mat2.adj G) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp [physDressedLax, auxDressedLax, higgsTransfer, partialTrace0,
           blockA, blockB, blockC, blockD, Lax, P_swap, kron, mul, add, smul, one,
           Mat2.higgsK, Mat2.mul, Mat2.add, Mat2.sub, Mat2.smul, Mat2.adj, Mat2.one]
    ext <;> ring

/-- Stage `A₅`: Adjugate-covariance preserves Yang–Baxter commutativity. -/
theorem stage_A5_multi_head_yang_baxter_commutativity_preservation
    (τ0 τ1 G : Mat2 R) (h_comm : Mat2.comm τ0 τ1 = Mat2.zero) :
    let τ0_ym := Mat2.mul (Mat2.mul G τ0) (Mat2.adj G)
    let τ1_ym := Mat2.mul (Mat2.mul G τ1) (Mat2.adj G)
    Mat2.comm τ0_ym τ1_ym =
      Mat2.smul (Mat2.det G) (Mat2.mul (Mat2.mul G (Mat2.comm τ0 τ1)) (Mat2.adj G)) ∧
    Mat2.comm τ0_ym τ1_ym = Mat2.zero := by
  intro τ0_ym τ1_ym
  have h_univ :
      Mat2.comm τ0_ym τ1_ym =
        Mat2.smul (Mat2.det G) (Mat2.mul (Mat2.mul G (Mat2.comm τ0 τ1)) (Mat2.adj G)) := by
    ext <;> dsimp [τ0_ym, τ1_ym, Mat2.comm, Mat2.mul, Mat2.sub, Mat2.smul, Mat2.adj, Mat2.det] <;> ring
  refine ⟨h_univ, ?_⟩
  rw [h_univ, h_comm]
  ext <;> dsimp [Mat2.mul, Mat2.smul, Mat2.zero] <;> ring

/-- Stage `A₁₀`: Closed-form Higgs transfer, unconditional multi-head commutativity,
    and Mexican-hat determinant invariant `w_B * w_C`. -/
theorem stage_A10_closed_form_higgs_transfer_and_unconditional_commutativity
    (w1 η1 w2 η2 q wB wC : R) (G : Mat2 R) :
    let τ1_bare := higgsTransfer q wB wC (Lax w1 η1)
    let τ1_ym   := higgsTransfer q wB wC (auxDressedLax w1 η1 G)
    let τ2_ym   := higgsTransfer q wB wC (auxDressedLax w2 η2 G)
    τ1_bare = Mat2.add (Mat2.smul (w1 * (1 - q)) Mat2.one)
                       (Mat2.smul η1 (Mat2.higgsK q wB wC)) ∧
    Mat2.comm τ1_ym τ2_ym = Mat2.zero ∧
    Mat2.det τ1_bare =
      w1 * (w1 + η1) * (1 - q) * (1 - q) -
      η1 * η1 * q * (1 + wB * wC) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp [higgsTransfer, auxDressedLax, blockA, blockB, blockC, blockD,
           Lax, P_swap, kron, mul, add, smul, one,
           Mat2.higgsK, Mat2.comm, Mat2.mul, Mat2.add, Mat2.sub, Mat2.smul,
           Mat2.adj, Mat2.det, Mat2.one, Mat2.zero]
    (try ext) <;> ring

end Ops
end Mat4

/-! ### 3. `8 × 8` Three-Space Algebra `AuxMat4 R` (`V₀ ⊗ V₁ ⊗ V₂`) — Stage `A₁₁` & `M₂–M₅` -/

/-- `2 × 2` block matrix over `Mat4 R` representing `End(V₀ ⊗ V₁ ⊗ V₂)`. -/
@[ext]
structure AuxMat4 (R : Type*) where
  A : Mat4 R
  B : Mat4 R
  C : Mat4 R
  D : Mat4 R
  deriving DecidableEq, Repr

namespace AuxMat4

section Ops
variable {R : Type*} [CommRing R]

def mul (X Y : AuxMat4 R) : AuxMat4 R :=
  ⟨Mat4.add (Mat4.mul X.A Y.A) (Mat4.mul X.B Y.C),
   Mat4.add (Mat4.mul X.A Y.B) (Mat4.mul X.B Y.D),
   Mat4.add (Mat4.mul X.C Y.A) (Mat4.mul X.D Y.C),
   Mat4.add (Mat4.mul X.C Y.B) (Mat4.mul X.D Y.D)⟩

def auxEmbed (G : Mat2 R) : AuxMat4 R :=
  ⟨Mat4.smul G.a11 Mat4.one, Mat4.smul G.a12 Mat4.one,
   Mat4.smul G.a21 Mat4.one, Mat4.smul G.a22 Mat4.one⟩

def physEmbed (M : Mat4 R) : AuxMat4 R :=
  ⟨M, Mat4.zero, Mat4.zero, M⟩

def Lax01 (w1 η : R) : AuxMat4 R :=
  ⟨Mat4.add (Mat4.smul w1 Mat4.one) (Mat4.smul η (Mat4.kron Mat2.E00 Mat2.one)),
   Mat4.smul η (Mat4.kron Mat2.E10 Mat2.one),
   Mat4.smul η (Mat4.kron Mat2.E01 Mat2.one),
   Mat4.add (Mat4.smul w1 Mat4.one) (Mat4.smul η (Mat4.kron Mat2.E11 Mat2.one))⟩

def Lax02 (w2 η : R) : AuxMat4 R :=
  ⟨Mat4.add (Mat4.smul w2 Mat4.one) (Mat4.smul η (Mat4.kron Mat2.one Mat2.E00)),
   Mat4.smul η (Mat4.kron Mat2.one Mat2.E10),
   Mat4.smul η (Mat4.kron Mat2.one Mat2.E01),
   Mat4.add (Mat4.smul w2 Mat4.one) (Mat4.smul η (Mat4.kron Mat2.one Mat2.E11))⟩

def R_ab (u_minus_v η : R) : AuxMat4 R := Lax01 u_minus_v η

def physDressedLax01 (w1 η : R) (G1 : Mat2 R) : AuxMat4 R :=
  mul (mul (physEmbed (Mat4.kron G1 Mat2.one)) (Lax01 w1 η))
      (physEmbed (Mat4.kron (Mat2.adj G1) Mat2.one))

def physDressedLax02 (w2 η : R) (G2 : Mat2 R) : AuxMat4 R :=
  mul (mul (physEmbed (Mat4.kron Mat2.one G2)) (Lax02 w2 η))
      (physEmbed (Mat4.kron Mat2.one (Mat2.adj G2)))

def gaugedLax_ar (u η : R) (Gr : Mat2 R) : AuxMat4 R :=
  physDressedLax02 u η Gr

def gaugedLax_br (v η : R) (Gr : Mat2 R) : AuxMat4 R :=
  mul (mul (physEmbed (Mat4.kron Mat2.one Gr)) (physEmbed (Mat4.Lax v η)))
      (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr)))

def trAux (K : Mat2 R) (T : AuxMat4 R) : Mat4 R :=
  Mat4.add (Mat4.add (Mat4.smul K.a11 T.A) (Mat4.smul K.a12 T.C))
           (Mat4.add (Mat4.smul K.a21 T.B) (Mat4.smul K.a22 T.D))

def bareMonodromy (u θ1 θ2 η : R) : AuxMat4 R :=
  mul (Lax02 (u - θ2) η) (Lax01 (u - θ1) η)

def openCocycleMonodromy (u θ1 θ2 η : R) (W21 : Mat2 R) : AuxMat4 R :=
  mul (mul (Lax02 (u - θ2) η) (auxEmbed W21)) (Lax01 (u - θ1) η)

def ymMonodromy (u θ1 θ2 η : R) (G1 G2 : Mat2 R) : AuxMat4 R :=
  mul (mul (auxEmbed (Mat2.adj G2))
           (openCocycleMonodromy u θ1 θ2 η (Mat2.wilsonLink G2 G1)))
      (auxEmbed G1)

def quantumDet (T_u T_u_shift : AuxMat4 R) : Mat4 R :=
  Mat4.sub (Mat4.mul T_u.A T_u_shift.D) (Mat4.mul T_u.B T_u_shift.C)

private theorem mul_assoc_aux (X Y Z : AuxMat4 R) :
    mul (mul X Y) Z = mul X (mul Y Z) := by
  apply AuxMat4.ext <;> dsimp [mul] <;>
    simp only [Mat4.mul_assoc_mat4, Mat4.add_mul_mat4, Mat4.mul_add_mat4] <;>
    (ext <;> dsimp [Mat4.add] <;> ring)

private def smul_aux (c : R) (X : AuxMat4 R) : AuxMat4 R :=
  ⟨Mat4.smul c X.A, Mat4.smul c X.B, Mat4.smul c X.C, Mat4.smul c X.D⟩

private theorem mul_smul_aux (c : R) (X Y : AuxMat4 R) :
    mul X (smul_aux c Y) = smul_aux c (mul X Y) := by
  ext <;> dsimp [mul, smul_aux] <;>
    simp only [Mat4.mul_smul_mat4, Mat4.smul_add_mat4]

private theorem smul_mul_aux (c : R) (X Y : AuxMat4 R) :
    mul (smul_aux c X) Y = smul_aux c (mul X Y) := by
  ext <;> dsimp [mul, smul_aux] <;>
    simp only [Mat4.smul_mul_mat4, Mat4.smul_add_mat4]

private theorem physEmbed_mul (M1 M2 : Mat4 R) :
    mul (physEmbed M1) (physEmbed M2) = physEmbed (Mat4.mul M1 M2) := by
  ext <;> dsimp [mul, physEmbed] <;>
    simp only [Mat4.zero_mul_mat4, Mat4.mul_zero_mat4, Mat4.add_zero_mat4, Mat4.zero_add_mat4]

private theorem physEmbed_one : physEmbed (Mat4.one : Mat4 R) = ⟨Mat4.one, Mat4.zero, Mat4.zero, Mat4.one⟩ := by
  dsimp [physEmbed]

private theorem physEmbed_one_mul (X : AuxMat4 R) : mul (physEmbed Mat4.one) X = X := by
  ext <;> dsimp [mul, physEmbed] <;>
    simp only [Mat4.one_mul_mat4, Mat4.zero_mul_mat4, Mat4.add_zero_mat4, Mat4.zero_add_mat4]

private theorem physEmbed_smul (c : R) (M : Mat4 R) :
    physEmbed (Mat4.smul c M) = smul_aux c (physEmbed M) := by
  ext <;> dsimp [physEmbed, smul_aux, Mat4.smul, Mat4.zero] <;> ring

private theorem auxEmbed_mul (A B : Mat2 R) :
    mul (auxEmbed A) (auxEmbed B) = auxEmbed (Mat2.mul A B) := by
  dsimp [auxEmbed, mul, Mat2.mul]
  ext <;> dsimp [Mat4.mul, Mat4.add, Mat4.smul, Mat4.one, Mat4.zero] <;> ring

set_option maxHeartbeats 800000 in
private theorem physEmbed_kron01_comm_Lax02 (w2 η : R) (G1 : Mat2 R) :
    mul (physEmbed (Mat4.kron G1 Mat2.one)) (Lax02 w2 η) =
      mul (Lax02 w2 η) (physEmbed (Mat4.kron G1 Mat2.one)) := by
  dsimp [physEmbed, Lax02, mul, Mat4.kron, Mat4.mul, Mat4.add, Mat4.smul, Mat4.one, Mat4.zero,
         Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.one]
  ext <;> ring

set_option maxHeartbeats 800000 in
private theorem physEmbed_kron02_comm_Lax01 (w1 η : R) (G2 : Mat2 R) :
    mul (physEmbed (Mat4.kron Mat2.one G2)) (Lax01 w1 η) =
      mul (Lax01 w1 η) (physEmbed (Mat4.kron Mat2.one G2)) := by
  dsimp [physEmbed, Lax01, mul, Mat4.kron, Mat4.mul, Mat4.add, Mat4.smul, Mat4.one, Mat4.zero,
         Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.one]
  ext <;> ring

set_option maxHeartbeats 800000 in
private theorem auxEmbed_Lax02_auxEmbed (w2 η : R) (G2 : Mat2 R) :
    mul (mul (auxEmbed (Mat2.adj G2)) (Lax02 w2 η)) (auxEmbed G2) = physDressedLax02 w2 η G2 := by
  dsimp [auxEmbed, physDressedLax02, physEmbed, Lax02, mul, Mat2.adj,
         Mat4.kron, Mat4.mul, Mat4.add, Mat4.smul, Mat4.one, Mat4.zero,
         Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.one]
  ext <;> ring

set_option maxHeartbeats 800000 in
private theorem auxEmbed_Lax01_auxEmbed (w1 η : R) (G1 : Mat2 R) :
    mul (mul (auxEmbed (Mat2.adj G1)) (Lax01 w1 η)) (auxEmbed G1) = physDressedLax01 w1 η G1 := by
  dsimp [auxEmbed, physDressedLax01, physEmbed, Lax01, mul, Mat2.adj,
         Mat4.kron, Mat4.mul, Mat4.add, Mat4.smul, Mat4.one, Mat4.zero,
         Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.one]
  ext <;> ring

set_option maxHeartbeats 800000 in
private theorem bare_rtt (u v η : R) :
    mul (mul (R_ab (u - v) η) (Lax02 u η)) (physEmbed (Mat4.Lax v η)) =
      mul (mul (physEmbed (Mat4.Lax v η)) (Lax02 u η)) (R_ab (u - v) η) := by
  dsimp [R_ab, Lax01, Lax02, physEmbed, mul, Mat4.Lax, Mat4.P_swap,
         Mat4.kron, Mat4.mul, Mat4.add, Mat4.smul, Mat4.one, Mat4.zero,
         Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.one]
  ext <;> ring

/-- Archetypes `M₂ & M₃`: 3-factor equivariant Yang–Baxter RTT braid relation,
    2-factor cocycle telescoping, and off-diagonal tensor corner activation. -/
theorem archetype_M2_M3_braid_rtt_intertwining_and_corner_activation
    (u v θ1 θ2 η q wB wC : R) (Gr G1 G2 W : Mat2 R) :
    let T_bare := bareMonodromy u θ1 θ2 η
    let T_open := openCocycleMonodromy u θ1 θ2 η W
    let τ_open := trAux (Mat2.higgsK q wB wC) T_open
    mul (mul (R_ab (u - v) η) (gaugedLax_ar u η Gr)) (gaugedLax_br v η Gr) =
      mul (mul (gaugedLax_br v η Gr) (gaugedLax_ar u η Gr)) (R_ab (u - v) η) ∧
    mul (physDressedLax02 (u - θ2) η G2) (physDressedLax01 (u - θ1) η G1) =
      ymMonodromy u θ1 θ2 η G1 G2 ∧
    T_bare.A.m41 = 0 ∧ T_bare.B.m41 = 0 ∧ T_bare.C.m41 = 0 ∧ T_bare.D.m41 = 0 ∧
    T_bare.A.m14 = 0 ∧ T_bare.B.m14 = 0 ∧ T_bare.C.m14 = 0 ∧ T_bare.D.m14 = 0 ∧
    T_open.B.m41 = η * η * W.a21 ∧
    T_open.C.m14 = η * η * W.a12 ∧
    τ_open.m41 = wB * (η * η * W.a21) ∧
    τ_open.m14 = (q * wC) * (η * η * W.a12) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hK : Mat4.mul (Mat4.kron (Mat2.adj Gr) Mat2.one) (Mat4.kron Gr Mat2.one) =
        Mat4.smul (Mat2.det Gr) Mat4.one := by
      rw [Mat4.kron_mul_kron]
      ext <;> dsimp [Mat4.kron, Mat4.smul, Mat4.one, Mat2.mul, Mat2.adj, Mat2.det, Mat2.one] <;> ring
    have hK2 : Mat4.mul (Mat4.kron Mat2.one (Mat2.adj Gr)) (Mat4.kron Mat2.one Gr) =
        Mat4.smul (Mat2.det Gr) Mat4.one := by
      rw [Mat4.kron_mul_kron]
      ext <;> dsimp [Mat4.kron, Mat4.smul, Mat4.one, Mat2.mul, Mat2.adj, Mat2.det, Mat2.one] <;> ring
    have hR_comm1 : ∀ M : Mat2 R,
        mul (R_ab (u - v) η) (physEmbed (Mat4.kron Mat2.one M)) =
          mul (physEmbed (Mat4.kron Mat2.one M)) (R_ab (u - v) η) :=
      fun M => (physEmbed_kron02_comm_Lax01 (u - v) η M).symm
    dsimp [gaugedLax_ar, gaugedLax_br, physDressedLax02]
    calc mul (mul (R_ab (u - v) η)
                  (mul (mul (physEmbed (Mat4.kron Mat2.one Gr)) (Lax02 u η))
                       (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr)))))
             (mul (mul (physEmbed (Mat4.kron Mat2.one Gr)) (physEmbed (Mat4.Lax v η)))
                  (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr))))
        = mul (physEmbed (Mat4.kron Mat2.one Gr))
              (mul (mul (mul (R_ab (u - v) η) (Lax02 u η))
                        (mul (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr)))
                             (physEmbed (Mat4.kron Mat2.one Gr))))
                   (mul (physEmbed (Mat4.Lax v η)) (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr))))) := by
          simp only [mul_assoc_aux]
          rw [← mul_assoc_aux (R_ab _ _) (physEmbed _) _, hR_comm1]
          simp only [mul_assoc_aux]
      _ = smul_aux (Mat2.det Gr)
              (mul (physEmbed (Mat4.kron Mat2.one Gr))
                   (mul (mul (mul (R_ab (u - v) η) (Lax02 u η)) (physEmbed (Mat4.Lax v η)))
                        (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr))))) := by
          rw [physEmbed_mul, hK2, physEmbed_smul, mul_smul_aux, smul_mul_aux, mul_smul_aux]
          simp only [mul_assoc_aux, physEmbed_one_mul]
      _ = smul_aux (Mat2.det Gr)
              (mul (physEmbed (Mat4.kron Mat2.one Gr))
                   (mul (mul (mul (physEmbed (Mat4.Lax v η)) (Lax02 u η)) (R_ab (u - v) η))
                        (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr))))) := by
          rw [bare_rtt]
      _ = mul (mul (mul (mul (physEmbed (Mat4.kron Mat2.one Gr)) (physEmbed (Mat4.Lax v η)))
                       (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr))))
                   (mul (mul (physEmbed (Mat4.kron Mat2.one Gr)) (Lax02 u η))
                        (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr)))))
              (R_ab (u - v) η) := by
          symm
          calc mul (mul (mul (mul (physEmbed (Mat4.kron Mat2.one Gr)) (physEmbed (Mat4.Lax v η)))
                             (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr))))
                        (mul (mul (physEmbed (Mat4.kron Mat2.one Gr)) (Lax02 u η))
                             (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr)))))
                   (R_ab (u - v) η)
              = mul (physEmbed (Mat4.kron Mat2.one Gr))
                    (mul (physEmbed (Mat4.Lax v η))
                         (mul (mul (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr)))
                                   (physEmbed (Mat4.kron Mat2.one Gr)))
                              (mul (Lax02 u η)
                                   (mul (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr))) (R_ab (u - v) η))))) := by
                simp only [mul_assoc_aux]
            _ = smul_aux (Mat2.det Gr)
                    (mul (physEmbed (Mat4.kron Mat2.one Gr))
                         (mul (mul (mul (physEmbed (Mat4.Lax v η)) (Lax02 u η)) (R_ab (u - v) η))
                              (physEmbed (Mat4.kron Mat2.one (Mat2.adj Gr))))) := by
                rw [physEmbed_mul, hK2, physEmbed_smul, smul_mul_aux, mul_smul_aux, mul_smul_aux]
                simp only [mul_assoc_aux, physEmbed_one_mul]
                rw [← hR_comm1 (Mat2.adj Gr)]
  · dsimp [ymMonodromy, openCocycleMonodromy, Mat2.wilsonLink]
    rw [← auxEmbed_Lax02_auxEmbed (u - θ2) η G2, ← auxEmbed_Lax01_auxEmbed (u - θ1) η G1]
    simp only [mul_assoc_aux]
    rw [← mul_assoc_aux (auxEmbed G2) (auxEmbed (Mat2.adj G1)) _, auxEmbed_mul]
  all_goals
    dsimp [openCocycleMonodromy, bareMonodromy, trAux, Lax01, Lax02, auxEmbed, mul,
           Mat2.higgsK, Mat4.kron, Mat4.mul, Mat4.add, Mat4.smul, Mat4.one, Mat4.zero,
           Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.one]
    ring

set_option maxHeartbeats 800000 in
/-- Unconditional commutativity of bare 2-factor twisted partial traces. -/
theorem bare_two_factor_trace_comm (u v θ1 θ2 η : R) (K : Mat2 R) :
    Mat4.comm (trAux K (bareMonodromy u θ1 θ2 η))
              (trAux K (bareMonodromy v θ1 θ2 η)) = Mat4.zero := by
  dsimp [trAux, bareMonodromy, Lax01, Lax02, mul,
         Mat4.comm, Mat4.kron, Mat4.mul, Mat4.add, Mat4.sub, Mat4.smul,
         Mat4.one, Mat4.zero, Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.one]
  ext <;> ring

private theorem trAux_auxEmbed_conj (K G1 G2 : Mat2 R) (T : AuxMat4 R) :
    trAux K (mul (mul (auxEmbed (Mat2.adj G2)) T) (auxEmbed G1)) =
      trAux (Mat2.mul (Mat2.mul G1 K) (Mat2.adj G2)) T := by
  dsimp [trAux, auxEmbed, mul, Mat2.mul, Mat2.adj]
  simp only [Mat4.smul_mul_mat4, Mat4.mul_smul_mat4, Mat4.one_mul_mat4, Mat4.mul_one_mat4,
             Mat4.smul_add_mat4, Mat4.smul_smul_mat4]
  ext <;> dsimp [Mat4.add, Mat4.smul] <;> ring

private theorem trAux_physEmbed_conj (K : Mat2 R) (M1 M2 : Mat4 R) (T : AuxMat4 R) :
    trAux K (mul (mul (physEmbed M1) T) (physEmbed M2)) =
      Mat4.mul (Mat4.mul M1 (trAux K T)) M2 := by
  dsimp [trAux, physEmbed, mul]
  simp only [Mat4.zero_mul_mat4, Mat4.mul_zero_mat4, Mat4.add_zero_mat4, Mat4.zero_add_mat4,
             Mat4.mul_add_mat4, Mat4.add_mul_mat4, Mat4.mul_smul_mat4, Mat4.smul_mul_mat4]

private theorem ymMonodromy_eq_physEmbed_conj (u θ1 θ2 η : R) (G1 G2 : Mat2 R) :
    ymMonodromy u θ1 θ2 η G1 G2 =
      mul (mul (physEmbed (Mat4.kron G1 G2)) (bareMonodromy u θ1 θ2 η))
          (physEmbed (Mat4.kron (Mat2.adj G1) (Mat2.adj G2))) := by
  have h1 : ymMonodromy u θ1 θ2 η G1 G2 =
      mul (physDressedLax02 (u - θ2) η G2) (physDressedLax01 (u - θ1) η G1) := by
    dsimp [ymMonodromy, openCocycleMonodromy, Mat2.wilsonLink]
    rw [← auxEmbed_Lax02_auxEmbed (u - θ2) η G2, ← auxEmbed_Lax01_auxEmbed (u - θ1) η G1]
    simp only [mul_assoc_aux]
    rw [← mul_assoc_aux (auxEmbed G2) (auxEmbed (Mat2.adj G1)) _, auxEmbed_mul]
  rw [h1]
  dsimp [physDressedLax02, physDressedLax01, bareMonodromy]
  have h1m : ∀ A : Mat2 R, Mat2.mul Mat2.one A = A := by
    intro A; ext <;> dsimp [Mat2.mul, Mat2.one] <;> ring
  have hm1 : ∀ A : Mat2 R, Mat2.mul A Mat2.one = A := by
    intro A; ext <;> dsimp [Mat2.mul, Mat2.one] <;> ring
  have hc1 : ∀ A : Mat2 R, mul (physEmbed (Mat4.kron Mat2.one A)) (physEmbed (Mat4.kron G1 Mat2.one)) =
      physEmbed (Mat4.kron G1 A) := by
    intro A; rw [physEmbed_mul, Mat4.kron_mul_kron, h1m, hm1]
  have hc2 : ∀ A : Mat2 R, mul (physEmbed (Mat4.kron Mat2.one A)) (physEmbed (Mat4.kron (Mat2.adj G1) Mat2.one)) =
      physEmbed (Mat4.kron (Mat2.adj G1) A) := by
    intro A; rw [physEmbed_mul, Mat4.kron_mul_kron, h1m, hm1]
  calc mul (mul (mul (physEmbed (Mat4.kron Mat2.one G2)) (Lax02 (u - θ2) η))
                (physEmbed (Mat4.kron Mat2.one (Mat2.adj G2))))
           (mul (mul (physEmbed (Mat4.kron G1 Mat2.one)) (Lax01 (u - θ1) η))
                (physEmbed (Mat4.kron (Mat2.adj G1) Mat2.one)))
      = mul (physEmbed (Mat4.kron Mat2.one G2))
            (mul (mul (Lax02 (u - θ2) η) (physEmbed (Mat4.kron G1 Mat2.one)))
                 (mul (mul (physEmbed (Mat4.kron Mat2.one (Mat2.adj G2))) (Lax01 (u - θ1) η))
                      (physEmbed (Mat4.kron (Mat2.adj G1) Mat2.one)))) := by
        simp only [mul_assoc_aux]
        rw [← mul_assoc_aux (physEmbed (Mat4.kron Mat2.one (Mat2.adj G2))) (physEmbed (Mat4.kron G1 Mat2.one)) _,
            ← mul_assoc_aux (physEmbed (Mat4.kron G1 Mat2.one)) (physEmbed (Mat4.kron Mat2.one (Mat2.adj G2))) _]
        have hcomm : mul (physEmbed (Mat4.kron Mat2.one (Mat2.adj G2))) (physEmbed (Mat4.kron G1 Mat2.one)) =
            mul (physEmbed (Mat4.kron G1 Mat2.one)) (physEmbed (Mat4.kron Mat2.one (Mat2.adj G2))) := by
          rw [physEmbed_mul, physEmbed_mul, Mat4.kron_mul_kron, Mat4.kron_mul_kron]
          simp only [h1m, hm1]
        rw [hcomm]
    _ = mul (mul (physEmbed (Mat4.kron G1 G2)) (mul (Lax02 (u - θ2) η) (Lax01 (u - θ1) η)))
            (physEmbed (Mat4.kron (Mat2.adj G1) (Mat2.adj G2))) := by
        rw [← physEmbed_kron01_comm_Lax02 (u - θ2) η G1,
            physEmbed_kron02_comm_Lax01 (u - θ1) η (Mat2.adj G2)]
        simp only [← mul_assoc_aux]
        rw [hc1 G2]
        simp only [mul_assoc_aux]
        rw [hc2 (Mat2.adj G2)]

/-- Intertwining of the gauged partial trace with Kronecker conjugation `G₁ ⊗ G₂`. -/
theorem gauged_trace_eq_kron_conj (u θ1 θ2 η : R) (K G1 G2 : Mat2 R) :
    trAux K (ymMonodromy u θ1 θ2 η G1 G2) =
      Mat4.mul (Mat4.mul (Mat4.kron G1 G2) (trAux K (bareMonodromy u θ1 θ2 η)))
               (Mat4.kron (Mat2.adj G1) (Mat2.adj G2)) := by
  rw [ymMonodromy_eq_physEmbed_conj, trAux_physEmbed_conj]

set_option maxHeartbeats 1200000 in
/-- Stage `A₁₁` & Archetypes `M₄–M₅`: parametric Kähler–Bergman quantum determinant collapse,
    open-cocycle seam equivalence, and unconditional 2-site gauged transfer commutativity. -/
theorem stage_A11_parametric_kahler_bergman_quantum_determinant_and_2site_commutativity
    (u v θ1 θ2 η : R) (K G1 G2 : Mat2 R) :
    let bergmanEta := ((u - θ1) * (u - θ1) - η * η) * ((u - θ2) * (u - θ2) - η * η)
    let K_seam     := Mat2.mul (Mat2.mul G1 K) (Mat2.adj G2)
    let τ_open_u   := trAux K_seam (openCocycleMonodromy u θ1 θ2 η (Mat2.wilsonLink G2 G1))
    let τ_ym_u     := trAux K (ymMonodromy u θ1 θ2 η G1 G2)
    let τ_ym_v     := trAux K (ymMonodromy v θ1 θ2 η G1 G2)
    quantumDet (bareMonodromy u θ1 θ2 η) (bareMonodromy (u - η) θ1 θ2 η) =
      Mat4.smul bergmanEta Mat4.one ∧
    τ_open_u = τ_ym_u ∧
    Mat4.comm τ_ym_u τ_ym_v = Mat4.zero := by
  intro bergmanEta K_seam τ_open_u τ_ym_u τ_ym_v
  refine ⟨?_, ?_, ?_⟩
  · ext <;> dsimp [quantumDet, bareMonodromy, Lax01, Lax02, mul,
                   Mat4.kron, Mat4.mul, Mat4.add, Mat4.sub, Mat4.smul,
                   Mat4.one, Mat2.E00, Mat2.E01, Mat2.E10, Mat2.E11, Mat2.one] <;> ring
  · dsimp [τ_open_u, τ_ym_u, K_seam, ymMonodromy]
    rw [trAux_auxEmbed_conj]
  · dsimp [τ_ym_u, τ_ym_v]
    rw [gauged_trace_eq_kron_conj u θ1 θ2 η K G1 G2,
        gauged_trace_eq_kron_conj v θ1 θ2 η K G1 G2,
        Mat4.kron_conj_comm G1 G2
          (trAux K (bareMonodromy u θ1 θ2 η))
          (trAux K (bareMonodromy v θ1 θ2 η)),
        bare_two_factor_trace_comm u v θ1 θ2 η K]
    ext <;> dsimp [Mat4.mul, Mat4.smul, Mat4.zero] <;> ring

end Ops
end AuxMat4
end InfoGeometry.Algebra.ConnesLottYangBaxterPoset
