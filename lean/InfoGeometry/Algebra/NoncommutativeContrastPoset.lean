/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives

/-!
# Noncommutative Contrast Poset & Inductive Bott–Clifford Tower / CFT Proposition 22

This module formalizes the repaired contrast poset (`CM₁`–`CM₅`) together with the
inductive Bott–Clifford tower parabolic monodromy (`CM₆`) and the noncommutative proof of
Córdova–Freed–Teleman Proposition 22 and Page 6 gerbe flatness (`CM₇`) over arbitrary
noncommutative rings `[Ring B]`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives

namespace InfoGeometry.Algebra.NoncommutativeContrastPoset

/-!
## $\mathcal{C}\mathcal{M}_1$: Non-Abelian Wilson 1-Cocycle vs. Central Braiding Collapse
-/

section CM1_WilsonCocycle

/-- Path-ordered Wilson 1-cocycle $\mathcal{W}_X^{(n)}(Q)$ in an arbitrary noncommutative ring $B$. -/
def wilsonCocycle {B : Type*} [Ring B] (X Xinv Q : B) : ℕ → B
  | 0     => 1
  | n + 1 => Q * (X * wilsonCocycle X Xinv Q n * Xinv)

/-- **Central Braiding Collapse**: If $Q$ commutes with $X$ and $X X_{\mathrm{inv}} = 1$,
$\mathcal{W}_X^{(n)}(Q)$ collapses to the naive power $Q^n$. -/
theorem cm1_central_braiding_collapse {B : Type*} [Ring B] (X Xinv Q : B)
    (h_inv : X * Xinv = 1) (h_comm : Q * X = X * Q) :
    ∀ n : ℕ, wilsonCocycle X Xinv Q n = Q ^ n
  | 0     => by simp [wilsonCocycle]
  | n + 1 => by
      simp only [wilsonCocycle, cm1_central_braiding_collapse X Xinv Q h_inv h_comm n]
      have h_comm_pow : Q ^ n * X = X * Q ^ n := by
        induction' n with k ih
        · simp
        · calc Q ^ (k + 1) * X = Q * (Q ^ k * X) := by rw [pow_succ', mul_assoc]
            _ = Q * (X * Q ^ k) := by rw [ih]
            _ = (Q * X) * Q ^ k := by rw [← mul_assoc]
            _ = (X * Q) * Q ^ k := by rw [h_comm]
            _ = X * Q ^ (k + 1) := by rw [mul_assoc, ← pow_succ']
      calc Q * (X * Q ^ n * Xinv)
          = Q * ((Q ^ n * X) * Xinv) := by rw [h_comm_pow]
        _ = Q * (Q ^ n * (X * Xinv)) := by rw [mul_assoc]
        _ = Q * Q ^ n := by rw [h_inv, mul_one]
        _ = Q ^ (n + 1) := by rw [← pow_succ']

/-- The canonical $Cl(1,1)$ light-cone nilpotent generator $N_{\mathrm{par}} = \Omega - \Gamma_1 = \bigl(\begin{smallmatrix} -1 & -1 \\ 1 & 1 \end{smallmatrix}\bigr)$
and unipotent parabolic holonomy $Q_{\mathrm{par}} = 1 + N_{\mathrm{par}} = \bigl(\begin{smallmatrix} 0 & -1 \\ 1 & 2 \end{smallmatrix}\bigr)$. -/
def N_par {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B := mat2 (-1) (-1) 1 1
def Q_par {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B := mat2 0 (-1) 1 2

theorem cm1_sigmaOp_involution {B : Type*} [Ring B] :
    (sigmaOp : Matrix (Fin 2) (Fin 2) B) * sigmaOp = 1 := by
  apply ext_fin2 <;> simp [sigmaOp]

theorem cm1_N_par_nilpotent_and_anticomm {B : Type*} [Ring B] :
    (N_par : Matrix (Fin 2) (Fin 2) B) = omegaOp - gamma1Op ∧
    (N_par : Matrix (Fin 2) (Fin 2) B) * N_par = 0 ∧
    (sigmaOp : Matrix (Fin 2) (Fin 2) B) * N_par * sigmaOp = -N_par := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;> simp [N_par, omegaOp, gamma1Op, sigmaOp])

theorem cm1_Q_par_pow {B : Type*} [Ring B] (n : ℕ) :
    (Q_par : Matrix (Fin 2) (Fin 2) B) ^ n = 1 + n • N_par := by
  have hQ : (Q_par : Matrix (Fin 2) (Fin 2) B) = 1 + N_par := by
    apply ext_fin2 <;> simp [Q_par, N_par]
    norm_num
  have hN2 : (N_par : Matrix (Fin 2) (Fin 2) B) * N_par = 0 :=
    cm1_N_par_nilpotent_and_anticomm.2.1
  induction' n with k ih
  · simp
  · rw [pow_succ, ih, hQ, add_nsmul, one_nsmul]
    have h_mul : (k • (N_par : Matrix (Fin 2) (Fin 2) B)) * N_par = 0 := by
      rw [nsmul_eq_mul, mul_assoc, hN2, mul_zero]
    calc (1 + k • (N_par : Matrix (Fin 2) (Fin 2) B)) * (1 + N_par)
      _ = 1 + (k • N_par + N_par) + (k • N_par) * N_par := by noncomm_ring
      _ = 1 + (k • N_par + N_par) := by rw [h_mul, add_zero]

/-- **Repaired 2-Cocycle Closure**: Because $\Sigma N_{\mathrm{par}} \Sigma = -N_{\mathrm{par}}$ and
$N_{\mathrm{par}}^2 = 0$, the Wilson 1-cocycle $\mathcal{W}_\Sigma^{(2)}(Q_{\mathrm{par}})$ closes to $1$
over every noncommutative ring $B$, even though $Q_{\mathrm{par}}^n = 1 + n \bullet N_{\mathrm{par}}$. -/
theorem cm1_nonabelian_wilson_closes_at_two {B : Type*} [Ring B] :
    wilsonCocycle (sigmaOp : Matrix (Fin 2) (Fin 2) B) sigmaOp Q_par 2 = 1 := by
  dsimp [wilsonCocycle]
  apply ext_fin2 <;> simp [sigmaOp, Q_par]

end CM1_WilsonCocycle

/-!
## $\mathcal{C}\mathcal{M}_2$: Fractal Uncertainty Principle (FUP) & Pore Leakage Variance
-/

section CM2_FractalUncertainty

def toeplitzOp {B : Type*} [Ring B] (P Q : B) : B := P * Q * P

theorem cm2_commuting_projection_triviality {B : Type*} [Ring B] (P Q : B)
    (hP : P * P = P) (hQ : Q * Q = Q) (h_comm : P * Q = Q * P) :
    toeplitzOp P Q - toeplitzOp P Q * toeplitzOp P Q = 0 := by
  dsimp [toeplitzOp]
  have h_idem : P * Q * P * (P * Q * P) = P * Q * P := by
    calc P * Q * P * (P * Q * P)
        = P * Q * (P * P) * Q * P := by noncomm_ring
      _ = P * Q * (P * Q) * P := by rw [hP]; noncomm_ring
      _ = P * Q * (Q * P) * P := by nth_rw 2 [h_comm]
      _ = P * (Q * Q) * (P * P) := by noncomm_ring
      _ = P * Q * P := by rw [hQ, hP]
  rw [h_idem, sub_self]

def P_plus {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 0
def Q_had  {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B := mat2 1 1 1 1

theorem cm2_noncomm_fup_variance {B : Type*} [Ring B] :
    2 • toeplitzOp (P_plus : Matrix (Fin 2) (Fin 2) B) Q_had -
    toeplitzOp P_plus Q_had * toeplitzOp P_plus Q_had = P_plus := by
  apply ext_fin2 <;> simp [toeplitzOp, P_plus, Q_had, two_smul]

end CM2_FractalUncertainty

/-!
## $\mathcal{C}\mathcal{M}_3$: Quaternion Braid Curvature vs. Abelian Collapse
-/

section CM3_BraidCurvature

def constCurvature {B : Type*} [Ring B] (A₁ A₂ : B) : B := A₁ * A₂ - A₂ * A₁

theorem cm3_abelian_curvature_collapse {B : Type*} [Ring B] (A₁ A₂ : B)
    (h_comm : A₁ * A₂ = A₂ * A₁) :
    constCurvature A₁ A₂ = 0 := by
  dsimp [constCurvature]; rw [h_comm, sub_self]

abbrev M2Z := Matrix (Fin 2) (Fin 2) ℤ
abbrev M4Z := Matrix (Fin 2) (Fin 2) M2Z

def I₂ : M2Z := mat2 1 0 0 1
def Z₂ : M2Z := mat2 1 0 0 (-1)
def X₂ : M2Z := mat2 0 1 1 0
def J₂ : M2Z := mat2 0 (-1) 1 0

def E₁ : M4Z := mat2 0 Z₂ (-Z₂) 0
def E₂ : M4Z := mat2 0 X₂ (-X₂) 0
def E₃ : M4Z := mat2 J₂ 0 0 J₂

theorem cm3_quaternion_braid_curvature :
    constCurvature E₁ E₂ = 2 • E₃ := by
  decide

end CM3_BraidCurvature

/-!
## $\mathcal{C}\mathcal{M}_4$: Noncommutative Cayley–Hamilton Obstruction ($\mathfrak{sl}_2$ Lie Cross-Product)
-/

section CM4_NoncommCayleyHamilton

/-- **Repaired Noncommutative Cayley–Hamilton Obstruction**:
For $M = \bigl(\begin{smallmatrix} a & b \\ c & -a \end{smallmatrix}\bigr)$ over any noncommutative `[Ring B]`,
$M^2 = (a^2 + b c) I_2 + \bigl(\begin{smallmatrix} 0 & \⁅a, b⁆ \\ \⁅c, a⁆ & \⁅c, b⁆ \end{smallmatrix}\bigr)$. -/
theorem cm4_noncomm_cayley_hamilton_obstruction {B : Type*} [Ring B] (a b c : B) :
    let M : Matrix (Fin 2) (Fin 2) B := mat2 a b c (-a)
    M * M = mat2 (a * a + b * c) 0 0 (a * a + b * c) +
            mat2 0 ⁅a, b⁆ ⁅c, a⁆ ⁅c, b⁆ := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp <;> first | noncomm_ring | abel

end CM4_NoncommCayleyHamilton

/-!
## $\mathcal{C}\mathcal{M}_5$: The Córdova–Freed–Teleman Dichotomy in $M_2(M_2(\mathbb{Z}))$
-/

section CM5_CFTDichotomy

def A_torsion : M4Z := mat2 0 (-I₂) I₂ 0
def X_witt_4  : M4Z := mat2 0 (1 - F_plus) (1 + F_plus) 0
def Q_par_4   : M4Z := mat2 Q_par 0 0 Q_par

theorem cm5_orthogonal_torsion_orthogonal :
    A_torsionᵀ * A_torsion = 1 := by
  apply ext_fin2 <;> apply ext_fin2 <;> simp [A_torsion, I₂]

theorem cm5_orthogonal_torsion_order_four :
    A_torsion ^ 2 = -1 ∧ A_torsion ^ 4 = 1 := by
  have h2 : A_torsion ^ 2 = -1 := by
    rw [sq]
    apply ext_fin2 <;> apply ext_fin2 <;> simp [A_torsion, I₂]
  refine ⟨h2, ?_⟩
  calc A_torsion ^ 4
    _ = (A_torsion ^ 2) * (A_torsion ^ 2) := by noncomm_ring
    _ = (-1) * (-1) := by rw [h2]
    _ = 1 := by noncomm_ring

theorem cm5_nonorthogonal_witt_infinite_order (n : ℕ) (hn : 1 ≤ n) :
    X_witt_4ᵀ * X_witt_4 ≠ 1 ∧ (Q_par_4 : M4Z) ^ n ≠ 1 := by
  refine ⟨by decide, ?_⟩
  have h_pow : ∀ k : ℕ, (Q_par_4 : M4Z) ^ k =
      mat2 (Q_par ^ k) 0 0 (Q_par ^ k) := by
    intro k; induction' k with k ih
    · apply ext_fin2 <;> apply ext_fin2 <;> rfl
    · rw [pow_succ, ih, pow_succ]
      apply ext_fin2 <;> simp [Q_par_4]
  intro h_eq
  have h_entry : (((Q_par_4 : M4Z) ^ n) 0 0) 1 0 = ((1 : M4Z) 0 0) 1 0 := by rw [h_eq]
  rw [h_pow n, cm1_Q_par_pow n, mat2_00] at h_entry
  rw [Matrix.add_apply, Matrix.smul_apply, one2_10, zero_add] at h_entry
  dsimp [N_par] at h_entry
  omega

end CM5_CFTDichotomy

/-!
## $\mathcal{C}\mathcal{M}_6$: Inductive Bott–Clifford Tower Lifting of the Parabolic Monodromy (`ClTower n B`)
-/

section CM6_InductiveTowerParabolicColimit

universe u

variable {B : Type u} [Ring B]

/-- Inductive tower lift of the shift involution $\Sigma^{(n)} \in \mathcal{C}\ell_{n+1}(B)$. -/
def sigmaTower : ∀ n : ℕ, ClTower B (n + 1)
  | 0     => sigmaOp
  | n + 1 => mat2 (sigmaTower n) 0 0 (sigmaTower n)

/-- Inductive tower lift of the light-cone nilpotent generator $N_{\mathrm{par}}^{(n)} \in \mathcal{C}\ell_{n+1}(B)$. -/
def nilpotentTower : ∀ n : ℕ, ClTower B (n + 1)
  | 0     => N_par
  | n + 1 => mat2 (nilpotentTower n) 0 0 (nilpotentTower n)

/-- Inductive tower parabolic monodromy $Q_{\mathrm{par}}^{(n)} = 1 + N_{\mathrm{par}}^{(n)} \in \mathcal{C}\ell_{n+1}(B)$. -/
def monodromyTower (n : ℕ) : ClTower B (n + 1) :=
  1 + nilpotentTower n

/-- Top-left corner projection functor $\pi_{00}^{(n)} : \mathcal{C}\ell_{n+1}(B) \to M_2(B)$. -/
def corner00 : ∀ n : ℕ, ClTower B (n + 1) → Matrix (Fin 2) (Fin 2) B
  | 0, M     => M
  | n + 1, M => corner00 n (M 0 0)

theorem nilpotentTower_sq : ∀ n : ℕ,
    (nilpotentTower n : ClTower B (n + 1)) * nilpotentTower n = 0
  | 0     => cm1_N_par_nilpotent_and_anticomm.2.1
  | n + 1 => by apply ext_fin2 <;> simp [nilpotentTower, nilpotentTower_sq n]

theorem sigmaTower_sq : ∀ n : ℕ,
    (sigmaTower n : ClTower B (n + 1)) * sigmaTower n = 1
  | 0     => cm1_sigmaOp_involution
  | n + 1 => by apply ext_fin2 <;> simp [sigmaTower, sigmaTower_sq n]

theorem sigmaTower_conj_nilpotent : ∀ n : ℕ,
    (sigmaTower n : ClTower B (n + 1)) * nilpotentTower n * sigmaTower n = -nilpotentTower n
  | 0     => cm1_N_par_nilpotent_and_anticomm.2.2
  | n + 1 => by apply ext_fin2 <;> simp [sigmaTower, nilpotentTower, sigmaTower_conj_nilpotent n]

theorem corner00_one_add_nsmul_nilpotent : ∀ (n k : ℕ),
    corner00 n ((1 : ClTower B (n + 1)) + k • nilpotentTower n) =
      1 + k • N_par
  | 0, _     => rfl
  | n + 1, k => by
      dsimp [corner00, nilpotentTower]
      exact corner00_one_add_nsmul_nilpotent n k

/-- **All-Scales Inductive Bott–Clifford Tower Parabolic Monodromy Theorem ($\mathcal{C}\mathcal{M}_6$)**:
At every level $n \in \mathbb{N}$ of the inductive tower $\mathcal{C}\ell_{n+1}(B)$:
1. $\mathcal{W}_{\Sigma^{(n)}}^{(2)}(Q_{\mathrm{par}}^{(n)}) = 1$ (2-step Wilson cocycle closure),
2. $(Q_{\mathrm{par}}^{(n)})^k = 1 + k \bullet N_{\mathrm{par}}^{(n)}$ for all $k \in \mathbb{N}$,
3. Over any `[CharZero B]`, $(Q_{\mathrm{par}}^{(n)})^k \neq 1$ for all $k > 0$. -/
theorem all_scales_tower_parabolic_monodromy [CharZero B] (n k : ℕ) (hk : 0 < k) :
    wilsonCocycle
      (sigmaTower n : ClTower B (n + 1)) (sigmaTower n) (monodromyTower n) 2 = 1 ∧
    (monodromyTower n : ClTower B (n + 1)) ^ k = 1 + k • nilpotentTower n ∧
    (monodromyTower n : ClTower B (n + 1)) ^ k ≠ 1 := by
  have hPow : ∀ m : ℕ, (monodromyTower n : ClTower B (n + 1)) ^ m = 1 + m • nilpotentTower n := by
    intro m; induction' m with m ih
    · simp
    · rw [pow_succ, ih, monodromyTower, add_nsmul, one_nsmul]
      have h_mul : (m • (nilpotentTower n : ClTower B (n + 1))) * nilpotentTower n = 0 := by
        rw [nsmul_eq_mul, mul_assoc, nilpotentTower_sq n, mul_zero]
      calc (1 + m • (nilpotentTower n : ClTower B (n + 1))) * (1 + nilpotentTower n)
        _ = 1 + (m • nilpotentTower n + nilpotentTower n) +
            (m • nilpotentTower n) * nilpotentTower n := by noncomm_ring
        _ = 1 + (m • nilpotentTower n + nilpotentTower n) := by rw [h_mul, add_zero]
  refine ⟨?_, hPow k, ?_⟩
  · dsimp [wilsonCocycle, monodromyTower]
    calc (1 + (nilpotentTower n : ClTower B (n + 1))) *
          (sigmaTower n * ((1 + nilpotentTower n) * (sigmaTower n * 1 * sigmaTower n)) * sigmaTower n)
      _ = (1 + nilpotentTower n) *
          (sigmaTower n * ((1 + nilpotentTower n) * 1) * sigmaTower n) := by
          rw [mul_one, sigmaTower_sq n]
      _ = (1 + nilpotentTower n) *
          (sigmaTower n * sigmaTower n + sigmaTower n * nilpotentTower n * sigmaTower n) := by
          noncomm_ring
      _ = (1 + nilpotentTower n) * (1 + -nilpotentTower n) := by
          rw [sigmaTower_sq n, sigmaTower_conj_nilpotent n]
      _ = 1 - nilpotentTower n * nilpotentTower n := by noncomm_ring
      _ = 1 := by rw [nilpotentTower_sq n, sub_zero]
  · intro h_eq
    have h_c : (corner00 n ((monodromyTower n : ClTower B (n + 1)) ^ k)) 1 0 =
               (corner00 n (1 : ClTower B (n + 1))) 1 0 := by rw [h_eq]
    rw [hPow k, corner00_one_add_nsmul_nilpotent n k] at h_c
    have h_zero_corner : ∀ m : ℕ, (corner00 m (1 : ClTower B (m + 1))) 1 0 = 0 := by
      intro m; induction' m with m ih
      · rfl
      · exact ih
    rw [h_zero_corner n] at h_c
    rw [Matrix.add_apply, Matrix.smul_apply, one2_10, zero_add] at h_c
    dsimp [N_par] at h_c
    rw [nsmul_one] at h_c
    exact Nat.ne_of_gt hk (Nat.cast_eq_zero.mp h_c)

end CM6_InductiveTowerParabolicColimit

/-!
## $\mathcal{C}\mathcal{M}_7$: Córdova–Freed–Teleman Proposition 22 (`r • B_gerbe = -Tr_r(F(A))`) & Page 6 Gerbe Flatness over `[Ring B]`
-/

section CM7_CordovaFreedTelemanProposition22

variable {B : Type*} [Ring B]

def IsRingDeriv (d : B →+ B) : Prop :=
  ∀ a b : B, d (a * b) = d a * b + a * d b

def liftMatrixDeriv {r : ℕ} (d : B →+ B) :
    Matrix (Fin r) (Fin r) B →+ Matrix (Fin r) (Fin r) B where
  toFun M := Matrix.of fun i j => d (M i j)
  map_zero' := by ext i j; simp
  map_add' M N := by ext i j; simp

def mcCurvature {R : Type*} [Ring R] (d₁ d₂ : R →+ R) (A₁ A₂ : R) : R :=
  d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆

def adjDeriv {R : Type*} [Ring R] (d : R →+ R) (A X : R) : R :=
  d X + ⁅A, X⁆

def gerbeEmbed (r : ℕ) (b : B) : Matrix (Fin r) (Fin r) B :=
  Matrix.of (fun i j => if i = j then b else 0)

def ncTrace {r : ℕ} (M : Matrix (Fin r) (Fin r) B) : B :=
  ∑ i : Fin r, M i i

def twistedBundleCurvature {r : ℕ}
    (d₁ d₂ : B →+ B) (A₁ A₂ : Matrix (Fin r) (Fin r) B) (B_gerbe : B) :
    Matrix (Fin r) (Fin r) B :=
  mcCurvature (liftMatrixDeriv d₁) (liftMatrixDeriv d₂) A₁ A₂ + gerbeEmbed r B_gerbe

theorem ncTrace_gerbeEmbed (r : ℕ) (b : B) :
    ncTrace (gerbeEmbed r b) = r • b := by
  dsimp [ncTrace, gerbeEmbed]; simp [Finset.sum_const]

/-- **Proposition 22 & Page 6 Theorem of Córdova–Freed–Teleman (`arXiv:2408.15148`) over `[Ring B]` ($\mathcal{C}\mathcal{M}_7$)**:
1. *Proposition 22*: If a rank-$r$ twisted bundle is projectively flat ($\Omega_E = 0$), then
   $r \bullet B_{\mathrm{gerbe}} = -\big(d_1(\mathrm{Tr}_r A_2) - d_2(\mathrm{Tr}_r A_1) + \mathrm{Tr}_r\⁅A_1, A_2⁆\big)$.
2. *Page 6 Bianchi Reduction*: If $F_{ij} + B_{ij} = 0$ with central curving $\⁅A_k, B_{ij}⁆ = 0$
   under commuting derivations $d_1, d_2, d_3$, then $d_1 B_{23} + d_2 B_{31} + d_3 B_{12} = 0$. -/
theorem cordova_freed_teleman_proposition22_and_gerbe_flatness
    {r : ℕ} {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁_mat A₂_mat : Matrix (Fin r) (Fin r) B) (B_gerbe : B)
    (h_flat : twistedBundleCurvature d₁ d₂ A₁_mat A₂_mat B_gerbe = 0)
    {A₁ A₂ A₃ B₂₃ B₃₁ B₁₂ : B}
    (h_flat₂₃ : mcCurvature d₂ d₃ A₂ A₃ + B₂₃ = 0)
    (h_flat₃₁ : mcCurvature d₃ d₁ A₃ A₁ + B₃₁ = 0)
    (h_flat₁₂ : mcCurvature d₁ d₂ A₁ A₂ + B₁₂ = 0)
    (h_comm₁ : ⁅A₁, B₂₃⁆ = 0) (h_comm₂ : ⁅A₂, B₃₁⁆ = 0) (h_comm₃ : ⁅A₃, B₁₂⁆ = 0) :
    r • B_gerbe = -(d₁ (ncTrace A₂_mat) - d₂ (ncTrace A₁_mat) + ncTrace ⁅A₁_mat, A₂_mat⁆) ∧
    d₁ B₂₃ + d₂ B₃₁ + d₃ B₁₂ = 0 := by
  refine ⟨?_, ?_⟩
  · have h_tr : ncTrace (twistedBundleCurvature d₁ d₂ A₁_mat A₂_mat B_gerbe) = 0 := by
      rw [h_flat]; dsimp [ncTrace]; simp
    have h_decomp : ncTrace (twistedBundleCurvature d₁ d₂ A₁_mat A₂_mat B_gerbe) =
        (d₁ (ncTrace A₂_mat) - d₂ (ncTrace A₁_mat) + ncTrace ⁅A₁_mat, A₂_mat⁆) + r • B_gerbe := by
      dsimp [twistedBundleCurvature, mcCurvature, ncTrace, liftMatrixDeriv]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, map_sum,
        ← ncTrace_gerbeEmbed r B_gerbe]
      rfl
    rw [h_decomp] at h_tr
    exact eq_neg_of_add_eq_zero_right h_tr
  · have h_bianchi :
        adjDeriv d₁ A₁ (mcCurvature d₂ d₃ A₂ A₃) +
        adjDeriv d₂ A₂ (mcCurvature d₃ d₁ A₃ A₁) +
        adjDeriv d₃ A₃ (mcCurvature d₁ d₂ A₁ A₂) = 0 := by
      dsimp [adjDeriv, mcCurvature]
      simp only [Ring.lie_def, map_add, map_sub]
      rw [hd₁ A₂ A₃, hd₁ A₃ A₂, hd₂ A₃ A₁, hd₂ A₁ A₃, hd₃ A₁ A₂, hd₃ A₂ A₁,
          h12 A₃, h23 A₁, h13 A₂]
      noncomm_ring
    have hF₂₃ : mcCurvature d₂ d₃ A₂ A₃ = -B₂₃ := eq_neg_of_add_eq_zero_left h_flat₂₃
    have hF₃₁ : mcCurvature d₃ d₁ A₃ A₁ = -B₃₁ := eq_neg_of_add_eq_zero_left h_flat₃₁
    have hF₁₂ : mcCurvature d₁ d₂ A₁ A₂ = -B₁₂ := eq_neg_of_add_eq_zero_left h_flat₁₂
    rw [hF₂₃, hF₃₁, hF₁₂] at h_bianchi
    dsimp [adjDeriv] at h_bianchi
    simp only [map_neg] at h_bianchi
    have hc₁ : ⁅A₁, -B₂₃⁆ = 0 := by
      rw [Ring.lie_def] at h_comm₁ ⊢
      have h : A₁ * B₂₃ = B₂₃ * A₁ := sub_eq_zero.mp h_comm₁
      rw [mul_neg, neg_mul, h, sub_self]
    have hc₂ : ⁅A₂, -B₃₁⁆ = 0 := by
      rw [Ring.lie_def] at h_comm₂ ⊢
      have h : A₂ * B₃₁ = B₃₁ * A₂ := sub_eq_zero.mp h_comm₂
      rw [mul_neg, neg_mul, h, sub_self]
    have hc₃ : ⁅A₃, -B₁₂⁆ = 0 := by
      rw [Ring.lie_def] at h_comm₃ ⊢
      have h : A₃ * B₁₂ = B₁₂ * A₃ := sub_eq_zero.mp h_comm₃
      rw [mul_neg, neg_mul, h, sub_self]
    rw [hc₁, hc₂, hc₃, add_zero, add_zero, add_zero] at h_bianchi
    calc d₁ B₂₃ + d₂ B₃₁ + d₃ B₁₂
      _ = -(-d₁ B₂₃ + -d₂ B₃₁ + -d₃ B₁₂) := by abel
      _ = -0 := by rw [h_bianchi]
      _ = 0 := neg_zero

end CM7_CordovaFreedTelemanProposition22

end InfoGeometry.Algebra.NoncommutativeContrastPoset
