/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Two-Sheeted Dirac–Connes–Higgs Mechanism & All-Scales Mass-Square Summability

Epistemic compilation of `TwoSheetDiracMassEntropy` ($\mathcal{D}\mathcal{H}_1$–$\mathcal{D}\mathcal{H}_4$)
over arbitrary noncommutative rings `[Ring B]` and `[StarRing B]`:
1. $\mathcal{D}\mathcal{H}_1$: Discrete two-sheet commutator $\⁅\mathcal{D}, e_L⁆$ and the exact
   non-central Lichnerowicz–Higgs square identity without assuming $\⁅D, m⁆ = 0$.
2. $\mathcal{D}\mathcal{H}_2$: Connes–Chamseddine inner fluctuations with bimodule covariant
   derivative $\nabla_{L,R}(H)$ and 4-term $\star$-positive quartic trace decomposition.
3. $\mathcal{D}\mathcal{H}_3$–$\mathcal{D}\mathcal{H}_4$: Inductive propagation of
   $\{\mathcal{D}_N, \Gamma^{(N)}\} = 0$, $(\Gamma^{(N)})^2 = 1$, and additive mass-square
   summability $\mathcal{D}_N^2 = \iota_{\mathrm{diag}}^{(N)}(D_0^2 + \sum_{k<N} m_k^2)$ across
   `ClTower B N`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives

namespace InfoGeometry.Algebra.TwoSheetDiracMassEntropy

section Matrix2Trace

variable {A : Type*} [Ring A]

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

end Matrix2Trace

/-!
## Archetype $\mathcal{D}\mathcal{H}_1$: Mass as the Two-Sheet Commutator & The Non-Central Lichnerowicz–Higgs Identity
-/

section ArchetypeDH1_TwoSheetCommutatorAndLichnerowicz

variable {B : Type*} [Ring B]

/-- Left chiral sheet projection $e_L = \mathrm{diag}(1, 0)$. -/
def sheetLeft : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 0

/-- General two-sheeted operator $\mathcal{D} = \bigl(\begin{smallmatrix} D_L & M_L \\ M_R & D_R \end{smallmatrix}\bigr)$. -/
def twoSheetDirac (D_L D_R M_L M_R : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 D_L M_L M_R D_R

/-- Single-step lifted operator $\mathcal{D}_{\mathrm{step}}(D, \Gamma, m) = \bigl(\begin{smallmatrix} D & \Gamma m \\ \Gamma m & D \end{smallmatrix}\bigr)$. -/
def liftDiracStep (D Γ m : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 D (Γ * m) (Γ * m) D

/-- **Two-Sheet Commutator & Exact Non-Central Lichnerowicz–Higgs Theorem ($\mathcal{D}\mathcal{H}_1$)**:
1. $\⁅\mathcal{D}, e_L⁆ = \bigl(\begin{smallmatrix} 0 & -M_L \\ M_R & 0 \end{smallmatrix}\bigr)$,
2. Whenever $\{D, \Gamma\} = 0$, $\Gamma^2 = 1$, and $\Gamma m = m \Gamma$ (without assuming $\⁅D, m⁆ = 0$),
   $(\mathcal{D}_{\mathrm{step}}(D, \Gamma, m))^2 = \bigl(\begin{smallmatrix} D^2 + m^2 & -\Gamma\⁅D, m⁆ \\ -\Gamma\⁅D, m⁆ & D^2 + m^2 \end{smallmatrix}\bigr)$,
3. When $\⁅D, m⁆ = 0$, the off-diagonal vanishes and $\mathcal{D}_{\mathrm{step}}(D, \Gamma, m)$
   anticommutes with $\mathrm{diag}(\Gamma, -\Gamma)$. -/
theorem mass_commutator_and_noncentral_lichnerowicz_higgs
    (D_L D_R M_L M_R D Γ m : B)
    (h_anticomm : D * Γ + Γ * D = 0)
    (h_gamma_sq : Γ * Γ = 1)
    (h_comm_m : Γ * m = m * Γ) :
    let D_next := liftDiracStep D Γ m
    let Γ_next : Matrix (Fin 2) (Fin 2) B := mat2 Γ 0 0 (-Γ)
    ⁅twoSheetDirac D_L D_R M_L M_R, (sheetLeft : Matrix (Fin 2) (Fin 2) B)⁆ =
      mat2 0 (-M_L) M_R 0 ∧
    D_next * D_next =
      mat2 (D * D + m * m) (-Γ * ⁅D, m⁆) (-Γ * ⁅D, m⁆) (D * D + m * m) ∧
    (⁅D, m⁆ = 0 →
      D_next * D_next = mat2 (D * D + m * m) 0 0 (D * D + m * m)) ∧
    D_next * Γ_next + Γ_next * D_next = 0 := by
  intro D_next Γ_next
  have hDΓ : D * Γ = -(Γ * D) := eq_neg_of_add_eq_zero_left h_anticomm
  have h_mass_sq : (Γ * m) * (Γ * m) = m * m := by
    calc (Γ * m) * (Γ * m) = Γ * (m * Γ) * m := by noncomm_ring
      _ = Γ * (Γ * m) * m := by rw [h_comm_m]
      _ = (Γ * Γ) * (m * m) := by noncomm_ring
      _ = m * m := by rw [h_gamma_sq, one_mul]
  have h_cross : D * (Γ * m) + (Γ * m) * D = -Γ * ⁅D, m⁆ := by
    rw [Ring.lie_def]
    calc D * (Γ * m) + (Γ * m) * D
      _ = (D * Γ) * m + Γ * (m * D) := by noncomm_ring
      _ = -(Γ * D) * m + Γ * (m * D) := by rw [hDΓ]
      _ = -Γ * (D * m - m * D) := by noncomm_ring
  have h_sq : D_next * D_next =
      mat2 (D * D + m * m) (-Γ * ⁅D, m⁆) (-Γ * ⁅D, m⁆) (D * D + m * m) := by
    apply ext_fin2 <;> simp [D_next, liftDiracStep, h_mass_sq, h_cross]
    · rw [add_comm, h_cross, neg_mul]
    · rw [add_comm]
  refine ⟨?_, h_sq, ?_, ?_⟩
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [twoSheetDirac, sheetLeft]
  · intro hDm
    rw [h_sq, hDm, mul_zero]
  · have h_off : -(Γ * m * Γ) + Γ * (Γ * m) = 0 := by
      calc -(Γ * m * Γ) + Γ * (Γ * m)
        _ = -(Γ * (m * Γ)) + (Γ * Γ) * m := by noncomm_ring
        _ = -(Γ * (Γ * m)) + (Γ * Γ) * m := by rw [h_comm_m]
        _ = 0 := by noncomm_ring
    have h_off2 : Γ * m * Γ - Γ * (Γ * m) = 0 := by
      calc Γ * m * Γ - Γ * (Γ * m) = -(-(Γ * m * Γ) + Γ * (Γ * m)) := by abel
        _ = 0 := by rw [h_off, neg_zero]
    apply ext_fin2
    · simp [D_next, Γ_next, liftDiracStep, h_anticomm]
    · simp [D_next, Γ_next, liftDiracStep, h_off]
    · simp [D_next, Γ_next, liftDiracStep]
      rw [← sub_eq_add_neg, h_off2]
    · simp [D_next, Γ_next, liftDiracStep]
      calc -(D * Γ) + -(Γ * D) = -(D * Γ + Γ * D) := by abel
        _ = 0 := by rw [h_anticomm, neg_zero]

end ArchetypeDH1_TwoSheetCommutatorAndLichnerowicz

/-!
## Archetype $\mathcal{D}\mathcal{H}_2$: Connes–Chamseddine Inner Fluctuations & Quartic Spectral Action
-/

section ArchetypeDH2_ConnesChamseddineHiggsMechanism

variable {B : Type*} [Ring B]

/-- Bimodule covariant derivative $\nabla_{L, R}(H) = D_L H - H D_R$. -/
def higgsCovDeriv (D_L D_R H : B) : B :=
  D_L * H - H * D_R

/-- Fluctuated two-sheeted operator $\mathcal{D}_{\mathrm{fluct}} = \bigl(\begin{smallmatrix} D_L & \Gamma H_+ \\ \Gamma H_- & D_R \end{smallmatrix}\bigr)$. -/
def fluctuatedDirac (D_L D_R Γ H_plus H_minus : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 D_L (Γ * H_plus) (Γ * H_minus) D_R

/-- **Connes–Chamseddine Inner Fluctuation & Quartic Higgs Spectral Action Theorem ($\mathcal{D}\mathcal{H}_2$)**:
For $\{D_L, \Gamma\} = \{D_R, \Gamma\} = 0$, $\Gamma^2 = 1$, and $\Gamma H_\pm = H_\pm \Gamma$:
1. $\mathcal{D}_{\mathrm{fluct}}^2 = \bigl(\begin{smallmatrix} D_L^2 + H_+ H_- & -\Gamma\,\nabla_{L,R}(H_+) \\ -\Gamma\,\nabla_{R,L}(H_-) & D_R^2 + H_- H_+ \end{smallmatrix}\bigr)$,
2. Over `[StarRing B]` with $H_- = H^\star, H_+ = H$ and $\Gamma^\star = \Gamma$,
   $\mathrm{Tr}((\mathcal{D}_{\mathrm{sa}}^2)^\dagger \mathcal{D}_{\mathrm{sa}}^2)$ decomposes into four
   $\star$-positive Hermitian squares. -/
theorem connes_chamseddine_higgs_curvature_and_quartic_action [StarRing B]
    (D_L D_R Γ H_plus H_minus H : B)
    (hL_anti : D_L * Γ + Γ * D_L = 0)
    (hR_anti : D_R * Γ + Γ * D_R = 0)
    (hΓ_sq : Γ * Γ = 1)
    (hH_plus : Γ * H_plus = H_plus * Γ)
    (hH_minus : Γ * H_minus = H_minus * Γ)
    (hH : Γ * H = H * Γ)
    (hΓ_sa : star Γ = Γ) :
    let D_fluct := fluctuatedDirac D_L D_R Γ H_plus H_minus
    let D_sa    := fluctuatedDirac D_L D_R Γ H (star H)
    D_fluct * D_fluct =
      mat2 (D_L * D_L + H_plus * H_minus) (-Γ * higgsCovDeriv D_L D_R H_plus)
           (-Γ * higgsCovDeriv D_R D_L H_minus) (D_R * D_R + H_minus * H_plus) ∧
    Matrix.trace ((D_sa * D_sa)ᴴ * (D_sa * D_sa)) =
      star (D_L * D_L + H * star H) * (D_L * D_L + H * star H) +
      star (higgsCovDeriv D_R D_L (star H)) * higgsCovDeriv D_R D_L (star H) +
      (star (higgsCovDeriv D_L D_R H) * higgsCovDeriv D_L D_R H +
       star (D_R * D_R + star H * H) * (D_R * D_R + star H * H)) := by
  intro D_fluct D_sa
  have hDL : D_L * Γ = -(Γ * D_L) := eq_neg_of_add_eq_zero_left hL_anti
  have hDR : D_R * Γ = -(Γ * D_R) := eq_neg_of_add_eq_zero_left hR_anti
  have h_prod : ∀ (X Y : B), Γ * X = X * Γ → (Γ * X) * (Γ * Y) = X * Y := by
    intro X Y hX
    calc (Γ * X) * (Γ * Y) = Γ * (X * Γ) * Y := by noncomm_ring
      _ = Γ * (Γ * X) * Y := by rw [hX]
      _ = (Γ * Γ) * (X * Y) := by noncomm_ring
      _ = X * Y := by rw [hΓ_sq, one_mul]
  have h_cov1 : ∀ (X : B), D_L * (Γ * X) + (Γ * X) * D_R = -Γ * higgsCovDeriv D_L D_R X := by
    intro X; dsimp [higgsCovDeriv]
    calc D_L * (Γ * X) + (Γ * X) * D_R
      _ = (D_L * Γ) * X + Γ * (X * D_R) := by noncomm_ring
      _ = -(Γ * D_L) * X + Γ * (X * D_R) := by rw [hDL]
      _ = -Γ * (D_L * X - X * D_R) := by noncomm_ring
  have h_cov2 : ∀ (Y : B), (Γ * Y) * D_L + D_R * (Γ * Y) = -Γ * higgsCovDeriv D_R D_L Y := by
    intro Y; dsimp [higgsCovDeriv]
    calc (Γ * Y) * D_L + D_R * (Γ * Y)
      _ = Γ * (Y * D_L) + (D_R * Γ) * Y := by noncomm_ring
      _ = Γ * (Y * D_L) + -(Γ * D_R) * Y := by rw [hDR]
      _ = -Γ * (D_R * Y - Y * D_L) := by noncomm_ring
  have hH_star : Γ * star H = star H * Γ := by
    calc Γ * star H = star (H * Γ) := by rw [star_mul, hΓ_sa]
      _ = star (Γ * H) := by rw [hH]
      _ = star H * Γ := by rw [star_mul, hΓ_sa]
  have h_sq_sa : D_sa * D_sa =
      mat2 (D_L * D_L + H * star H) (-Γ * higgsCovDeriv D_L D_R H)
           (-Γ * higgsCovDeriv D_R D_L (star H)) (D_R * D_R + star H * H) := by
    apply ext_fin2 <;>
      simp [D_sa, fluctuatedDirac, h_prod H (star H) hH,
            h_prod (star H) H hH_star, h_cov1 H, h_cov2 (star H)]
    rw [add_comm]
  have h_norm : ∀ (X : B), star (-Γ * X) * (-Γ * X) = star X * X := by
    intro X
    simp only [star_mul, star_neg, hΓ_sa]
    calc (star X * -Γ) * (-Γ * X) = star X * (Γ * Γ) * X := by noncomm_ring
      _ = star X * X := by rw [hΓ_sq]; noncomm_ring
  refine ⟨?_, ?_⟩
  · apply ext_fin2 <;>
      simp [D_fluct, fluctuatedDirac, h_prod H_plus H_minus hH_plus,
            h_prod H_minus H_plus hH_minus, h_cov1 H_plus, h_cov2 H_minus]
    rw [add_comm]
  · rw [h_sq_sa]
    simp only [trace_fin2, mul2_00, mul2_11, ct2_00, ct2_01, ct2_10, ct2_11,
      mat2_00, mat2_01, mat2_10, mat2_11]
    rw [h_norm, h_norm]

end ArchetypeDH2_ConnesChamseddineHiggsMechanism

/-!
## Archetype $\mathcal{D}\mathcal{H}_3$ & $\mathcal{D}\mathcal{H}_4$: All-Scales Kronecker Dirac–Connes Tower & Mass-Square Summability
-/

section ArchetypeDH3_DH4_AllScalesDiracMassSummability

universe u

variable {B : Type u} [Ring B]

def diagEmbed {n : ℕ} (X : ClTower B n) : ClTower B (n + 1) :=
  mat2 X 0 0 X

def towerScalar : ∀ (n : ℕ), B → ClTower B n
  | 0,     b => b
  | n + 1, b => diagEmbed (towerScalar n b)

/-- $n$-scale Kronecker chirality involution $\Gamma^{(n)} \in \mathcal{C}\ell_n(B)$. -/
def kroneckerGamma (γ₀ : B) : ∀ (n : ℕ), ClTower B n
  | 0     => γ₀
  | n + 1 => mat2 (kroneckerGamma γ₀ n) 0 0 (-kroneckerGamma γ₀ n)

/-- $n$-scale Kronecker Dirac–Connes operator $\mathcal{D}_n \in \mathcal{C}\ell_n(B)$. -/
def connesDiracTower (D₀ γ₀ : B) (m : ℕ → B) : ∀ (n : ℕ), ClTower B n
  | 0     => D₀
  | n + 1 =>
      liftDiracStep
        (connesDiracTower D₀ γ₀ m n)
        (kroneckerGamma γ₀ n)
        (towerScalar n (m n))

/-- Cumulative sum of squared masses $D_0^2 + \sum_{k=0}^{n-1} m_k^2 \in B$. -/
def cumulativeMassSq (D₀ : B) (m : ℕ → B) : ℕ → B
  | 0     => D₀ * D₀
  | n + 1 => cumulativeMassSq D₀ m n + m n * m n

def towerTrace : ∀ {n : ℕ}, ClTower B n → B
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace (γ₀ : B) {n : ℕ} (M : ClTower B n) : B :=
  towerTrace (kroneckerGamma γ₀ n * M)

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower B n), towerTrace (-X) = -towerTrace X
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace]
      change towerTrace (-(X 0 0)) + towerTrace (-(X 1 1)) = -(towerTrace (X 0 0) + towerTrace (X 1 1))
      rw [towerTrace_neg, towerTrace_neg]
      abel

lemma towerTrace_add : ∀ (n : ℕ) (X Y : ClTower B n),
    towerTrace (X + Y) = towerTrace X + towerTrace Y
  | 0,     _, _ => rfl
  | n + 1, X, Y => by
      simp only [towerTrace, Matrix.add_apply]
      rw [towerTrace_add n (X 0 0) (Y 0 0), towerTrace_add n (X 1 1) (Y 1 1)]
      abel

lemma towerTrace_sub : ∀ (n : ℕ) (X Y : ClTower B n),
    towerTrace (X - Y) = towerTrace X - towerTrace Y := by
  intro n X Y
  rw [sub_eq_add_neg, towerTrace_add, towerTrace_neg]
  exact (sub_eq_add_neg _ _).symm

lemma towerScalar_add (n : ℕ) (x y : B) :
    towerScalar n (x + y) = towerScalar n x + towerScalar n y := by
  induction' n with k ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, diagEmbed, ih]

lemma towerScalar_mul (n : ℕ) (x y : B) :
    towerScalar n (x * y) = towerScalar n x * towerScalar n y := by
  induction' n with k ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, diagEmbed, ih]

lemma towerScalar_central {c : B} (hc : ∀ x : B, c * x = x * c) :
    ∀ (n : ℕ) (X : ClTower B n), towerScalar n c * X = X * towerScalar n c
  | 0,     X => hc X
  | n + 1, X => by
      have ih := towerScalar_central hc n
      apply ext_fin2 <;>
        simp [towerScalar, diagEmbed, ih (X 0 0), ih (X 0 1), ih (X 1 0), ih (X 1 1)]

lemma kroneckerGamma_sq {γ₀ : B} (hγ₀ : γ₀ * γ₀ = 1) :
    ∀ (n : ℕ), kroneckerGamma γ₀ n * kroneckerGamma γ₀ n = 1
  | 0     => hγ₀
  | n + 1 => by apply ext_fin2 <;> simp [kroneckerGamma, kroneckerGamma_sq hγ₀ n]

/-- **All-Scales Mass-Square Summability Across `ClTower B N` ($\mathcal{D}\mathcal{H}_3$ & $\mathcal{D}\mathcal{H}_4$)**:
Given $D_0, \gamma_0 \in B$ with $\{D_0, \gamma_0\} = 0$ and $\gamma_0^2 = 1$, and central scale
masses $m : \mathbb{N} \to B$, for every $N \in \mathbb{N}$:
1. $(\Gamma^{(N)})^2 = 1$,
2. $\{\mathcal{D}_N, \Gamma^{(N)}\} = 0$,
3. $\mathcal{D}_N^2 = \iota_{\mathrm{diag}}^{(N)}(D_0^2 + \sum_{k=0}^{N-1} m_k^2)$,
4. $\mathrm{Str}_{2^{N+1}}(\mathcal{D}_{N+1}^2) = 0$. -/
theorem all_scales_connes_dirac_mass_entropy_tower
    (D₀ γ₀ : B) (m : ℕ → B)
    (h_anti₀ : D₀ * γ₀ + γ₀ * D₀ = 0)
    (h_γ₀_sq : γ₀ * γ₀ = 1)
    (hm_central : ∀ (k : ℕ) (x : B), m k * x = x * m k) (N : ℕ) :
    let D_N := connesDiracTower D₀ γ₀ m N
    let Γ_N := kroneckerGamma γ₀ N
    Γ_N * Γ_N = 1 ∧
    D_N * Γ_N + Γ_N * D_N = 0 ∧
    D_N * D_N = towerScalar N (cumulativeMassSq D₀ m N) ∧
    superTrace γ₀ (n := N + 1)
      (connesDiracTower D₀ γ₀ m (N + 1) * connesDiracTower D₀ γ₀ m (N + 1)) = 0 := by
  have h_ind : ∀ (n : ℕ),
      connesDiracTower D₀ γ₀ m n * kroneckerGamma γ₀ n +
        kroneckerGamma γ₀ n * connesDiracTower D₀ γ₀ m n = 0 ∧
      connesDiracTower D₀ γ₀ m n * connesDiracTower D₀ γ₀ m n =
        towerScalar n (cumulativeMassSq D₀ m n) := by
    intro n; induction' n with k ih
    · exact ⟨h_anti₀, rfl⟩
    · rcases ih with ⟨ih_anti, ih_sq⟩
      have h_cent_k := towerScalar_central (hm_central k) k
      have h_comm_Γ : kroneckerGamma γ₀ k * towerScalar k (m k) =
          towerScalar k (m k) * kroneckerGamma γ₀ k :=
        (h_cent_k (kroneckerGamma γ₀ k)).symm
      have h_comm_D : ⁅connesDiracTower D₀ γ₀ m k, towerScalar k (m k)⁆ = 0 := by
        rw [Ring.lie_def, h_cent_k (connesDiracTower D₀ γ₀ m k), sub_self]
      rcases mass_commutator_and_noncentral_lichnerowicz_higgs
        0 0 0 0 (connesDiracTower D₀ γ₀ m k) (kroneckerGamma γ₀ k) (towerScalar k (m k))
        ih_anti (kroneckerGamma_sq h_γ₀_sq k) h_comm_Γ with ⟨_, _, h_step_sq, h_step_anti⟩
      refine ⟨h_step_anti, ?_⟩
      dsimp [connesDiracTower, cumulativeMassSq, towerScalar, diagEmbed]
      rw [h_step_sq h_comm_D, ih_sq, ← towerScalar_mul, ← towerScalar_add]
  refine ⟨kroneckerGamma_sq h_γ₀_sq N, (h_ind N).1, (h_ind N).2, ?_⟩
  rw [(h_ind (N + 1)).2]
  dsimp [superTrace, kroneckerGamma, towerScalar, diagEmbed, towerTrace]
  simp [neg_mul, towerTrace_neg]

end ArchetypeDH3_DH4_AllScalesDiracMassSummability

section ArchetypeUZ1_NonCentralDiracHiggsTower

variable {B : Type u} [Ring B]

/-- Recursive two-sheet Dirac tower with arbitrary, potentially noncentral
Higgs operators at each scale. -/
def noncentralDiracTower (D₀ γ₀ : B)
    (H_plus H_minus : ∀ n : ℕ, ClTower B n) : ∀ n : ℕ, ClTower B n
  | 0 => D₀
  | n + 1 =>
      let D_n := noncentralDiracTower D₀ γ₀ H_plus H_minus n
      let Γ_n := kroneckerGamma γ₀ n
      mat2 D_n (Γ_n * H_plus n) (Γ_n * H_minus n) D_n

/-- For arbitrary even scale Higgs operators, chirality and the exact
noncentral square obstruction propagate at every finite tower scale. The
supertrace here is the repository's recursive `B`-valued `towerTrace`; it is
not asserted to be a scalar-valued Atiyah–Singer index. -/
theorem noncentral_all_scales_dirac_higgs_tower
    (D₀ γ₀ : B) (H_plus H_minus : ∀ n : ℕ, ClTower B n)
    (h_anti₀ : D₀ * γ₀ + γ₀ * D₀ = 0)
    (h_γ₀_sq : γ₀ * γ₀ = 1)
    (hH_plus_even : ∀ n : ℕ,
      kroneckerGamma γ₀ n * H_plus n = H_plus n * kroneckerGamma γ₀ n)
    (hH_minus_even : ∀ n : ℕ,
      kroneckerGamma γ₀ n * H_minus n = H_minus n * kroneckerGamma γ₀ n)
    (N : ℕ) :
    let D_N := noncentralDiracTower D₀ γ₀ H_plus H_minus N
    let D_N1 := noncentralDiracTower D₀ γ₀ H_plus H_minus (N + 1)
    let Γ_N := kroneckerGamma γ₀ N
    Γ_N * Γ_N = 1 ∧
    D_N * Γ_N + Γ_N * D_N = 0 ∧
    D_N1 * D_N1 =
      mat2 (D_N * D_N + H_plus N * H_minus N)
        (-Γ_N * ⁅D_N, H_plus N⁆)
        (-Γ_N * ⁅D_N, H_minus N⁆)
        (D_N * D_N + H_minus N * H_plus N) ∧
    superTrace γ₀ (n := N + 1) (D_N1 * D_N1) =
      superTrace γ₀ ⁅H_plus N, H_minus N⁆ := by
  intro D_N D_N1 Γ_N
  have h_anti_all : ∀ n : ℕ,
      noncentralDiracTower D₀ γ₀ H_plus H_minus n * kroneckerGamma γ₀ n +
        kroneckerGamma γ₀ n * noncentralDiracTower D₀ γ₀ H_plus H_minus n = 0 := by
    intro n
    induction n with
    | zero => exact h_anti₀
    | succ k ih =>
        have h_off₁ :
            -(kroneckerGamma γ₀ k * H_plus k * kroneckerGamma γ₀ k) +
              kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_plus k) = 0 := by
          calc
            _ = -(kroneckerGamma γ₀ k * (H_plus k * kroneckerGamma γ₀ k)) +
                kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_plus k) := by noncomm_ring
            _ = 0 := by rw [← hH_plus_even k]; abel
        have h_off₂ :
            kroneckerGamma γ₀ k * H_minus k * kroneckerGamma γ₀ k -
              kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_minus k) = 0 := by
          calc
            _ = kroneckerGamma γ₀ k * (H_minus k * kroneckerGamma γ₀ k) -
                kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_minus k) := by noncomm_ring
            _ = 0 := by rw [← hH_minus_even k]; abel
        have h_off₂_add :
            kroneckerGamma γ₀ k * H_minus k * kroneckerGamma γ₀ k +
              -(kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_minus k)) = 0 := by
          calc
            _ = kroneckerGamma γ₀ k * H_minus k * kroneckerGamma γ₀ k -
                kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_minus k) :=
                  (sub_eq_add_neg _ _).symm
            _ = 0 := h_off₂
        apply ext_fin2
        · simp [noncentralDiracTower, kroneckerGamma, ih]
        · simp [noncentralDiracTower, kroneckerGamma, h_off₁]
        · simp [noncentralDiracTower, kroneckerGamma, h_off₂_add]
        · simp [noncentralDiracTower, kroneckerGamma]
          calc
            _ = -(noncentralDiracTower D₀ γ₀ H_plus H_minus k * kroneckerGamma γ₀ k +
                  kroneckerGamma γ₀ k * noncentralDiracTower D₀ γ₀ H_plus H_minus k) := by abel
            _ = 0 := by rw [ih, neg_zero]
  have hΓ_sq := kroneckerGamma_sq h_γ₀_sq N
  have hD_anti := h_anti_all N
  have hDΓ : D_N * Γ_N = -(Γ_N * D_N) :=
    eq_neg_of_add_eq_zero_left hD_anti
  have h_prod : ∀ (X Y : ClTower B N), Γ_N * X = X * Γ_N →
      (Γ_N * X) * (Γ_N * Y) = X * Y := by
    intro X Y hX
    calc
      (Γ_N * X) * (Γ_N * Y) = Γ_N * (X * Γ_N) * Y := by noncomm_ring
      _ = Γ_N * (Γ_N * X) * Y := by rw [hX]
      _ = (Γ_N * Γ_N) * (X * Y) := by noncomm_ring
      _ = X * Y := by rw [hΓ_sq, one_mul]
  have h_cross : ∀ (X : ClTower B N),
      D_N * (Γ_N * X) + (Γ_N * X) * D_N = -Γ_N * ⁅D_N, X⁆ := by
    intro X
    rw [Ring.lie_def]
    calc
      D_N * (Γ_N * X) + (Γ_N * X) * D_N =
          (D_N * Γ_N) * X + Γ_N * (X * D_N) := by noncomm_ring
      _ = -(Γ_N * D_N) * X + Γ_N * (X * D_N) := by rw [hDΓ]
      _ = -Γ_N * (D_N * X - X * D_N) := by noncomm_ring
  have h_cross_rev : ∀ (X : ClTower B N),
      (Γ_N * X) * D_N + D_N * (Γ_N * X) = -Γ_N * ⁅D_N, X⁆ := by
    intro X
    rw [add_comm, h_cross X]
  have h_sq : D_N1 * D_N1 =
      mat2 (D_N * D_N + H_plus N * H_minus N)
        (-Γ_N * ⁅D_N, H_plus N⁆)
        (-Γ_N * ⁅D_N, H_minus N⁆)
        (D_N * D_N + H_minus N * H_plus N) := by
    change (mat2 D_N (Γ_N * H_plus N) (Γ_N * H_minus N) D_N :
        ClTower B (N + 1)) *
      mat2 D_N (Γ_N * H_plus N) (Γ_N * H_minus N) D_N = _
    apply ext_fin2
    · simp only [mul2_00, mat2_00, mat2_01, mat2_10]
      rw [h_prod (H_plus N) (H_minus N) (hH_plus_even N)]
    · simp only [mul2_01, mat2_00, mat2_01, mat2_11]
      exact h_cross (H_plus N)
    · simp only [mul2_10, mat2_10, mat2_00, mat2_11]
      exact h_cross_rev (H_minus N)
    · simp only [mul2_11, mat2_10, mat2_01, mat2_11]
      rw [h_prod (H_minus N) (H_plus N) (hH_minus_even N)]
      abel
  refine ⟨hΓ_sq, hD_anti, h_sq, ?_⟩
  rw [h_sq]
  simp only [superTrace, kroneckerGamma, towerTrace,
    mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
    zero_mul, add_zero, zero_add]
  change towerTrace (Γ_N * (D_N * D_N + H_plus N * H_minus N)) +
      towerTrace ((-Γ_N) * (D_N * D_N + H_minus N * H_plus N)) =
    towerTrace (Γ_N * (H_plus N * H_minus N - H_minus N * H_plus N))
  rw [neg_mul, towerTrace_neg, mul_add, mul_add,
    towerTrace_add, towerTrace_add, mul_sub, towerTrace_sub]
  abel

end ArchetypeUZ1_NonCentralDiracHiggsTower

end InfoGeometry.Algebra.TwoSheetDiracMassEntropy
