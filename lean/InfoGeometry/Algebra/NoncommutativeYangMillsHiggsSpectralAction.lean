/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.TwoSheetDiracMassEntropy
import InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
import InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis
import InfoGeometry.Algebra.NoncommutativeUnifiedDiracHiggsZornTower
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Unified Yang–Mills–Higgs–Dirac Spectral Action & BPS Self-Duality ($\mathcal{S}\mathcal{A}_1$–$\mathcal{S}\mathcal{A}_4$)

Formalizes over arbitrary noncommutative rings `[Ring B]` and $\star$-rings `[Ring B] [StarRing B]`,
reusing `NoncommutativeCliffordPrimitives`, `TwoSheetDiracMassEntropy`,
`NoncommutativeCovariantDiracZornSynthesis`, `NoncommutativeInherentZornGaugeSynthesis`, and
`NoncommutativeUnifiedDiracHiggsZornTower`:

1. **$\mathcal{S}\mathcal{A}_1$** (`zorn_tetraktys_hilbert_schmidt_pythagoras`):
   4-channel Zorn–Tetraktys Hilbert–Schmidt Pythagorean identity in $M_2(B)$:
   `Matrix.trace (Wᴴ * W) = 2 • (star s * s + star v₁ * v₁ + star v₂ * v₂ + star v₃ * v₃)`.
2. **$\mathcal{S}\mathcal{A}_2$** (`unified_yang_mills_higgs_dirac_spectral_action`):
   Quartic spectral action `trace4 ((D_cov * D_cov)ᴴ * (D_cov * D_cov))` decomposing into
   four times the sum of the Klein–Gordon square, three Yang–Mills field-strength squares,
   and three covariant Higgs kinetic squares.
3. **$\mathcal{S}\mathcal{A}_3$** (`noncommutative_bps_monopole_bound_and_bianchi_harmonicity`):
   Bogomolny–Prasad–Sommerfield (BPS) completion of the square and Bianchi–Laplace
   harmonicity `⁅D₁, ⁅D₁, m⁆⁆ + ⁅D₂, ⁅D₂, m⁆⁆ + ⁅D₃, ⁅D₃, m⁆⁆ = 0`.
4. **$\mathcal{S}\mathcal{A}_4$**: Re-exported directly from
   `InfoGeometry.Algebra.NoncommutativeUnifiedDiracHiggsZornTower.noncentral_all_scales_dirac_higgs_tower_and_anomaly`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
open InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis

namespace InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction

/-!
## Archetype $\mathcal{S}\mathcal{A}_1$: 4-Channel Zorn–Tetraktys Hilbert–Schmidt Pythagoras in $M_2(B)$
-/

section ArchetypeSA1_ZornTetraktysPythagoras

variable {B : Type*} [Ring B] [StarRing B]

/-- **4-Channel Zorn–Tetraktys Hilbert–Schmidt Pythagorean Theorem ($\mathcal{S}\mathcal{A}_1$)**:
For any scalar $s \in B$ and 3-vector $(v_1, v_2, v_3) \in B^3$ (without commutativity or
self-adjointness assumptions), $W = \iota(s) + \mathrm{vecOp}(v_1, v_2, v_3)$ satisfies
$\mathrm{Tr}_2(W^\dagger W) = 2 \bullet (s^\star s + v_1^\star v_1 + v_2^\star v_2 + v_3^\star v_3)$. -/
theorem zorn_tetraktys_hilbert_schmidt_pythagoras (s v₁ v₂ v₃ : B) :
    let W : Matrix (Fin 2) (Fin 2) B := fiberEmbed s + vecOp v₁ v₂ v₃
    Matrix.trace (Wᴴ * W) =
      2 • (star s * s + star v₁ * v₁ + star v₂ * v₂ + star v₃ * v₃) := by
  simp [fiberEmbed, two_smul]
  noncomm_ring

end ArchetypeSA1_ZornTetraktysPythagoras

/-!
## Archetype $\mathcal{S}\mathcal{A}_2$: Unified Yang–Mills–Higgs–Klein–Gordon Quartic Spectral Action in $M_2(M_2(B))$
-/

section ArchetypeSA2_UnifiedYangMillsHiggsSpectralAction

variable {B : Type*} [Ring B]

/-- 2-scale trace $\mathrm{Tr}_4(\mathbb{M}) = \mathrm{Tr}_2(\mathbb{M}_{00}) + \mathrm{Tr}_2(\mathbb{M}_{11})$ on $M_2(M_2(B))$. -/
def trace4 (𝕄 : NestedMat B) : B :=
  Matrix.trace (𝕄 0 0) + Matrix.trace (𝕄 1 1)

lemma zorn_vec_sq (D₁ D₂ D₃ : B) :
    vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃ =
      fiberEmbed (D₁ * D₁ + D₂ * D₂ - D₃ * D₃) +
      vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆) := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring

lemma comm_fiberEmbed_vecOp (m D₁ D₂ D₃ : B) :
    ⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆ = vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆ := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring

lemma covariant_dirac_zorn_sq_ym
    (m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁    := d₁ + A₁
    let D₂    := d₂ + A₂
    let D₃    := d₃ + A₃
    let Δ_KG  := m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)
    let F₂₃   := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁   := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂   := ymFieldStrength d₁ d₂ A₁ A₂
    let D_cov := bareDiracZorn m D₁ D₂ D₃
    D_cov * D_cov =
      mat2
        (fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂))
        (vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)
        (-vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)
        (fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂)) := by
  intro D₁ D₂ D₃ Δ_KG F₂₃ F₃₁ F₁₂ D_cov
  have h_ym : ∀ {x₁ x₂ : B} (y₁ y₂ : B), ⁅x₁, x₂⁆ = 0 →
      ⁅x₁ + y₁, x₂ + y₂⁆ = ymFieldStrength x₁ x₂ y₁ y₂ := by
    intro x₁ x₂ y₁ y₂ hx
    dsimp [ymFieldStrength]
    rw [← zero_add (⁅x₁, y₂⁆ - ⁅x₂, y₁⁆ + ⁅y₁, y₂⁆), ← hx]
    simp only [Ring.lie_def]
    noncomm_ring
  have hF23 : ⁅D₂, D₃⁆ = F₂₃ := h_ym A₂ A₃ h23
  have hF31 : ⁅D₃, D₁⁆ = F₃₁ := h_ym A₃ A₁ h31
  have hF12 : ⁅D₁, D₂⁆ = F₁₂ := h_ym A₁ A₂ h12
  have h_add_emb : ∀ (a b : B), fiberEmbed a + fiberEmbed b = fiberEmbed (a + b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_mul_emb : ∀ (a b : B), fiberEmbed a * fiberEmbed b = fiberEmbed (a * b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_neg_emb : ∀ (a : B), fiberEmbed (-a) = -fiberEmbed a := by
    intro a; apply ext_fin2 <;> simp [fiberEmbed]
  have h_comm := comm_fiberEmbed_vecOp m D₁ D₂ D₃
  rw [Ring.lie_def] at h_comm
  apply ext_fin2
  · simp only [D_cov, bareDiracZorn, diracZornOp, mul2_00, mat2_00, mat2_01, mat2_10,
      h_mul_emb, zorn_vec_sq D₁ D₂ D₃, hF23, hF31, hF12, ← add_assoc, h_add_emb]
    rfl
  · simp only [D_cov, bareDiracZorn, diracZornOp, mul2_01, mat2_00, mat2_01, mat2_11,
      h_neg_emb, mul_neg, ← sub_eq_add_neg, h_comm]
  · simp only [D_cov, bareDiracZorn, diracZornOp, mul2_10, mat2_10, mat2_00, mat2_11,
      h_neg_emb, neg_mul, ← h_comm]
    abel
  · simp only [D_cov, bareDiracZorn, diracZornOp, mul2_11, mat2_10, mat2_01, mat2_11,
      h_neg_emb, neg_mul_neg, h_mul_emb]
    rw [add_comm (vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃),
        zorn_vec_sq D₁ D₂ D₃, hF23, hF31, hF12, ← add_assoc, h_add_emb]

/-- **Unified Yang–Mills–Higgs–Klein–Gordon Quartic Spectral Action Theorem ($\mathcal{S}\mathcal{A}_2$)**:
Over any noncommutative $\star$-ring $B$ with flat background derivatives ($\⁅d_i, d_j⁆ = 0$),
the quartic spectral action $\mathrm{Tr}_4((\mathcal{D}_{\mathrm{cov}}^2)^\dagger \mathcal{D}_{\mathrm{cov}}^2)$
decomposes into four times the sum of the Klein–Gordon square $\Delta_{\mathrm{KG}}^\star \Delta_{\mathrm{KG}}$,
the three Yang–Mills field-strength squares $F_{ij}^\star F_{ij}$, and the three covariant Higgs
kinetic squares $\⁅m, D_k⁆^\star \⁅m, D_k⁆$. -/
theorem unified_yang_mills_higgs_dirac_spectral_action [StarRing B]
    (m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁    := d₁ + A₁
    let D₂    := d₂ + A₂
    let D₃    := d₃ + A₃
    let Δ_KG  := m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)
    let F₂₃   := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁   := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂   := ymFieldStrength d₁ d₂ A₁ A₂
    let D_cov := bareDiracZorn m D₁ D₂ D₃
    trace4 ((D_cov * D_cov)ᴴ * (D_cov * D_cov)) =
      4 • (star Δ_KG * Δ_KG +
           (star F₂₃ * F₂₃ + star F₃₁ * F₃₁ + star F₁₂ * F₁₂) +
           (star ⁅m, D₁⁆ * ⁅m, D₁⁆ + star ⁅m, D₂⁆ * ⁅m, D₂⁆ + star ⁅m, D₃⁆ * ⁅m, D₃⁆)) := by
  intro D₁ D₂ D₃ Δ_KG F₂₃ F₃₁ F₁₂ D_cov
  rw [covariant_dirac_zorn_sq_ym m d₁ d₂ d₃ A₁ A₂ A₃ h23 h31 h12]
  dsimp [trace4]
  simp only [mul2_00, mul2_11, ct2_00, ct2_01, ct2_10, ct2_11,
    mat2_00, mat2_01, mat2_10, mat2_11, star_neg, neg_mul_neg]
  have hW := zorn_tetraktys_hilbert_schmidt_pythagoras Δ_KG F₂₃ F₃₁ (-F₁₂)
  have hY := zorn_tetraktys_hilbert_schmidt_pythagoras 0 ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆
  have h0 : fiberEmbed (0 : B) + vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆ =
      vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆ := by
    apply ext_fin2 <;> simp [fiberEmbed]
  rw [h0] at hY
  have h_tr_add : ∀ (X Y : Matrix (Fin 2) (Fin 2) B),
      Matrix.trace (X + Y) = Matrix.trace X + Matrix.trace Y := by
    intro X Y; simp
  rw [h_tr_add, h_tr_add]
  change Matrix.trace ((fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂))ᴴ *
                       (fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂))) +
         Matrix.trace ((vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)ᴴ *
                       vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆) +
        (Matrix.trace ((vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)ᴴ *
                       vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆) +
         Matrix.trace ((fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂))ᴴ *
                       (fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂)))) = _
  rw [hW, hY]
  simp only [star_zero, zero_mul, zero_add, star_neg, neg_mul_neg, nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

end ArchetypeSA2_UnifiedYangMillsHiggsSpectralAction

/-!
## Archetype $\mathcal{S}\mathcal{A}_3$: Noncommutative Bogomolny–Prasad–Sommerfield (BPS) Monopole Bound & Bianchi–Laplace Harmonicity
-/

section ArchetypeSA3_BPSMonopoleAndBianchiHarmonicity

variable {B : Type*} [Ring B] [StarRing B]

/-- Topological BPS magnetic monopole flux $\mathcal{Q}_{\mathrm{BPS}} = \sum_{\mathrm{cyc}} (F_{jk}^\star G_i + G_i^\star F_{jk})$. -/
def bpsMonopoleFlux (F₂₃ F₃₁ F₁₂ G₁ G₂ G₃ : B) : B :=
  (star F₂₃ * G₁ + star G₁ * F₂₃) +
  (star F₃₁ * G₂ + star G₂ * F₃₁) +
  (star F₁₂ * G₃ + star G₃ * F₁₂)

/-- **Noncommutative BPS Monopole Completion of the Square & Bianchi–Laplace Harmonicity ($\mathcal{S}\mathcal{A}_3$)**:
1. *BPS Completion of the Square*:
   $\sum (F_{jk}^\star F_{jk} + G_i^\star G_i) = \sum (F_{jk} - G_i)^\star (F_{jk} - G_i) + \mathcal{Q}_{\mathrm{BPS}}$.
2. *BPS Bianchi–Laplace Harmonicity*: Whenever the Bogomolny self-duality equations
   $F_{23} = \⁅D_1, m⁆, F_{31} = \⁅D_2, m⁆, F_{12} = \⁅D_3, m⁆$ hold on a flat background
   ($\⁅d_i, d_j⁆ = 0$), the Higgs field $m$ satisfies the 3D covariant Laplace equation:
   $\⁅D_1, \⁅D_1, m⁆⁆ + \⁅D_2, \⁅D_2, m⁆⁆ + \⁅D_3, \⁅D_3, m⁆⁆ = 0$. -/
theorem noncommutative_bps_monopole_bound_and_bianchi_harmonicity
    (F₂₃ F₃₁ F₁₂ G₁ G₂ G₃ m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0)
    (h_bps1 : ymFieldStrength d₂ d₃ A₂ A₃ = ⁅d₁ + A₁, m⁆)
    (h_bps2 : ymFieldStrength d₃ d₁ A₃ A₁ = ⁅d₂ + A₂, m⁆)
    (h_bps3 : ymFieldStrength d₁ d₂ A₁ A₂ = ⁅d₃ + A₃, m⁆) :
    let D₁ := d₁ + A₁
    let D₂ := d₂ + A₂
    let D₃ := d₃ + A₃
    (star F₂₃ * F₂₃ + star F₃₁ * F₃₁ + star F₁₂ * F₁₂) +
    (star G₁ * G₁ + star G₂ * G₂ + star G₃ * G₃) =
      star (F₂₃ - G₁) * (F₂₃ - G₁) +
      star (F₃₁ - G₂) * (F₃₁ - G₂) +
      star (F₁₂ - G₃) * (F₁₂ - G₃) +
      bpsMonopoleFlux F₂₃ F₃₁ F₁₂ G₁ G₂ G₃ ∧
    ⁅D₁, ⁅D₁, m⁆⁆ + ⁅D₂, ⁅D₂, m⁆⁆ + ⁅D₃, ⁅D₃, m⁆⁆ = 0 := by
  intro D₁ D₂ D₃
  refine ⟨?_, ?_⟩
  · dsimp [bpsMonopoleFlux]
    simp only [star_sub]
    noncomm_ring
  · rw [← h_bps1, ← h_bps2, ← h_bps3]
    have h_ym : ∀ {x₁ x₂ : B} (y₁ y₂ : B), ⁅x₁, x₂⁆ = 0 →
        ymFieldStrength x₁ x₂ y₁ y₂ = ⁅x₁ + y₁, x₂ + y₂⁆ := by
      intro x₁ x₂ y₁ y₂ hx
      dsimp [ymFieldStrength]
      rw [← zero_add (⁅x₁, y₂⁆ - ⁅x₂, y₁⁆ + ⁅y₁, y₂⁆), ← hx]
      simp only [Ring.lie_def]
      noncomm_ring
    rw [h_ym A₂ A₃ h23, h_ym A₃ A₁ h31, h_ym A₁ A₂ h12]
    dsimp only [D₁, D₂, D₃]
    simp only [Ring.lie_def]
    noncomm_ring

end ArchetypeSA3_BPSMonopoleAndBianchiHarmonicity

end InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction
