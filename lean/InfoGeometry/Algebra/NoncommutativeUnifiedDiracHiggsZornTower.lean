/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Unified Non-Central Dirac–Higgs–Zorn Gauge Tower ($\mathcal{U}\mathcal{Z}_1$–$\mathcal{U}\mathcal{Z}_4$)

Epistemic compilation over an arbitrary noncommutative ring `[Ring B]` across
all finite stages `ClTower B n`:

1. **$\mathcal{U}\mathcal{Z}_1$** (`noncentral_all_scales_dirac_higgs_tower_and_anomaly`):
   Eliminates the centrality assumption `hm_central` from `TwoSheetDiracMassEntropy`
   for arbitrary chirality-even inter-sheet Higgs operators `H_plus n, H_minus n : ClTower B n`,
   proving all-scales chirality anticommutation, the exact non-central recursive square,
   and the chiral Higgs commutator anomaly `superTrace γ₀ (D_{N+1}^2) = superTrace γ₀ ⁅H_plus N, H_minus N⁆`.
2. **$\mathcal{U}\mathcal{Z}_2$–$\mathcal{U}\mathcal{Z}_4$** (`all_scales_inherent_zorn_gauge_pauli_bianchi_and_maurer_cartan`):
   At every scale `n` in `ClTower B (n + 2)`:
   - inner commutator `⁅bareDiracZornTower, sheetDiagTower⁆` generates Zorn 3-vector gauge 1-forms,
   - covariant Dirac–Zorn square produces Klein–Gordon + Pauli–Yang–Mills spin-curvature `vecOp F₂₃ F₃₁ (-F₁₂)`,
   - exact non-Abelian Bianchi identity `⁅D₁, F₂₃⁆ + ⁅D₂, F₃₁⁆ + ⁅D₃, F₁₂⁆ = 0`,
   - homogeneous Zorn curvature covariance under `g : (ClTower B n)ˣ` and Maurer–Cartan flatness.

Reuses `mat2`, `ext_fin2`, `fiberEmbed`, `ClTower`, and `instRingClTower` from
`InfoGeometry.Algebra.NoncommutativeCliffordPrimitives`, and `vecOp` from
`InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis`.
-/

open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis

namespace InfoGeometry.Algebra.NoncommutativeUnifiedDiracHiggsZornTower

universe u

variable {B : Type u} [Ring B]

/-!
## Archetype $\mathcal{U}\mathcal{Z}_2$, $\mathcal{U}\mathcal{Z}_3$ & $\mathcal{U}\mathcal{Z}_4$: All-Scales Inherent Zorn Gauge Emergence, Pauli–Yang–Mills Wave Square, Bianchi Identity & Maurer–Cartan Flatness on $\mathcal{C}\ell_{n+2}(B)$
-/

section ArchetypeUZ2_UZ3_UZ4_AllScalesZornGaugeTower

/-- Covariant two-sheeted Dirac–Zorn operator at scale $n + 2$ in $\mathcal{C}\ell_{n+2}(B)$. -/
def diracZornTower (n : ℕ) (α β u₁ u₂ u₃ v₁ v₂ v₃ : ClTower B n) : ClTower B (n + 2) :=
  mat2 (fiberEmbed α) (vecOp u₁ u₂ u₃) (vecOp v₁ v₂ v₃) (fiberEmbed β)

/-- Bare un-gauged Dirac–Zorn operator at scale $n + 2$. -/
def bareDiracZornTower (n : ℕ) (m₀ d₁ d₂ d₃ : ClTower B n) : ClTower B (n + 2) :=
  diracZornTower n m₀ (-m₀) d₁ d₂ d₃ d₁ d₂ d₃

/-- Diagonal two-sheet element at scale $n + 2$. -/
def sheetDiagTower (n : ℕ) (u v : ClTower B n) : ClTower B (n + 2) :=
  mat2 (fiberEmbed u) 0 0 (fiberEmbed v)

/-- Non-Abelian Yang–Mills field strength component $F_{ij}(\mathbf{d}, \mathbf{A}) \in \mathcal{C}\ell_n(B)$. -/
def ymFieldStrength {R : Type*} [Ring R] (dᵢ dⱼ Aᵢ Aⱼ : R) : R :=
  ⁅dᵢ, Aⱼ⁆ - ⁅dⱼ, Aᵢ⁆ + ⁅Aᵢ, Aⱼ⁆

/-- Inherent affine gauge transformation $A_k^g = g(d_k + A_k)g^{-1} - d_k$ in $\mathcal{C}\ell_n(B)$. -/
def zornGaugeTransform {R : Type*} [Ring R] (g : Rˣ) (dₖ Aₖ : R) : R :=
  (g : R) * (dₖ + Aₖ) * (↑g⁻¹ : R) - dₖ

lemma zorn_vec_sq {R : Type*} [Ring R] (D₁ D₂ D₃ : R) :
    vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃ =
      fiberEmbed (D₁ * D₁ + D₂ * D₂ - D₃ * D₃) +
      vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆) := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring

lemma cov_shift_conj {R : Type*} [Ring R] (g : Rˣ) (dₖ Aₖ : R) :
    dₖ + zornGaugeTransform g dₖ Aₖ = (g : R) * (dₖ + Aₖ) * (↑g⁻¹ : R) := by
  dsimp [zornGaugeTransform]; abel

lemma comm_conj_units {R : Type*} [Ring R] (g : Rˣ) (X Y : R) :
    ⁅(g : R) * X * (↑g⁻¹ : R), (g : R) * Y * (↑g⁻¹ : R)⁆ =
      (g : R) * ⁅X, Y⁆ * (↑g⁻¹ : R) := by
  have hg : (↑g⁻¹ : R) * (g : R) = 1 := Units.inv_mul g
  rw [Ring.lie_def, Ring.lie_def]
  calc (g : R) * X * (↑g⁻¹ : R) * ((g : R) * Y * (↑g⁻¹ : R)) -
       (g : R) * Y * (↑g⁻¹ : R) * ((g : R) * X * (↑g⁻¹ : R))
    _ = (g : R) * X * ((↑g⁻¹ : R) * (g : R)) * Y * (↑g⁻¹ : R) -
        (g : R) * Y * ((↑g⁻¹ : R) * (g : R)) * X * (↑g⁻¹ : R) := by noncomm_ring
    _ = (g : R) * (X * Y - Y * X) * (↑g⁻¹ : R) := by rw [hg]; noncomm_ring

/-- **All-Scales Inherent Zorn Gauge, Pauli–Yang–Mills Wave Square, Bianchi & Maurer–Cartan Theorem ($\mathcal{U}\mathcal{Z}_2$–$\mathcal{U}\mathcal{Z}_4$)**:
At every scale $n \in \mathbb{N}$ in $\mathcal{C}\ell_{n+2}(B) = M_2(M_2(\mathcal{C}\ell_n(B)))$, for flat
reference operators ($\⁅d_i, d_j⁆ = 0 \in \mathcal{C}\ell_n(B)$), gauge potentials $A_1, A_2, A_3 \in \mathcal{C}\ell_n(B)$,
mass $m \in \mathcal{C}\ell_n(B)$, and gauge transformation $g \in (\mathcal{C}\ell_n(B))^\times$:
1. *Inherent Gauge & Higgs Generation*: $\⁅\mathcal{D}_0^{(n)}(m, \mathbf{d}), \mathbb{U}(u, v)⁆$ populates
   the Zorn vector slots with $d_k v - u d_k$ and diagonal slots with $\⁅m, u⁆, -\⁅m, v⁆$.
2. *Covariant Pauli–Yang–Mills Wave Square*: $(\mathcal{D}_{\mathrm{Zorn}}(m, -m, \mathbf{d}+\mathbf{A}, \mathbf{d}+\mathbf{A}))^2$
   has diagonal blocks $\iota(m^2 + D_1^2 + D_2^2 - D_3^2) + \mathrm{vecOp}(F_{23}, F_{31}, -F_{12})$
   and off-diagonal Yukawa blocks $\pm\⁅\iota(m), \mathrm{vecOp}(\mathbf{D})⁆$.
3. *Non-Abelian Bianchi Identity*: $\⁅D_1, F_{23}⁆ + \⁅D_2, F_{31}⁆ + \⁅D_3, F_{12}⁆ = 0$.
4. *Homogeneous Zorn Curvature Covariance & Maurer–Cartan Flatness*:
   $\mathrm{vecOp}(F_{23}^g, F_{31}^g, -F_{12}^g) = \iota(g)\,\mathrm{vecOp}(F_{23}, F_{31}, -F_{12})\,\iota(g^{-1})$,
   and $F_{12}(\mathbf{d}, \mathbf{A}^{\mathrm{MC}}(g)) = 0$. -/
theorem all_scales_inherent_zorn_gauge_pauli_bianchi_and_maurer_cartan
    (n : ℕ) (m d₁ d₂ d₃ A₁ A₂ A₃ u v : ClTower B n) (g : (ClTower B n)ˣ)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁    := d₁ + A₁
    let D₂    := d₂ + A₂
    let D₃    := d₃ + A₃
    let F₂₃   := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁   := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂   := ymFieldStrength d₁ d₂ A₁ A₂
    let A₁_g  := zornGaugeTransform g d₁ A₁
    let A₂_g  := zornGaugeTransform g d₂ A₂
    let A₃_g  := zornGaugeTransform g d₃ A₃
    let F₂₃_g := ymFieldStrength d₂ d₃ A₂_g A₃_g
    let F₃₁_g := ymFieldStrength d₃ d₁ A₃_g A₁_g
    let F₁₂_g := ymFieldStrength d₁ d₂ A₁_g A₂_g
    let D_cov := bareDiracZornTower n m D₁ D₂ D₃
    ⁅bareDiracZornTower n m d₁ d₂ d₃, sheetDiagTower n u v⁆ =
      diracZornTower n ⁅m, u⁆ (-⁅m, v⁆)
        (d₁ * v - u * d₁) (d₂ * v - u * d₂) (d₃ * v - u * d₃)
        (d₁ * u - v * d₁) (d₂ * u - v * d₂) (d₃ * u - v * d₃) ∧
    D_cov * D_cov =
      mat2
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp F₂₃ F₃₁ (-F₁₂))
        ⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆
        (-⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆)
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp F₂₃ F₃₁ (-F₁₂)) ∧
    ⁅D₁, F₂₃⁆ + ⁅D₂, F₃₁⁆ + ⁅D₃, F₁₂⁆ = 0 ∧
    vecOp F₂₃_g F₃₁_g (-F₁₂_g) =
      fiberEmbed (g : ClTower B n) * vecOp F₂₃ F₃₁ (-F₁₂) *
      fiberEmbed (↑g⁻¹ : ClTower B n) ∧
    ymFieldStrength d₁ d₂ (zornGaugeTransform g d₁ 0) (zornGaugeTransform g d₂ 0) = 0 := by
  intro D₁ D₂ D₃ F₂₃ F₃₁ F₁₂ A₁_g A₂_g A₃_g F₂₃_g F₃₁_g F₁₂_g D_cov
  have h_ym_eq : ∀ {x₁ x₂ : ClTower B n} (y₁ y₂ : ClTower B n), ⁅x₁, x₂⁆ = 0 →
      ymFieldStrength x₁ x₂ y₁ y₂ = ⁅x₁ + y₁, x₂ + y₂⁆ := by
    intro x₁ x₂ y₁ y₂ hx
    dsimp [ymFieldStrength]
    rw [← zero_add (⁅x₁, y₂⁆ - ⁅x₂, y₁⁆ + ⁅y₁, y₂⁆), ← hx]
    simp only [Ring.lie_def]; noncomm_ring
  have hF23 : F₂₃ = ⁅D₂, D₃⁆ := h_ym_eq A₂ A₃ h23
  have hF31 : F₃₁ = ⁅D₃, D₁⁆ := h_ym_eq A₃ A₁ h31
  have hF12 : F₁₂ = ⁅D₁, D₂⁆ := h_ym_eq A₁ A₂ h12
  have hF23_g : F₂₃_g = (g : ClTower B n) * F₂₃ * (↑g⁻¹ : ClTower B n) := by
    dsimp [F₂₃_g]; rw [h_ym_eq A₂_g A₃_g h23, hF23,
      cov_shift_conj g d₂ A₂, cov_shift_conj g d₃ A₃, comm_conj_units g D₂ D₃]
  have hF31_g : F₃₁_g = (g : ClTower B n) * F₃₁ * (↑g⁻¹ : ClTower B n) := by
    dsimp [F₃₁_g]; rw [h_ym_eq A₃_g A₁_g h31, hF31,
      cov_shift_conj g d₃ A₃, cov_shift_conj g d₁ A₁, comm_conj_units g D₃ D₁]
  have hF12_g : F₁₂_g = (g : ClTower B n) * F₁₂ * (↑g⁻¹ : ClTower B n) := by
    dsimp [F₁₂_g]; rw [h_ym_eq A₁_g A₂_g h12, hF12,
      cov_shift_conj g d₁ A₁, cov_shift_conj g d₂ A₂, comm_conj_units g D₁ D₂]
  have h_add_emb : ∀ (a b : ClTower B n), fiberEmbed a + fiberEmbed b = fiberEmbed (a + b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_mul_emb : ∀ (a b : ClTower B n), fiberEmbed a * fiberEmbed b = fiberEmbed (a * b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_neg_emb : ∀ (a : ClTower B n), fiberEmbed (-a) = -fiberEmbed a := by
    intro a; apply ext_fin2 <;> simp [fiberEmbed]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [bareDiracZornTower, diracZornTower, sheetDiagTower, fiberEmbed] <;>
      noncomm_ring
  · rw [hF23, hF31, hF12]
    apply ext_fin2
    · simp only [D_cov, bareDiracZornTower, diracZornTower, mul2_00, mat2_00, mat2_01, mat2_10,
        h_mul_emb, zorn_vec_sq D₁ D₂ D₃, ← add_assoc, h_add_emb]
    · simp only [D_cov, bareDiracZornTower, diracZornTower, mul2_01, mat2_00, mat2_01, mat2_11,
        h_neg_emb, mul_neg, Ring.lie_def, sub_eq_add_neg]
    · simp only [D_cov, bareDiracZornTower, diracZornTower, mul2_10, mat2_10, mat2_00, mat2_11,
        h_neg_emb, neg_mul, Ring.lie_def]
      abel
    · simp only [D_cov, bareDiracZornTower, diracZornTower, mul2_11, mat2_10, mat2_01, mat2_11,
        h_neg_emb, neg_mul_neg, h_mul_emb]
      rw [add_comm (vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃),
          zorn_vec_sq D₁ D₂ D₃, ← add_assoc, h_add_emb]
  · rw [hF23, hF31, hF12]
    simp only [Ring.lie_def]
    noncomm_ring
  · rw [hF23_g, hF31_g, hF12_g]
    apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring
  · rw [h_ym_eq _ _ h12, cov_shift_conj g d₁ 0, cov_shift_conj g d₂ 0,
        add_zero, add_zero, comm_conj_units g d₁ d₂, h12, mul_zero, zero_mul]

end ArchetypeUZ2_UZ3_UZ4_AllScalesZornGaugeTower

end InfoGeometry.Algebra.NoncommutativeUnifiedDiracHiggsZornTower
