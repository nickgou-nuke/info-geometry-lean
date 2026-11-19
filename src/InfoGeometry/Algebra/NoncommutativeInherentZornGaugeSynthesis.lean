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
# Noncommutative Matrix-Encoding Gauge Identities ($\mathcal{G}\mathcal{Z}_1$–$\mathcal{G}\mathcal{Z}_4$)

Reuses `InfoGeometry.Algebra.NoncommutativeCliffordPrimitives` (`mat2`, `ext_fin2`,
`fiberEmbed`) and `InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis`
(`NestedMat`, `vecOp`, `zornCross1`, `zornCross2`, `zornCross3`, `diracZornOp`) over an
arbitrary associative ring `[Ring B]` to formalize finite matrix identities. Here `vecOp` is
an encoding into an associative matrix algebra; it is not the repository's native
nonassociative Zorn product. “Inherent gauge” is interpretive: these theorems describe
specified commutators and unit conjugations, and do not construct a geometric connection or
differential calculus from the algebra alone. The module formalizes:

1. **$\mathcal{G}\mathcal{Z}_1$** (`inherent_gauge_higgs_from_inner_commutator`):
   Inner commutator $\⁅\mathcal{D}_0(m_0, \mathbf{d}), \mathbb{U}(u, v)⁆$ populates
   off-diagonal 3-vector gauge 1-forms and diagonal Higgs shifts, and shifting
   $d_k \mapsto d_k + A_k$ splits `bareDiracZorn` additively.
2. **$\mathcal{G}\mathcal{Z}_2$** (`zorn_cross_product_is_yang_mills_curvature_and_bianchi`):
   When $\⁅d_i, d_j⁆ = 0$, the Zorn cross product of $\mathbf{d} + \mathbf{A}$ equals
   the non-Abelian Yang–Mills field strength $(F_{23}, F_{31}, -F_{12})$ and satisfies
   the exact non-Abelian Bianchi identity.
3. **$\mathcal{G}\mathcal{Z}_3$ & $\mathcal{G}\mathcal{Z}_4$**
   (`zorn_gauge_covariance_and_maurer_cartan_flatness`):
   Conjugation by $\mathbb{G}(g) = \mathrm{diag}(\iota(g), \iota(g))$ ($g \in B^\times$)
   induces the affine gauge transformation $A_k^g = g(d_k + A_k)g^{-1} - d_k$, homogeneous
   conjugation covariance of $F_{ij}$ and $\mathrm{vecOp}(\mathbf{F})$, and Maurer–Cartan
   pure-gauge flatness for each of the three flat reference pairs.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis

namespace InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis

/-!
## Archetype $\mathcal{G}\mathcal{Z}_1$: Inherent Emergence of Gauge & Higgs Potentials as Inner Commutators
-/

section ArchetypeGZ1_InherentGaugeFromInnerCommutator

variable {B : Type*} [Ring B]

/-- Bare un-gauged Dirac–Zorn operator $\mathcal{D}_0(m_0, d_1, d_2, d_3)$. -/
def bareDiracZorn (m₀ d₁ d₂ d₃ : B) : NestedMat B :=
  diracZornOp m₀ (-m₀) d₁ d₂ d₃ d₁ d₂ d₃

/-- Diagonal two-sheet algebra element $\mathbb{U}(u, v) = \mathrm{diag}(\iota(u), \iota(v))$. -/
def sheetDiag (u v : B) : NestedMat B :=
  mat2 (fiberEmbed u) 0 0 (fiberEmbed v)

/-- **Inherent Emergence of Zorn Gauge & Higgs Potentials ($\mathcal{G}\mathcal{Z}_1$)**:
1. The inner commutator $\⁅\mathcal{D}_0(m_0, \mathbf{d}), \mathbb{U}(u, v)⁆$ populates
   the off-diagonal Zorn vector slots with $d_k v - u d_k$ and the diagonal slots with
   $\⁅m_0, u⁆, -\⁅m_0, v⁆$.
2. Shifting $d_k \mapsto d_k + A_k$ splits the covariant Dirac–Zorn operator additively into
   $\mathcal{D}_0(m_0, \mathbf{d}) + \mathcal{D}_{\mathrm{Zorn}}(0, 0, \mathbf{A}, \mathbf{A})$. -/
theorem inherent_gauge_higgs_from_inner_commutator
    (m₀ d₁ d₂ d₃ u v A₁ A₂ A₃ : B) :
    ⁅bareDiracZorn m₀ d₁ d₂ d₃, sheetDiag u v⁆ =
      diracZornOp ⁅m₀, u⁆ (-⁅m₀, v⁆)
        (d₁ * v - u * d₁) (d₂ * v - u * d₂) (d₃ * v - u * d₃)
        (d₁ * u - v * d₁) (d₂ * u - v * d₂) (d₃ * u - v * d₃) ∧
    bareDiracZorn m₀ (d₁ + A₁) (d₂ + A₂) (d₃ + A₃) =
      bareDiracZorn m₀ d₁ d₂ d₃ + diracZornOp 0 0 A₁ A₂ A₃ A₁ A₂ A₃ := by
  simp only [Ring.lie_def]
  refine ⟨?_, ?_⟩
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [bareDiracZorn, diracZornOp, sheetDiag, fiberEmbed] <;>
      noncomm_ring
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [bareDiracZorn, diracZornOp, fiberEmbed] <;>
      abel

end ArchetypeGZ1_InherentGaugeFromInnerCommutator

/-!
## Archetype $\mathcal{G}\mathcal{Z}_2$: Zorn Cross Product as Non-Abelian Yang–Mills Field Strength
-/

section ArchetypeGZ2_ZornCrossProductYangMills

variable {B : Type*} [Ring B]

/-- Non-Abelian Yang–Mills field strength component
$F_{ij}(\mathbf{d}, \mathbf{A}) = \⁅d_i, A_j⁆ - \⁅d_j, A_i⁆ + \⁅A_i, A_j⁆$. -/
def ymFieldStrength (dᵢ dⱼ Aᵢ Aⱼ : B) : B :=
  ⁅dᵢ, Aⱼ⁆ - ⁅dⱼ, Aᵢ⁆ + ⁅Aᵢ, Aⱼ⁆

/-- Expanding the commutator of two covariant shifts separates background
curvature from the Yang--Mills field-strength term. The coefficient order is
retained, so no commutativity assumption is needed. -/
theorem covariant_commutator_eq_background_add_ymFieldStrength
    (dᵢ dⱼ Aᵢ Aⱼ : B) :
    ⁅dᵢ + Aᵢ, dⱼ + Aⱼ⁆ =
      ⁅dᵢ, dⱼ⁆ + ymFieldStrength dᵢ dⱼ Aᵢ Aⱼ := by
  simp only [ymFieldStrength, Ring.lie_def]
  noncomm_ring

/-- **Zorn Cross Product as Yang–Mills Field Strength & Non-Abelian Bianchi Theorem ($\mathcal{G}\mathcal{Z}_2$)**:
1. $\⁅d_1 + A_1, d_2 + A_2⁆ = \⁅d_1, d_2⁆ + F_{12}(\mathbf{d}, \mathbf{A})$.
2. When $\⁅d_i, d_j⁆ = 0$, $\mathrm{vecOp}(\mathrm{zornCross}(\mathbf{d} + \mathbf{A}, \mathbf{d} + \mathbf{A}))$
   equals $\mathrm{vecOp}(F_{23}, F_{31}, -F_{12})$.
3. Exact non-Abelian Bianchi identity: $\⁅D_1, F_{23}⁆ + \⁅D_2, F_{31}⁆ + \⁅D_3, F_{12}⁆ = 0$. -/
theorem zorn_cross_product_is_yang_mills_curvature_and_bianchi
    (d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁  := d₁ + A₁
    let D₂  := d₂ + A₂
    let D₃  := d₃ + A₃
    let F₂₃ := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁ := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂ := ymFieldStrength d₁ d₂ A₁ A₂
    ⁅D₁, D₂⁆ = ⁅d₁, d₂⁆ + F₁₂ ∧
    vecOp (zornCross1 D₁ D₂ D₃ D₁ D₂ D₃)
          (zornCross2 D₁ D₂ D₃ D₁ D₂ D₃)
          (zornCross3 D₁ D₂ D₃ D₁ D₂ D₃) =
      vecOp F₂₃ F₃₁ (-F₁₂) ∧
    ⁅D₁, F₂₃⁆ + ⁅D₂, F₃₁⁆ + ⁅D₃, F₁₂⁆ = 0 := by
  intro D₁ D₂ D₃ F₂₃ F₃₁ F₁₂
  have h_decomp : ∀ (x₁ x₂ y₁ y₂ : B),
      ⁅x₁ + y₁, x₂ + y₂⁆ = ⁅x₁, x₂⁆ + ymFieldStrength x₁ x₂ y₁ y₂ := by
    intro x₁ x₂ y₁ y₂
    exact covariant_commutator_eq_background_add_ymFieldStrength x₁ x₂ y₁ y₂
  have hF23 : F₂₃ = ⁅D₂, D₃⁆ := by
    have h := h_decomp d₂ d₃ A₂ A₃; rw [h23, zero_add] at h; exact h.symm
  have hF31 : F₃₁ = ⁅D₃, D₁⁆ := by
    have h := h_decomp d₃ d₁ A₃ A₁; rw [h31, zero_add] at h; exact h.symm
  have hF12 : F₁₂ = ⁅D₁, D₂⁆ := by
    have h := h_decomp d₁ d₂ A₁ A₂; rw [h12, zero_add] at h; exact h.symm
  refine ⟨h_decomp d₁ d₂ A₁ A₂, ?_, ?_⟩
  · rw [hF23, hF31, hF12]
    rfl
  · rw [hF23, hF31, hF12]
    simp only [Ring.lie_def]
    noncomm_ring

end ArchetypeGZ2_ZornCrossProductYangMills

/-!
## Archetypes $\mathcal{G}\mathcal{Z}_3$ & $\mathcal{G}\mathcal{Z}_4$: Affine Gauge Transformation, Curvature Covariance & Maurer–Cartan Flatness
-/

section ArchetypeGZ3_GZ4_GaugeCovarianceAndMaurerCartan

variable {B : Type*} [Ring B]

/-- Inherent affine gauge transformation of a Zorn vector potential:
$A_k^g = g (d_k + A_k) g^{-1} - d_k$. -/
def zornGaugeTransform (g : Bˣ) (dₖ Aₖ : B) : B :=
  (g : B) * (dₖ + Aₖ) * (↑g⁻¹ : B) - dₖ

lemma cov_shift_conj (g : Bˣ) (dₖ Aₖ : B) :
    dₖ + zornGaugeTransform g dₖ Aₖ = (g : B) * (dₖ + Aₖ) * (↑g⁻¹ : B) := by
  dsimp [zornGaugeTransform]; abel

lemma comm_conj_units (g : Bˣ) (X Y : B) :
    ⁅(g : B) * X * (↑g⁻¹ : B), (g : B) * Y * (↑g⁻¹ : B)⁆ =
      (g : B) * ⁅X, Y⁆ * (↑g⁻¹ : B) := by
  have hg : (↑g⁻¹ : B) * (g : B) = 1 := Units.inv_mul g
  rw [Ring.lie_def, Ring.lie_def]
  calc (g : B) * X * (↑g⁻¹ : B) * ((g : B) * Y * (↑g⁻¹ : B)) -
       (g : B) * Y * (↑g⁻¹ : B) * ((g : B) * X * (↑g⁻¹ : B))
    _ = (g : B) * X * ((↑g⁻¹ : B) * (g : B)) * Y * (↑g⁻¹ : B) -
        (g : B) * Y * ((↑g⁻¹ : B) * (g : B)) * X * (↑g⁻¹ : B) := by noncomm_ring
    _ = (g : B) * (X * Y - Y * X) * (↑g⁻¹ : B) := by rw [hg]; noncomm_ring

/-- **Inherent Zorn Gauge Covariance & Maurer–Cartan Vacuum Flatness Theorem ($\mathcal{G}\mathcal{Z}_3$ & $\mathcal{G}\mathcal{Z}_4$)**:
For any invertible $g \in B^\times$ and flat reference derivatives ($\⁅d_i, d_j⁆ = 0$):
1. Conjugating $\mathcal{D}_0(m, \mathbf{d}+\mathbf{A})$ by $\mathrm{diag}(\iota(g), \iota(g))$
   transforms $m \mapsto g m g^{-1}$ and $A_k \mapsto A_k^g$.
2. Homogeneous adjoint covariance: $F_{12}^g = g F_{12} g^{-1}$ and
   $\mathrm{vecOp}(F_{23}^g, F_{31}^g, -F_{12}^g) = \iota(g)\,\mathrm{vecOp}(F_{23}, F_{31}, -F_{12})\,\iota(g^{-1})$.
3. Maurer–Cartan pure-gauge flatness for each of the three flat reference pairs. -/
theorem zorn_gauge_covariance_and_maurer_cartan_flatness
    (g : Bˣ) (m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let A₁_g := zornGaugeTransform g d₁ A₁
    let A₂_g := zornGaugeTransform g d₂ A₂
    let A₃_g := zornGaugeTransform g d₃ A₃
    let m_g  := (g : B) * m * (↑g⁻¹ : B)
    let F₂₃   := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁   := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂   := ymFieldStrength d₁ d₂ A₁ A₂
    let F₂₃_g := ymFieldStrength d₂ d₃ A₂_g A₃_g
    let F₃₁_g := ymFieldStrength d₃ d₁ A₃_g A₁_g
    let F₁₂_g := ymFieldStrength d₁ d₂ A₁_g A₂_g
    sheetDiag (g : B) (g : B) *
      bareDiracZorn m (d₁ + A₁) (d₂ + A₂) (d₃ + A₃) *
      sheetDiag (↑g⁻¹ : B) (↑g⁻¹ : B) =
      bareDiracZorn m_g (d₁ + A₁_g) (d₂ + A₂_g) (d₃ + A₃_g) ∧
    F₁₂_g = (g : B) * F₁₂ * (↑g⁻¹ : B) ∧
    vecOp F₂₃_g F₃₁_g (-F₁₂_g) =
      fiberEmbed (g : B) * vecOp F₂₃ F₃₁ (-F₁₂) * fiberEmbed (↑g⁻¹ : B) ∧
    ymFieldStrength d₂ d₃ (zornGaugeTransform g d₂ 0) (zornGaugeTransform g d₃ 0) = 0 ∧
    ymFieldStrength d₃ d₁ (zornGaugeTransform g d₃ 0) (zornGaugeTransform g d₁ 0) = 0 ∧
    ymFieldStrength d₁ d₂ (zornGaugeTransform g d₁ 0) (zornGaugeTransform g d₂ 0) = 0 := by
  intro A₁_g A₂_g A₃_g m_g F₂₃ F₃₁ F₁₂ F₂₃_g F₃₁_g F₁₂_g
  have h_ym_eq : ∀ {x₁ x₂ : B} (y₁ y₂ : B), ⁅x₁, x₂⁆ = 0 →
      ymFieldStrength x₁ x₂ y₁ y₂ = ⁅x₁ + y₁, x₂ + y₂⁆ := by
    intro x₁ x₂ y₁ y₂ hx
    dsimp [ymFieldStrength]
    rw [← zero_add (⁅x₁, y₂⁆ - ⁅x₂, y₁⁆ + ⁅y₁, y₂⁆), ← hx]
    simp only [Ring.lie_def]
    noncomm_ring
  have hF23_g : F₂₃_g = (g : B) * F₂₃ * (↑g⁻¹ : B) := by
    dsimp [F₂₃_g, F₂₃]
    rw [h_ym_eq A₂_g A₃_g h23, h_ym_eq A₂ A₃ h23,
        cov_shift_conj g d₂ A₂, cov_shift_conj g d₃ A₃,
        comm_conj_units g (d₂ + A₂) (d₃ + A₃)]
  have hF31_g : F₃₁_g = (g : B) * F₃₁ * (↑g⁻¹ : B) := by
    dsimp [F₃₁_g, F₃₁]
    rw [h_ym_eq A₃_g A₁_g h31, h_ym_eq A₃ A₁ h31,
        cov_shift_conj g d₃ A₃, cov_shift_conj g d₁ A₁,
        comm_conj_units g (d₃ + A₃) (d₁ + A₁)]
  have hF12_g : F₁₂_g = (g : B) * F₁₂ * (↑g⁻¹ : B) := by
    dsimp [F₁₂_g, F₁₂]
    rw [h_ym_eq A₁_g A₂_g h12, h_ym_eq A₁ A₂ h12,
        cov_shift_conj g d₁ A₁, cov_shift_conj g d₂ A₂,
        comm_conj_units g (d₁ + A₁) (d₂ + A₂)]
  have hflat : ∀ {x y : B}, ⁅x, y⁆ = 0 →
      ymFieldStrength x y (zornGaugeTransform g x 0) (zornGaugeTransform g y 0) = 0 := by
    intro x y hxy
    rw [h_ym_eq _ _ hxy, cov_shift_conj g x 0, cov_shift_conj g y 0,
      add_zero, add_zero, comm_conj_units g x y, hxy, mul_zero, zero_mul]
  refine ⟨?_, hF12_g, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [sheetDiag, bareDiracZorn, diracZornOp, fiberEmbed,
            A₁_g, A₂_g, A₃_g, m_g, zornGaugeTransform] <;>
      noncomm_ring
  · rw [hF23_g, hF31_g, hF12_g]
    apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring
  · exact hflat h23
  · exact hflat h31
  · exact hflat h12

end ArchetypeGZ3_GZ4_GaugeCovarianceAndMaurerCartan

end InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis
