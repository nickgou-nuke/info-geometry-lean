/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.TwoSheetDiracMassEntropy
import InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
import InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis
import InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction
import InfoGeometry.Algebra.NoncommutativeDiracSheetMixingAndEntropyTower
import InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Noncommutative Kitaev 4-Majorana Fractionalization, Hexagonal Holonomy & Tower Projection

Pure noncommutative matrix/operator-algebraic formalization over an arbitrary
associative ring `[Ring B]`, without commutativity, centrality, or scalar-diagonal
assumptions. Reuses all shared primitives from `NoncommutativeCliffordPrimitives`,
`TwoSheetDiracMassEntropy`, `NoncommutativeCovariantDiracZornSynthesis`,
`NoncommutativeInherentZornGaugeSynthesis`, `NoncommutativeDiracSheetMixingAndEntropyTower`,
and `NoncommutativeKramersCompassHallSynthesis`.

Scope: the declarations below prove finite-stage matrix identities and
`B`-valued recursive trace formulas. They do not prove a thermal Hall
conductance, a topological index, or a physical quantization statement.

## Causal Poset of Archetypes
* `KM₁` — 4-Majorana fractionalization in `M₂(M₂(B))`: parity `kitaevGaugeD`,
  spin bilinears `S_α = b_α c`, commutation `[D, S_α] = 0`, bond factorization
  `S_α S_β = -b_α b_β`, and cubic identity `S₁ S₂ S₃ = -D`.
* `KM₂` — Non-Abelian vertex gauge covariance `W_hex(U^g) = g₁ W_hex(U) g₁⁻¹`
  and central `ℤ₂` invariance for `hexPlaquette`.
* `KM₃` — Bipartite Dirac–Zorn operator `kitaevHoneycombH = bareDiracZorn Δ_H K₁ K₂ K₃`:
  zero-field chiral anticommutation, squared curvature vs. quadratic gap at
  `K₁² + K₂² - K₃² = 0`, and sublattice supertrace sign flip.
* `KM₄` — All-scales projection splitting on `ClTower B (n + 1)`:
  `majoranaPlusProj + majoranaMinusProj = fullDiracModeProj` with
  `2 • towerTrace M_+ = towerTrace D_full = 2 • 1`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
open InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis
open InfoGeometry.Algebra.NoncommutativeDiracSheetMixingAndEntropyTower
open InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis

namespace InfoGeometry.Algebra.NoncommutativeKitaevMajoranaThermalHallSynthesis

/-! ## KM₁: 4-Majorana Fractionalization & Three-Spin Identity in `M₂(M₂(B))` -/

section ArchetypeKM1_KitaevMajoranaFractionalization

variable {B : Type*} [Ring B]

/-- Itinerant Majorana `c = Σ_outer` and bond Majoranas `b₁, b₂, b₃ ∈ M₂(M₂(B))`. -/
def majC : NestedMat B := mat2 0 (1 : Matrix (Fin 2) (Fin 2) B)
  (1 : Matrix (Fin 2) (Fin 2) B) 0
def majB1 : NestedMat B := mat2 0 (-1 : Matrix (Fin 2) (Fin 2) B)
  (1 : Matrix (Fin 2) (Fin 2) B) 0
def majB2 : NestedMat B := mat2 sigmaOp 0 0 (-sigmaOp)
def majB3 : NestedMat B := mat2 omegaOp 0 0 (-omegaOp)

/-- 4-Majorana parity volume operator `D_Kitaev = b₁ b₂ b₃ c`. -/
def kitaevGaugeD : NestedMat B := majB1 * majB2 * majB3 * majC

/-- Fractionalized spin bilinears `S_α = b_α c` (`α = 1, 2, 3`). -/
def kitaevSpin1 : NestedMat B := majB1 * majC
def kitaevSpin2 : NestedMat B := majB2 * majC
def kitaevSpin3 : NestedMat B := majB3 * majC

/-- The concrete nested matrices satisfy the split Clifford relations. -/
theorem kitaev_majorana_clifford_relations :
    (majC : NestedMat B) * majC = (1 : NestedMat B) ∧
    (majB1 : NestedMat B) * majB1 = -(1 : NestedMat B) ∧
    (majB2 : NestedMat B) * majB2 = (1 : NestedMat B) ∧
    (majB3 : NestedMat B) * majB3 = -(1 : NestedMat B) ∧
    majC * majB1 + majB1 * majC = (0 : NestedMat B) ∧
    majC * majB2 + majB2 * majC = (0 : NestedMat B) ∧
    majC * majB3 + majB3 * majC = (0 : NestedMat B) ∧
    majB1 * majB2 + majB2 * majB1 = (0 : NestedMat B) ∧
    majB1 * majB3 + majB3 * majB1 = (0 : NestedMat B) ∧
    majB2 * majB3 + majB3 * majB2 = (0 : NestedMat B) := by
  simp only [majC, majB1, majB2, majB3, sigmaOp, omegaOp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;> apply ext_fin2 <;>
      norm_num [mat2, Matrix.mul_apply, Fin.sum_univ_two])

/-- Explicit non-commutativity witness for `majC` and `majB1` when `2 ≠ 0`. -/
theorem kitaev_majorana_noncommuting [Nontrivial B] (hchar : (2 : B) ≠ 0) :
    let c : NestedMat B := majC
    let b1 : NestedMat B := majB1
    c * b1 ≠ b1 * c := by
  intro c b1 h
  have h00 := congrArg (fun M => M 0 0 0 0) h
  simp [c, b1, majC, majB1, mat2] at h00
  have htwo : (2 : B) = 0 := by
    calc
      (2 : B) = (1 : B) + 1 := by norm_num
      _ = (-1 : B) + 1 := congrArg (fun x : B => x + 1) h00
      _ = 0 := neg_add_cancel 1
  exact hchar htwo

/-- Explicit non-commutativity witness for `Matrix (Fin 2) (Fin 2) B` over any nontrivial ring. -/
theorem mat2_basis_noncommuting [Nontrivial B] :
    ∃ A C : Matrix (Fin 2) (Fin 2) B, A * C ≠ C * A := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], ?_⟩
  intro h
  have h01 := congrArg (fun M => M 0 1) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- **Kitaev 4-Majorana Fractionalization & Cubic Spin Identity (`KM₁`)**. -/
theorem kitaev_majorana_fractionalization_and_three_spin_identity :
    (kitaevGaugeD : NestedMat B) * kitaevGaugeD = 1 ∧
    ⁅(kitaevGaugeD : NestedMat B), (kitaevSpin1 : NestedMat B)⁆ = 0 ∧
    ⁅(kitaevGaugeD : NestedMat B), (kitaevSpin2 : NestedMat B)⁆ = 0 ∧
    ⁅(kitaevGaugeD : NestedMat B), (kitaevSpin3 : NestedMat B)⁆ = 0 ∧
    (kitaevSpin1 : NestedMat B) * kitaevSpin2 = -(majB1 * majB2) ∧
    (kitaevSpin2 : NestedMat B) * kitaevSpin3 = -(majB2 * majB3) ∧
    (kitaevSpin3 : NestedMat B) * kitaevSpin1 = -(majB3 * majB1) ∧
    (kitaevSpin1 : NestedMat B) * kitaevSpin2 * kitaevSpin3 = -kitaevGaugeD := by
  simp only [Ring.lie_def]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;> apply ext_fin2 <;>
      simp [kitaevGaugeD, kitaevSpin1, kitaevSpin2, kitaevSpin3,
            majC, majB1, majB2, majB3, sigmaOp, omegaOp])

end ArchetypeKM1_KitaevMajoranaFractionalization

/-! ## KM₂: Hexagonal Plaquette Holonomy & Non-Abelian / Central Gauge Invariance -/

section ArchetypeKM2_HexagonalVisonPlaquette

variable {R : Type*} [Ring R]

/-- Directed link gauge transformation `Uᵢⱼ^g = gᵢ Uᵢⱼ gⱼ⁻¹` for `gᵢ, gⱼ ∈ Rˣ`. -/
def linkGauge (gᵢ gⱼ : Rˣ) (Uᵢⱼ : R) : R :=
  (gᵢ : R) * Uᵢⱼ * (↑gⱼ⁻¹ : R)

/-- **Hexagonal Plaquette Gauge Covariance & Central Invariance (`KM₂`)**,
reusing `hexPlaquette` from `NoncommutativeKramersCompassHallSynthesis`. -/
theorem hexagonal_vison_plaquette_gauge_covariance_and_invariance
    (g₁ g₂ g₃ g₄ g₅ g₆ : Rˣ) (U₁₂ U₂₃ U₃₄ U₄₅ U₅₆ U₆₁ : R)
    (hg₁_cent : ∀ X : R, (g₁ : R) * X = X * (g₁ : R)) :
    let W_g := hexPlaquette
      (linkGauge g₁ g₂ U₁₂) (linkGauge g₂ g₃ U₂₃) (linkGauge g₃ g₄ U₃₄)
      (linkGauge g₄ g₅ U₄₅) (linkGauge g₅ g₆ U₅₆) (linkGauge g₆ g₁ U₆₁)
    let W_0 := hexPlaquette U₁₂ U₂₃ U₃₄ U₄₅ U₅₆ U₆₁
    W_g = (g₁ : R) * W_0 * (↑g₁⁻¹ : R) ∧
    W_g = W_0 := by
  intro W_g W_0
  have h2 : (↑g₂⁻¹ : R) * (g₂ : R) = 1 := Units.inv_mul g₂
  have h3 : (↑g₃⁻¹ : R) * (g₃ : R) = 1 := Units.inv_mul g₃
  have h4 : (↑g₄⁻¹ : R) * (g₄ : R) = 1 := Units.inv_mul g₄
  have h5 : (↑g₅⁻¹ : R) * (g₅ : R) = 1 := Units.inv_mul g₅
  have h6 : (↑g₆⁻¹ : R) * (g₆ : R) = 1 := Units.inv_mul g₆
  have h_cov : W_g = (g₁ : R) * W_0 * (↑g₁⁻¹ : R) := by
    dsimp [W_g, W_0, hexPlaquette, linkGauge]
    calc (g₁ : R) * U₁₂ * (↑g₂⁻¹ : R) * ((g₂ : R) * U₂₃ * (↑g₃⁻¹ : R)) *
         ((g₃ : R) * U₃₄ * (↑g₄⁻¹ : R)) * ((g₄ : R) * U₄₅ * (↑g₅⁻¹ : R)) *
         ((g₅ : R) * U₅₆ * (↑g₆⁻¹ : R)) * ((g₆ : R) * U₆₁ * (↑g₁⁻¹ : R))
      _ = (g₁ : R) * U₁₂ * ((↑g₂⁻¹ : R) * (g₂ : R)) * U₂₃ * ((↑g₃⁻¹ : R) * (g₃ : R)) *
          U₃₄ * ((↑g₄⁻¹ : R) * (g₄ : R)) * U₄₅ * ((↑g₅⁻¹ : R) * (g₅ : R)) *
          U₅₆ * ((↑g₆⁻¹ : R) * (g₆ : R)) * U₆₁ * (↑g₁⁻¹ : R) := by noncomm_ring
      _ = (g₁ : R) * (U₁₂ * U₂₃ * U₃₄ * U₄₅ * U₅₆ * U₆₁) * (↑g₁⁻¹ : R) := by
          rw [h2, h3, h4, h5, h6]; noncomm_ring
  refine ⟨h_cov, ?_⟩
  rw [h_cov, hg₁_cent W_0, mul_assoc, Units.mul_inv, mul_one]

end ArchetypeKM2_HexagonalVisonPlaquette

/-! ## KM₃: Bipartite Dirac–Zorn Cone, Quadratic Gap & Sublattice Trace Flip -/

section ArchetypeKM3_DiracConeMagneticGapAndThermalHall

variable {B : Type*} [Ring B]

/-- Bipartite Dirac–Zorn operator, reusing `bareDiracZorn` from
`NoncommutativeInherentZornGaugeSynthesis`. -/
abbrev kitaevHoneycombH (Δ_H K₁ K₂ K₃ : B) : NestedMat B :=
  bareDiracZorn Δ_H K₁ K₂ K₃

/-- Sublattice chirality grading `Γ_sub = diag(1, -1)` on `NestedMat B`. -/
def sublatticeGamma : NestedMat B := mat2 1 0 0 (-1)

/-- Sublattice chiral supertrace `Str_sub(M) = Tr₂(M₀₀) - Tr₂(M₁₁)`. -/
def sublatticeSuperTrace (𝕄 : NestedMat B) : B :=
  Matrix.trace (𝕄 0 0) - Matrix.trace (𝕄 1 1)

/-- Unconditional noncommutative square of the bipartite Dirac–Zorn operator.
The curvature commutators and mass-gradient commutators remain explicit; no
commutation assumptions on `m` or the three directions are imposed. -/
theorem kitaev_honeycomb_square_general (m K₁ K₂ K₃ : B) :
    kitaevHoneycombH m K₁ K₂ K₃ * kitaevHoneycombH m K₁ K₂ K₃ =
      mat2
        (fiberEmbed (m * m + (K₁ * K₁ + K₂ * K₂ - K₃ * K₃)) +
         vecOp ⁅K₂, K₃⁆ ⁅K₃, K₁⁆ (-⁅K₁, K₂⁆))
        ⁅fiberEmbed m, vecOp K₁ K₂ K₃⁆
        (-⁅fiberEmbed m, vecOp K₁ K₂ K₃⁆)
        (fiberEmbed (m * m + (K₁ * K₁ + K₂ * K₂ - K₃ * K₃)) +
         vecOp ⁅K₂, K₃⁆ ⁅K₃, K₁⁆ (-⁅K₁, K₂⁆)) := by
  have h_add_emb : ∀ (a b : B), fiberEmbed a + fiberEmbed b = fiberEmbed (a + b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_mul_emb : ∀ (a b : B), fiberEmbed a * fiberEmbed b = fiberEmbed (a * b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_vec_sq := (zorn_vector_product_dot_plus_cross 0 0 0 0 0 0 K₁ K₂ K₃).2
  apply ext_fin2
  · simp only [kitaevHoneycombH, bareDiracZorn, diracZornOp, mul2_00, mat2_00, mat2_01, mat2_10,
      h_mul_emb, h_vec_sq, ← add_assoc, h_add_emb]
  · simp only [kitaevHoneycombH, bareDiracZorn, diracZornOp, mul2_01, mat2_00, mat2_01, mat2_11,
      Ring.lie_def]
    apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring
  · simp only [kitaevHoneycombH, bareDiracZorn, diracZornOp, mul2_10, mat2_10, mat2_00, mat2_11,
      Ring.lie_def]
    apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring
  · simp only [kitaevHoneycombH, bareDiracZorn, diracZornOp, mul2_11, mat2_10, mat2_01, mat2_11,
      neg_mul_neg, h_mul_emb]
    rw [add_comm (vecOp K₁ K₂ K₃ * vecOp K₁ K₂ K₃),
        h_vec_sq, ← add_assoc, h_add_emb]

/-- **Dirac–Zorn Cone Gap & Sublattice Trace Sign Reversal (`KM₃`)**.
The trace is the finite block trace defined above; this theorem makes no
assertion about a thermal transport observable. -/
theorem kitaev_dirac_cone_mass_square_and_sublattice_trace_sign_flip
    (Δ_H K₁ K₂ K₃ : B)
    (h23 : ⁅K₂, K₃⁆ = 0) (h31 : ⁅K₃, K₁⁆ = 0) (h12 : ⁅K₁, K₂⁆ = 0)
    (hΔ1 : ⁅Δ_H, K₁⁆ = 0) (hΔ2 : ⁅Δ_H, K₂⁆ = 0) (hΔ3 : ⁅Δ_H, K₃⁆ = 0)
    (h_cone : K₁ * K₁ + K₂ * K₂ - K₃ * K₃ = 0) :
    let H_0 := kitaevHoneycombH 0 K₁ K₂ K₃
    let H_Δ := kitaevHoneycombH Δ_H K₁ K₂ K₃
    H_0 * sublatticeGamma + sublatticeGamma * H_0 = 0 ∧
    H_Δ * H_Δ =
      mat2
        (fiberEmbed (Δ_H * Δ_H + (K₁ * K₁ + K₂ * K₂ - K₃ * K₃)) +
         vecOp ⁅K₂, K₃⁆ ⁅K₃, K₁⁆ (-⁅K₁, K₂⁆))
        ⁅fiberEmbed Δ_H, vecOp K₁ K₂ K₃⁆
        (-⁅fiberEmbed Δ_H, vecOp K₁ K₂ K₃⁆)
        (fiberEmbed (Δ_H * Δ_H + (K₁ * K₁ + K₂ * K₂ - K₃ * K₃)) +
         vecOp ⁅K₂, K₃⁆ ⁅K₃, K₁⁆ (-⁅K₁, K₂⁆)) ∧
    H_0 * H_0 = 0 ∧
    H_Δ * H_Δ = mat2 (fiberEmbed (Δ_H * Δ_H)) 0 0 (fiberEmbed (Δ_H * Δ_H)) ∧
    sublatticeSuperTrace H_Δ = 4 • Δ_H ∧
    sublatticeSuperTrace (kitaevHoneycombH (-Δ_H) K₁ K₂ K₃) = -sublatticeSuperTrace H_Δ := by
  intro H_0 H_Δ
  have h_sq_gen (m : B) := kitaev_honeycomb_square_general m K₁ K₂ K₃
  have h_vec_zero : vecOp (0 : B) 0 0 = 0 := by
    apply ext_fin2 <;> simp
  have h_comm_Δ : ⁅fiberEmbed Δ_H, vecOp K₁ K₂ K₃⁆ = 0 := by
    have h_c : ⁅fiberEmbed Δ_H, vecOp K₁ K₂ K₃⁆ = vecOp ⁅Δ_H, K₁⁆ ⁅Δ_H, K₂⁆ ⁅Δ_H, K₃⁆ := by
      simp only [Ring.lie_def]
      apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring
    rw [h_c, hΔ1, hΔ2, hΔ3, h_vec_zero]
  have h_comm_0 : ⁅fiberEmbed (0 : B), vecOp K₁ K₂ K₃⁆ = 0 := by
    rw [Ring.lie_def]; apply ext_fin2 <;> simp [fiberEmbed]
  refine ⟨?_, h_sq_gen Δ_H, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [H_0, bareDiracZorn, diracZornOp, sublatticeGamma, fiberEmbed]
  · dsimp [H_0]
    rw [h_sq_gen 0]
    simp only [h23, h31, h12, h_cone, h_comm_0, neg_zero, add_zero, mul_zero, h_vec_zero]
    apply ext_fin2 <;> apply ext_fin2 <;> simp [fiberEmbed]
  · dsimp [H_Δ]
    rw [h_sq_gen Δ_H]
    simp only [h23, h31, h12, h_cone, h_comm_Δ, neg_zero, add_zero, h_vec_zero]
  · dsimp [sublatticeSuperTrace, H_Δ, kitaevHoneycombH, bareDiracZorn, diracZornOp, fiberEmbed]
    simp only [trace_fin2, mat2_00, mat2_11, nsmul_eq_mul, Nat.cast_ofNat]
    noncomm_ring
  · dsimp [sublatticeSuperTrace, H_Δ, kitaevHoneycombH, bareDiracZorn, diracZornOp, fiberEmbed]
    simp only [trace_fin2, mat2_00, mat2_11]
    abel

end ArchetypeKM3_DiracConeMagneticGapAndThermalHall

/-! ## KM₃ → SA₂: Covariant Kitaev operator and spectral action -/

section ArchetypeKM3SpectralActionIntertwining

variable {B : Type*} [Ring B]

/-- The covariant Kitaev Dirac–Zorn Hamiltonian inherits the quartic
Yang–Mills–Higgs trace decomposition from the existing spectral-action owner.
The reference directions satisfy flatness; gauge potentials and covariant
directions may be noncentral and mutually noncommuting. -/
theorem kitaev_covariant_honeycomb_quartic_trace_decomposition [StarRing B]
    (m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁ := d₁ + A₁
    let D₂ := d₂ + A₂
    let D₃ := d₃ + A₃
    let Δ := m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)
    let F₂₃ := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁ := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂ := ymFieldStrength d₁ d₂ A₁ A₂
    let H := kitaevHoneycombH m D₁ D₂ D₃
    InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction.trace4
        ((H ^ 2)ᴴ * H ^ 2) =
      4 • (star Δ * Δ +
        (star F₂₃ * F₂₃ + star F₃₁ * F₃₁ + star F₁₂ * F₁₂) +
        (star ⁅m, D₁⁆ * ⁅m, D₁⁆ +
         star ⁅m, D₂⁆ * ⁅m, D₂⁆ +
         star ⁅m, D₃⁆ * ⁅m, D₃⁆)) := by
  simpa [kitaevHoneycombH, bareDiracZorn] using
    (InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction.unified_yang_mills_higgs_dirac_spectral_action
      m d₁ d₂ d₃ A₁ A₂ A₃ h23 h31 h12)

end ArchetypeKM3SpectralActionIntertwining

/-! ## KM₄: All-Scales Chiral Projection Trace Splitting on `ClTower B n` -/

section ArchetypeKM4_HalfQuantizedMajoranaModes

universe u

variable {B : Type u} [Ring B]

private lemma towerTrace_zero_km : ∀ (n : ℕ), towerTrace (0 : ClTower B n) = 0
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace]
      rw [towerTrace_zero_km n, add_zero]

private lemma towerTrace_cantorProj_km : ∀ (n : ℕ),
    towerTrace (cantorProj n : ClTower B n) = 1
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace, cantorProj]
      rw [towerTrace_zero_km n, add_zero, towerTrace_cantorProj_km n]

/-- Full doubled mode projection `diag(cantorProj n, cantorProj n) ∈ ClTower B (n + 1)`. -/
def fullDiracModeProj (n : ℕ) : ClTower B (n + 1) :=
  mat2 (cantorProj n) 0 0 (cantorProj n)

/-- Orthogonal chiral Majorana mode projections in `ClTower B (n + 1)`. -/
def majoranaPlusProj (n : ℕ) : ClTower B (n + 1) :=
  mat2 (cantorProj n) 0 0 0

def majoranaMinusProj (n : ℕ) : ClTower B (n + 1) :=
  mat2 0 0 0 (cantorProj n)

/-- **All-Scales Chiral Projection Trace-Splitting Theorem (`KM₄`)**,
reusing `cantorProj` from `NoncommutativeDiracSheetMixingAndEntropyTower` and
`towerTrace` from `TwoSheetDiracMassEntropy`. The equation is in the recursively
defined `B`-valued trace and is not, by itself, a physical quantization claim. -/
theorem all_scales_chiral_projection_trace_split (n : ℕ) :
    let M_plus  := majoranaPlusProj (B := B) n
    let M_minus := majoranaMinusProj (B := B) n
    let D_full  := fullDiracModeProj (B := B) n
    M_plus + M_minus = D_full ∧
    M_plus * M_plus = M_plus ∧
    M_minus * M_minus = M_minus ∧
    M_plus * M_minus = 0 ∧
    M_minus * M_plus = 0 ∧
    D_full * D_full = D_full ∧
    towerTrace D_full = 2 • (1 : B) ∧
    towerTrace M_plus = 1 ∧
    towerTrace M_minus = 1 ∧
    2 • towerTrace M_plus = towerTrace D_full := by
  intro M_plus M_minus D_full
  have h_tr_P : towerTrace M_plus = (1 : B) := by
    dsimp [M_plus, majoranaPlusProj, towerTrace]
    rw [towerTrace_cantorProj_km n, towerTrace_zero_km n, add_zero]
  have h_tr_M : towerTrace M_minus = (1 : B) := by
    dsimp [M_minus, majoranaMinusProj, towerTrace]
    rw [towerTrace_zero_km n, towerTrace_cantorProj_km n, zero_add]
  have h_tr_D : towerTrace D_full = 2 • (1 : B) := by
    dsimp [D_full, fullDiracModeProj, towerTrace]
    rw [towerTrace_cantorProj_km n, two_smul]
  have h_proj : cantorProj (A := B) n * cantorProj (A := B) n = cantorProj (A := B) n :=
    cantorProj_idem (A := B) n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h_tr_D, h_tr_P, h_tr_M,
    by rw [h_tr_P, h_tr_D]⟩
  · apply ext_fin2 <;> simp [M_plus, M_minus, D_full,
      majoranaPlusProj, majoranaMinusProj, fullDiracModeProj]
  · apply ext_fin2 <;> simp [M_plus, majoranaPlusProj, h_proj]
  · apply ext_fin2 <;> simp [M_minus, majoranaMinusProj, h_proj]
  · apply ext_fin2 <;> simp [M_plus, M_minus, majoranaPlusProj, majoranaMinusProj]
  · apply ext_fin2 <;> simp [M_plus, M_minus, majoranaPlusProj, majoranaMinusProj]
  · apply ext_fin2 <;> simp [D_full, fullDiracModeProj, h_proj]

end ArchetypeKM4_HalfQuantizedMajoranaModes

end InfoGeometry.Algebra.NoncommutativeKitaevMajoranaThermalHallSynthesis
