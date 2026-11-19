/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Common `2I`/`A₅` Invariance of Klein's Icosahedral Forms, Level-One `j` Hauptmodul, & Quintic Galois Resolvent

This module closes all three gaps documented on `InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ`
and `InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent`:

1. **Common Literature `2I` / `A₅` Invariance of Klein's Icosahedral Triple `(F, H, T)`**:
   - Constructs `kleinAlignedIntertwiner := !![(1 : ℂ), 0; 0, -1] * kleinBinaryBasisChange`
     intertwining the actual generating matrices `(icosianGenA, icosianGenB)` of
     `binaryIcosahedralGroup ⊂ SU(2)` with `(kleinBinaryStandardGenA, kleinAlignedStandardGenB)`;
   - Proves exact `ℤ[φ]` polynomial covariance (`F(φ z₁ - z₂, -z₁ - φ z₂) = (φ² + 1)⁶ F`,
     `H(...) = (φ² + 1)¹⁰ H`, `T(...) = -(φ² + 1)¹⁵ T`) via a two-coordinate `ℤ[φ]` reduction;
   - Deduces that `(kleinIcosahedralVertexF, kleinIcosahedralFaceH, kleinIcosahedralEdgeT)`
     are strictly invariant under both standard generators, and proves that the aligned triple
     `(kleinAlignedVertexF, kleinAlignedFaceH, kleinAlignedEdgeT)` and `kleinAlignedRatio` are
     strictly invariant under **every** element of `binaryIcosahedralGroup` (`Subgroup.closure`)
     and descend to `icosahedralPSU2Subgroup ≃* alternatingGroup (Fin 5)`.
2. **Analytic Simple Cusp Pole & Canonical Level-One `j` Hauptmodul Theorem**:
   - Defines `jCuspFunction` on `Metric.ball 0 1`, proves `jInvariant z = jCuspFunction (qParam 1 z)`,
     holomorphicity on the punctured unit disc `Metric.ball 0 1 \ {0}`, the exact simple-pole
     limits `Tendsto (fun q => q * jCuspFunction q) (𝓝[≠] 0) (𝓝 1)` and
     `Tendsto (fun q => ‖jCuspFunction q‖) (𝓝[≠] 0) atTop`, and the `LaurentSeries ℂ` (`ℂ⸨X⸩`)
     principal part `jLaurentSeries.coeff (-1) = 1`;
   - Proves algebraic transcendence (`jInvariant_aeval_injective`, `normalizedJInvariant_aeval_injective`);
   - Proves the **Level-One Hauptmodul Polynomial Theorem** (`∀ n (g : ModularForm 𝒮ℒ (12 * n)),
     ∃! P : ℂ[X], P.natDegree ≤ n ∧ ∀ z, g z / Δ z ^ n = P.eval (jInvariant z)`) and the
     **Equal-Even-Weight Rational Generation Theorem** (`Q(j(z)) * g₁(z) = P(j(z)) * g₂(z)` for
     any `g₁, g₂ : ModularForm 𝒮ℒ (2 * m)` with `g₂ ≠ 0`, `Q ≠ 0`).
3. **Generic Quintic Galois Resolvent (`F₂₀` Sextic), Tschirnhaus Chain, & Radical Criterion**:
   - Constructs `frobenius20Subgroup : Subgroup (Equiv.Perm (Fin 5))` (`AGL(1, 𝔽₅)` of order `20`),
     proves `Nat.card frobenius20Subgroup = 20`, `Group.IsSolvable frobenius20Subgroup`, and
     `Nat.card ↥(frobenius20Subgroup ⊓ alternatingGroup (Fin 5)) = 10`;
   - Defines the `F₂₀`-invariant Cayley–Weber sextic resolvent polynomial `cayleyWeberSexticResolvent`,
     descends it unconditionally to `K[X]` for any separable quintic `P : K[X]` over a field `K`
     with splitting field `E`, and proves the **Galois Sextic Resolvent Theorem**:
     under generic distinctness of the 6 coset values, `R₆` has a root in `K` iff `Gal(E/K)`
     embeds into a conjugate of `F₂₀`, which implies `Group.IsSolvable Gal(E/K)` (and
     contrapositively `A₅ ≤ Gal(E/K) → ¬ ∃ α : K, R₆.eval α = 0`);
   - Proves the universal quadratic Tschirnhaus reduction from an arbitrary quintic to a
     Principal Quintic (`e₁ = e₂ = 0`), Brioschi rescaling (`Z = M⁵ / K²`), and splitting-field
     Galois group transfer under polynomial root maps.

Note on scope: Level-one modular forms `ModularForm 𝒮ℒ k` in Mathlib encode holomorphicity on
`ℍ` and holomorphicity at the cusp `∞`, so the Hauptmodul theorem is stated and proved natively
over `ModularForm 𝒮ℒ`, `cuspFunction`, and `LaurentSeries ℂ`, without requiring a scheme-theoretic
compactified modular curve `X(1)` not present in this checkout.

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

noncomputable section

open Complex Matrix UpperHalfPlane ModularForm ModularFormClass SlashInvariantForm CongruenceSubgroup
open Filter Set Metric Polynomial
open InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ
open InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
open scoped MatrixGroups Topology Polynomial HahnSeries

namespace InfoGeometry.Canonical.KleinIcosahedralHauptmodulAndGaloisResolvent

/-! ## Section 0: Noncommutativity Ground Witnesses (T16) -/

/-- Closed T16 noncommutativity witness on `Mat2C := Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem kleinClosure_mat2C_noncommutative :
    ∃ a b : Matrix (Fin 2) (Fin 2) ℂ, a * b ≠ b * a :=
  ⟨matQuatI, matQuatJ, matQuatI_mul_matQuatJ_ne⟩

/-- Closed T16 noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℤ`. -/
theorem kleinClosure_mat2Z_noncommutative :
    ∃ a b : Matrix (Fin 2) (Fin 2) ℤ, a * b ≠ b * a :=
  ⟨modularMatSZ, modularMatTZ, modularMatSZ_mul_modularMatTZ_ne⟩

/-! ## Section 1: Common Literature `2I` / `A₅` Invariance of Klein's Icosahedral Triple `(F, H, T)` -/

section AlignedIcosahedralInvariance

/-- Two-coordinate `ℤ[φ]` evaluation `p.1 + φ * p.2` (`φ² = φ + 1`), enabling exact bivariate
`ring` verification without high-degree `φ` expansion. -/
private def zphiEval {R : Type*} [CommRing R] (φ : R) (p : R × R) : R :=
  p.1 + φ * p.2

private def zphiAdd {R : Type*} [Add R] (p q : R × R) : R × R :=
  (p.1 + q.1, p.2 + q.2)

private def zphiSub {R : Type*} [Sub R] (p q : R × R) : R × R :=
  (p.1 - q.1, p.2 - q.2)

private def zphiNeg {R : Type*} [Neg R] (p : R × R) : R × R :=
  (-p.1, -p.2)

private def zphiScale {R : Type*} [Mul R] (c : R) (p : R × R) : R × R :=
  (c * p.1, c * p.2)

private def zphiMul {R : Type*} [CommRing R] (p q : R × R) : R × R :=
  (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1 + p.2 * q.2)

private lemma zphiEval_add {R : Type*} [CommRing R] (φ : R) (p q : R × R) :
    zphiEval φ (zphiAdd p q) = zphiEval φ p + zphiEval φ q := by
  simp only [zphiEval, zphiAdd]
  ring

private lemma zphiEval_sub {R : Type*} [CommRing R] (φ : R) (p q : R × R) :
    zphiEval φ (zphiSub p q) = zphiEval φ p - zphiEval φ q := by
  simp only [zphiEval, zphiSub]
  ring

private lemma zphiEval_neg {R : Type*} [CommRing R] (φ : R) (p : R × R) :
    zphiEval φ (zphiNeg p) = -zphiEval φ p := by
  simp only [zphiEval, zphiNeg]
  ring

private lemma zphiEval_scale {R : Type*} [CommRing R] (φ c : R) (p : R × R) :
    zphiEval φ (zphiScale c p) = c * zphiEval φ p := by
  simp only [zphiEval, zphiScale]
  ring

private lemma zphiEval_mul {R : Type*} [CommRing R] {φ : R} (hφ : φ ^ 2 = φ + 1)
    (p q : R × R) :
    zphiEval φ (zphiMul p q) = zphiEval φ p * zphiEval φ q := by
  simp only [zphiEval, zphiMul]
  linear_combination -(p.2 * q.2) * hφ

private lemma zphiEval_AB {R : Type*} [CommRing R] {φ : R} (hφ : φ ^ 2 = φ + 1) (z₁ z₂ : R) :
    (φ * z₁ - z₂) * (-z₁ - φ * z₂) =
      zphiEval φ (0, -z₁ ^ 2 - z₁ * z₂ + z₂ ^ 2) := by
  simp only [zphiEval]
  linear_combination -(z₁ * z₂) * hφ

private lemma goldenRatio_power_identities {R : Type*} [CommRing R] {φ : R}
    (hφ : φ ^ 2 = φ + 1) :
    φ ^ 2 = φ + 1 ∧ φ ^ 3 = 2 * φ + 1 ∧ φ ^ 4 = 3 * φ + 2 ∧
    φ ^ 5 = 5 * φ + 3 ∧ φ ^ 6 = 8 * φ + 5 ∧ φ ^ 7 = 13 * φ + 8 ∧
    φ ^ 8 = 21 * φ + 13 ∧ φ ^ 9 = 34 * φ + 21 ∧ φ ^ 10 = 55 * φ + 34 ∧
    φ ^ 11 = 89 * φ + 55 ∧ φ ^ 12 = 144 * φ + 89 := by
  have h2 : φ ^ 2 = φ + 1 := hφ
  have h3 : φ ^ 3 = 2 * φ + 1 := by
    calc
      φ ^ 3 = φ * φ ^ 2 := by ring
      _ = φ * (φ + 1) := by rw [h2]
      _ = 2 * φ + 1 := by
        calc
          φ * (φ + 1) = φ ^ 2 + φ := by ring
          _ = 2 * φ + 1 := by rw [h2]; ring
  have h4 : φ ^ 4 = 3 * φ + 2 := by rw [pow_succ, h3]; linear_combination 2 * h2
  have h5 : φ ^ 5 = 5 * φ + 3 := by rw [pow_succ, h4]; linear_combination 3 * h2
  have h6 : φ ^ 6 = 8 * φ + 5 := by rw [pow_succ, h5]; linear_combination 5 * h2
  have h7 : φ ^ 7 = 13 * φ + 8 := by rw [pow_succ, h6]; linear_combination 8 * h2
  have h8 : φ ^ 8 = 21 * φ + 13 := by rw [pow_succ, h7]; linear_combination 13 * h2
  have h9 : φ ^ 9 = 34 * φ + 21 := by rw [pow_succ, h8]; linear_combination 21 * h2
  have h10 : φ ^ 10 = 55 * φ + 34 := by rw [pow_succ, h9]; linear_combination 34 * h2
  have h11 : φ ^ 11 = 89 * φ + 55 := by rw [pow_succ, h10]; linear_combination 55 * h2
  have h12 : φ ^ 12 = 144 * φ + 89 := by rw [pow_succ, h11]; linear_combination 89 * h2
  exact ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

private lemma zphiEval_A5 {R : Type*} [CommRing R] {φ : R} (hφ : φ ^ 2 = φ + 1) (z₁ z₂ : R) :
    (φ * z₁ - z₂) ^ 5 =
      zphiEval φ
        (3 * z₁ ^ 5 - 10 * z₁ ^ 4 * z₂ + 10 * z₁ ^ 3 * z₂ ^ 2 -
            10 * z₁ ^ 2 * z₂ ^ 3 - z₂ ^ 5,
         5 * z₁ ^ 5 - 15 * z₁ ^ 4 * z₂ + 20 * z₁ ^ 3 * z₂ ^ 2 -
            10 * z₁ ^ 2 * z₂ ^ 3 + 5 * z₁ * z₂ ^ 4) := by
  simp only [zphiEval]
  linear_combination
    ((φ ^ 3 + φ ^ 2 + 2 * φ + 3) * z₁ ^ 5 +
      (-5 * φ ^ 2 - 5 * φ - 10) * z₁ ^ 4 * z₂ +
      (10 * φ + 10) * z₁ ^ 3 * z₂ ^ 2 - 10 * z₁ ^ 2 * z₂ ^ 3) * hφ

private lemma zphiEval_B5 {R : Type*} [CommRing R] {φ : R} (hφ : φ ^ 2 = φ + 1) (z₁ z₂ : R) :
    (-z₁ - φ * z₂) ^ 5 =
      zphiEval φ
        (-z₁ ^ 5 - 10 * z₁ ^ 3 * z₂ ^ 2 - 10 * z₁ ^ 2 * z₂ ^ 3 -
            10 * z₁ * z₂ ^ 4 - 3 * z₂ ^ 5,
         -5 * z₁ ^ 4 * z₂ - 10 * z₁ ^ 3 * z₂ ^ 2 - 20 * z₁ ^ 2 * z₂ ^ 3 -
            15 * z₁ * z₂ ^ 4 - 5 * z₂ ^ 5) := by
  simp only [zphiEval]
  linear_combination
    ((-φ ^ 3 - φ ^ 2 - 2 * φ - 3) * z₂ ^ 5 +
      (-5 * φ ^ 2 - 5 * φ - 10) * z₁ * z₂ ^ 4 +
      (-10 * φ - 10) * z₁ ^ 2 * z₂ ^ 3 - 10 * z₁ ^ 3 * z₂ ^ 2) * hφ

private lemma zphi_F_identity {R : Type*} [CommRing R] {φ : R} (hφ : φ ^ 2 = φ + 1)
    (z₁ z₂ : R) :
    kleinIcosahedralVertexF (φ * z₁ - z₂) (-z₁ - φ * z₂) =
      (φ ^ 2 + 1) ^ 6 * kleinIcosahedralVertexF z₁ z₂ := by
  let A5p : R × R :=
    (3 * z₁ ^ 5 - 10 * z₁ ^ 4 * z₂ + 10 * z₁ ^ 3 * z₂ ^ 2 - 10 * z₁ ^ 2 * z₂ ^ 3 - z₂ ^ 5,
     5 * z₁ ^ 5 - 15 * z₁ ^ 4 * z₂ + 20 * z₁ ^ 3 * z₂ ^ 2 - 10 * z₁ ^ 2 * z₂ ^ 3 + 5 * z₁ * z₂ ^ 4)
  let B5p : R × R :=
    (-z₁ ^ 5 - 10 * z₁ ^ 3 * z₂ ^ 2 - 10 * z₁ ^ 2 * z₂ ^ 3 - 10 * z₁ * z₂ ^ 4 - 3 * z₂ ^ 5,
     -5 * z₁ ^ 4 * z₂ - 10 * z₁ ^ 3 * z₂ ^ 2 - 20 * z₁ ^ 2 * z₂ ^ 3 - 15 * z₁ * z₂ ^ 4 - 5 * z₂ ^ 5)
  let ABp : R × R := (0, -z₁ ^ 2 - z₁ * z₂ + z₂ ^ 2)
  have hF_lhs : kleinIcosahedralVertexF (φ * z₁ - z₂) (-z₁ - φ * z₂) =
      zphiEval φ (zphiMul ABp
        (zphiSub (zphiAdd (zphiMul A5p A5p) (zphiScale 11 (zphiMul A5p B5p))) (zphiMul B5p B5p))) := by
    have h10A : (φ * z₁ - z₂) ^ 10 = zphiEval φ (zphiMul A5p A5p) := by
      rw [show (10 : ℕ) = 5 + 5 by norm_num, pow_add, zphiEval_A5 hφ, zphiEval_mul hφ]
    have h10B : (-z₁ - φ * z₂) ^ 10 = zphiEval φ (zphiMul B5p B5p) := by
      rw [show (10 : ℕ) = 5 + 5 by norm_num, pow_add, zphiEval_B5 hφ, zphiEval_mul hφ]
    have h55 : (φ * z₁ - z₂) ^ 5 * (-z₁ - φ * z₂) ^ 5 = zphiEval φ (zphiMul A5p B5p) := by
      rw [zphiEval_A5 hφ, zphiEval_B5 hφ, zphiEval_mul hφ]
    rw [zphiEval_mul hφ, zphiEval_sub, zphiEval_add, zphiEval_scale, ← zphiEval_AB hφ, ← h10A,
      ← h10B, ← h55]
    simp only [kleinIcosahedralVertexF]
    ring
  have hS6 : (φ ^ 2 + 1) ^ 6 = zphiEval φ (625, 1000) := by
    rcases goldenRatio_power_identities hφ with ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    have hbinom : (φ ^ 2 + 1) ^ 6 = φ ^ 12 + 6 * φ ^ 10 + 15 * φ ^ 8 +
        20 * φ ^ 6 + 15 * φ ^ 4 + 6 * φ ^ 2 + 1 := by ring
    rw [hbinom, h12, h10, h8, h6, h4, h2]
    simp only [zphiEval]
    ring
  have hF_rhs : (φ ^ 2 + 1) ^ 6 * kleinIcosahedralVertexF z₁ z₂ =
      zphiEval φ (625 * kleinIcosahedralVertexF z₁ z₂, 1000 * kleinIcosahedralVertexF z₁ z₂) := by
    rw [hS6]
    simp only [zphiEval]
    ring
  rw [hF_lhs, hF_rhs]
  congr 1
  rcases goldenRatio_power_identities hφ with ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  ext <;> simp only [A5p, B5p, ABp, zphiMul, zphiAdd, zphiSub, zphiScale, kleinIcosahedralVertexF] <;>
    ring

private lemma zphi_S_norm_five {R : Type*} [CommRing R] {φ : R} (hφ : φ ^ 2 = φ + 1) :
    (φ ^ 2 + 1) ^ 5 = zphiEval φ (175, 275) := by
  have h1 : (φ ^ 2 + 1) = zphiEval φ (2, 1) := by
    simp only [zphiEval]
    rw [hφ]
    ring
  have h2 := zphiEval_mul hφ (2, 1) (2, 1)
  have h3 := zphiEval_mul hφ (zphiMul (2, 1) (2, 1)) (2, 1)
  have h4 := zphiEval_mul hφ (zphiMul (zphiMul (2, 1) (2, 1)) (2, 1)) (2, 1)
  have h5 := zphiEval_mul hφ (zphiMul (zphiMul (zphiMul (2, 1) (2, 1)) (2, 1)) (2, 1)) (2, 1)
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one, h1, ← h2, ← h3, ← h4, ← h5]
  norm_num [zphiMul]

private lemma zphi_H10_pow {R : Type*} [CommRing R] {φ : R} (hφ : φ ^ 2 = φ + 1) :
    (φ ^ 2 + 1) ^ 10 = zphiEval φ (106250, 171875) := by
  have h5 := zphi_S_norm_five hφ
  have h10 : (φ ^ 2 + 1) ^ 10 = zphiEval φ (zphiMul (175, 275) (175, 275)) := by
    rw [show (10 : ℕ) = 5 + 5 by norm_num, pow_add, h5, zphiEval_mul hφ]
  rw [h10]
  norm_num [zphiMul]

private lemma zphi_H_identity {R : Type*} [CommRing R] {φ : R} (hφ : φ ^ 2 = φ + 1)
    (z₁ z₂ : R) :
    kleinIcosahedralFaceH (φ * z₁ - z₂) (-z₁ - φ * z₂) =
      (φ ^ 2 + 1) ^ 10 * kleinIcosahedralFaceH z₁ z₂ := by
  let A5p : R × R :=
    (3 * z₁ ^ 5 - 10 * z₁ ^ 4 * z₂ + 10 * z₁ ^ 3 * z₂ ^ 2 - 10 * z₁ ^ 2 * z₂ ^ 3 - z₂ ^ 5,
     5 * z₁ ^ 5 - 15 * z₁ ^ 4 * z₂ + 20 * z₁ ^ 3 * z₂ ^ 2 - 10 * z₁ ^ 2 * z₂ ^ 3 + 5 * z₁ * z₂ ^ 4)
  let B5p : R × R :=
    (-z₁ ^ 5 - 10 * z₁ ^ 3 * z₂ ^ 2 - 10 * z₁ ^ 2 * z₂ ^ 3 - 10 * z₁ * z₂ ^ 4 - 3 * z₂ ^ 5,
     -5 * z₁ ^ 4 * z₂ - 10 * z₁ ^ 3 * z₂ ^ 2 - 20 * z₁ ^ 2 * z₂ ^ 3 - 15 * z₁ * z₂ ^ 4 - 5 * z₂ ^ 5)
  let A10p : R × R := zphiMul A5p A5p
  let B10p : R × R := zphiMul B5p B5p
  let A5B5p : R × R := zphiMul A5p B5p
  have hA10 : (φ * z₁ - z₂) ^ 10 = zphiEval φ A10p := by
    rw [show (10 : ℕ) = 5 + 5 by norm_num, pow_add, zphiEval_A5 hφ, zphiEval_mul hφ]
  have hB10 : (-z₁ - φ * z₂) ^ 10 = zphiEval φ B10p := by
    rw [show (10 : ℕ) = 5 + 5 by norm_num, pow_add, zphiEval_B5 hφ, zphiEval_mul hφ]
  have hA5B5 : (φ * z₁ - z₂) ^ 5 * (-z₁ - φ * z₂) ^ 5 = zphiEval φ A5B5p := by
    rw [zphiEval_A5 hφ, zphiEval_B5 hφ, zphiEval_mul hφ]
  have hH_lhs : kleinIcosahedralFaceH (φ * z₁ - z₂) (-z₁ - φ * z₂) =
      zphiEval φ (zphiSub
        (zphiAdd (zphiNeg (zphiAdd (zphiMul A10p A10p) (zphiMul B10p B10p)))
          (zphiScale 228 (zphiSub (zphiMul A10p A5B5p) (zphiMul A5B5p B10p))))
        (zphiScale 494 (zphiMul A10p B10p))) := by
    simp only [zphiEval_sub, zphiEval_add, zphiEval_neg, zphiEval_scale, zphiEval_mul hφ,
      ← hA10, ← hB10, ← hA5B5]
    simp only [kleinIcosahedralFaceH]
    ring
  have hH_rhs : (φ ^ 2 + 1) ^ 10 * kleinIcosahedralFaceH z₁ z₂ =
      zphiEval φ (106250 * kleinIcosahedralFaceH z₁ z₂, 171875 * kleinIcosahedralFaceH z₁ z₂) := by
    rw [zphi_H10_pow hφ]
    simp only [zphiEval]
    ring
  rw [hH_lhs, hH_rhs]
  congr 1
  ext <;>
    simp only [A10p, B10p, A5B5p, A5p, B5p, zphiMul, zphiAdd, zphiSub, zphiNeg, zphiScale,
      kleinIcosahedralFaceH] <;> ring

private lemma zphi_S_norm_fifteen {R : Type*} [CommRing R] {φ : R} (hφ : φ ^ 2 = φ + 1) :
    (φ ^ 2 + 1) ^ 15 = zphiEval φ (65859375, 106562500) := by
  have h5 := zphi_S_norm_five hφ
  have h10 : (φ ^ 2 + 1) ^ 10 = zphiEval φ (zphiMul (175, 275) (175, 275)) := by
    rw [show (10 : ℕ) = 5 + 5 by norm_num, pow_add, h5, zphiEval_mul hφ]
  have h15 : (φ ^ 2 + 1) ^ 15 = zphiEval φ (zphiMul (zphiMul (175, 275) (175, 275)) (175, 275)) := by
    rw [show (15 : ℕ) = 10 + 5 by norm_num, pow_add, h10, h5, ← zphiEval_mul hφ]
  rw [h15]
  norm_num [zphiMul]

private lemma zphi_T_identity {R : Type*} [CommRing R] {φ : R} (hφ : φ ^ 2 = φ + 1)
    (z₁ z₂ : R) :
    kleinIcosahedralEdgeT (φ * z₁ - z₂) (-z₁ - φ * z₂) =
      -((φ ^ 2 + 1) ^ 15 * kleinIcosahedralEdgeT z₁ z₂) := by
  let A5p : R × R :=
    (3 * z₁ ^ 5 - 10 * z₁ ^ 4 * z₂ + 10 * z₁ ^ 3 * z₂ ^ 2 - 10 * z₁ ^ 2 * z₂ ^ 3 - z₂ ^ 5,
     5 * z₁ ^ 5 - 15 * z₁ ^ 4 * z₂ + 20 * z₁ ^ 3 * z₂ ^ 2 - 10 * z₁ ^ 2 * z₂ ^ 3 + 5 * z₁ * z₂ ^ 4)
  let B5p : R × R :=
    (-z₁ ^ 5 - 10 * z₁ ^ 3 * z₂ ^ 2 - 10 * z₁ ^ 2 * z₂ ^ 3 - 10 * z₁ * z₂ ^ 4 - 3 * z₂ ^ 5,
     -5 * z₁ ^ 4 * z₂ - 10 * z₁ ^ 3 * z₂ ^ 2 - 20 * z₁ ^ 2 * z₂ ^ 3 - 15 * z₁ * z₂ ^ 4 - 5 * z₂ ^ 5)
  let A10p : R × R := zphiMul A5p A5p
  let B10p : R × R := zphiMul B5p B5p
  let A20p : R × R := zphiMul A10p A10p
  let B20p : R × R := zphiMul B10p B10p
  let A5B5p : R × R := zphiMul A5p B5p
  have hA10 : (φ * z₁ - z₂) ^ 10 = zphiEval φ A10p := by
    rw [show (10 : ℕ) = 5 + 5 by norm_num, pow_add, zphiEval_A5 hφ, zphiEval_mul hφ]
  have hB10 : (-z₁ - φ * z₂) ^ 10 = zphiEval φ B10p := by
    rw [show (10 : ℕ) = 5 + 5 by norm_num, pow_add, zphiEval_B5 hφ, zphiEval_mul hφ]
  have hA20 : (φ * z₁ - z₂) ^ 20 = zphiEval φ A20p := by
    rw [show (20 : ℕ) = 10 + 10 by norm_num, pow_add, hA10, ← zphiEval_mul hφ]
  have hB20 : (-z₁ - φ * z₂) ^ 20 = zphiEval φ B20p := by
    rw [show (20 : ℕ) = 10 + 10 by norm_num, pow_add, hB10, ← zphiEval_mul hφ]
  have hA5B5 : (φ * z₁ - z₂) ^ 5 * (-z₁ - φ * z₂) ^ 5 = zphiEval φ A5B5p := by
    rw [zphiEval_A5 hφ, zphiEval_B5 hφ, zphiEval_mul hφ]
  have hT_lhs : kleinIcosahedralEdgeT (φ * z₁ - z₂) (-z₁ - φ * z₂) =
      zphiEval φ (zphiSub
        (zphiAdd (zphiAdd (zphiMul A20p A10p) (zphiMul B20p B10p))
          (zphiScale 522 (zphiSub (zphiMul A20p A5B5p) (zphiMul A5B5p B20p))))
        (zphiScale 10005 (zphiAdd (zphiMul A20p B10p) (zphiMul A10p B20p)))) := by
    simp only [zphiEval_sub, zphiEval_add, zphiEval_scale, zphiEval_mul hφ,
      ← hA20, ← hB20, ← hA10, ← hB10, ← hA5B5]
    simp only [kleinIcosahedralEdgeT]
    ring
  have hT_rhs : -((φ ^ 2 + 1) ^ 15 * kleinIcosahedralEdgeT z₁ z₂) =
      zphiEval φ (-65859375 * kleinIcosahedralEdgeT z₁ z₂, -106562500 * kleinIcosahedralEdgeT z₁ z₂) := by
    rw [zphi_S_norm_fifteen hφ]
    simp only [zphiEval]
    ring
  exact hT_lhs.trans (by
    rw [hT_rhs]
    congr 1
    ext <;>
      simp only [A20p, B20p, A10p, B10p, A5B5p, A5p, B5p, zphiMul, zphiAdd, zphiSub, zphiScale,
        kleinIcosahedralEdgeT] <;> ring)

/-- Basis change matrix aligning `KleinIcosahedralQuinticModularJ`'s quaternion generators
`icosianGenA, icosianGenB` simultaneously with Klein's classical `(F, H, T)` invariants. -/
noncomputable def kleinAlignedIntertwiner : Mat2C :=
  !![(1 : ℂ), 0; 0, -1] * kleinBinaryBasisChange

/-- Image of `icosianGenB` under `kleinAlignedIntertwiner`. -/
noncomputable def kleinAlignedStandardGenB : Mat2C :=
  !![kleinBinaryStandardB_U * Complex.I, -kleinBinaryStandardB_V * Complex.I;
    -kleinBinaryStandardB_V * Complex.I, -kleinBinaryStandardB_U * Complex.I]

private lemma ext_mat2C_local {A B : Mat2C}
    (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem kleinAlignedIntertwiner_isUnit : IsUnit kleinAlignedIntertwiner := by
  have hdiag : IsUnit (!![(1 : ℂ), 0; 0, -1] : Mat2C) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    norm_num [Matrix.det_fin_two]
  exact hdiag.mul kleinBinaryBasisChange_isUnit

theorem icosianGenA_alignedIntertwining :
    kleinAlignedIntertwiner * (icosianGenA : Mat2C) =
      kleinBinaryStandardGenA * kleinAlignedIntertwiner := by
  have hA := icosianGenA_binaryBasisIntertwining
  have hcomm : !![(1 : ℂ), 0; 0, -1] * kleinBinaryStandardGenA =
      kleinBinaryStandardGenA * !![(1 : ℂ), 0; 0, -1] := by
    apply ext_mat2C_local <;>
      simp [kleinBinaryStandardGenA, Matrix.mul_apply, Fin.sum_univ_two]
  calc
    kleinAlignedIntertwiner * (icosianGenA : Mat2C) =
        !![(1 : ℂ), 0; 0, -1] * (kleinBinaryBasisChange * (icosianGenA : Mat2C)) :=
      Matrix.mul_assoc _ _ _
    _ = !![(1 : ℂ), 0; 0, -1] * (kleinBinaryStandardGenA * kleinBinaryBasisChange) := by rw [hA]
    _ = (!![(1 : ℂ), 0; 0, -1] * kleinBinaryStandardGenA) * kleinBinaryBasisChange :=
      (Matrix.mul_assoc _ _ _).symm
    _ = (kleinBinaryStandardGenA * !![(1 : ℂ), 0; 0, -1]) * kleinBinaryBasisChange := by
      rw [hcomm]
    _ = kleinBinaryStandardGenA * kleinAlignedIntertwiner := Matrix.mul_assoc _ _ _

theorem icosianGenB_alignedIntertwining :
    kleinAlignedIntertwiner * (icosianGenB : Mat2C) =
      kleinAlignedStandardGenB * kleinAlignedIntertwiner := by
  have hB := icosianGenB_binaryBasisIntertwining
  have hdiag : !![(1 : ℂ), 0; 0, -1] * kleinBinaryStandardGenB =
      kleinAlignedStandardGenB * !![(1 : ℂ), 0; 0, -1] := by
    apply ext_mat2C_local <;>
      simp [kleinBinaryStandardGenB, kleinAlignedStandardGenB, Matrix.mul_apply, Fin.sum_univ_two]
  calc
    kleinAlignedIntertwiner * (icosianGenB : Mat2C) =
        !![(1 : ℂ), 0; 0, -1] * (kleinBinaryBasisChange * (icosianGenB : Mat2C)) :=
      Matrix.mul_assoc _ _ _
    _ = !![(1 : ℂ), 0; 0, -1] * (kleinBinaryStandardGenB * kleinBinaryBasisChange) := by rw [hB]
    _ = (!![(1 : ℂ), 0; 0, -1] * kleinBinaryStandardGenB) * kleinBinaryBasisChange :=
      (Matrix.mul_assoc _ _ _).symm
    _ = (kleinAlignedStandardGenB * !![(1 : ℂ), 0; 0, -1]) * kleinBinaryBasisChange := by
      rw [hdiag]
    _ = kleinAlignedStandardGenB * kleinAlignedIntertwiner := Matrix.mul_assoc _ _ _

private lemma standardB_golden_relations :
    kleinBinaryStandardB_U = Real.goldenRatio * kleinBinaryStandardB_V ∧
      (Real.goldenRatio ^ 2 + 1) * kleinBinaryStandardB_V ^ 2 = 1 := by
  refine ⟨kleinBinaryStandardB_U_eq_goldenRatio_mul_V, ?_⟩
  calc
    (Real.goldenRatio ^ 2 + 1) * kleinBinaryStandardB_V ^ 2 =
        (Real.goldenRatio * kleinBinaryStandardB_V) ^ 2 + kleinBinaryStandardB_V ^ 2 := by
          ring
    _ = kleinBinaryStandardB_U ^ 2 + kleinBinaryStandardB_V ^ 2 := by
          rw [kleinBinaryStandardB_U_eq_goldenRatio_mul_V]
    _ = 1 := kleinBinaryStandardB_U_sq_add_V_sq

/-- Klein's canonical binary forms `(F, H, T)` are simultaneously fixed by BOTH the aligned
order-ten generator AND the aligned order-four generator in the same coordinate system. -/
theorem kleinBinaryForms_invariant_under_alignedGenB (z₁ z₂ : ℂ) :
    let w := kleinBinaryMatrixAction kleinAlignedStandardGenB (z₁, z₂)
    kleinIcosahedralVertexF w.1 w.2 = kleinIcosahedralVertexF z₁ z₂ ∧
      kleinIcosahedralFaceH w.1 w.2 = kleinIcosahedralFaceH z₁ z₂ ∧
      kleinIcosahedralEdgeT w.1 w.2 = kleinIcosahedralEdgeT z₁ z₂ := by
  dsimp only
  rcases standardB_golden_relations with ⟨hUV, hnorm⟩
  let φc : ℂ := (Real.goldenRatio : ℂ)
  let Vc : ℂ := (kleinBinaryStandardB_V : ℂ)
  let c : ℂ := Complex.I * Vc
  have hφc : φc ^ 2 = φc + 1 := by
    dsimp [φc]
    exact_mod_cast Real.goldenRatio_sq
  have hUVc : (kleinBinaryStandardB_U : ℂ) = φc * Vc := by
    dsimp [φc, Vc]
    exact_mod_cast hUV
  have hnormC : (φc ^ 2 + 1) * Vc ^ 2 = 1 := by
    dsimp [φc, Vc]
    exact_mod_cast hnorm
  have hw1 : (kleinBinaryMatrixAction kleinAlignedStandardGenB (z₁, z₂)).1 =
      c * (φc * z₁ - z₂) := by
    simp only [kleinBinaryMatrixAction, kleinAlignedStandardGenB, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, c, Vc]
    rw [hUVc]
    ring
  have hw2 : (kleinBinaryMatrixAction kleinAlignedStandardGenB (z₁, z₂)).2 =
      c * (-z₁ - φc * z₂) := by
    simp only [kleinBinaryMatrixAction, kleinAlignedStandardGenB, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, c, Vc]
    rw [hUVc]
    ring
  have hc2 : c ^ 2 = -Vc ^ 2 := by
    dsimp [c]
    calc
      (Complex.I * Vc) ^ 2 = Complex.I ^ 2 * Vc ^ 2 := by ring
      _ = (-1) * Vc ^ 2 := by rw [Complex.I_sq]
      _ = -Vc ^ 2 := by ring
  rw [hw1, hw2]
  refine ⟨?_, ?_, ?_⟩
  · rw [kleinIcosahedralVertexF_homog, zphi_F_identity hφc]
    have hc12 : c ^ 12 * (φc ^ 2 + 1) ^ 6 = 1 := by
      calc
        c ^ 12 * (φc ^ 2 + 1) ^ 6 = (c ^ 2) ^ 6 * (φc ^ 2 + 1) ^ 6 := by ring
        _ = (-Vc ^ 2) ^ 6 * (φc ^ 2 + 1) ^ 6 := by rw [hc2]
        _ = ((φc ^ 2 + 1) * Vc ^ 2) ^ 6 := by ring
        _ = 1 ^ 6 := by rw [hnormC]
        _ = 1 := one_pow 6
    calc
      c ^ 12 * ((φc ^ 2 + 1) ^ 6 * kleinIcosahedralVertexF z₁ z₂) =
          (c ^ 12 * (φc ^ 2 + 1) ^ 6) * kleinIcosahedralVertexF z₁ z₂ := by ring
      _ = kleinIcosahedralVertexF z₁ z₂ := by rw [hc12, one_mul]
  · rw [kleinIcosahedralFaceH_homog, zphi_H_identity hφc]
    have hc20 : c ^ 20 * (φc ^ 2 + 1) ^ 10 = 1 := by
      calc
        c ^ 20 * (φc ^ 2 + 1) ^ 10 = (c ^ 2) ^ 10 * (φc ^ 2 + 1) ^ 10 := by ring
        _ = (-Vc ^ 2) ^ 10 * (φc ^ 2 + 1) ^ 10 := by rw [hc2]
        _ = ((φc ^ 2 + 1) * Vc ^ 2) ^ 10 := by ring
        _ = 1 ^ 10 := by rw [hnormC]
        _ = 1 := one_pow 10
    calc
      c ^ 20 * ((φc ^ 2 + 1) ^ 10 * kleinIcosahedralFaceH z₁ z₂) =
          (c ^ 20 * (φc ^ 2 + 1) ^ 10) * kleinIcosahedralFaceH z₁ z₂ := by ring
      _ = kleinIcosahedralFaceH z₁ z₂ := by rw [hc20, one_mul]
  · rw [kleinIcosahedralEdgeT_homog, zphi_T_identity hφc]
    have hc30 : c ^ 30 * -((φc ^ 2 + 1) ^ 15) = 1 := by
      calc
        c ^ 30 * -((φc ^ 2 + 1) ^ 15) = -((c ^ 2) ^ 15 * (φc ^ 2 + 1) ^ 15) := by ring
        _ = -((-Vc ^ 2) ^ 15 * (φc ^ 2 + 1) ^ 15) := by rw [hc2]
        _ = ((φc ^ 2 + 1) * Vc ^ 2) ^ 15 := by ring
        _ = 1 ^ 15 := by rw [hnormC]
        _ = 1 := one_pow 15
    calc
      c ^ 30 * -((φc ^ 2 + 1) ^ 15 * kleinIcosahedralEdgeT z₁ z₂) =
          (c ^ 30 * -((φc ^ 2 + 1) ^ 15)) * kleinIcosahedralEdgeT z₁ z₂ := by ring
      _ = kleinIcosahedralEdgeT z₁ z₂ := by rw [hc30, one_mul]

/-- The aligned Klein icosahedral forms evaluated on the original `SU2` carrier via the single common
intertwiner `kleinAlignedIntertwiner`. -/
noncomputable def kleinAlignedVertexF (z₁ z₂ : ℂ) : ℂ :=
  let w := kleinBinaryMatrixAction kleinAlignedIntertwiner (z₁, z₂)
  kleinIcosahedralVertexF w.1 w.2

noncomputable def kleinAlignedFaceH (z₁ z₂ : ℂ) : ℂ :=
  let w := kleinBinaryMatrixAction kleinAlignedIntertwiner (z₁, z₂)
  kleinIcosahedralFaceH w.1 w.2

noncomputable def kleinAlignedEdgeT (z₁ z₂ : ℂ) : ℂ :=
  let w := kleinBinaryMatrixAction kleinAlignedIntertwiner (z₁, z₂)
  kleinIcosahedralEdgeT w.1 w.2

noncomputable def kleinAlignedRatio (z₁ z₂ : ℂ) : ℂ :=
  -(kleinAlignedFaceH z₁ z₂ ^ 3) / (kleinAlignedVertexF z₁ z₂ ^ 5)

noncomputable def kleinAlignedBrioschiParam (z₁ z₂ : ℂ) : ℂ :=
  kleinAlignedVertexF z₁ z₂ ^ 5 / kleinAlignedEdgeT z₁ z₂ ^ 2

theorem kleinAligned_syzygy_1728 (z₁ z₂ : ℂ) :
    kleinAlignedEdgeT z₁ z₂ ^ 2 + kleinAlignedFaceH z₁ z₂ ^ 3 =
      1728 * kleinAlignedVertexF z₁ z₂ ^ 5 :=
  klein_icosahedral_syzygy_1728 _ _

theorem kleinAligned_homog (c z₁ z₂ : ℂ) :
    kleinAlignedVertexF (c * z₁) (c * z₂) = c ^ 12 * kleinAlignedVertexF z₁ z₂ ∧
      kleinAlignedFaceH (c * z₁) (c * z₂) = c ^ 20 * kleinAlignedFaceH z₁ z₂ ∧
      kleinAlignedEdgeT (c * z₁) (c * z₂) = c ^ 30 * kleinAlignedEdgeT z₁ z₂ := by
  have hact : kleinBinaryMatrixAction kleinAlignedIntertwiner (c * z₁, c * z₂) =
      (c * (kleinBinaryMatrixAction kleinAlignedIntertwiner (z₁, z₂)).1,
       c * (kleinBinaryMatrixAction kleinAlignedIntertwiner (z₁, z₂)).2) := by
    apply Prod.ext <;> simp [kleinBinaryMatrixAction] <;> ring
  refine ⟨?_, ?_, ?_⟩ <;> simp only [kleinAlignedVertexF, kleinAlignedFaceH, kleinAlignedEdgeT, hact]
  · exact kleinIcosahedralVertexF_homog c _ _
  · exact kleinIcosahedralFaceH_homog c _ _
  · exact kleinIcosahedralEdgeT_homog c _ _

private lemma kleinBinaryMatrixAction_mul (A B : Mat2C) (z : ℂ × ℂ) :
    kleinBinaryMatrixAction (A * B) z =
      kleinBinaryMatrixAction A (kleinBinaryMatrixAction B z) := by
  apply Prod.ext <;> simp [kleinBinaryMatrixAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma kleinBinaryAction_eq_matrix (g : SU2) (z₁ z₂ : ℂ) :
    kleinBinaryAction g z₁ z₂ = kleinBinaryMatrixAction (g : Mat2C) (z₁, z₂) := rfl

private lemma kleinBinaryAction_one (z₁ z₂ : ℂ) :
    kleinBinaryAction (1 : SU2) z₁ z₂ = (z₁, z₂) := by
  apply Prod.ext <;> simp [kleinBinaryAction]

private lemma kleinBinaryAction_mul (g h : SU2) (z₁ z₂ : ℂ) :
    kleinBinaryAction (g * h) z₁ z₂ =
      kleinBinaryAction g (kleinBinaryAction h z₁ z₂).1 (kleinBinaryAction h z₁ z₂).2 := by
  rw [kleinBinaryAction_eq_matrix, kleinBinaryAction_eq_matrix, kleinBinaryAction_eq_matrix,
    Submonoid.coe_mul, kleinBinaryMatrixAction_mul]

/-- **Full Binary Icosahedral Invariance Theorem (`2I ⊂ SU(2)`)**:
Every element `g ∈ binaryIcosahedralGroup` (`Subgroup.closure {icosianGenA, icosianGenB}`) fixes all
three aligned Klein forms `(kleinAlignedVertexF, kleinAlignedFaceH, kleinAlignedEdgeT)`, the rational
ratio `kleinAlignedRatio`, and the Brioschi parameter `kleinAlignedBrioschiParam`. -/
theorem binaryIcosahedralGroup_invariant_alignedForms
    {g : SU2} (hg : g ∈ binaryIcosahedralGroup) (z₁ z₂ : ℂ) :
    let w := kleinBinaryAction g z₁ z₂
    kleinAlignedVertexF w.1 w.2 = kleinAlignedVertexF z₁ z₂ ∧
      kleinAlignedFaceH w.1 w.2 = kleinAlignedFaceH z₁ z₂ ∧
      kleinAlignedEdgeT w.1 w.2 = kleinAlignedEdgeT z₁ z₂ := by
  let invSub : Subgroup SU2 :=
    { carrier :=
        { k : SU2 | ∀ u₁ u₂ : ℂ,
            let w := kleinBinaryAction k u₁ u₂
            kleinAlignedVertexF w.1 w.2 = kleinAlignedVertexF u₁ u₂ ∧
              kleinAlignedFaceH w.1 w.2 = kleinAlignedFaceH u₁ u₂ ∧
              kleinAlignedEdgeT w.1 w.2 = kleinAlignedEdgeT u₁ u₂ }
      one_mem' := fun u₁ u₂ => by simp [kleinBinaryAction_one]
      mul_mem' := fun {a b} ha hb u₁ u₂ => by
        dsimp only
        rw [kleinBinaryAction_mul]
        have ha' := ha (kleinBinaryAction b u₁ u₂).1 (kleinBinaryAction b u₁ u₂).2
        have hb' := hb u₁ u₂
        exact ⟨ha'.1.trans hb'.1, ha'.2.1.trans hb'.2.1, ha'.2.2.trans hb'.2.2⟩
      inv_mem' := fun {k} hk u₁ u₂ => by
        dsimp only
        have hback : kleinBinaryAction k (kleinBinaryAction k⁻¹ u₁ u₂).1
            (kleinBinaryAction k⁻¹ u₁ u₂).2 = (u₁, u₂) := by
          rw [← kleinBinaryAction_mul, mul_inv_cancel, kleinBinaryAction_one]
        have hk' := hk (kleinBinaryAction k⁻¹ u₁ u₂).1 (kleinBinaryAction k⁻¹ u₁ u₂).2
        rw [hback] at hk'
        exact ⟨hk'.1.symm, hk'.2.1.symm, hk'.2.2.symm⟩ }
  have hle : binaryIcosahedralGroup ≤ invSub := by
    rw [binaryIcosahedralGroup, Subgroup.closure_le]
    rintro k (rfl | rfl) u₁ u₂
    · dsimp only [kleinAlignedVertexF, kleinAlignedFaceH, kleinAlignedEdgeT]
      rw [kleinBinaryAction_eq_matrix, ← kleinBinaryMatrixAction_mul,
        icosianGenA_alignedIntertwining, kleinBinaryMatrixAction_mul]
      let t := kleinBinaryMatrixAction kleinAlignedIntertwiner (u₁, u₂)
      have hA : kleinBinaryMatrixAction kleinBinaryStandardGenA t =
          (kleinBinaryStandardGenA 0 0 * t.1, kleinBinaryStandardGenA 1 1 * t.2) := by
        apply Prod.ext <;> simp [kleinBinaryMatrixAction, kleinBinaryStandardGenA]
      rw [hA]
      exact kleinBinaryForms_invariant_under_standardGenA t.1 t.2
    · dsimp only [kleinAlignedVertexF, kleinAlignedFaceH, kleinAlignedEdgeT]
      rw [kleinBinaryAction_eq_matrix, ← kleinBinaryMatrixAction_mul,
        icosianGenB_alignedIntertwining, kleinBinaryMatrixAction_mul]
      exact kleinBinaryForms_invariant_under_alignedGenB _ _
  exact hle hg z₁ z₂

theorem binaryIcosahedralGroup_invariant_ratio
    {g : SU2} (hg : g ∈ binaryIcosahedralGroup) (z₁ z₂ : ℂ) :
    let w := kleinBinaryAction g z₁ z₂
    kleinAlignedRatio w.1 w.2 = kleinAlignedRatio z₁ z₂ ∧
      kleinAlignedBrioschiParam w.1 w.2 = kleinAlignedBrioschiParam z₁ z₂ := by
  have h := binaryIcosahedralGroup_invariant_alignedForms hg z₁ z₂
  dsimp only [kleinAlignedRatio, kleinAlignedBrioschiParam] at h ⊢
  rw [h.1, h.2.1, h.2.2]
  exact ⟨rfl, rfl⟩

/-- Every element `σ ∈ alternatingGroup (Fin 5)` acts on binary rays via its projective
icosahedral representative `(kleinIcosahedralPSU2Embedding σ : PSU2)` and strictly preserves
`(kleinAlignedVertexF, kleinAlignedFaceH, kleinAlignedEdgeT, kleinAlignedRatio)`. -/
theorem alternatingGroup5_invariant_alignedForms
    (σ : alternatingGroup (Fin 5)) (z₁ z₂ : ℂ) :
    ∃ g : SU2, QuotientGroup.mk g = kleinIcosahedralPSU2Embedding σ ∧
      g ∈ binaryIcosahedralGroup ∧
      let w := kleinBinaryAction g z₁ z₂
      kleinAlignedVertexF w.1 w.2 = kleinAlignedVertexF z₁ z₂ ∧
        kleinAlignedFaceH w.1 w.2 = kleinAlignedFaceH z₁ z₂ ∧
        kleinAlignedEdgeT w.1 w.2 = kleinAlignedEdgeT z₁ z₂ ∧
        kleinAlignedRatio w.1 w.2 = kleinAlignedRatio z₁ z₂ := by
  have hmem : kleinIcosahedralPSU2Embedding σ ∈ icosahedralPSU2Subgroup :=
    (kleinIcosahedralMulEquiv σ).2
  rcases hmem with ⟨g, hg, hq⟩
  have hf := binaryIcosahedralGroup_invariant_alignedForms hg z₁ z₂
  have hr := binaryIcosahedralGroup_invariant_ratio hg z₁ z₂
  exact ⟨g, hq, hg, hf.1, hf.2.1, hf.2.2, hr.1⟩

end AlignedIcosahedralInvariance

/-! ## Section 2: Level-One `j`-Invariant Analytic Simple Pole, `LaurentSeries`, & Hauptmodul Theorem -/

section ModularJHauptmodul

/-- Analytic cusp-chart lift of `jInvariant` on the unit disc `Metric.ball 0 1`, defined on
`q = exp(2πi z)`. -/
noncomputable def jCuspFunction (q : ℂ) : ℂ :=
  cuspFunction 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) q ^ 3 /
    cuspFunction 1 CuspForm.discriminant q

theorem jInvariant_eq_jCuspFunction_qParam (z : ℍ) :
    jInvariant z = jCuspFunction (Function.Periodic.qParam 1 z) := by
  have h1ne : (1 : ℝ) ≠ 0 := one_ne_zero
  have hE : cuspFunction 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) (Function.Periodic.qParam 1 z) =
      ModularForm.E₄ z :=
    SlashInvariantFormClass.eq_cuspFunction (ModularForm.E₄ : ModularForm 𝒮ℒ 4) z
      one_mem_strictPeriods_SL h1ne
  have hD : cuspFunction 1 CuspForm.discriminant (Function.Periodic.qParam 1 z) =
      ModularForm.discriminant z :=
    SlashInvariantFormClass.eq_cuspFunction CuspForm.discriminant z
      one_mem_strictPeriods_SL h1ne
  rw [jInvariant, jCuspFunction, hE, hD]

private lemma cuspFunction_E4_zero :
    cuspFunction 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) 0 = 1 := by
  have h1 : (qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4)).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
  rwa [UpperHalfPlane.qExpansion_coeff, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
    iteratedDeriv_zero] at h1

private lemma cuspFunction_discriminant_zero :
    cuspFunction 1 CuspForm.discriminant 0 = 0 := by
  have h0 : (qExpansion 1 CuspForm.discriminant).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL
  rwa [UpperHalfPlane.qExpansion_coeff, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
    iteratedDeriv_zero] at h0

private lemma deriv_cuspFunction_discriminant_zero :
    deriv (cuspFunction 1 CuspForm.discriminant) 0 = 1 := by
  have h1 : (qExpansion 1 CuspForm.discriminant).coeff 1 = 1 :=
    ModularForm.discriminant_qExpansion_coeff_one
  rwa [UpperHalfPlane.qExpansion_coeff, Nat.factorial_one, Nat.cast_one, inv_one, one_mul,
    iteratedDeriv_one] at h1

/-- **Analytic Simple Pole at the Cusp `q = 0`**:
`q * jCuspFunction q → 1` as `q → 0` (`q ≠ 0`), and `‖jCuspFunction q‖ → +∞`, showing that
`jInvariant` extends meromorphically to the cusp with a literal first-order pole of residue `1`. -/
theorem jCuspFunction_tendsto_simple_pole :
    Tendsto (fun q : ℂ => q * jCuspFunction q) (𝓝[≠] 0) (𝓝 1) ∧
      Tendsto (fun q : ℂ => ‖jCuspFunction q‖) (𝓝[≠] 0) Filter.atTop := by
  have hD_diff : DifferentiableAt ℂ (cuspFunction 1 CuspForm.discriminant) 0 :=
    ModularFormClass.differentiableAt_cuspFunction CuspForm.discriminant
      one_pos one_mem_strictPeriods_SL (by simp)
  have hE_diff : DifferentiableAt ℂ (cuspFunction 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4)) 0 :=
    ModularFormClass.differentiableAt_cuspFunction (ModularForm.E₄ : ModularForm 𝒮ℒ 4)
      one_pos one_mem_strictPeriods_SL (by simp)
  have hD_hasDeriv : HasDerivAt (cuspFunction 1 CuspForm.discriminant) 1 0 := by
    rw [← deriv_cuspFunction_discriminant_zero]
    exact hD_diff.hasDerivAt
  have hslope : Tendsto (fun q : ℂ => cuspFunction 1 CuspForm.discriminant q / q) (𝓝[≠] 0) (𝓝 1) := by
    have hs := hD_hasDeriv.tendsto_slope_zero
    have hs' : Tendsto (fun q : ℂ => q⁻¹ * (cuspFunction 1 CuspForm.discriminant q -
        cuspFunction 1 CuspForm.discriminant 0)) (𝓝[≠] 0) (𝓝 1) := by
      simpa only [smul_eq_mul, zero_add] using hs
    have hfun : (fun q : ℂ => cuspFunction 1 CuspForm.discriminant q / q) =
        fun q => q⁻¹ * (cuspFunction 1 CuspForm.discriminant q -
          cuspFunction 1 CuspForm.discriminant 0) := by
      funext q
      rw [cuspFunction_discriminant_zero]
      simp [div_eq_mul_inv, mul_comm]
    rw [hfun]
    exact hs'
  have hE_lim : Tendsto (fun q : ℂ => cuspFunction 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) q ^ 3)
      (𝓝[≠] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun q : ℂ => cuspFunction 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) q ^ 3) 0 :=
      (hE_diff.continuousAt.pow 3)
    have hlim : Tendsto
        (fun q : ℂ => cuspFunction 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) q ^ 3)
        (𝓝[≠] 0) (𝓝 (cuspFunction 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) 0 ^ 3)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa [cuspFunction_E4_zero] using hlim
  have hq_prod : Tendsto (fun q : ℂ => q * jCuspFunction q) (𝓝[≠] 0) (𝓝 1) := by
    have hdiv := hE_lim.div hslope one_ne_zero
    rw [div_one] at hdiv
    have hDquot_ne : ∀ᶠ q : ℂ in 𝓝[≠] 0,
        cuspFunction 1 CuspForm.discriminant q / q ≠ 0 :=
      hslope.eventually (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))
    refine hdiv.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hDquot_ne] with q hq hDquot
    have hq0 : q ≠ 0 := hq
    simp only [Pi.div_apply, jCuspFunction]
    field_simp [hq0, hDquot]
  refine ⟨hq_prod, ?_⟩
  have hnorm_prod : Tendsto (fun q : ℂ => ‖q‖ * ‖jCuspFunction q‖) (𝓝[≠] 0) (𝓝 1) := by
    simpa [norm_mul] using hq_prod.norm
  have hinv_top : Tendsto (fun q : ℂ => ‖q‖⁻¹) (𝓝[≠] 0) Filter.atTop := by
    have h0 : Tendsto (fun q : ℂ => ‖q‖) (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := by
      simpa using (continuous_norm.tendsto (0 : ℂ))
    have hn : Tendsto (fun q : ℂ => ‖q‖) (𝓝[≠] 0) (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (h0.mono_left nhdsWithin_le_nhds)
        (Eventually.mono self_mem_nhdsWithin fun q hq => norm_pos_iff.mpr hq)
    exact tendsto_inv_nhdsGT_zero.comp hn
  have hmul := hinv_top.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hnorm_prod
  refine hmul.congr' ?_
  refine Eventually.mono self_mem_nhdsWithin fun q hq => ?_
  have hq_norm : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  field_simp [hq_norm]

/-- `jCuspFunction` is holomorphic at every point of the punctured unit disc `Metric.ball 0 1 \ {0}`. -/
theorem differentiableOn_jCuspFunction_punctured :
    DifferentiableOn ℂ jCuspFunction (Metric.ball 0 1 \ {0}) := by
  intro q hq
  have hball : ‖q‖ < 1 := mem_ball_zero_iff.mp hq.1
  have hq0 : q ≠ 0 := hq.2
  have hE : DifferentiableAt ℂ (cuspFunction 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4)) q :=
    ModularFormClass.differentiableAt_cuspFunction (ModularForm.E₄ : ModularForm 𝒮ℒ 4)
      one_pos one_mem_strictPeriods_SL hball
  have hD : DifferentiableAt ℂ (cuspFunction 1 CuspForm.discriminant) q :=
    ModularFormClass.differentiableAt_cuspFunction CuspForm.discriminant
      one_pos one_mem_strictPeriods_SL hball
  have hD_ne : cuspFunction 1 CuspForm.discriminant q ≠ 0 := by
    have hpos := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hball hq0
    let z : ℍ := ⟨Function.Periodic.invQParam 1 q, hpos⟩
    have hval : cuspFunction 1 CuspForm.discriminant q = ModularForm.discriminant z := by
      have hqinv : Function.Periodic.qParam 1 z = q := Function.Periodic.qParam_right_inv one_ne_zero hq0
      simpa [hqinv] using
        SlashInvariantFormClass.eq_cuspFunction CuspForm.discriminant z one_mem_strictPeriods_SL
          one_ne_zero
    rw [hval]
    exact ModularForm.discriminant_ne_zero z
  exact ((hE.pow 3).div hD hD_ne).differentiableWithinAt

/-- Formal cusp Laurent series `j(q) = q⁻¹ + ∑_{n ≥ 0} cₙ qⁿ ∈ ℂ⸨X⸩`. -/
noncomputable def jLaurentSeries : LaurentSeries ℂ :=
  let Δq : PowerSeries ℂ := qExpansion 1 CuspForm.discriminant
  let u : (PowerSeries ℂ)ˣ := PowerSeries.Unit_of_divided_by_X_pow_order Δq
  let reg : PowerSeries ℂ := qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) ^ 3 * (↑u⁻¹ : PowerSeries ℂ)
  (HahnSeries.single (-1 : ℤ) (1 : ℂ)) * (HahnSeries.ofPowerSeries ℤ ℂ reg)

theorem jLaurentSeries_principal_part :
    jLaurentSeries.coeff (-1) = 1 ∧ ∀ n : ℤ, n < -1 → jLaurentSeries.coeff n = 0 := by
  let Δq : PowerSeries ℂ := qExpansion 1 CuspForm.discriminant
  let u : (PowerSeries ℂ)ˣ := PowerSeries.Unit_of_divided_by_X_pow_order Δq
  let reg : PowerSeries ℂ := qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) ^ 3 * (↑u⁻¹ : PowerSeries ℂ)
  have hord : Δq.order = 1 := ModularForm.discriminant_qExpansion_order
  have hΔne : Δq ≠ 0 := fun hz => by
    have ht := PowerSeries.order_eq_top.mpr hz
    rw [hord] at ht
    simp at ht
  have hunit : (↑u : PowerSeries ℂ) = Δq.divXPowOrder :=
    PowerSeries.Unit_of_divided_by_X_pow_order_nonzero hΔne
  have horderNat : Δq.order.toNat = 1 := by rw [hord]; rfl
  have hfactor : PowerSeries.X * (↑u : PowerSeries ℂ) = Δq := by
    calc
      PowerSeries.X * (↑u : PowerSeries ℂ) =
          PowerSeries.X ^ Δq.order.toNat * Δq.divXPowOrder := by rw [horderNat, pow_one, hunit]
      _ = Δq := PowerSeries.X_pow_order_mul_divXPowOrder
  have hu0 : PowerSeries.constantCoeff (↑u : PowerSeries ℂ) = 1 := by
    have h1 := ModularForm.discriminant_qExpansion_coeff_one
    change Δq.coeff 1 = 1 at h1
    rw [← hfactor, show (1 : ℕ) = 0 + 1 by rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff] at h1
    exact h1
  have hinv0 : PowerSeries.constantCoeff (↑u⁻¹ : PowerSeries ℂ) = 1 := by
    have hm := congrArg PowerSeries.constantCoeff (Units.val_inv u)
    rw [map_mul, hu0, one_mul] at hm
    exact hm
  have hE4_0 : PowerSeries.constantCoeff
      (qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) ^ 3) = 1 := by
    have hE := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
    rw [map_pow]
    have hE' : PowerSeries.constantCoeff (qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4)) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE
    rw [hE']
    norm_num
  have hreg0 : PowerSeries.coeff 0 reg = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    dsimp [reg]
    rw [map_mul, hE4_0, hinv0, mul_one]
  refine ⟨?_, ?_⟩
  · change ((HahnSeries.single (-1 : ℤ) (1 : ℂ)) *
        (HahnSeries.ofPowerSeries ℤ ℂ reg)).coeff ((0 : ℤ) + (-1 : ℤ)) = 1
    rw [HahnSeries.coeff_single_mul_add, one_mul,
      show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, hreg0]
  · intro n hn
    have hn' : n = (n + 1 : ℤ) + (-1 : ℤ) := by ring
    change ((HahnSeries.single (-1 : ℤ) (1 : ℂ)) *
        (HahnSeries.ofPowerSeries ℤ ℂ reg)).coeff n = 0
    rw [hn', HahnSeries.coeff_single_mul_add, one_mul, HahnSeries.ofPowerSeries_apply,
      HahnSeries.embDomain_of_notMem_range]
    simp only [Nat.castOrderEmbedding_apply, Set.mem_range, not_exists]
    intro k hk
    omega

/-- **Algebraic Transcendence of `jInvariant`**: no nonzero complex polynomial vanishes on
`{jInvariant z | z : ℍ}`. Proved directly from the simple pole at `q = 0`. -/
theorem jInvariant_aeval_injective :
    Function.Injective (fun P : ℂ[X] => fun z : ℍ => P.eval (jInvariant z)) := by
  intro P Q hPQ
  rw [← sub_eq_zero]
  by_contra hne
  let R : ℂ[X] := P - Q
  have hR_ne : R ≠ 0 := hne
  have hR_zero : ∀ z : ℍ, R.eval (jInvariant z) = 0 := fun z => by
    simp [R, congrFun hPQ z]
  have hR_cusp : ∀ q : ℂ, q ∈ Metric.ball (0 : ℂ) 1 \ {0} → R.eval (jCuspFunction q) = 0 := by
    rintro q ⟨hqb, hq0⟩
    have hpos := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos (mem_ball_zero_iff.mp hqb) hq0
    let z : ℍ := ⟨Function.Periodic.invQParam 1 q, hpos⟩
    have hqz : Function.Periodic.qParam 1 z = q := Function.Periodic.qParam_right_inv one_ne_zero hq0
    have hj : jCuspFunction q = jInvariant z := by
      rw [jInvariant_eq_jCuspFunction_qParam z, hqz]
    rw [hj]
    exact hR_zero z
  let d : ℕ := R.natDegree
  have hmem : Metric.ball (0 : ℂ) 1 \ {0} ∈ 𝓝[≠] (0 : ℂ) :=
    Filter.inter_mem (Filter.mem_inf_of_left (Metric.ball_mem_nhds 0 zero_lt_one))
      self_mem_nhdsWithin
  have h_zero_lim : Tendsto (fun q : ℂ => q ^ d * R.eval (jCuspFunction q)) (𝓝[≠] 0) (𝓝 0) := by
    have h0 : Tendsto (fun _ : ℂ => (0 : ℂ)) (𝓝[≠] 0) (𝓝 0) := tendsto_const_nhds
    refine h0.congr' ?_
    refine Eventually.mono hmem fun q hq => ?_
    dsimp only
    rw [hR_cusp q hq, mul_zero]
  have hpole := jCuspFunction_tendsto_simple_pole.1
  have hlead_lim :
      Tendsto (fun q : ℂ => q ^ d * R.eval (jCuspFunction q)) (𝓝[≠] 0) (𝓝 R.leadingCoeff) := by
    have hdecomp : ∀ q : ℂ, q ≠ 0 →
        q ^ d * R.eval (jCuspFunction q) =
          ∑ k ∈ Finset.range (d + 1), R.coeff k * q ^ (d - k) * (q * jCuspFunction q) ^ k := by
      intro q hq0
      rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      calc
        q ^ d * (R.coeff k * jCuspFunction q ^ k) =
            R.coeff k * (q ^ (d - k + k) * jCuspFunction q ^ k) := by
          rw [Nat.sub_add_cancel hk_le]; ring
        _ = R.coeff k * q ^ (d - k) * (q * jCuspFunction q) ^ k := by
          rw [pow_add, mul_pow]; ring
    have hsum_lim : Tendsto
        (fun q : ℂ => ∑ k ∈ Finset.range (d + 1), R.coeff k * q ^ (d - k) * (q * jCuspFunction q) ^ k)
        (𝓝[≠] 0) (𝓝 (∑ k ∈ Finset.range (d + 1), if k = d then R.leadingCoeff else 0)) := by
      refine tendsto_finsetSum _ fun k hk => ?_
      have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hkd : k = d
      · subst hkd
        simp only [ite_true, Nat.sub_self, pow_zero, mul_one]
        have hlc : R.coeff d = R.leadingCoeff := rfl
        rw [hlc]
        have ht := (hpole.pow d).const_mul R.leadingCoeff
        simpa using ht
      · have hk_lt : k < d := lt_of_le_of_ne hk_le hkd
        have hd_pos : 0 < d - k := Nat.sub_pos_of_lt hk_lt
        simp only [hkd, ↓reduceIte]
        have hqpow : Tendsto (fun q : ℂ => q ^ (d - k)) (𝓝[≠] 0) (𝓝 0) := by
          have hc : ContinuousAt (fun q : ℂ => q ^ (d - k)) 0 := continuousAt_id.pow (d - k)
          have hcz : Tendsto (fun q : ℂ => q ^ (d - k)) (𝓝[≠] 0) (𝓝 ((0 : ℂ) ^ (d - k))) :=
            hc.tendsto.mono_left nhdsWithin_le_nhds
          simpa [zero_pow hd_pos.ne'] using hcz
        have hterm := ((tendsto_const_nhds (x := R.coeff k)).mul hqpow).mul (hpole.pow k)
        simpa using hterm
    have hsum_val : (∑ k ∈ Finset.range (d + 1), if k = d then R.leadingCoeff else 0) =
        R.leadingCoeff := by
      simp [Finset.sum_ite_eq', Finset.mem_range]
    rw [hsum_val] at hsum_lim
    refine hsum_lim.congr' ?_
    refine Eventually.mono self_mem_nhdsWithin fun q hq0 => (hdecomp q hq0).symm
  have hlead0 : R.leadingCoeff = 0 := tendsto_nhds_unique hlead_lim h_zero_lim
  exact hR_ne (Polynomial.leadingCoeff_eq_zero.mp hlead0)

theorem normalizedJInvariant_aeval_injective :
    Function.Injective (fun P : ℂ[X] => fun z : ℍ => P.eval (normalizedJInvariant z)) := by
  intro P Q hPQ
  have hscale : (fun z : ℍ => (P.comp (Polynomial.C (1 / 1728 : ℂ) * Polynomial.X)).eval (jInvariant z)) =
      (fun z : ℍ => (Q.comp (Polynomial.C (1 / 1728 : ℂ) * Polynomial.X)).eval (jInvariant z)) := by
    ext z
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    simpa [normalizedJInvariant, div_eq_inv_mul, one_div] using congrFun hPQ z
  have heq := jInvariant_aeval_injective hscale
  have hinj : Function.Injective (fun F : ℂ[X] => F.comp (Polynomial.C (1 / 1728 : ℂ) * Polynomial.X)) := by
    intro A B hAB
    have hinv := congrArg (fun G : ℂ[X] => G.comp (Polynomial.C (1728 : ℂ) * Polynomial.X)) hAB
    have hl : (Polynomial.C (1 / 1728 : ℂ) * Polynomial.X).comp (Polynomial.C (1728 : ℂ) * Polynomial.X) =
        Polynomial.X := by
      simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc, ← map_mul]
      norm_num
    rw [Polynomial.comp_assoc, Polynomial.comp_assoc, hl, Polynomial.comp_X,
      Polynomial.comp_X] at hinv
    exact hinv
  exact hinj heq

private lemma modularForm_sum_apply {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*}
    (s : Finset ι) (f : ι → ModularForm Γ k) (z : ℍ) :
    (∑ i ∈ s, f i) z = ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, _root_.add_apply, ih]

/-- Construct the explicit weight-`12 * n` modular form `Δ(z)^n * P(j(z))` from any polynomial
`P` of degree `≤ n`. -/
noncomputable def modularFormOfJPoly (n : ℕ) (P : ℂ[X]) (_hdeg : P.natDegree ≤ n) :
    ModularForm 𝒮ℒ (12 * (n : ℤ)) :=
  ∑ k : Fin (n + 1),
    P.coeff k.1 • ModularForm.mcast (by
      have hk : k.1 ≤ n := Nat.le_of_lt_succ k.2
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk]
      ring)
      (((ModularForm.E₄ : ModularForm 𝒮ℒ 4).pow (3 * k.1)).mul
        ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow (n - k.1)))

theorem modularFormOfJPoly_apply (n : ℕ) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (z : ℍ) :
    modularFormOfJPoly n P hdeg z = ModularForm.discriminant z ^ n * P.eval (jInvariant z) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.mul_sum,
    ← Fin.sum_univ_eq_sum_range]
  dsimp only [modularFormOfJPoly]
  rw [modularForm_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk_le : k.1 ≤ n := Nat.le_of_lt_succ k.2
  have hΔ_ne : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  simp only [_root_.smul_apply, smul_eq_mul, ModularForm.coe_mcast, ModularForm.coe_mul,
    Pi.mul_apply, ModularForm.coe_pow, Pi.pow_apply]
  have hD : ((CuspForm.discriminant : ModularForm 𝒮ℒ 12) z) = ModularForm.discriminant z := rfl
  rw [hD]
  have hE_pow : (ModularForm.E₄ z) ^ (3 * k.1) = (ModularForm.E₄ z ^ 3) ^ k.1 := by ring
  have hj_pow : (ModularForm.discriminant z) ^ n * (jInvariant z) ^ k.1 =
      (ModularForm.E₄ z ^ 3) ^ k.1 * (ModularForm.discriminant z) ^ (n - k.1) := by
    have hpow : (ModularForm.discriminant z) ^ n =
        (ModularForm.discriminant z) ^ (n - k.1) * (ModularForm.discriminant z) ^ k.1 := by
      rw [← pow_add, Nat.sub_add_cancel hk_le]
    rw [jInvariant, div_pow, hpow]
    field_simp [hΔ_ne]
  rw [hE_pow, ← hj_pow]
  ring

/-- **Canonical Level-One `j` Hauptmodul Theorem (Weight `12 * n`)**:
Every level-one modular form `g` of weight `12 * n` is UNIQUELY of the form `Δ(z)^n * P(j(z))`
for a complex polynomial `P` of degree at most `n` (equivalently `g / Δ^n = P ∘ jInvariant`). -/
theorem modularForm_weight_twelve_mul_eq_poly_jInvariant :
    ∀ (n : ℕ) (g : ModularForm 𝒮ℒ (12 * (n : ℤ))),
      ∃! P : ℂ[X], P.natDegree ≤ n ∧
        ∀ z : ℍ, g z / ModularForm.discriminant z ^ n = P.eval (jInvariant z) := by
  intro n
  induction n with
  | zero =>
    intro g
    let hg0 : ModularForm 𝒮ℒ 0 := ModularForm.mcast (by norm_num) g
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const hg0
    have hgz : ∀ z : ℍ, g z = hg0 z := fun z => by rfl
    refine ⟨Polynomial.C c, ⟨Polynomial.natDegree_C c |>.le, fun z => ?_⟩, ?_⟩
    · have hcz : hg0 z = c := congrFun hc z
      simp [hgz z, hcz]
    · rintro Q ⟨_, hQ⟩
      apply jInvariant_aeval_injective
      ext z
      dsimp only
      rw [← hQ z]
      have hcz : hg0 z = c := congrFun hc z
      simp [hgz z, hcz]
  | succ m ih =>
    intro g
    let c₀ : ℂ := (qExpansion 1 g).coeff 0
    let E4pow : ModularForm 𝒮ℒ (12 * ((m + 1 : ℕ) : ℤ)) :=
      ModularForm.mcast (by push_cast; ring)
        ((ModularForm.E₄ : ModularForm 𝒮ℒ 4).pow (3 * (m + 1)))
    let h : ModularForm 𝒮ℒ (12 * ((m + 1 : ℕ) : ℤ)) := g - c₀ • E4pow
    have hE4_coeff0 : (qExpansion 1 E4pow).coeff 0 = 1 := by
      have hcast : (qExpansion 1 E4pow) =
          qExpansion 1 ((ModularForm.E₄ : ModularForm 𝒮ℒ 4).pow (3 * (m + 1))) := rfl
      rw [hcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
        PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
      have hE := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
      have hE' : PowerSeries.constantCoeff (qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4)) = 1 := by
        simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE
      rw [hE', one_pow]
    have hh0 : (qExpansion 1 h).coeff 0 = 0 := by
      have hsub : qExpansion 1 h = qExpansion 1 g - qExpansion 1 (c₀ • E4pow) :=
        ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL g (c₀ • E4pow)
      have hsmul : qExpansion 1 (c₀ • E4pow) = c₀ • qExpansion 1 E4pow :=
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c₀ E4pow
      rw [hsub, hsmul, map_sub, PowerSeries.coeff_smul, smul_eq_mul, hE4_coeff0,
        mul_one, sub_self]
    let hCusp : CuspForm 𝒮ℒ (12 * ((m + 1 : ℕ) : ℤ)) := ModularForm.toCuspForm h hh0
    let g₁ : ModularForm 𝒮ℒ (12 * (m : ℤ)) :=
      ModularForm.mcast (by push_cast; ring) (CuspForm.discriminantEquiv hCusp)
    obtain ⟨Q, ⟨hQdeg, hQeq⟩, _⟩ := ih g₁
    let P : ℂ[X] := Polynomial.C c₀ * Polynomial.X ^ (m + 1) + Q
    have hPdeg : P.natDegree ≤ m + 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (hQdeg.trans (Nat.le_succ m)))
      exact (Polynomial.natDegree_C_mul_X_pow_le c₀ (m + 1))
    have hPeq : ∀ z : ℍ, g z / ModularForm.discriminant z ^ (m + 1) = P.eval (jInvariant z) := by
      intro z
      have hΔne : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
      have hg₁_mul : ModularForm.discriminant z * g₁ z = g z - c₀ * (ModularForm.E₄ z ^ 3) ^ (m + 1) := by
        have hm := ModularForm.discriminant_mul_discriminantEquiv_apply hCusp z
        have hg1val : g₁ z = (CuspForm.discriminantEquiv hCusp) z := rfl
        have hhval : (hCusp : ℍ → ℂ) z = g z - c₀ * (ModularForm.E₄ z ^ 3) ^ (m + 1) := by
          change h z = g z - c₀ * (ModularForm.E₄ z ^ 3) ^ (m + 1)
          have he4 : (ModularForm.E₄ z) ^ (3 * (m + 1)) = (ModularForm.E₄ z ^ 3) ^ (m + 1) := by ring
          simp only [h, E4pow, _root_.sub_apply, _root_.smul_apply, smul_eq_mul,
            ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply]
          rw [he4]
        rw [hg1val, hm, hhval]
      have hg₁_val : g₁ z = ModularForm.discriminant z ^ m * Q.eval (jInvariant z) := by
        have hpow_ne : ModularForm.discriminant z ^ m ≠ 0 := pow_ne_zero m hΔne
        exact (div_eq_iff hpow_ne).mp (hQeq z) |>.trans (mul_comm _ _)
      have hg_val : g z = c₀ * (ModularForm.E₄ z ^ 3) ^ (m + 1) +
          ModularForm.discriminant z ^ (m + 1) * Q.eval (jInvariant z) := by
        have h1 : ModularForm.discriminant z * g₁ z =
            ModularForm.discriminant z ^ (m + 1) * Q.eval (jInvariant z) := by
          rw [hg₁_val, pow_succ']
          ring
        linear_combination -hg₁_mul + h1
      rw [hg_val, add_div, mul_div_assoc, ← div_pow, ← jInvariant,
        mul_div_cancel_left₀ _ (pow_ne_zero (m + 1) hΔne)]
      simp [P]
    refine ⟨P, ⟨hPdeg, hPeq⟩, ?_⟩
    rintro P' ⟨_, hP'⟩
    apply jInvariant_aeval_injective
    ext z
    dsimp only
    rw [← hP' z, ← hPeq z]

/-- Normalized Hauptmodul statement for `j / 1728`: every weight-`12 * n` modular form divided by
`Δ^n` is uniquely a polynomial of degree `≤ n` in `normalizedJInvariant`. -/
theorem modularForm_weight_twelve_mul_eq_poly_normalizedJInvariant (n : ℕ)
    (g : ModularForm 𝒮ℒ (12 * (n : ℤ))) :
    ∃! P : ℂ[X], P.natDegree ≤ n ∧
      ∀ z : ℍ, g z / ModularForm.discriminant z ^ n = P.eval (normalizedJInvariant z) := by
  obtain ⟨P₀, ⟨hdeg₀, heq₀⟩, huniq₀⟩ := modularForm_weight_twelve_mul_eq_poly_jInvariant n g
  let P : ℂ[X] := P₀.comp (Polynomial.C (1728 : ℂ) * Polynomial.X)
  have hdeg : P.natDegree ≤ n := by
    calc
      P.natDegree ≤ P₀.natDegree * (Polynomial.C (1728 : ℂ) * Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ P₀.natDegree * 1 :=
        Nat.mul_le_mul_left _ ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
      _ = P₀.natDegree := mul_one _
      _ ≤ n := hdeg₀
  have hPeq : ∀ z : ℍ, g z / ModularForm.discriminant z ^ n = P.eval (normalizedJInvariant z) :=
    fun z => by
      simp only [P, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, normalizedJInvariant]
      have h1728 : (1728 : ℂ) * (jInvariant z / 1728) = jInvariant z := by ring
      rw [h1728]
      exact heq₀ z
  refine ⟨P, ⟨hdeg, hPeq⟩, ?_⟩
  rintro Q ⟨_, hQ⟩
  apply normalizedJInvariant_aeval_injective
  ext z
  dsimp only
  rw [← hQ z, ← hPeq z]

/-- **Rational Function Field Generation Theorem (`ℂ(X(1)) = ℂ(j)`)**:
Any ratio `g₁ / g₂` of two level-one modular forms of equal even weight `2 * m` (`g₂ ≠ 0`)
equals a rational function `P(j) / Q(j)` with `Q ≠ 0`, globally on `ℍ`:
`∀ z : ℍ, Q.eval (jInvariant z) * g₁ z = P.eval (jInvariant z) * g₂ z`. -/
theorem modularForm_even_weight_rational_jInvariant (m : ℕ)
    (g₁ g₂ : ModularForm 𝒮ℒ (2 * (m : ℤ))) (hg₂ : g₂ ≠ 0) :
    ∃ P Q : ℂ[X], Q ≠ 0 ∧ P.natDegree ≤ m ∧ Q.natDegree ≤ m ∧
      ∀ z : ℍ, Q.eval (jInvariant z) * g₁ z = P.eval (jInvariant z) * g₂ z := by
  let f₀ : ModularForm 𝒮ℒ (10 * (m : ℤ)) :=
    ModularForm.mcast (by ring)
      (((ModularForm.E₄ : ModularForm 𝒮ℒ 4).pow m).mul
        ((ModularForm.E₆ : ModularForm 𝒮ℒ 6).pow m))
  have hf₀_coeff : (qExpansion 1 f₀).coeff 0 = 1 := by
    have hq : qExpansion 1 f₀ =
        qExpansion 1 ((ModularForm.E₄ : ModularForm 𝒮ℒ 4).pow m) *
          qExpansion 1 ((ModularForm.E₆ : ModularForm 𝒮ℒ 6).pow m) := by
      change qExpansion 1 (((ModularForm.E₄ : ModularForm 𝒮ℒ 4).pow m).mul
        ((ModularForm.E₆ : ModularForm 𝒮ℒ 6).pow m)) = _
      exact ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL _ _
    rw [hq, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow, map_pow]
    have hE4 := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
    have hE6 := EisensteinSeries.E_qExpansion_coeff_zero (k := 6) (by norm_num) ⟨3, rfl⟩
    have hE4' : PowerSeries.constantCoeff (qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4)) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE4
    have hE6' : PowerSeries.constantCoeff (qExpansion 1 (ModularForm.E₆ : ModularForm 𝒮ℒ 6)) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE6
    rw [hE4', hE6', one_pow, mul_one]
  have hf₀_ne : qExpansion 1 f₀ ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hf₀_coeff
    exact one_ne_zero hf₀_coeff.symm
  let h₁ : ModularForm 𝒮ℒ (12 * (m : ℤ)) := ModularForm.mcast (by ring) (f₀.mul g₁)
  let h₂ : ModularForm 𝒮ℒ (12 * (m : ℤ)) := ModularForm.mcast (by ring) (f₀.mul g₂)
  obtain ⟨P, ⟨hPdeg, hPeq⟩, _⟩ := modularForm_weight_twelve_mul_eq_poly_jInvariant m h₁
  obtain ⟨Q, ⟨hQdeg, hQeq⟩, _⟩ := modularForm_weight_twelve_mul_eq_poly_jInvariant m h₂
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have hmul0 : h₂ = 0 := by
      ext z
      have hdiv := hQeq z
      rw [hQ0, Polynomial.eval_zero, div_eq_zero_iff] at hdiv
      rcases hdiv with hz | hΔ0
      · exact hz
      · exact absurd hΔ0 (pow_ne_zero m (ModularForm.discriminant_ne_zero z))
    have hq_mul : qExpansion 1 f₀ * qExpansion 1 g₂ = 0 := by
      rw [← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f₀ g₂]
      change qExpansion 1 h₂ = 0
      rw [hmul0]
      exact UpperHalfPlane.qExpansion_zero 1
    rcases mul_eq_zero.mp hq_mul with hfa | hga
    · exact hf₀_ne hfa
    · exact hg₂ ((ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_SL g₂).mp hga)
  let Qmod := modularFormOfJPoly m Q hQdeg
  let Pmod := modularFormOfJPoly m P hPdeg
  let G : ModularForm 𝒮ℒ (12 * (m : ℤ) + 2 * (m : ℤ)) := Qmod.mul g₁ - Pmod.mul g₂
  have hfG_zero : f₀.mul G = 0 := by
    ext z
    have h1z : f₀ z * g₁ z = ModularForm.discriminant z ^ m * P.eval (jInvariant z) := by
      have h := hPeq z
      exact (div_eq_iff (pow_ne_zero m (ModularForm.discriminant_ne_zero z))).mp h |>.trans
        (mul_comm _ _)
    have h2z : f₀ z * g₂ z = ModularForm.discriminant z ^ m * Q.eval (jInvariant z) := by
      have h := hQeq z
      exact (div_eq_iff (pow_ne_zero m (ModularForm.discriminant_ne_zero z))).mp h |>.trans
        (mul_comm _ _)
    change f₀ z * (Qmod z * g₁ z - Pmod z * g₂ z) = 0
    rw [modularFormOfJPoly_apply m Q hQdeg z, modularFormOfJPoly_apply m P hPdeg z]
    calc
      f₀ z * (ModularForm.discriminant z ^ m * Q.eval (jInvariant z) * g₁ z -
          ModularForm.discriminant z ^ m * P.eval (jInvariant z) * g₂ z) =
          ModularForm.discriminant z ^ m * Q.eval (jInvariant z) * (f₀ z * g₁ z) -
          ModularForm.discriminant z ^ m * P.eval (jInvariant z) * (f₀ z * g₂ z) := by ring
      _ = 0 := by rw [h1z, h2z]; ring
  have hqG_zero : qExpansion 1 f₀ * qExpansion 1 G = 0 := by
    rw [← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f₀ G, hfG_zero]
    exact UpperHalfPlane.qExpansion_zero 1
  have hG_q0 : qExpansion 1 G = 0 := (mul_eq_zero.mp hqG_zero).resolve_left hf₀_ne
  have hG_zero : G = 0 :=
    (ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_SL G).mp hG_q0
  refine ⟨P, Q, hQ_ne, hPdeg, hQdeg, fun z => ?_⟩
  have hGz : G z = 0 := by rw [hG_zero]; rfl
  change Qmod z * g₁ z - Pmod z * g₂ z = 0 at hGz
  rw [modularFormOfJPoly_apply m Q hQdeg z, modularFormOfJPoly_apply m P hPdeg z] at hGz
  have hfac : ModularForm.discriminant z ^ m *
      (Q.eval (jInvariant z) * g₁ z - P.eval (jInvariant z) * g₂ z) = 0 := by
    linear_combination hGz
  have hsub := (mul_eq_zero.mp hfac).resolve_left
    (pow_ne_zero m (ModularForm.discriminant_ne_zero z))
  exact sub_eq_zero.mp hsub

end ModularJHauptmodul

/-! ## Section 3: Generic Quintic Galois Resolvent (`F₂₀` Sextic), Tschirnhaus Chain, & `A₅` Obstruction -/

section QuinticGaloisResolvent

/-- Affine permutation `(a, b) • x = a * x + b` on `Fin 5 ≃+* ZMod 5` for the Frobenius group `F₂₀`. -/
def affinePerm5 (a : (ZMod 5)ˣ) (b : ZMod 5) : Equiv.Perm (Fin 5) :=
  let e : Fin 5 ≃ ZMod 5 := (ZMod.finEquiv 5).toEquiv
  let aff : Equiv.Perm (ZMod 5) :=
    { toFun := fun x => (a : ZMod 5) * x + b
      invFun := fun x => (↑a⁻¹ : ZMod 5) * (x - b)
      left_inv := fun x => by simp [← mul_assoc]
      right_inv := fun x => by simp [mul_sub, ← mul_assoc] }
  e.symm.trans (aff.trans e)

@[simp] private lemma affinePerm5_apply (a : (ZMod 5)ˣ) (b : ZMod 5) (i : Fin 5) :
    (ZMod.finEquiv 5) (affinePerm5 a b i) = (a : ZMod 5) * (ZMod.finEquiv 5) i + b :=
  (ZMod.finEquiv 5).toEquiv.apply_symm_apply _

/-- The maximal metacyclic solvable subgroup `F₂₀ = AGL(1, 𝔽₅) ⊂ S₅` of order 20. -/
def frobenius20Subgroup : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := { σ | ∃ (a : (ZMod 5)ˣ) (b : ZMod 5), σ = affinePerm5 a b }
  one_mem' := ⟨1, 0, Equiv.Perm.ext fun i => (ZMod.finEquiv 5).injective (by simp)⟩
  mul_mem' := by
    rintro σ₁ σ₂ ⟨a₁, b₁, rfl⟩ ⟨a₂, b₂, rfl⟩
    refine ⟨a₁ * a₂, (a₁ : ZMod 5) * b₂ + b₁, Equiv.Perm.ext fun i =>
      (ZMod.finEquiv 5).injective ?_⟩
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, affinePerm5_apply, Units.val_mul]
    ring
  inv_mem' := by
    rintro σ ⟨a, b, rfl⟩
    refine ⟨a⁻¹, -(↑a⁻¹ : ZMod 5) * b, Equiv.Perm.ext fun i => (ZMod.finEquiv 5).injective ?_⟩
    have hinv : (affinePerm5 a b) ((affinePerm5 a b).symm i) = i := (affinePerm5 a b).apply_symm_apply i
    have h1 := congrArg (ZMod.finEquiv 5) hinv
    simp only [affinePerm5_apply] at h1 ⊢
    calc
      (ZMod.finEquiv 5) ((affinePerm5 a b)⁻¹ i) =
          (↑a⁻¹ : ZMod 5) * ((ZMod.finEquiv 5) i - b) := by
        rw [← h1]; simp [← mul_assoc]
      _ = (↑a⁻¹ : ZMod 5) * (ZMod.finEquiv 5) i + -(↑a⁻¹ : ZMod 5) * b := by ring

private lemma affinePerm5_injective :
    Function.Injective (fun p : (ZMod 5)ˣ × ZMod 5 => affinePerm5 p.1 p.2) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  have h0 := congrArg (ZMod.finEquiv 5) (Equiv.Perm.ext_iff.mp h 0)
  have h1 := congrArg (ZMod.finEquiv 5) (Equiv.Perm.ext_iff.mp h 1)
  simp only [affinePerm5_apply, map_zero, map_one, mul_zero, zero_add, mul_one] at h0 h1
  have hb : b₁ = b₂ := h0
  subst hb
  have ha : (a₁ : ZMod 5) = (a₂ : ZMod 5) := add_right_cancel h1
  exact Prod.ext (Units.ext ha) rfl

instance : DecidablePred (· ∈ frobenius20Subgroup) := fun σ =>
  decidable_of_iff (∃ p : (ZMod 5)ˣ × ZMod 5, σ = affinePerm5 p.1 p.2)
    ⟨fun ⟨p, hp⟩ => ⟨p.1, p.2, hp⟩, fun ⟨a, b, h⟩ => ⟨(a, b), h⟩⟩

private def linCoeff5 (σ : Equiv.Perm (Fin 5)) : ZMod 5 :=
  (ZMod.finEquiv 5) (σ 1) - (ZMod.finEquiv 5) (σ 0)

private lemma linCoeff5_affinePerm5 (a : (ZMod 5)ˣ) (b : ZMod 5) :
    linCoeff5 (affinePerm5 a b) = (a : ZMod 5) := by
  simp [linCoeff5, affinePerm5_apply]

theorem frobenius20Subgroup_card_and_solvable :
    Nat.card frobenius20Subgroup = 20 ∧
      Nat.card ↥(frobenius20Subgroup ⊓ alternatingGroup (Fin 5)) = 10 ∧
      Group.IsSolvable frobenius20Subgroup := by
  have hcard20 : Nat.card frobenius20Subgroup = 20 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype (Finset.univ.image
        fun p : (ZMod 5)ˣ × ZMod 5 => affinePerm5 p.1 p.2) (fun σ => by
      change σ ∈ Finset.univ.image (fun p : (ZMod 5)ˣ × ZMod 5 => affinePerm5 p.1 p.2) ↔
        ∃ a : (ZMod 5)ˣ, ∃ b : ZMod 5, σ = affinePerm5 a b
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
      exact ⟨fun ⟨a, b, h⟩ => ⟨a, b, h.symm⟩, fun ⟨a, b, h⟩ => ⟨a, b, h.symm⟩⟩)]
    rw [Finset.card_image_of_injective _ affinePerm5_injective]
    decide
  have hcard10 : Nat.card ↥(frobenius20Subgroup ⊓ alternatingGroup (Fin 5)) = 10 := by
    let S : Finset (Equiv.Perm (Fin 5)) :=
      Finset.univ.filter fun σ : Equiv.Perm (Fin 5) =>
        σ ∈ frobenius20Subgroup ∧ Equiv.Perm.sign σ = 1
    have hS : ∀ σ : Equiv.Perm (Fin 5),
        σ ∈ S ↔ σ ∈ frobenius20Subgroup ⊓ alternatingGroup (Fin 5) := fun σ => by
      simp [S, Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup]
    let : DecidablePred (· ∈ frobenius20Subgroup ⊓ alternatingGroup (Fin 5)) := fun σ =>
      decidable_of_iff (σ ∈ frobenius20Subgroup ∧ Equiv.Perm.sign σ = 1)
        ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype S hS]
    decide
  have hsolv : Group.IsSolvable frobenius20Subgroup := by
    let trans : Multiplicative (ZMod 5) →* frobenius20Subgroup :=
      { toFun := fun b => ⟨affinePerm5 1 (Multiplicative.toAdd b), ⟨1, Multiplicative.toAdd b, rfl⟩⟩
        map_one' := Subtype.ext (Equiv.Perm.ext fun i => (ZMod.finEquiv 5).injective (by simp))
        map_mul' := fun x y => Subtype.ext (Equiv.Perm.ext fun i =>
          (ZMod.finEquiv 5).injective (by
            simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply,
              affinePerm5_apply, Units.val_one, one_mul, toAdd_mul]
            ring)) }
    let homA : frobenius20Subgroup →* (ZMod 5)ˣ :=
      { toFun := fun σ =>
          { val := linCoeff5 σ.1
            inv := linCoeff5 (σ⁻¹).1
            val_inv := by
              rcases σ.2 with ⟨a, b, ha⟩
              rcases σ⁻¹.2 with ⟨a', b', ha'⟩
              have hprod : affinePerm5 a b * affinePerm5 a' b' = 1 := by
                rw [← ha, ← ha']
                exact congrArg Subtype.val (mul_inv_cancel σ)
              have h0 := congrArg (fun τ : Equiv.Perm (Fin 5) =>
                linCoeff5 τ) hprod
              have haa' : (a * a' : ZMod 5) = 1 := by
                have h1 := congrArg (ZMod.finEquiv 5) (Equiv.Perm.ext_iff.mp hprod 1)
                have h0' := congrArg (ZMod.finEquiv 5) (Equiv.Perm.ext_iff.mp hprod 0)
                simp only [Equiv.Perm.coe_mul, Function.comp_apply, affinePerm5_apply,
                  Equiv.Perm.one_apply, map_one, map_zero] at h1 h0'
                linear_combination h1 - h0'
              rw [ha, ha', linCoeff5_affinePerm5, linCoeff5_affinePerm5]
              exact haa'
            inv_val := by
              rcases σ.2 with ⟨a, b, ha⟩
              rcases σ⁻¹.2 with ⟨a', b', ha'⟩
              have hprod : affinePerm5 a b * affinePerm5 a' b' = 1 := by
                rw [← ha, ← ha']
                exact congrArg Subtype.val (mul_inv_cancel σ)
              have haa' : (a' * a : ZMod 5) = 1 := by
                have h1 := congrArg (ZMod.finEquiv 5) (Equiv.Perm.ext_iff.mp hprod 1)
                have h0' := congrArg (ZMod.finEquiv 5) (Equiv.Perm.ext_iff.mp hprod 0)
                simp only [Equiv.Perm.coe_mul, Function.comp_apply, affinePerm5_apply,
                  Equiv.Perm.one_apply, map_one, map_zero] at h1 h0'
                linear_combination h1 - h0'
              rw [ha, ha', linCoeff5_affinePerm5, linCoeff5_affinePerm5]
              exact haa' }
        map_one' := Units.ext (by simp [linCoeff5])
        map_mul' := fun σ₁ σ₂ => Units.ext (by
          rcases σ₁.2 with ⟨a₁, b₁, h₁⟩
          rcases σ₂.2 with ⟨a₂, b₂, h₂⟩
          dsimp only
          simp only [Units.val_mul]
          have h12 : (σ₁ * σ₂).1 = affinePerm5 (a₁ * a₂) ((a₁ : ZMod 5) * b₂ + b₁) := by
            apply Equiv.Perm.ext
            intro i
            apply (ZMod.finEquiv 5).injective
            simp only [Subgroup.coe_mul, h₁, h₂, Equiv.Perm.coe_mul, Function.comp_apply,
              affinePerm5_apply, Units.val_mul]
            ring
          rw [h12, h₁, h₂, linCoeff5_affinePerm5, linCoeff5_affinePerm5, linCoeff5_affinePerm5,
            Units.val_mul]) }
    have hker : homA.ker ≤ trans.range := by
      intro σ hσ
      rw [MonoidHom.mem_ker, Units.ext_iff] at hσ
      rcases σ.2 with ⟨a, b, ha⟩
      have ha1 : (a : ZMod 5) = 1 := by
        simpa [homA, ha, linCoeff5_affinePerm5] using hσ
      have ha_eq : a = 1 := Units.ext ha1
      refine ⟨Multiplicative.ofAdd b, Subtype.ext ?_⟩
      simp [trans, ha, ha_eq]
    have : Group.IsSolvable (Multiplicative (ZMod 5)) := Group.isSolvable_of_comm mul_comm
    have : Group.IsSolvable (ZMod 5)ˣ := Group.isSolvable_of_comm mul_comm
    exact Group.isSolvable_of_ker_le_range trans homA hker
  exact ⟨hcard20, hcard10, hsolv⟩

/-- Next index `(i + 1) mod 5` in `Fin 5`, and double step `(i + 2) mod 5`. -/
private def succ1 (i : Fin 5) : Fin 5 :=
  (ZMod.finEquiv 5).symm ((ZMod.finEquiv 5) i + 1)

private def succ2 (i : Fin 5) : Fin 5 :=
  (ZMod.finEquiv 5).symm ((ZMod.finEquiv 5) i + 2)

/-- Cayley–Weber degree-4 `F₂₀`-invariant of a 5-tuple `r : Fin 5 → R`:
`(∑ i, rᵢ r_{i+1} - ∑ i, rᵢ r_{i+2})²`. -/
def cayleyWeberRootInv {R : Type*} [CommRing R] (r : Fin 5 → R) : R :=
  (∑ i : Fin 5, r i * r (succ1 i) - ∑ i : Fin 5, r i * r (succ2 i)) ^ 2

private lemma cayleyWeberRootInv_comp_shift (b : ZMod 5) {R : Type*} [CommRing R] (r : Fin 5 → R) :
    cayleyWeberRootInv (fun i => r (affinePerm5 1 b i)) = cayleyWeberRootInv r := by
  let σ : Equiv.Perm (Fin 5) := affinePerm5 1 b
  have hs1 : ∀ i : Fin 5, σ (succ1 i) = succ1 (σ i) := fun i => by
    apply (ZMod.finEquiv 5).injective
    simp [σ, succ1, affinePerm5_apply]
    ring
  have hs2 : ∀ i : Fin 5, σ (succ2 i) = succ2 (σ i) := fun i => by
    apply (ZMod.finEquiv 5).injective
    simp [σ, succ2, affinePerm5_apply]
    ring
  change (∑ i : Fin 5, r (σ i) * r (σ (succ1 i)) -
      ∑ i : Fin 5, r (σ i) * r (σ (succ2 i))) ^ 2 = cayleyWeberRootInv r
  simp only [cayleyWeberRootInv, hs1, hs2]
  have hf1 : ∑ i : Fin 5, r (σ i) * r (succ1 (σ i)) = ∑ j : Fin 5, r j * r (succ1 j) :=
    Equiv.sum_comp σ fun j => r j * r (succ1 j)
  have hf2 : ∑ i : Fin 5, r (σ i) * r (succ2 (σ i)) = ∑ j : Fin 5, r j * r (succ2 j) :=
    Equiv.sum_comp σ fun j => r j * r (succ2 j)
  rw [hf1, hf2]

theorem cayleyWeberRootInv_frobenius20_invariant {R : Type*} [CommRing R] (r : Fin 5 → R)
    {τ : Equiv.Perm (Fin 5)} (hτ : τ ∈ frobenius20Subgroup) :
    cayleyWeberRootInv (fun i => r (τ i)) = cayleyWeberRootInv r := by
  rcases hτ with ⟨a, b, rfl⟩
  have hsplit : (fun i => r (affinePerm5 a b i)) =
      fun i => (fun j => r (affinePerm5 a 0 j)) (affinePerm5 1 ((↑a⁻¹ : ZMod 5) * b) i) := by
    funext i
    congr 1
    apply (ZMod.finEquiv 5).injective
    simp only [affinePerm5_apply, Units.val_one, one_mul, add_zero]
    rw [mul_add, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [hsplit]
  have hc := cayleyWeberRootInv_comp_shift ((↑a⁻¹ : ZMod 5) * b) (fun j => r (affinePerm5 a 0 j))
  rw [hc]
  have hs1 : succ1 0 = 1 ∧ succ1 1 = 2 ∧ succ1 2 = 3 ∧ succ1 3 = 4 ∧ succ1 4 = 0 := by decide
  have hs2 : succ2 0 = 2 ∧ succ2 1 = 3 ∧ succ2 2 = 4 ∧ succ2 3 = 0 ∧ succ2 4 = 1 := by decide
  have ha_cases : ∀ x : (ZMod 5)ˣ,
      (affinePerm5 x 0 0 = 0 ∧ affinePerm5 x 0 1 = 1 ∧ affinePerm5 x 0 2 = 2 ∧
        affinePerm5 x 0 3 = 3 ∧ affinePerm5 x 0 4 = 4) ∨
      (affinePerm5 x 0 0 = 0 ∧ affinePerm5 x 0 1 = 2 ∧ affinePerm5 x 0 2 = 4 ∧
        affinePerm5 x 0 3 = 1 ∧ affinePerm5 x 0 4 = 3) ∨
      (affinePerm5 x 0 0 = 0 ∧ affinePerm5 x 0 1 = 3 ∧ affinePerm5 x 0 2 = 1 ∧
        affinePerm5 x 0 3 = 4 ∧ affinePerm5 x 0 4 = 2) ∨
      (affinePerm5 x 0 0 = 0 ∧ affinePerm5 x 0 1 = 4 ∧ affinePerm5 x 0 2 = 3 ∧
        affinePerm5 x 0 3 = 2 ∧ affinePerm5 x 0 4 = 1) := by
    decide
  rcases ha_cases a with ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ |
      ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ <;>
    { simp only [cayleyWeberRootInv, Fin.sum_univ_five,
        hs1.1, hs1.2.1, hs1.2.2.1, hs1.2.2.2.1, hs1.2.2.2.2,
        hs2.1, hs2.2.1, hs2.2.2.1, hs2.2.2.2.1, hs2.2.2.2.2,
        h0, h1, h2, h3, h4]
      all_goals ring }

/-- Left-coset value of the Cayley–Weber invariant on `Equiv.Perm (Fin 5) ⧸ frobenius20Subgroup`. -/
def cayleyWeberCosetVal {R : Type*} [CommRing R] (r : Fin 5 → R) :
    (Equiv.Perm (Fin 5) ⧸ frobenius20Subgroup) → R :=
  Quotient.lift (fun g : Equiv.Perm (Fin 5) => cayleyWeberRootInv (fun i => r (g i)))
    (fun g₁ g₂ h => by
      have hmem : g₁⁻¹ * g₂ ∈ frobenius20Subgroup :=
        (QuotientGroup.leftRel_apply).mp h
      have heq : (fun i => r (g₂ i)) = fun i => (fun j => r (g₁ j)) ((g₁⁻¹ * g₂) i) := by
        funext i
        simp [Equiv.Perm.mul_apply]
      rw [heq]
      exact (cayleyWeberRootInv_frobenius20_invariant (fun j => r (g₁ j)) hmem).symm)

@[simp] theorem cayleyWeberCosetVal_mk {R : Type*} [CommRing R] (r : Fin 5 → R)
    (g : Equiv.Perm (Fin 5)) :
    cayleyWeberCosetVal r (QuotientGroup.mk g) = cayleyWeberRootInv (fun i => r (g i)) :=
  rfl

/-- Degree-6 monic Cayley–Weber sextic resolvent polynomial over `R[X]`. -/
noncomputable def cayleyWeberSexticResolvent {R : Type*} [CommRing R] (r : Fin 5 → R) : R[X] :=
  ∏ q : Equiv.Perm (Fin 5) ⧸ frobenius20Subgroup, (Polynomial.X - Polynomial.C (cayleyWeberCosetVal r q))

theorem cayleyWeberSexticResolvent_monic_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    (r : Fin 5 → R) :
    (cayleyWeberSexticResolvent r).Monic ∧ (cayleyWeberSexticResolvent r).natDegree = 6 := by
  have hm : (cayleyWeberSexticResolvent r).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun q _ => Polynomial.monic_X_sub_C _
  have hcard : Fintype.card (Equiv.Perm (Fin 5) ⧸ frobenius20Subgroup) = 6 := by
    have hidx : frobenius20Subgroup.index = 6 := by
      rw [Subgroup.index_eq_card_div, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
        frobenius20Subgroup_card_and_solvable.1]
      decide
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card] at hidx
    exact hidx
  refine ⟨hm, ?_⟩
  rw [cayleyWeberSexticResolvent, Polynomial.natDegree_prod_of_monic _ _ fun q _ =>
    Polynomial.monic_X_sub_C _]
  simp [hcard]

private noncomputable def algEquivRootPerm {K E : Type*} [Field K] [Field E] [Algebra K E]
    (P : K[X]) (σ : E ≃ₐ[K] E) : Equiv.Perm (P.rootSet E) where
  toFun y := ⟨σ y.1, (Polynomial.mem_rootSet).mpr
    ⟨(Polynomial.mem_rootSet.mp y.2).1, by
      change (Polynomial.aeval (σ.toAlgHom y.1)) P = 0
      rw [Polynomial.aeval_algHom_apply σ.toAlgHom y.1 P,
        (Polynomial.mem_rootSet.mp y.2).2, map_zero]⟩⟩
  invFun y := ⟨σ⁻¹ y.1, (Polynomial.mem_rootSet).mpr
    ⟨(Polynomial.mem_rootSet.mp y.2).1, by
      change (Polynomial.aeval (σ⁻¹.toAlgHom y.1)) P = 0
      rw [Polynomial.aeval_algHom_apply σ⁻¹.toAlgHom y.1 P,
        (Polynomial.mem_rootSet.mp y.2).2, map_zero]⟩⟩
  left_inv y := Subtype.ext (σ.left_inv y.1)
  right_inv y := Subtype.ext (σ.right_inv y.1)

/-- Faithful representation `Gal(E/K) →* S₅` induced by a root bijection `e : Fin 5 ≃ P.rootSet E`. -/
noncomputable def galFieldToPerm {K E : Type*} [Field K] [Field E] [Algebra K E]
    (P : K[X]) (e : Fin 5 ≃ P.rootSet E) : (E ≃ₐ[K] E) →* Equiv.Perm (Fin 5) where
  toFun σ := (e.trans (algEquivRootPerm P σ)).trans e.symm
  map_one' := by
    ext i
    simp [algEquivRootPerm]
  map_mul' σ₁ σ₂ := by
    ext i
    simp [algEquivRootPerm, Equiv.Perm.mul_apply]

theorem galFieldToPerm_spec {K E : Type*} [Field K] [Field E] [Algebra K E]
    (P : K[X]) (e : Fin 5 ≃ P.rootSet E) (σ : E ≃ₐ[K] E) (i : Fin 5) :
    (e (galFieldToPerm P e σ i)).1 = σ (e i).1 := by
  simp [galFieldToPerm, algEquivRootPerm]

theorem galFieldToPerm_injective {K E : Type*} [Field K] [Field E] [Algebra K E]
    (P : K[X]) [Polynomial.IsSplittingField K E P] (e : Fin 5 ≃ P.rootSet E) :
    Function.Injective (galFieldToPerm P e) := by
  intro σ₁ σ₂ h
  ext x
  have hx : x ∈ Algebra.adjoin K (P.rootSet E : Set E) := by
    rw [Polynomial.IsSplittingField.adjoin_rootSet E P]
    exact Algebra.mem_top
  refine (AlgHom.mem_equalizer σ₁.toAlgHom σ₂.toAlgHom x).mp ?_
  have hle : Algebra.adjoin K (P.rootSet E : Set E) ≤
      AlgHom.equalizer σ₁.toAlgHom σ₂.toAlgHom := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    obtain ⟨i, hi⟩ := e.surjective ⟨y, hy⟩
    have hy' : y = (e i).1 := congrArg Subtype.val hi.symm
    have hperm := Equiv.Perm.ext_iff.mp h i
    have h1 := galFieldToPerm_spec P e σ₁ i
    have h2 := galFieldToPerm_spec P e σ₂ i
    rw [hperm] at h1
    rw [hy']
    exact h1.symm.trans h2
  exact hle hx

/-- Canonical isomorphism `(E ≃ₐ[K] E) ≃* P.Gal` whenever `E` is a splitting field of `P`. -/
noncomputable def splittingGalMulEquiv {K E : Type*} [Field K] [Field E] [Algebra K E]
    (P : K[X]) [hsp : Polynomial.IsSplittingField K E P] :
    (E ≃ₐ[K] E) ≃* P.Gal :=
  let f : P.SplittingField →ₐ[K] E :=
    Polynomial.IsSplittingField.lift P.SplittingField P (Polynomial.IsSplittingField.splits E P)
  have hbij : Function.Bijective f := by
    refine ⟨f.injective, ?_⟩
    intro x
    have htop : (x : E) ∈ f.range := by
      rw [← Polynomial.IsSplittingField.adjoin_rootSet_eq_range P.SplittingField P f,
        Polynomial.IsSplittingField.adjoin_rootSet E P]
      exact Algebra.mem_top
    exact htop
  let eAlg : P.SplittingField ≃ₐ[K] E := AlgEquiv.ofBijective f hbij
  { toFun := fun σ => eAlg.trans (σ.trans eAlg.symm)
    invFun := fun τ => eAlg.symm.trans (τ.trans eAlg)
    left_inv := fun σ => by ext x; simp
    right_inv := fun τ => by
      ext x
      change eAlg.symm (eAlg (τ (eAlg.symm (eAlg x)))) = τ x
      rw [eAlg.symm_apply_apply, eAlg.symm_apply_apply]
    map_mul' := fun σ₁ σ₂ => by
      ext x
      change eAlg.symm ((σ₁ * σ₂) (eAlg x)) = eAlg.symm (σ₁ (eAlg (eAlg.symm (σ₂ (eAlg x)))))
      rw [AlgEquiv.mul_apply, eAlg.apply_symm_apply] }

theorem exists_rootEquiv_of_separable_degFive {K E : Type*} [Field K] [Field E] [Algebra K E]
    (P : K[X]) [Polynomial.IsSplittingField K E P] (hsep : P.Separable) (hdeg : P.natDegree = 5) :
    Nonempty (Fin 5 ≃ P.rootSet E) := by
  have hcard : Fintype.card (P.rootSet E) = 5 := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep (Polynomial.IsSplittingField.splits E P), hdeg]
  exact ⟨(Fintype.equivFinOfCardEq hcard).symm⟩

/-- Alternating-group (`Gal ⊆ A₅`) criterion via the root Vandermonde determinant. -/
def quinticVandermonde {E : Type*} [CommRing E] (r : Fin 5 → E) : E :=
  (Matrix.vandermonde r).det

theorem quinticVandermonde_alternating_iff {K E : Type*} [Field K] [Field E] [Algebra K E]
    (h2 : (2 : E) ≠ 0) (P : K[X]) [Polynomial.IsSplittingField K E P]
    (hsep : P.Separable) (e : Fin 5 ≃ P.rootSet E) :
    (∀ σ : E ≃ₐ[K] E, galFieldToPerm P e σ ∈ alternatingGroup (Fin 5)) ↔
      quinticVandermonde (fun i => (e i).1) ∈ Set.range (algebraMap K E) := by
  have : IsGalois K E := IsGalois.of_separable_splitting_field hsep
  have : FiniteDimensional K E := Polynomial.IsSplittingField.finiteDimensional E P
  have hinj : Function.Injective (fun i : Fin 5 => (e i).1) := fun i j hij =>
    e.injective (Subtype.ext hij)
  have hne : quinticVandermonde (fun i => (e i).1) ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  refine ⟨fun halt σ => ?_, fun hfix σ => ?_⟩
  · have hσ : galFieldToPerm P e σ ∈ alternatingGroup (Fin 5) := halt σ
    have hsign : Equiv.Perm.sign (galFieldToPerm P e σ) = 1 := hσ
    have hact : (fun i => σ (e i).1) = fun i => (e (galFieldToPerm P e σ i)).1 := by
      funext i
      exact (galFieldToPerm_spec P e σ i).symm
    have hmap : σ (quinticVandermonde (fun i => (e i).1)) =
        quinticVandermonde (fun i => σ (e i).1) := by
      simp only [quinticVandermonde, Matrix.det_vandermonde, map_prod, map_sub]
    rw [hmap, hact]
    change (Matrix.vandermonde (fun i => (e (galFieldToPerm P e σ i)).1)).det =
      quinticVandermonde (fun i => (e i).1)
    have hsub : Matrix.vandermonde (fun i => (e (galFieldToPerm P e σ i)).1) =
        (Matrix.vandermonde (fun i => (e i).1)).submatrix (galFieldToPerm P e σ) id := by
      ext i j
      simp [Matrix.vandermonde]
    rw [hsub, Matrix.det_permute, hsign, Units.val_one, Int.cast_one, one_mul]
    rfl
  · rw [Equiv.Perm.mem_alternatingGroup]
    have hmap : σ (quinticVandermonde (fun i => (e i).1)) =
        quinticVandermonde (fun i => σ (e i).1) := by
      simp only [quinticVandermonde, Matrix.det_vandermonde, map_prod, map_sub]
    have hact : (fun i => σ (e i).1) = fun i => (e (galFieldToPerm P e σ i)).1 := by
      funext i
      exact (galFieldToPerm_spec P e σ i).symm
    have heq := hfix σ
    rw [hmap, hact] at heq
    have hsub : Matrix.vandermonde (fun i => (e (galFieldToPerm P e σ i)).1) =
        (Matrix.vandermonde (fun i => (e i).1)).submatrix (galFieldToPerm P e σ) id := by
      ext i j
      simp [Matrix.vandermonde]
    change (Matrix.vandermonde (fun i => (e (galFieldToPerm P e σ i)).1)).det =
      quinticVandermonde (fun i => (e i).1) at heq
    rw [hsub, Matrix.det_permute] at heq
    have hmul1 : ((Equiv.Perm.sign (galFieldToPerm P e σ) : ℤ) : E) *
        quinticVandermonde (fun i => (e i).1) = 1 * quinticVandermonde (fun i => (e i).1) := by
      simpa [quinticVandermonde] using heq
    have hcast : ((Equiv.Perm.sign (galFieldToPerm P e σ) : ℤ) : E) = 1 :=
      mul_right_cancel₀ hne hmul1
    rcases Int.units_eq_one_or (Equiv.Perm.sign (galFieldToPerm P e σ)) with hs | hs
    · exact hs
    · exfalso
      rw [hs] at hcast
      norm_num at hcast
      exact h2 (by linear_combination -hcast)

/-- Descend any Galois-invariant polynomial over `E` uniquely to a polynomial in `K[X]`. -/
private theorem descendFixedPoly {K E : Type*} [Field K] [Field E] [Algebra K E]
    [IsGalois K E] [FiniteDimensional K E]
    (Q : E[X]) (hfix : ∀ σ : E ≃ₐ[K] E, Q.map σ.toRingHom = Q) :
    ∃! R : K[X], R.Monic = Q.Monic ∧ R.natDegree = Q.natDegree ∧
      R.map (algebraMap K E) = Q := by
  have hmem : ∀ i : ℕ, Q.coeff i ∈ Set.range (algebraMap K E) := fun i => by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    simpa [Polynomial.coeff_map] using congrArg (fun F : E[X] => F.coeff i) (hfix σ)
  let R : K[X] :=
    ∑ i ∈ Finset.range (Q.natDegree + 1),
      Polynomial.C (Classical.choose (hmem i)) * Polynomial.X ^ i
  have hR_map : R.map (algebraMap K E) = Q := by
    rw [Polynomial.map_sum]
    have hterm : ∀ i : ℕ,
        (Polynomial.C (Classical.choose (hmem i)) * Polynomial.X ^ i).map (algebraMap K E) =
          Polynomial.C (Q.coeff i) * Polynomial.X ^ i := fun i => by
      simp [Classical.choose_spec (hmem i)]
    simp_rw [hterm]
    exact (Polynomial.as_sum_range_C_mul_X_pow Q).symm
  have hinj : Function.Injective (algebraMap K E) := RingHom.injective (algebraMap K E)
  have hdeg : R.natDegree = Q.natDegree := by
    rw [← hR_map, Polynomial.natDegree_map_eq_of_injective hinj]
  have hmon : R.Monic ↔ Q.Monic := by
    rw [← hR_map, Polynomial.monic_map_iff]
  refine ⟨R, ⟨propext hmon, hdeg, hR_map⟩, fun R' ⟨_, _, hR'⟩ => ?_⟩
  exact Polynomial.map_injective (algebraMap K E) hinj (hR'.trans hR_map.symm)

/-- **Galois Sextic Resolvent Descent Theorem**:
For ANY separable quintic `P : K[X]` with splitting field `E` and root numbering `e : Fin 5 ≃ P.rootSet E`,
the Cayley–Weber sextic resolvent `cayleyWeberSexticResolvent (fun i => (e i).1)` is fixed by `Gal(E/K)`
and therefore descends UNIQUELY to a monic degree-6 resolvent polynomial `R₆ ∈ K[X]`. -/
theorem cayleyWeberSexticResolvent_descends {K E : Type*} [Field K] [Field E] [Algebra K E]
    (P : K[X]) [Polynomial.IsSplittingField K E P] (hsep : P.Separable)
    (e : Fin 5 ≃ P.rootSet E) :
    let r : Fin 5 → E := fun i => (e i).1
    ∃! R₆ : K[X], R₆.Monic ∧ R₆.natDegree = 6 ∧
      R₆.map (algebraMap K E) = cayleyWeberSexticResolvent r := by
  dsimp only
  let r : Fin 5 → E := fun i => (e i).1
  have : IsGalois K E := IsGalois.of_separable_splitting_field hsep
  have : FiniteDimensional K E := Polynomial.IsSplittingField.finiteDimensional E P
  have hfix : ∀ σ : E ≃ₐ[K] E, (cayleyWeberSexticResolvent r).map σ.toRingHom =
      cayleyWeberSexticResolvent r := by
    intro σ
    rw [cayleyWeberSexticResolvent, Polynomial.map_prod]
    let p : Equiv.Perm (Fin 5) := galFieldToPerm P e σ
    let eqv : (Equiv.Perm (Fin 5) ⧸ frobenius20Subgroup) ≃
        (Equiv.Perm (Fin 5) ⧸ frobenius20Subgroup) :=
      Equiv.ofBijective (fun q => p • q)
        ⟨fun q₁ q₂ h => smul_left_cancel p h, fun q => ⟨p⁻¹ • q, by simp⟩⟩
    have hact : ∀ q : Equiv.Perm (Fin 5) ⧸ frobenius20Subgroup,
        σ (cayleyWeberCosetVal r q) = cayleyWeberCosetVal r (p • q) := fun q => by
      refine Quotient.inductionOn q fun g => ?_
      change σ (cayleyWeberRootInv (fun i => r (g i))) =
        cayleyWeberRootInv (fun i => r ((p * g) i))
      have hpoly : σ (cayleyWeberRootInv (fun i => r (g i))) =
          cayleyWeberRootInv (fun i => σ (r (g i))) := by
        simp only [cayleyWeberRootInv, map_pow, map_sub, map_sum, map_mul]
      rw [hpoly]
      congr 1
      funext i
      exact (galFieldToPerm_spec P e σ (g i)).symm
    have hprod : ∏ q, ((Polynomial.X - Polynomial.C (cayleyWeberCosetVal r q)).map σ.toRingHom) =
        ∏ q, (Polynomial.X - Polynomial.C (cayleyWeberCosetVal r (p • q))) := by
      refine Finset.prod_congr rfl fun q _ => ?_
      simp [hact q]
    rw [hprod]
    exact Finset.prod_equiv eqv (fun _ => by simp) (fun q _ => rfl)
  obtain ⟨R₆, ⟨hmon_eq, hdeg_eq, hmap⟩, huniq⟩ :=
    descendFixedPoly (cayleyWeberSexticResolvent r) hfix
  rcases cayleyWeberSexticResolvent_monic_natDegree r with ⟨hmonQ, hdegQ⟩
  refine ⟨R₆, ⟨hmon_eq.mpr hmonQ, hdeg_eq.trans hdegQ, hmap⟩, ?_⟩
  intro R' ⟨_, _, hR'⟩
  exact huniq R' ⟨propext (by rw [← hR', Polynomial.monic_map_iff]),
    by rw [← hR', Polynomial.natDegree_map_eq_of_injective (RingHom.injective (algebraMap K E))],
    hR'⟩

/-- **Generic Quintic Galois Sextic Resolvent Theorem**:
Under generic separability of the 6 Cayley–Weber coset values, a descended resolvent `R₆ ∈ K[X]`
has a root in `K` IF AND ONLY IF the Galois group `Gal(E/K) ⊆ S₅` is conjugate to a subgroup of
`frobenius20Subgroup = AGL(1, 𝔽₅)` — which forces `Group.IsSolvable Gal(E/K)` (and `P.Gal`)! -/
theorem cayleyWeberSexticResolvent_galois_criterion {K E : Type*} [Field K] [Field E] [Algebra K E]
    (P : K[X]) [Polynomial.IsSplittingField K E P] (hsep : P.Separable)
    (e : Fin 5 ≃ P.rootSet E)
    (hdistinct : Function.Injective (cayleyWeberCosetVal (fun i => (e i).1)))
    {R₆ : K[X]} (hR₆ : R₆.map (algebraMap K E) = cayleyWeberSexticResolvent (fun i => (e i).1)) :
    ((∃ α : K, R₆.eval α = 0) ↔
        ∃ g : Equiv.Perm (Fin 5), (galFieldToPerm P e).range ≤
          Subgroup.map (MulAut.conj g).toMonoidHom frobenius20Subgroup) ∧
      ((∃ α : K, R₆.eval α = 0) →
        Group.IsSolvable (E ≃ₐ[K] E) ∧ Group.IsSolvable P.Gal) := by
  let r : Fin 5 → E := fun i => (e i).1
  have : IsGalois K E := IsGalois.of_separable_splitting_field hsep
  have : FiniteDimensional K E := Polynomial.IsSplittingField.finiteDimensional E P
  have hiff : (∃ α : K, R₆.eval α = 0) ↔
      ∃ g : Equiv.Perm (Fin 5), (galFieldToPerm P e).range ≤
        Subgroup.map (MulAut.conj g).toMonoidHom frobenius20Subgroup := by
    constructor
    · rintro ⟨α, hα⟩
      have hev : (cayleyWeberSexticResolvent r).eval (algebraMap K E α) = 0 := by
        rw [← hR₆, Polynomial.eval_map, Polynomial.eval₂_at_apply, hα, map_zero]
      rw [cayleyWeberSexticResolvent, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hev
      obtain ⟨q, _, hq0⟩ := hev
      obtain ⟨g, rfl⟩ := Quotient.exists_rep q
      have hval_eq : cayleyWeberCosetVal r (QuotientGroup.mk g) = algebraMap K E α :=
        sub_eq_zero.mp (by simpa using hq0) |>.symm
      have hfix : ∀ σ : E ≃ₐ[K] E, σ (cayleyWeberCosetVal r (QuotientGroup.mk g)) =
          cayleyWeberCosetVal r (QuotientGroup.mk g) := fun σ => by
        rw [hval_eq, AlgEquiv.commutes]
      refine ⟨g, ?_⟩
      rintro _ ⟨σ, rfl⟩
      have hact : σ (cayleyWeberCosetVal r (QuotientGroup.mk g)) =
          cayleyWeberCosetVal r (QuotientGroup.mk (galFieldToPerm P e σ * g)) := by
        have hpoly : σ (cayleyWeberRootInv (fun i => r (g i))) =
            cayleyWeberRootInv (fun i => σ (r (g i))) := by
          simp only [cayleyWeberRootInv, map_pow, map_sub, map_sum, map_mul]
        change σ (cayleyWeberRootInv (fun i => r (g i))) =
          cayleyWeberRootInv (fun i => r ((galFieldToPerm P e σ * g) i))
        rw [hpoly]
        congr 1
        funext i
        exact (galFieldToPerm_spec P e σ (g i)).symm
      have heq_coset : QuotientGroup.mk (galFieldToPerm P e σ * g) =
          (QuotientGroup.mk g : Equiv.Perm (Fin 5) ⧸ frobenius20Subgroup) :=
        hdistinct ((hact.symm.trans (hfix σ)))
      have hmemF : g⁻¹ * (galFieldToPerm P e σ * g) ∈ frobenius20Subgroup :=
        (QuotientGroup.eq).mp heq_coset.symm
      refine ⟨g⁻¹ * (galFieldToPerm P e σ * g), hmemF, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨g, hsub⟩
      have hfix : ∀ σ : E ≃ₐ[K] E,
          σ (cayleyWeberCosetVal r (QuotientGroup.mk g)) =
            cayleyWeberCosetVal r (QuotientGroup.mk g) := fun σ => by
        have hmem : galFieldToPerm P e σ ∈
            Subgroup.map (MulAut.conj g).toMonoidHom frobenius20Subgroup :=
          hsub ⟨σ, rfl⟩
        rcases hmem with ⟨τ, hτ, hτeq⟩
        have hperm : g⁻¹ * (galFieldToPerm P e σ * g) = τ := by
          have := congrArg (fun x => g⁻¹ * x * g) hτeq.symm
          simpa [MulAut.conj_apply, mul_assoc] using this
        have heq_coset : (QuotientGroup.mk (galFieldToPerm P e σ * g) :
              Equiv.Perm (Fin 5) ⧸ frobenius20Subgroup) = QuotientGroup.mk g := by
          symm
          rw [QuotientGroup.eq, hperm]
          exact hτ
        have hpoly : σ (cayleyWeberRootInv (fun i => r (g i))) =
            cayleyWeberRootInv (fun i => σ (r (g i))) := by
          simp only [cayleyWeberRootInv, map_pow, map_sub, map_sum, map_mul]
        change σ (cayleyWeberRootInv (fun i => r (g i))) = _
        rw [hpoly]
        have h1 : cayleyWeberRootInv (fun i => σ (r (g i))) =
            cayleyWeberCosetVal r (QuotientGroup.mk (galFieldToPerm P e σ * g)) := by
          change _ = cayleyWeberRootInv (fun i => r ((galFieldToPerm P e σ * g) i))
          congr 1
          funext i
          exact (galFieldToPerm_spec P e σ (g i)).symm
        rw [h1, heq_coset]
      obtain ⟨α, hα⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
        (cayleyWeberCosetVal r (QuotientGroup.mk g))).mpr hfix
      refine ⟨α, ?_⟩
      have hroot : (cayleyWeberSexticResolvent r).eval (algebraMap K E α) = 0 := by
        rw [hα, cayleyWeberSexticResolvent, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
        exact ⟨QuotientGroup.mk g, Finset.mem_univ _, by simp⟩
      rw [← hR₆, Polynomial.eval_map_algebraMap] at hroot
      exact (RingHom.injective (algebraMap K E)) (by simpa using hroot)
  refine ⟨hiff, fun hroot => ?_⟩
  obtain ⟨g, hsub⟩ := hiff.mp hroot
  have hsolvF : Group.IsSolvable frobenius20Subgroup :=
    frobenius20Subgroup_card_and_solvable.2.2
  have hsolvConj : Group.IsSolvable
      (Subgroup.map (MulAut.conj g).toMonoidHom frobenius20Subgroup) :=
    Group.isSolvable_of_surjective
      (f := (MulEquiv.subgroupMap (MulAut.conj g) frobenius20Subgroup).toMonoidHom)
      (MulEquiv.surjective _)
  have hsolvRange : Group.IsSolvable (galFieldToPerm P e).range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hsub)
  have heqv : (E ≃ₐ[K] E) ≃* (galFieldToPerm P e).range :=
    MulEquiv.ofBijective ((galFieldToPerm P e).rangeRestrict)
      ⟨fun a b h => galFieldToPerm_injective P e (congrArg Subtype.val h),
       (galFieldToPerm P e).rangeRestrict_surjective⟩
  have hsolvE : Group.IsSolvable (E ≃ₐ[K] E) :=
    Group.isSolvable_of_surjective (f := heqv.symm.toMonoidHom) heqv.symm.surjective
  have hsolvP : Group.IsSolvable P.Gal :=
    Group.isSolvable_of_surjective (f := (splittingGalMulEquiv (E := E) P).toMonoidHom)
      (splittingGalMulEquiv (E := E) P).surjective
  exact ⟨hsolvE, hsolvP⟩

/-- Contrapositive `A₅` Obstruction: if `alternatingGroup (Fin 5) ≤ (galFieldToPerm P e).range`
(e.g. an `A₅` or `S₅` quintic), then the Cayley–Weber sextic resolvent has NO root in `K`, and
no root of `P` lies in `solvableByRad K E`. -/
theorem quintic_A5_sextic_no_root {K E : Type*} [Field K] [Field E] [Algebra K E]
    (P : K[X]) [Polynomial.IsSplittingField K E P] (hsep : P.Separable)
    (hirr : Irreducible P)
    (e : Fin 5 ≃ P.rootSet E)
    (hdistinct : Function.Injective (cayleyWeberCosetVal (fun i => (e i).1)))
    {R₆ : K[X]} (hR₆ : R₆.map (algebraMap K E) = cayleyWeberSexticResolvent (fun i => (e i).1))
    (hA5 : alternatingGroup (Fin 5) ≤ (galFieldToPerm P e).range) :
    (¬ ∃ α : K, R₆.eval α = 0) ∧ ¬ Group.IsSolvable P.Gal ∧
      ∀ y : E, Polynomial.aeval y P = 0 → y ∉ solvableByRad K E := by
  have hcrit := cayleyWeberSexticResolvent_galois_criterion P hsep e hdistinct hR₆
  have hno_solvP : ¬ Group.IsSolvable P.Gal := by
    intro hsolvP
    have hsolvE : Group.IsSolvable (E ≃ₐ[K] E) :=
      Group.isSolvable_of_surjective (f := (splittingGalMulEquiv (E := E) P).symm.toMonoidHom)
        (splittingGalMulEquiv (E := E) P).symm.surjective
    have heqv : (E ≃ₐ[K] E) ≃* (galFieldToPerm P e).range :=
      MulEquiv.ofBijective ((galFieldToPerm P e).rangeRestrict)
        ⟨fun a b h => galFieldToPerm_injective P e (congrArg Subtype.val h),
         (galFieldToPerm P e).rangeRestrict_surjective⟩
    have hsolvR : Group.IsSolvable (galFieldToPerm P e).range :=
      Group.isSolvable_of_surjective (f := heqv.toMonoidHom) heqv.surjective
    exact not_isSolvable_alternatingGroup_five
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hA5))
  have hno_root : ¬ ∃ α : K, R₆.eval α = 0 := fun hex => hno_solvP (hcrit.2 hex).2
  refine ⟨hno_root, hno_solvP, fun y hy hrad => ?_⟩
  exact hno_solvP (isSolvable_gal_of_irreducible hrad hirr hy)

/-- **Universal Quadratic Tschirnhaus Reduction to Principal Quintic (`e₁ = 0` and `e₂ = 0`)**:
For any 5 roots `x : Fin 5 → K` in a field `[CharZero K]` (or `[Invertible (5 : K)]`), if `t, u`
solve the power-sum quadratic
`(5 * p₂ - p₁²) * t² + (10 * p₃ - 2 * p₁ * p₂) * t + (5 * p₄ - p₂²) = 0` and `5 * u = -(p₂ + p₁ * t)`,
then the transformed roots `yᵢ = xᵢ² + t xᵢ + u` have zero first and second power sums (`∑ yᵢ = 0`,
`∑ yᵢ² = 0`), eliminating BOTH `X⁴` and `X³` terms of the transformed quintic `∏ (X - yᵢ)`. -/
theorem tschirnhausPrincipal_powerSums_zero {K : Type*} [Field K] [CharZero K]
    (x : Fin 5 → K) (t u : K)
    (hp1 : let p₁ := ∑ i : Fin 5, x i
           let p₂ := ∑ i : Fin 5, x i ^ 2
           5 * u = -(p₂ + p₁ * t))
    (hp2 : let p₁ := ∑ i : Fin 5, x i
           let p₂ := ∑ i : Fin 5, x i ^ 2
           let p₃ := ∑ i : Fin 5, x i ^ 3
           let p₄ := ∑ i : Fin 5, x i ^ 4
           (5 * p₂ - p₁ ^ 2) * t ^ 2 + (10 * p₃ - 2 * p₁ * p₂) * t + (5 * p₄ - p₂ ^ 2) = 0) :
    let y : Fin 5 → K := fun i => x i ^ 2 + t * x i + u
    ∑ i : Fin 5, y i = 0 ∧ ∑ i : Fin 5, y i ^ 2 = 0 ∧
      (∏ i : Fin 5, (Polynomial.X - Polynomial.C (y i))).coeff 4 = 0 ∧
      (∏ i : Fin 5, (Polynomial.X - Polynomial.C (y i))).coeff 3 = 0 := by
  dsimp only at hp1 hp2 ⊢
  let p₁ : K := ∑ i : Fin 5, x i
  let p₂ : K := ∑ i : Fin 5, x i ^ 2
  let p₃ : K := ∑ i : Fin 5, x i ^ 3
  let p₄ : K := ∑ i : Fin 5, x i ^ 4
  let y : Fin 5 → K := fun i => x i ^ 2 + t * x i + u
  have hsum1 : ∑ i : Fin 5, y i = p₂ + t * p₁ + 5 * u := by
    simp only [y, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hy1 : ∑ i : Fin 5, y i = 0 := by
    rw [hsum1]
    linear_combination hp1
  have hsum2 : 5 * ∑ i : Fin 5, y i ^ 2 =
      ((5 * p₂ - p₁ ^ 2) * t ^ 2 + (10 * p₃ - 2 * p₁ * p₂) * t + (5 * p₄ - p₂ ^ 2)) +
        ((p₂ + p₁ * t + 5 * u) ^ 2) := by
    have hpt : ∀ i : Fin 5, y i ^ 2 =
        x i ^ 4 + 2 * t * x i ^ 3 + (t ^ 2 + 2 * u) * x i ^ 2 + (2 * t * u) * x i + u ^ 2 := fun i => by
      dsimp [y]; ring
    simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    change 5 * (p₄ + 2 * t * p₃ + (t ^ 2 + 2 * u) * p₂ + (2 * t * u) * p₁ + 5 * u ^ 2) = _
    ring
  have hy2 : ∑ i : Fin 5, y i ^ 2 = 0 := by
    have h5zero : (5 : K) * ∑ i : Fin 5, y i ^ 2 = 0 := by
      rw [hsum2, hp2, zero_add]
      have h0 : p₂ + p₁ * t + 5 * u = 0 := by linear_combination hp1
      rw [h0, zero_pow two_ne_zero]
    exact (mul_eq_zero.mp h5zero).resolve_left (by norm_num)
  have hexp : ∏ i : Fin 5, (Polynomial.X - Polynomial.C (y i)) =
      Polynomial.X ^ 5 -
        Polynomial.C (y 0 + y 1 + y 2 + y 3 + y 4) * Polynomial.X ^ 4 +
        Polynomial.C (y 0 * y 1 + y 0 * y 2 + y 0 * y 3 + y 0 * y 4 + y 1 * y 2 +
          y 1 * y 3 + y 1 * y 4 + y 2 * y 3 + y 2 * y 4 + y 3 * y 4) * Polynomial.X ^ 3 -
        Polynomial.C (y 0 * y 1 * y 2 + y 0 * y 1 * y 3 + y 0 * y 1 * y 4 + y 0 * y 2 * y 3 +
          y 0 * y 2 * y 4 + y 0 * y 3 * y 4 + y 1 * y 2 * y 3 + y 1 * y 2 * y 4 +
          y 1 * y 3 * y 4 + y 2 * y 3 * y 4) * Polynomial.X ^ 2 +
        Polynomial.C (y 0 * y 1 * y 2 * y 3 + y 0 * y 1 * y 2 * y 4 + y 0 * y 1 * y 3 * y 4 +
          y 0 * y 2 * y 3 * y 4 + y 1 * y 2 * y 3 * y 4) * Polynomial.X -
        Polynomial.C (y 0 * y 1 * y 2 * y 3 * y 4) := by
    rw [Fin.prod_univ_five]
    simp only [map_add, map_mul]
    ring
  have hcoeff4 : (∏ i : Fin 5, (Polynomial.X - Polynomial.C (y i))).coeff 4 = -(∑ i : Fin 5, y i) := by
    rw [hexp]
    simp only [Fin.sum_univ_five, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  have hcoeff3 : (∏ i : Fin 5, (Polynomial.X - Polynomial.C (y i))).coeff 3 =
      ((∑ i : Fin 5, y i) ^ 2 - ∑ i : Fin 5, y i ^ 2) / 2 := by
    rw [hexp]
    simp only [Fin.sum_univ_five, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
    field_simp
    ring
  refine ⟨hy1, hy2, ?_, ?_⟩
  · rw [hcoeff4, hy1, neg_zero]
  · rw [hcoeff3, hy1, hy2]
    norm_num

/-- **Exact Brioschi Normal Form Rescaling Identity**:
Any quintic `w⁵ - 10 M w³ + 45 M² w - K₀` (`M ≠ 0, K₀ ≠ 0`) rescales linearly via `w = (K₀ / M²) u`
to the 1-parameter Brioschi resolvent `u⁵ - 10 Z u³ + 45 Z² u - Z²` with `Z = M⁵ / K₀²`. -/
def brioschiResolventField {R : Type*} [CommRing R] (Z : R) : R[X] :=
  Polynomial.X ^ 5 - Polynomial.C (10 * Z) * Polynomial.X ^ 3 +
    Polynomial.C (45 * Z ^ 2) * Polynomial.X - Polynomial.C (Z ^ 2)

theorem brioschi_rescaling_identity {K : Type*} [Field K]
    (M K₀ u : K) (hM : M ≠ 0) (hK₀ : K₀ ≠ 0) :
    let s : K := K₀ / M ^ 2
    let Z : K := M ^ 5 / K₀ ^ 2
    let Q : K[X] := Polynomial.X ^ 5 - Polynomial.C (10 * M) * Polynomial.X ^ 3 +
      Polynomial.C (45 * M ^ 2) * Polynomial.X - Polynomial.C K₀
    Q.eval (s * u) = s ^ 5 * (brioschiResolventField Z).eval u := by
  dsimp only [brioschiResolventField]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  field_simp [hM, hK₀]

/-- **Splitting-Field Galois Homomorphism Under Polynomial Tschirnhaus Transform**:
For ANY polynomial `φ : K[X]`, the transformed quintic `Q` whose roots are `aeval (e i).1 φ` admits
a canonical surjective Galois homomorphism `P.Gal →* Q.Gal`, which upgrades to an isomorphism
`P.Gal ≃* Q.Gal` whenever the original roots lie back in `IntermediateField.adjoin K (Q.rootSet E)`. -/
theorem tschirnhaus_splitting_galois_hom {K E : Type*} [Field K] [Field E] [Algebra K E]
    (P Q : K[X]) [Polynomial.IsSplittingField K E P]
    (hQ_splits : (Q.map (algebraMap K E)).Splits) :
    Nonempty ((E ≃ₐ[K] E) →* Q.Gal) ∧
      Function.Surjective (@Polynomial.Gal.restrict K _ Q E _ _ ⟨hQ_splits⟩) ∧
      (Polynomial.IsSplittingField K E Q → Nonempty (P.Gal ≃* Q.Gal)) := by
  refine ⟨⟨@Polynomial.Gal.restrict K _ Q E _ _ ⟨hQ_splits⟩⟩,
    @Polynomial.Gal.restrict_surjective K _ Q E _ _ ⟨hQ_splits⟩ (Normal.of_isSplittingField P),
    fun hspQ => ?_⟩
  let eP : (E ≃ₐ[K] E) ≃* P.Gal := splittingGalMulEquiv P
  let eQ : (E ≃ₐ[K] E) ≃* Q.Gal := @splittingGalMulEquiv K E _ _ _ Q hspQ
  exact ⟨eP.symm.trans eQ⟩

end QuinticGaloisResolvent

/-- Master verification conjunction closing all three gaps on the icosahedral quintic and `j`
Hauptmodul owner: common `2I`/`A₅` invariance, `j` simple pole + level-1 Hauptmodul generation,
and generic Cayley–Weber Galois sextic resolvent + Tschirnhaus principal/Brioschi reduction. -/
theorem icosahedral_hauptmodul_galois_closure_master :
    (Matrix.det kleinAlignedIntertwiner ≠ 0) ∧
      (∀ (g : SU2), g ∈ binaryIcosahedralGroup → ∀ z₁ z₂ : ℂ,
        let w := kleinBinaryAction g z₁ z₂
        kleinAlignedVertexF w.1 w.2 = kleinAlignedVertexF z₁ z₂ ∧
          kleinAlignedFaceH w.1 w.2 = kleinAlignedFaceH z₁ z₂ ∧
          kleinAlignedEdgeT w.1 w.2 = kleinAlignedEdgeT z₁ z₂) ∧
      (Tendsto (fun q : ℂ => q * jCuspFunction q) (𝓝[≠] 0) (𝓝 1)) ∧
      Function.Injective (fun P : ℂ[X] => fun z : ℍ => P.eval (jInvariant z)) ∧
      (Nat.card frobenius20Subgroup = 20 ∧ Group.IsSolvable frobenius20Subgroup) ∧
      (∀ (n : ℕ) (g : ModularForm 𝒮ℒ (12 * (n : ℤ))),
        ∃! P : ℂ[X], P.natDegree ≤ n ∧
          ∀ z : ℍ, g z / ModularForm.discriminant z ^ n = P.eval (jInvariant z)) ∧
      (∀ (m : ℕ) (g₁ g₂ : ModularForm 𝒮ℒ (2 * (m : ℤ))), g₂ ≠ 0 →
        ∃ P Q : ℂ[X], Q ≠ 0 ∧ P.natDegree ≤ m ∧ Q.natDegree ≤ m ∧
          ∀ z : ℍ, Q.eval (jInvariant z) * g₁ z = P.eval (jInvariant z) * g₂ z) ∧
      (∀ (P : ℚ[X]) (E : Type) [Field E] [Algebra ℚ E] [Polynomial.IsSplittingField ℚ E P],
        P.Separable → ∀ e : Fin 5 ≃ P.rootSet E,
          ∃! R₆ : ℚ[X], R₆.Monic ∧ R₆.natDegree = 6 ∧
            R₆.map (algebraMap ℚ E) = cayleyWeberSexticResolvent (fun i => (e i).1)) ∧
      (∀ (P : ℚ[X]) (E : Type) [Field E] [Algebra ℚ E] [Polynomial.IsSplittingField ℚ E P],
        P.Separable → Irreducible P → ∀ e : Fin 5 ≃ P.rootSet E,
          Function.Injective (cayleyWeberCosetVal (fun i => (e i).1)) →
          ∀ {R₆ : ℚ[X]}, R₆.map (algebraMap ℚ E) = cayleyWeberSexticResolvent (fun i => (e i).1) →
          alternatingGroup (Fin 5) ≤ (galFieldToPerm P e).range →
            (¬ ∃ α : ℚ, R₆.eval α = 0) ∧ ¬ Group.IsSolvable P.Gal ∧
              ∀ y : E, Polynomial.aeval y P = 0 → y ∉ solvableByRad ℚ E) ∧
      (∀ (x : Fin 5 → ℂ) (t u : ℂ),
        5 * u = -((∑ i : Fin 5, x i ^ 2) + (∑ i : Fin 5, x i) * t) →
        (5 * (∑ i : Fin 5, x i ^ 2) - (∑ i : Fin 5, x i) ^ 2) * t ^ 2 +
          (10 * (∑ i : Fin 5, x i ^ 3) - 2 * (∑ i : Fin 5, x i) * (∑ i : Fin 5, x i ^ 2)) * t +
          (5 * (∑ i : Fin 5, x i ^ 4) - (∑ i : Fin 5, x i ^ 2) ^ 2) = 0 →
        let y : Fin 5 → ℂ := fun i => x i ^ 2 + t * x i + u
        ∑ i : Fin 5, y i = 0 ∧ ∑ i : Fin 5, y i ^ 2 = 0 ∧
          (∏ i : Fin 5, (Polynomial.X - Polynomial.C (y i))).coeff 4 = 0 ∧
          (∏ i : Fin 5, (Polynomial.X - Polynomial.C (y i))).coeff 3 = 0) ∧
      (∀ (M K₀ u : ℂ), M ≠ 0 → K₀ ≠ 0 →
        let s : ℂ := K₀ / M ^ 2
        let Z : ℂ := M ^ 5 / K₀ ^ 2
        let Q : ℂ[X] := Polynomial.X ^ 5 - Polynomial.C (10 * M) * Polynomial.X ^ 3 +
          Polynomial.C (45 * M ^ 2) * Polynomial.X - Polynomial.C K₀
        Q.eval (s * u) = s ^ 5 * (brioschiResolventField Z).eval u) :=
  ⟨(Matrix.isUnit_iff_isUnit_det _).mp kleinAlignedIntertwiner_isUnit |> IsUnit.ne_zero,
   fun _ hg z₁ z₂ => binaryIcosahedralGroup_invariant_alignedForms hg z₁ z₂,
   jCuspFunction_tendsto_simple_pole.1,
   jInvariant_aeval_injective,
   ⟨frobenius20Subgroup_card_and_solvable.1, frobenius20Subgroup_card_and_solvable.2.2⟩,
   modularForm_weight_twelve_mul_eq_poly_jInvariant,
   modularForm_even_weight_rational_jInvariant,
   fun P _E _ _ _ hsep e => cayleyWeberSexticResolvent_descends P hsep e,
   fun P _E _ _ _ hsep hirr e hdist _ hR6 hA5 => quintic_A5_sextic_no_root P hsep hirr e hdist hR6 hA5,
   tschirnhausPrincipal_powerSums_zero,
   brioschi_rescaling_identity⟩

end InfoGeometry.Canonical.KleinIcosahedralHauptmodulAndGaloisResolvent
