/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import InfoGeometry.Quantum.OrientedKitaevChain
import InfoGeometry.Quantum.AZTenFoldFullPeriodicTable
import InfoGeometry.Canonical.KitaevPinMinusParityArithmeticBridge
import InfoGeometry.PinMinus88Triality.PinMinus88TrialityPoset
import InfoGeometry.WignerHurwitzAdamsKTheory.WignerHurwitzAdamsKTheoryPoset

/-!
# Pin-Minus, BDI / Class-D Kitaev Chain Parity, and Normalized $\mathbb{Z}_8$ Rotor Bridge

## i. Overview

This module establishes the explicit typed cross-carrier bridges connecting:
1. **Oriented Finite Kitaev Chains (`InfoGeometry.Quantum.OrientedKitaevChain`)**:
   Signed matching-sum Pfaffian volume `chainVolume`, `ZMod 2` negative-Pfaffian parity `chainIndexZ2`,
   the 2-mode topological dimer cell `negativeGenerator` ($\mathrm{Pf} = -1$), and the parameterized
   4-mode two-site cell `kitaevFourModeCell mu t delta` ($\mathrm{Pf} = \mu^2 + t^2 - \Delta^2$).
2. **$\mathrm{Pin}_-(8,8)$ & $\mathcal{C}\ell(1,1)$ Matrix Algebra (`InfoGeometry.PinMinus88Triality.PinMinus88TrialityPoset`)**:
   The $2 \times 2$ complex structure `Mat2.complexJ`, parity reflection `Mat2.parityP`, time reflection
   `Mat2.timeT`, chiral product `Mat2.chiralPT = parityP * timeT`, and the 8th cyclotomic polynomial `Phi8`.
3. **BDI / $\mathrm{Pin}_-$ / Class-D Residue Arithmetic (`InfoGeometry.Canonical.KitaevPinMinusParityArithmeticBridge`)**:
   The ring homomorphisms `bdiIntegerToPinMinusEight : ℤ →+* ZMod 8`,
   `pinMinusEightToClassD : ZMod 8 →+* ZMod 2`, and the `ZMod 24 ≃+* ZMod 8 × ZMod 3` CRT split.
4. **Normalized $\mathrm{SO}(2)$ Eighth-Root Rotor Representation of `ZMod 8`**:
   Constructs `pinMinusNormalizedRotor2 = (1 / √2) • (I₂ - negativeGenerator.pairing)` in `Mat2 ℝ`,
   proves `Ûᵀ Û = 1`, `det Û = 1`, `Û² = -negativeGenerator.pairing`, `Û⁴ = -1 ≠ 1`, `Phi8 Û = 0`,
   and `Û⁸ = 1` (eliminating the unnormalized factor of `16` from `brownGaussU`), and proves that
   `pinMinusRotorZMod8 (z : ZMod 8) := Û ^ z.val` is an **injective** additive-to-multiplicative
   representation `ZMod 8 → Mat2 ℝ` whose index parity agrees with `chainIndexZ2 (List.replicate z.val negativeGenerator)`.

## ii. Key results

- `oriented_chainVolume_append`, `oriented_chainIndexZ2_append_of_chainVolume_ne_zero`
- `oriented_chainVolume_replicate_negativeGenerator`, `oriented_chainIndexZ2_replicate_negativeGenerator`
- `kitaevFourModeCell_index_dichotomy`
- `negativeGenerator_pairing_eq_pinMinus_parityP_and_chiralPT`
- `bdiChiralDimerCell`, `bdiChiralDimerCell_anticommutes_and_pfaffian`
- `oriented_chain_fusion_compatible_with_mod8_reduction`
- `oriented_negativeGenerator_stack_bdi_mod8_and_classD_parity`
- `pinMinusNormalizedRotor2`, `pinMinusNormalizedRotor2_orthogonal_and_order_eight`
- `pinMinusRotorZMod8`, `pinMinusRotorZMod8_homomorphism_and_injective`
- `pin_minus_bdi_kitaev_parity_and_zmod8_rotor_bridge`

## iii. Table of contents

- Section 1: Oriented Majorana Chain Concatenation, Gapped Parity Additivity & `n`-Stack Formula
- Section 2: Exact Matrix Carrier Identification & `ℤ → ZMod 8 → ZMod 2` Stack Factorization
- Section 3: Normalized $\mathrm{SO}(2)$ Eighth-Root Rotor $\hat{U}_8 \in \mathrm{Mat}_2(\mathbb{R})$ & Faithful `ZMod 8` Representation
- Section 4: Master Cross-Lane Synthesis (`pin_minus_bdi_kitaev_parity_and_zmod8_rotor_bridge`)

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `oriented_chainVolume_append`, `oriented_chainIndexZ2_append_of_chainVolume_ne_zero`,
  - `oriented_chainVolume_replicate_negativeGenerator`, `oriented_chainVolume_replicate_negativeGenerator_ne_zero`, `oriented_chainIndexZ2_replicate_negativeGenerator`,
  - `kitaevFourModeCell_index_dichotomy`,
  - `negativeGenerator_pairing_eq_pinMinus_parityP_and_chiralPT`,
  - `oriented_chain_parity_has_mod8_lift`, `oriented_chain_fusion_compatible_with_mod8_reduction`,
  - `oriented_negativeGenerator_stack_bdi_mod8_and_classD_parity`,
  - `pinMinusNormalizedRotor2_orthogonal_and_order_eight`,
  - `pinMinusRotorZMod8_homomorphism_and_injective`,
  - `pin_minus_bdi_kitaev_parity_and_zmod8_rotor_bridge`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Non-vanishing signed chain volume (`h₁ : chainVolume chain₁ ≠ 0`, `h₂ : chainVolume chain₂ ≠ 0`) is an explicit hypothesis in `oriented_chainIndexZ2_append_of_chainVolume_ne_zero` and `oriented_chain_fusion_compatible_with_mod8_reduction`.
* **BUCKET 3 — Out-of-Scope Continuum / Bordism Claims:**
  - Infinite-volume thermodynamic bulk classification, interacting many-body Fock-space Fidkowski–Kitaev phase maps, and smooth manifold $\Omega_2^{\mathrm{Pin}_-}(\mathrm{pt}) \cong \mathbb{Z}_8$ cobordism constructions remain outside this finite-dimensional matrix and chain-Pfaffian scope.

## iv. References

- L. Fidkowski and A. Kitaev, *Effects of interactions on the topological classification of free fermion systems*, Phys. Rev. B 81, 134509 (2010).
- A. Y. Kitaev, *Unpaired Majorana fermions in quantum wires*, Phys.-Usp. 44, 131 (2001).
- `InfoGeometry.Quantum.OrientedKitaevChain`
- `InfoGeometry.Canonical.KitaevPinMinusParityArithmeticBridge`
- `InfoGeometry.PinMinus88Triality.PinMinus88TrialityPoset`
-/

namespace InfoGeometry.PinMinus88Triality.PinMinusBDIKTheoryParityBridge

open Matrix
open InfoGeometry.Volume.OrientedPfaffian
open InfoGeometry.Quantum.OrientedKitaevChain
open InfoGeometry.Quantum.AZTenFoldFullPeriodicTable
open InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge
open InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian
open InfoGeometry.Canonical.KitaevPinMinusParityArithmeticBridge
open PinMinus88TrialityPoset

-- ============================================================================
-- SECTION 1: Oriented Majorana Chain Concatenation & n-Stack Formula
-- ============================================================================

/-- Signed chain volume is multiplicative under list concatenation of oriented cells. -/
theorem oriented_chainVolume_append (chain₁ chain₂ : List Cell) :
    chainVolume (chain₁ ++ chain₂) = chainVolume chain₁ * chainVolume chain₂ := by
  have hMap : (chain₁ ++ chain₂).map Cell.pfaffian =
      chain₁.map Cell.pfaffian ++ chain₂.map Cell.pfaffian :=
    List.map_append
  dsimp [chainVolume]
  rw [hMap, List.prod_append]

/-- In the gapped (nonzero `chainVolume`) sector, the `ZMod 2` negative-Pfaffian parity
of an oriented chain is additive under concatenation. -/
theorem oriented_chainIndexZ2_append_of_chainVolume_ne_zero
    (chain₁ chain₂ : List Cell)
    (h₁ : chainVolume chain₁ ≠ 0) (h₂ : chainVolume chain₂ ≠ 0) :
    chainIndexZ2 (chain₁ ++ chain₂) = chainIndexZ2 chain₁ + chainIndexZ2 chain₂ := by
  dsimp [chainIndexZ2]
  rw [oriented_chainVolume_append]
  exact pfaffianSignParity_mul_of_nonzero h₁ h₂

/-- A stack of `n` copies of `negativeGenerator` has signed chain volume `(-1) ^ n`. -/
theorem oriented_chainVolume_replicate_negativeGenerator (n : ℕ) :
    chainVolume (List.replicate n negativeGenerator) = (-1 : ℝ) ^ n := by
  have hMap : (List.replicate n negativeGenerator).map Cell.pfaffian =
      List.replicate n (-1 : ℝ) := by
    rw [List.map_replicate, negativeGenerator_pfaffian]
  dsimp [chainVolume]
  rw [hMap, List.prod_replicate]

/-- A stack of `n` copies of `negativeGenerator` always has nonzero signed chain volume. -/
theorem oriented_chainVolume_replicate_negativeGenerator_ne_zero (n : ℕ) :
    chainVolume (List.replicate n negativeGenerator) ≠ 0 := by
  rw [oriented_chainVolume_replicate_negativeGenerator]
  exact pow_ne_zero n (by norm_num)

/-- A stack of `n` copies of `negativeGenerator` has `ZMod 2` negative-Pfaffian parity `(n : ZMod 2)`. -/
theorem oriented_chainIndexZ2_replicate_negativeGenerator (n : ℕ) :
    chainIndexZ2 (List.replicate n negativeGenerator) = (n : ZMod 2) := by
  induction n with
  | zero =>
    dsimp [chainIndexZ2, chainVolume]
    simp
  | succ n ih =>
    have hrep : List.replicate (n + 1) negativeGenerator =
        [negativeGenerator] ++ List.replicate n negativeGenerator := by
      rw [List.replicate_succ]
      rfl
    have h1 : chainVolume [negativeGenerator] ≠ 0 :=
      oriented_chainVolume_replicate_negativeGenerator_ne_zero 1
    have hn : chainVolume (List.replicate n negativeGenerator) ≠ 0 :=
      oriented_chainVolume_replicate_negativeGenerator_ne_zero n
    rw [hrep, oriented_chainIndexZ2_append_of_chainVolume_ne_zero [negativeGenerator] _ h1 hn,
      singleton_negativeGenerator_index, ih, Nat.cast_add, Nat.cast_one, add_comm]

/-- **Two-Site Parameterized Oriented Kitaev Cell Phase Dichotomy**:
For `kitaevFourModeCell mu t delta`:
1. In the topological regime `μ² + (t² - Δ²) < 0`, `chainIndexZ2 [kitaevFourModeCell mu t delta] = 1`.
2. In the trivial/critical regime `0 ≤ μ² + (t² - Δ²)`, `chainIndexZ2 [kitaevFourModeCell mu t delta] = 0`. -/
theorem kitaevFourModeCell_index_dichotomy (mu t delta : ℝ) :
    (mu ^ 2 + (t ^ 2 - delta ^ 2) < 0 →
      chainIndexZ2 [kitaevFourModeCell mu t delta] = 1) ∧
    (0 ≤ mu ^ 2 + (t ^ 2 - delta ^ 2) →
      chainIndexZ2 [kitaevFourModeCell mu t delta] = 0) := by
  have hvol : chainVolume [kitaevFourModeCell mu t delta] = mu ^ 2 + (t ^ 2 - delta ^ 2) := by
    dsimp [chainVolume]
    rw [List.map_singleton, List.prod_singleton, kitaevFourModeCell_pfaffian,
      kitaev_pfaffian4_formula]
  refine ⟨fun hneg => ?_, fun hnonneg => ?_⟩
  · dsimp [chainIndexZ2]
    rw [hvol]
    simp [hneg]
  · dsimp [chainIndexZ2]
    rw [hvol]
    simp [not_lt.mpr hnonneg]

-- ============================================================================
-- SECTION 2: Exact Matrix Carrier Identification & ℤ → ZMod 8 → ZMod 2 Stack
-- ============================================================================

/-- The 2-mode topological Majorana pairing matrix `negativeGenerator.pairing` typed in `Mat2 ℝ`. -/
abbrev negGenPairing2 : Mat2 ℝ := negativeGenerator.pairing

/-- **Exact Matrix Carrier Identification (`negativeGenerator_pairing_eq_pinMinus_parityP_and_chiralPT`)**:
The $2 \times 2$ Majorana pairing matrix `negativeGenerator.pairing` (`negGenPairing2`) of the oriented
Kitaev cell is definitionally identical to the spacelike $\mathrm{Pin}_-$ reflection generator
`PinMinus88TrialityPoset.Mat2.parityP` (`P² = -I₂`) and to the chiral-time product
`Mat2.chiralPT * Mat2.timeT` in `Mat2 ℝ`:
1. `negGenPairing2 = Mat2.parityP`,
2. `negGenPairing2 = Mat2.chiralPT * Mat2.timeT`,
3. `negGenPairing2 * negGenPairing2 = -1`,
4. `Matrix.det negGenPairing2 = 1`. -/
theorem negativeGenerator_pairing_eq_pinMinus_parityP_and_chiralPT :
    negGenPairing2 = (Mat2.parityP : Mat2 ℝ) ∧
    negGenPairing2 = (Mat2.chiralPT : Mat2 ℝ) * Mat2.timeT ∧
    negGenPairing2 * negGenPairing2 = -1 ∧
    Matrix.det negGenPairing2 = 1 := by
  have hP : negGenPairing2 = (Mat2.parityP : Mat2 ℝ) := rfl
  have hCT : negGenPairing2 = (Mat2.chiralPT : Mat2 ℝ) * Mat2.timeT := by
    rw [hP]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Mat2.parityP, Mat2.chiralPT, Mat2.timeT, Matrix.mul_apply, Fin.sum_univ_two]
  have hSq : negGenPairing2 * negGenPairing2 = -1 := by
    rw [hP]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Mat2.parityP, Matrix.mul_apply, Fin.sum_univ_two]
  have hDet : Matrix.det negGenPairing2 = 1 := by
    rw [hP]
    dsimp [Mat2.parityP]
    rw [Matrix.det_fin_two]
    norm_num
  exact ⟨hP, hCT, hSq, hDet⟩

/-- Skew-symmetry of the $2 \times 2$ chiral BDI Majorana dimer matrix `!![(0 : ℝ), b; -b, 0]`. -/
private lemma bdiChiralDimer_skew (b : ℝ) :
    @InfoGeometry.Volume.OrientedPfaffian.IsSkew 1
      (!![(0 : ℝ), b; -b, 0] : Matrix (Fin (2 * 1)) (Fin (2 * 1)) ℝ) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp

/-- Concrete 2-mode chiral BDI Majorana dimer cell with real off-diagonal coupling `b : ℝ`:
$$A_{\mathrm{BDI}}(b) = \begin{pmatrix} 0 & b \\ -b & 0 \end{pmatrix} = (-b) \cdot \mathrm{parityP}.$$
It is skew-symmetric and anti-commutes with the chiral grading `Mat2.timeT = diag(1, -1)`. -/
def bdiChiralDimerCell (b : ℝ) : Cell where
  halfDim := 1
  pairing := !![(0 : ℝ), b; -b, 0]
  skew := bdiChiralDimer_skew b

/-- The $2 \times 2$ pairing matrix of `bdiChiralDimerCell b` typed in `Mat2 ℝ`. -/
abbrev bdiChiralDimerMat2 (b : ℝ) : Mat2 ℝ := (bdiChiralDimerCell b).pairing

/-- **Chiral BDI Dimer Anticommutation, Exact Pfaffian & Chain Product (`bdiChiralDimerCell_anticommutes_and_pfaffian`)**:
For the 2-mode chiral BDI dimer cell `bdiChiralDimerCell b`:
1. At `b = -1`, `bdiChiralDimerCell (-1) = negativeGenerator`.
2. Its pairing matrix anti-commutes with the $\mathbb{Z}_2$ chiral grading `Mat2.timeT` (`timeT² = I₂`):
   `bdiChiralDimerMat2 b * Mat2.timeT + Mat2.timeT * bdiChiralDimerMat2 b = 0`.
3. Its signed matching-sum Pfaffian is `(bdiChiralDimerCell b).pfaffian = b`.
4. For any finite list of couplings `bs : List ℝ`, `chainVolume (bs.map bdiChiralDimerCell) = bs.prod`. -/
theorem bdiChiralDimerCell_anticommutes_and_pfaffian (b : ℝ) (bs : List ℝ) :
    bdiChiralDimerCell (-1) = negativeGenerator ∧
    bdiChiralDimerMat2 b * (Mat2.timeT : Mat2 ℝ) +
      (Mat2.timeT : Mat2 ℝ) * bdiChiralDimerMat2 b = 0 ∧
    (bdiChiralDimerCell b).pfaffian = b ∧
    chainVolume (bs.map bdiChiralDimerCell) = bs.prod := by
  have hNeg1 : bdiChiralDimerCell (-1) = negativeGenerator := by
    dsimp [bdiChiralDimerCell, negativeGenerator]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hAnti : bdiChiralDimerMat2 b * (Mat2.timeT : Mat2 ℝ) +
      (Mat2.timeT : Mat2 ℝ) * bdiChiralDimerMat2 b = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bdiChiralDimerMat2, bdiChiralDimerCell, Mat2.timeT]
  have hPf : ∀ x : ℝ, (bdiChiralDimerCell x).pfaffian = x := by
    intro x
    change orientedPfaffian 1 (!![(0 : ℝ), x; -x, 0]) = x
    simpa using orientedPfaffian_fin_two x
  have hVol : chainVolume (bs.map bdiChiralDimerCell) = bs.prod := by
    induction bs with
    | nil =>
      dsimp [chainVolume]
      rfl
    | cons x xs ih =>
      simp only [chainVolume, List.map_cons, List.prod_cons, hPf x] at ih ⊢
      rw [ih]
  exact ⟨hNeg1, hAnti, hPf b, hVol⟩

/-- Every oriented Kitaev chain parity has a mod-8 arithmetic lift in `ZMod 8`. -/
theorem oriented_chain_parity_has_mod8_lift (chain : List Cell) :
    ∃ z : ZMod 8, pinMinusEightToClassD z = chainIndexZ2 chain := by
  have h := pinMinusEightToClassD_surjective (chainIndexZ2 chain)
  exact h

/-- **Oriented Chain Concatenation Compatibility with Mod-8 Reduction**:
If `z₁, z₂ : ZMod 8` reduce under `pinMinusEightToClassD : ZMod 8 →+* ZMod 2` to the
signed Pfaffian parities of two gapped oriented chains `chain₁, chain₂`, then `z₁ + z₂`
reduces to the signed Pfaffian parity of `chain₁ ++ chain₂`. -/
theorem oriented_chain_fusion_compatible_with_mod8_reduction
    (chain₁ chain₂ : List Cell) (z₁ z₂ : ZMod 8)
    (h₁ : chainVolume chain₁ ≠ 0) (h₂ : chainVolume chain₂ ≠ 0)
    (hz₁ : pinMinusEightToClassD z₁ = chainIndexZ2 chain₁)
    (hz₂ : pinMinusEightToClassD z₂ = chainIndexZ2 chain₂) :
    pinMinusEightToClassD (z₁ + z₂) = chainIndexZ2 (chain₁ ++ chain₂) := by
  rw [map_add, hz₁, hz₂,
    oriented_chainIndexZ2_append_of_chainVolume_ne_zero chain₁ chain₂ h₁ h₂]

/-- **Stack Realization of `ℤ →+* ZMod 8 →+* ZMod 2` on `List.replicate n negativeGenerator`**:
1. For any `n : ℕ`, reducing the BDI stack count `(n : ℤ)` through `ZMod 8` to `ZMod 2` equals
   the actual signed Pfaffian parity `chainIndexZ2 (List.replicate n negativeGenerator)`.
2. For any residue `z : ZMod 8`, the stack of `z.val` copies of `negativeGenerator` has
   `chainIndexZ2 (List.replicate z.val negativeGenerator) = pinMinusEightToClassD z`.
3. At `n = 1`: `bdiIntegerToPinMinusEight 1 = 1` and `chainIndexZ2 = 1` (both nontrivial).
4. At `n = 2` and `n = 4`: `chainIndexZ2 = 0` (class-D parity is already trivial for 2 or 4 chains),
   whereas `bdiIntegerToPinMinusEight 2 = 2 ≠ 0` and `bdiIntegerToPinMinusEight 4 = 4 ≠ 0` in `ZMod 8`.
5. At `n = 8`: both `bdiIntegerToPinMinusEight 8 = 0` and `chainIndexZ2 = 0`. -/
theorem oriented_negativeGenerator_stack_bdi_mod8_and_classD_parity :
    (∀ n : ℕ,
      pinMinusEightToClassD (bdiIntegerToPinMinusEight (n : ℤ)) =
        chainIndexZ2 (List.replicate n negativeGenerator)) ∧
    (∀ z : ZMod 8,
      chainIndexZ2 (List.replicate z.val negativeGenerator) =
        pinMinusEightToClassD z) ∧
    (bdiIntegerToPinMinusEight 1 = 1 ∧
      chainIndexZ2 (List.replicate 1 negativeGenerator) = 1) ∧
    (bdiIntegerToPinMinusEight 2 = 2 ∧ (2 : ZMod 8) ≠ 0 ∧
      chainIndexZ2 (List.replicate 2 negativeGenerator) = 0) ∧
    (bdiIntegerToPinMinusEight 4 = 4 ∧ (4 : ZMod 8) ≠ 0 ∧
      chainIndexZ2 (List.replicate 4 negativeGenerator) = 0) ∧
    (bdiIntegerToPinMinusEight 8 = 0 ∧
      chainIndexZ2 (List.replicate 8 negativeGenerator) = 0) := by
  have hStack : ∀ n : ℕ,
      pinMinusEightToClassD (bdiIntegerToPinMinusEight (n : ℤ)) =
        chainIndexZ2 (List.replicate n negativeGenerator) := by
    intro n
    rw [bdi_integer_reduction_factors_through_mod8,
      oriented_chainIndexZ2_replicate_negativeGenerator, Int.cast_natCast]
  have hZMod : ∀ z : ZMod 8,
      chainIndexZ2 (List.replicate z.val negativeGenerator) =
        pinMinusEightToClassD z := by
    intro z
    rw [oriented_chainIndexZ2_replicate_negativeGenerator]
    revert z
    decide
  have h1 : bdiIntegerToPinMinusEight 1 = 1 ∧
      chainIndexZ2 (List.replicate 1 negativeGenerator) = 1 := by
    refine ⟨rfl, ?_⟩
    rw [oriented_chainIndexZ2_replicate_negativeGenerator]
    rfl
  have h2 : bdiIntegerToPinMinusEight 2 = 2 ∧ (2 : ZMod 8) ≠ 0 ∧
      chainIndexZ2 (List.replicate 2 negativeGenerator) = 0 := by
    refine ⟨rfl, by decide, ?_⟩
    rw [oriented_chainIndexZ2_replicate_negativeGenerator]
    decide
  have h4 : bdiIntegerToPinMinusEight 4 = 4 ∧ (4 : ZMod 8) ≠ 0 ∧
      chainIndexZ2 (List.replicate 4 negativeGenerator) = 0 := by
    refine ⟨rfl, by decide, ?_⟩
    rw [oriented_chainIndexZ2_replicate_negativeGenerator]
    decide
  have h8 : bdiIntegerToPinMinusEight 8 = 0 ∧
      chainIndexZ2 (List.replicate 8 negativeGenerator) = 0 := by
    refine ⟨by decide, ?_⟩
    rw [oriented_chainIndexZ2_replicate_negativeGenerator]
    decide
  exact ⟨hStack, hZMod, h1, h2, h4, h8⟩

-- ============================================================================
-- SECTION 3: Normalized SO(2) Eighth-Root Rotor & Faithful ZMod 8 Representation
-- ============================================================================

/-- The normalized $2 \times 2$ $\mathrm{SO}(2)$ eighth-root rotor built from `Mat2.I2` and
`negGenPairing2` (`= Mat2.parityP`):
$$\hat{U}_8 = \frac{1}{\sqrt{2}}(I_2 - P) = \frac{1}{\sqrt{2}}\begin{pmatrix} 1 & 1 \\ -1 & 1 \end{pmatrix}.$$ -/
noncomputable def pinMinusNormalizedRotor2 : Mat2 ℝ :=
  (1 / Real.sqrt 2) • (Mat2.I2 - (Mat2.parityP : Mat2 ℝ))

/-- **Normalized Eighth-Root Rotor Orthogonality, $\Phi_8$ Root & Exact Order 8**:
In `Mat2 ℝ`, `pinMinusNormalizedRotor2` satisfies:
1. `pinMinusNormalizedRotor2ᵀ * pinMinusNormalizedRotor2 = 1` and `det pinMinusNormalizedRotor2 = 1`,
2. `pinMinusNormalizedRotor2 ^ 2 = -negGenPairing2`,
3. `pinMinusNormalizedRotor2 ^ 4 = -1` and `pinMinusNormalizedRotor2 ^ 4 ≠ 1`,
4. `pinMinusNormalizedRotor2 ^ 4 + 1 = 0` and `Polynomial.aeval pinMinusNormalizedRotor2 (Polynomial.cyclotomic 8 ℝ) = 0` (exact matrix root of $\Phi_8(X) = X^4 + 1 = 0$),
5. `pinMinusNormalizedRotor2 ^ 8 = 1` (exact period 8 without any unnormalized scalar factor). -/
theorem pinMinusNormalizedRotor2_orthogonal_and_order_eight :
    pinMinusNormalizedRotor2.transpose * pinMinusNormalizedRotor2 = 1 ∧
    Matrix.det pinMinusNormalizedRotor2 = 1 ∧
    pinMinusNormalizedRotor2 ^ 2 = -negGenPairing2 ∧
    pinMinusNormalizedRotor2 ^ 4 = -1 ∧
    pinMinusNormalizedRotor2 ^ 4 ≠ 1 ∧
    (pinMinusNormalizedRotor2 ^ 4 + 1 = 0 ∧
      Polynomial.aeval pinMinusNormalizedRotor2 (Polynomial.cyclotomic 8 ℝ) = 0) ∧
    pinMinusNormalizedRotor2 ^ 8 = 1 := by
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, hsqrt2]
  have hOrth : pinMinusNormalizedRotor2.transpose * pinMinusNormalizedRotor2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pinMinusNormalizedRotor2, Mat2.I2, Mat2.parityP, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.one_apply] <;>
      nlinarith [hinv2]
  have hDet : Matrix.det pinMinusNormalizedRotor2 = 1 := by
    simp [pinMinusNormalizedRotor2, Mat2.I2, Mat2.parityP, Matrix.det_fin_two]
    nlinarith [hinv2]
  have hSq : pinMinusNormalizedRotor2 ^ 2 = -negGenPairing2 := by
    rw [sq, negativeGenerator_pairing_eq_pinMinus_parityP_and_chiralPT.1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pinMinusNormalizedRotor2, Mat2.I2, Mat2.parityP, Matrix.mul_apply,
        Fin.sum_univ_two] <;>
      nlinarith [hinv2]
  have hPow4 : pinMinusNormalizedRotor2 ^ 4 = -1 := by
    have h4 : pinMinusNormalizedRotor2 ^ 4 =
        (pinMinusNormalizedRotor2 ^ 2) * (pinMinusNormalizedRotor2 ^ 2) := by
      noncomm_ring
    rw [h4, hSq, neg_mul_neg, negativeGenerator_pairing_eq_pinMinus_parityP_and_chiralPT.2.2.1]
  have hPow4Ne : pinMinusNormalizedRotor2 ^ 4 ≠ 1 := by
    rw [hPow4]
    intro hEq
    have h00 := congrArg (fun M : Mat2 ℝ => M 0 0) hEq
    norm_num at h00
  have hPhi8 : pinMinusNormalizedRotor2 ^ 4 + 1 = 0 := by
    rw [hPow4, neg_add_cancel]
  have hAeval : Polynomial.aeval pinMinusNormalizedRotor2 (Polynomial.cyclotomic 8 ℝ) = 0 := by
    have h8 : (8 : ℕ) = 2 ^ (2 + 1) := by decide
    rw [h8, Polynomial.cyclotomic_prime_pow_eq_geom_sum (by decide : Nat.Prime 2)]
    simpa [Finset.sum_range_succ, add_comm] using hPhi8
  have hPow8 : pinMinusNormalizedRotor2 ^ 8 = 1 := by
    have h8 : pinMinusNormalizedRotor2 ^ 8 =
        (pinMinusNormalizedRotor2 ^ 4) * (pinMinusNormalizedRotor2 ^ 4) := by
      noncomm_ring
    rw [h8, hPow4, neg_mul_neg, one_mul]
  exact ⟨hOrth, hDet, hSq, hPow4, hPow4Ne, ⟨hPhi8, hAeval⟩, hPow8⟩

/-- The `ZMod 8`-indexed rotor family `z ↦ pinMinusNormalizedRotor2 ^ z.val` in `Mat2 ℝ`. -/
noncomputable def pinMinusRotorZMod8 (z : ZMod 8) : Mat2 ℝ :=
  pinMinusNormalizedRotor2 ^ z.val

/-- **Faithful Additive-to-Multiplicative `ZMod 8` Representation (`pinMinusRotorZMod8_homomorphism_and_injective`)**:
1. `pinMinusRotorZMod8 0 = 1`, `pinMinusRotorZMod8 2 = -negGenPairing2`, and `pinMinusRotorZMod8 4 = -1`.
2. For all `z₁, z₂ : ZMod 8`, `pinMinusRotorZMod8 (z₁ + z₂) = pinMinusRotorZMod8 z₁ * pinMinusRotorZMod8 z₂`.
3. `pinMinusRotorZMod8` is injective on `ZMod 8` (all 8 residues produce distinct $2 \times 2$ orthogonal matrices). -/
theorem pinMinusRotorZMod8_homomorphism_and_injective :
    pinMinusRotorZMod8 0 = 1 ∧
    pinMinusRotorZMod8 2 = -negGenPairing2 ∧
    pinMinusRotorZMod8 4 = -1 ∧
    (∀ z₁ z₂ : ZMod 8,
      pinMinusRotorZMod8 (z₁ + z₂) = pinMinusRotorZMod8 z₁ * pinMinusRotorZMod8 z₂) ∧
    Function.Injective pinMinusRotorZMod8 := by
  have hOrd := pinMinusNormalizedRotor2_orthogonal_and_order_eight
  have hR0 : pinMinusRotorZMod8 0 = 1 := by
    dsimp [pinMinusRotorZMod8]
    simp
  have hR2 : pinMinusRotorZMod8 2 = -negGenPairing2 := by
    change pinMinusNormalizedRotor2 ^ 2 = -negGenPairing2
    exact hOrd.2.2.1
  have hR4 : pinMinusRotorZMod8 4 = -1 := by
    change pinMinusNormalizedRotor2 ^ 4 = -1
    exact hOrd.2.2.2.1
  have hR4Ne : pinMinusRotorZMod8 4 ≠ 1 := by
    change pinMinusNormalizedRotor2 ^ 4 ≠ 1
    exact hOrd.2.2.2.2.1
  have hHom : ∀ z₁ z₂ : ZMod 8,
      pinMinusRotorZMod8 (z₁ + z₂) = pinMinusRotorZMod8 z₁ * pinMinusRotorZMod8 z₂ := by
    intro z₁ z₂
    dsimp [pinMinusRotorZMod8]
    rw [← pow_add, ZMod.val_add]
    have hdiv := (Nat.div_add_mod (z₁.val + z₂.val) 8).symm
    conv_rhs => rw [hdiv]
    rw [pow_add, pow_mul, hOrd.2.2.2.2.2.2, one_pow, one_mul]
  have hcases_all : ∀ z : ZMod 8,
      z = 0 ∨ z = 4 ∨ (2 : ZMod 8) * z = 4 ∨ (4 : ZMod 8) * z = 4 := by
    decide
  have hEqOne : ∀ z : ZMod 8, pinMinusRotorZMod8 z = 1 → z = 0 := by
    intro z hz
    have hz2 : pinMinusRotorZMod8 (2 * z) = 1 := by
      have h2z : (2 : ZMod 8) * z = z + z := two_mul z
      rw [h2z, hHom, hz, mul_one]
    have hz4 : pinMinusRotorZMod8 (4 * z) = 1 := by
      have h4z : (4 : ZMod 8) * z = (2 * z) + (2 * z) := by ring
      rw [h4z, hHom, hz2, mul_one]
    rcases hcases_all z with rfl | rfl | h2 | h4
    · rfl
    · exfalso
      exact hR4Ne hz
    · exfalso
      rw [h2] at hz2
      exact hR4Ne hz2
    · exfalso
      rw [h4] at hz4
      exact hR4Ne hz4
  have hInj : Function.Injective pinMinusRotorZMod8 := by
    intro z₁ z₂ hEq
    have hSub : pinMinusRotorZMod8 (z₁ - z₂) = 1 := by
      have h1 : pinMinusRotorZMod8 (z₁ - z₂) * pinMinusRotorZMod8 z₂ =
          pinMinusRotorZMod8 z₁ := by
        rw [← hHom, sub_add_cancel]
      calc pinMinusRotorZMod8 (z₁ - z₂)
        _ = pinMinusRotorZMod8 (z₁ - z₂) * pinMinusRotorZMod8 (z₂ + -z₂) := by
          rw [add_neg_cancel, hR0, mul_one]
        _ = (pinMinusRotorZMod8 (z₁ - z₂) * pinMinusRotorZMod8 z₂) *
            pinMinusRotorZMod8 (-z₂) := by
          rw [hHom, mul_assoc]
        _ = pinMinusRotorZMod8 z₂ * pinMinusRotorZMod8 (-z₂) := by
          rw [h1, hEq]
        _ = pinMinusRotorZMod8 (z₂ + -z₂) := (hHom z₂ (-z₂)).symm
        _ = 1 := by rw [add_neg_cancel, hR0]
    exact sub_eq_zero.mp (hEqOne (z₁ - z₂) hSub)
  exact ⟨hR0, hR2, hR4, hHom, hInj⟩

-- ============================================================================
-- SECTION 4: Master Cross-Lane Synthesis
-- ============================================================================

/-- **Master Cross-Lane Bridge (`pin_minus_bdi_kitaev_parity_and_zmod8_rotor_bridge`)**:
Unifies the Altland–Zirnbauer 1D classification labels, the oriented Kitaev chain
signed Pfaffian carrier, the `PinMinus88TrialityPoset` $2 \times 2$ matrix carrier,
the normalized order-8 $\mathrm{SO}(2)$ rotor representation of `ZMod 8`, and the
`ZMod 24 ≃+* ZMod 8 × ZMod 3` CRT parity factorization:
1. `azFullTable AZClass.BDI 1 = .Z` and `azFullTable AZClass.D 1 = .Z2`,
2. `negGenPairing2 = Mat2.parityP = Mat2.chiralPT * Mat2.timeT`,
3. `∀ n : ℕ, pinMinusEightToClassD (bdiIntegerToPinMinusEight n) = chainIndexZ2 (List.replicate n negativeGenerator)`,
4. `pinMinusNormalizedRotor2 ^ 2 = -negGenPairing2`, `pinMinusNormalizedRotor2 ^ 4 = -1`,
   `Polynomial.aeval pinMinusNormalizedRotor2 (Polynomial.cyclotomic 8 ℝ) = 0`, and `pinMinusNormalizedRotor2 ^ 8 = 1`,
5. `Function.Injective pinMinusRotorZMod8` and `∀ z₁ z₂ : ZMod 8, pinMinusRotorZMod8 (z₁ + z₂) = pinMinusRotorZMod8 z₁ * pinMinusRotorZMod8 z₂`,
6. `∀ x : ZMod 24, pinMinus24ToClassD x = pinMinusEightToClassD (pinMinus24ToFactors x).1`,
7. `∀ s : ZMod 2 →+ ZMod 8, ¬ ∀ x : ZMod 2, pinMinusEightToClassD (s x) = x`. -/
theorem pin_minus_bdi_kitaev_parity_and_zmod8_rotor_bridge :
    (azFullTable AZClass.BDI 1 = TopologicalGroup.Z ∧
      azFullTable AZClass.D 1 = TopologicalGroup.Z2) ∧
    (negGenPairing2 = (Mat2.parityP : Mat2 ℝ) ∧
      negGenPairing2 = (Mat2.chiralPT : Mat2 ℝ) * Mat2.timeT) ∧
    (∀ n : ℕ,
      pinMinusEightToClassD (bdiIntegerToPinMinusEight (n : ℤ)) =
        chainIndexZ2 (List.replicate n negativeGenerator)) ∧
    (pinMinusNormalizedRotor2 ^ 2 = -negGenPairing2 ∧
      pinMinusNormalizedRotor2 ^ 4 = -1 ∧
      Polynomial.aeval pinMinusNormalizedRotor2 (Polynomial.cyclotomic 8 ℝ) = 0 ∧
      pinMinusNormalizedRotor2 ^ 8 = 1) ∧
    (Function.Injective pinMinusRotorZMod8 ∧
      ∀ z₁ z₂ : ZMod 8,
        pinMinusRotorZMod8 (z₁ + z₂) = pinMinusRotorZMod8 z₁ * pinMinusRotorZMod8 z₂) ∧
    (∀ x : ZMod 24,
      pinMinus24ToClassD x = pinMinusEightToClassD (pinMinus24ToFactors x).1) ∧
    (∀ s : ZMod 2 →+ ZMod 8,
      ¬ ∀ x : ZMod 2, pinMinusEightToClassD (s x) = x) := by
  have hMat := negativeGenerator_pairing_eq_pinMinus_parityP_and_chiralPT
  have hStack := oriented_negativeGenerator_stack_bdi_mod8_and_classD_parity
  have hOrd := pinMinusNormalizedRotor2_orthogonal_and_order_eight
  have hRep := pinMinusRotorZMod8_homomorphism_and_injective
  exact ⟨⟨class_BDI_1D_is_Z, class_D_1D_is_Z2⟩,
    ⟨hMat.1, hMat.2.1⟩,
    hStack.1,
    ⟨hOrd.2.2.1, hOrd.2.2.2.1, hOrd.2.2.2.2.2.1.2, hOrd.2.2.2.2.2.2⟩,
    ⟨hRep.2.2.2.2, hRep.2.2.2.1⟩,
    pinMinus24_parity_factors_through_mod8,
    pinMinusEightToClassD_no_additive_section⟩

end InfoGeometry.PinMinus88Triality.PinMinusBDIKTheoryParityBridge
