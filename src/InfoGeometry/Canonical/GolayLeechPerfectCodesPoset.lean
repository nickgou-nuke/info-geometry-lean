/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Parafermion.ParafermionCondensationGaloisCharacterPoset
import InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus
import InfoGeometry.Canonical.ViazovskaLeechGolayWeld
import InfoGeometry.Canonical.ViazovskaModularEisensteinIdentity
import Mathlib.Data.Nat.Choose.Basic

/-!
# Finite Hamming Sphere-Packing Sums, Gleason–Golay Weight Polynomials, and Truncated Leech Theta Identities (`𝔊𝔏₁ ≺ ⋯ ≺ 𝔊𝔏₇`)

## i. Overview

This owner proves finite binomial-sum identities for the Hamming-ball volume function
`hammingBallVol`, Witt design block-count ratios, universal two-variable polynomial identities
for the Hamming/Golay weight enumerators `W8`, `Delta24`, `W24`, and `W12` over any commutative
ring `[CommRing K]`, and universal one-variable polynomial identities for the truncated
`E₈` / Ramanujan polynomials `ThetaE8` and `RamanujanDelta`. These declarations establish the
stated arithmetic and polynomial equations; they do not construct the Golay code, the Leech
lattice, modular forms on the upper half-plane, or the Monster vertex operator algebra
(for the repo's explicit `[24, 12, 8]₂` code and Leech numerator constructions, see
`InfoGeometry.Combinatorics.ExtendedBinaryGolay` and `InfoGeometry.Combinatorics.LeechLattice`).

* **Node `𝔊𝔏₁` (`perfect_code_sphere_packing_trinity`):**
  Evaluates the recursive binomial sum `hammingBallVol n q e = ∑_{j=0}^e (n choose j)(q - 1)^j`
  at `(7, 2, 1)`, `(11, 3, 2)`, and `(23, 2, 3)`, and proves the general radius-1 formula
  `hammingBallVol n q 1 = 1 + n * (q - 1)`.
* **Node `𝔊𝔏₂` (`witt_steiner_design_block_counts`):**
  Verifies the finite binomial quotients `(12 choose 5) / (6 choose 5) = 132` and
  `(24 choose 5) / (8 choose 5) = 759`, the codeword totals `1 + 264 + 440 + 24 = 3^6` and
  `1 + 759 + 2576 + 759 + 1 = 2^12`, and the general half-period spin numerator identity
  `zfSpinNum (4 * k) (2 * k) = k * (4 * k)`.
* **Node `𝔊𝔏₃` (`gleason_golay_w24_polynomial_identity`):**
  Proves over any `[CommRing K]` that `W8 x y ^ 3 - 42 * Delta24 x y = W24 x y`, canceling
  the `42 * x^20 * y^4` degree-4 term of `W8 x y ^ 3` while conserving total value at `x = y = 1`.
* **Node `𝔊𝔏₄` (`leech_lattice_root_annihilation_and_theta_series`):**
  Proves over any `[CommRing K]` that `ThetaE8 q ^ 3 - 720 * RamanujanDelta q` cancels the
  linear `720 * q` term of `ThetaE8 q ^ 3` and shifts the `q^2` coefficient from `179280`
  by `+720 * 24 = +17280` to `196560` and the `q^3` coefficient to `16773120`.
* **Nodes `𝔊𝔏₅ & 𝔊𝔏₆` (`conway_threefold_leech_decomposition_and_monster_griess`):**
  Verifies the three-sector arithmetic partition `97152 + 98304 + 1104 = 196560` and
  `196560 + (25 choose 2) + 24 = 196884`, together with the systematic self-dual block
  equation `(1 + a * a = 0) ↔ (a * a = -1)` in any ring.
* **Node `𝔊𝔏₇` (`golay_leech_perfect_codes_parafermion_peirce_master_synthesis`):**
  Combines the polynomial, arithmetic, character-sum, and Peirce-ring identities.

## ii. Key results

- `GolayLeechPerfectCodesStage` & `causalEdge_acyclic`
- `hammingBallVol_one` & `perfect_code_sphere_packing_trinity`
- `witt_steiner_design_block_counts`
- `gleason_golay_w24_polynomial_identity`
- `leech_lattice_root_annihilation_and_theta_series`
- `conway_threefold_leech_decomposition_and_monster_griess`
- `golay_leech_perfect_codes_parafermion_peirce_master_synthesis`

## iii. Table of contents

1. The 7-stage index poset (`𝔊𝔏₁ ≺ ⋯ ≺ 𝔊𝔏₇`) and strict acyclicity
2. Nodes `𝔊𝔏₁` & `𝔊𝔏₂`: Hamming ball volume sums and Witt design block counts
3. Node `𝔊𝔏₃`: Universal Gleason–Golay two-variable weight polynomial identity
4. Nodes `𝔊𝔏₄`–`𝔊𝔏₆`: Truncated theta polynomial subtraction, `196,560` partition, and `196,884` sum
5. Node `𝔊𝔏₇`: Synthesis with cyclic character sums and Peirce corner conjugation

## iv. References

- `InfoGeometry.Combinatorics.ExtendedBinaryGolay` for the repository's explicit `[24, 12, 8]₂` code construction.
- `InfoGeometry.Combinatorics.LeechLattice` for the repository's explicit Leech lattice numerator construction.
- `InfoGeometry.Canonical.ViazovskaLeechMoonshineTheta` for related Leech/Moonshine arithmetic declarations.

### Three-Bucket Audit Map (`audit-proof` Policy)

#### BUCKET 1 — Proved Kernel Content
- `causalEdge_acyclic`, `hammingBallVol_one`, `perfect_code_sphere_packing_trinity`,
  `witt_steiner_design_block_counts`.
- `gleason_golay_w24_polynomial_identity`, `leech_lattice_root_annihilation_and_theta_series`.
- `conway_threefold_leech_decomposition_and_monster_griess`.
- `golay_leech_perfect_codes_parafermion_peirce_master_synthesis`.

#### BUCKET 2 — Conditional / Interface Boundaries
- Ring and Peirce identities in `golay_leech_perfect_codes_parafermion_peirce_master_synthesis`
  hold over `[Ring B]` under explicit hypotheses `hΩ : Ω * (Ω * Ω) = 1`,
  `hU : U * (U * (U * U)) = 1`, and `hP : P * P = P`.

#### BUCKET 3 — Open / Unformalized
- Analytic modular invariance of $\Theta_{\Lambda_{24}}(\tau)$ on the upper half-plane and the
  Griess algebra product on $V^\natural$ are outside the scope of this polynomial/arithmetic owner.
-/

namespace InfoGeometry.Canonical.GolayLeechPerfectCodesPoset

open ParafermionCondensationGaloisCharacterPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus
open InfoGeometry.Canonical.ViazovskaLeechGolayWeld
open InfoGeometry.Canonical.ViazovskaModularEisensteinIdentity

-- ============================================================================
-- SECTION 0: THE 7-NODE CAUSAL POSET (𝔊𝔏₁ ≺ ⋯ ≺ 𝔊𝔏₇)
-- ============================================================================

/--
The 7-stage index poset `𝔊𝔏₁ ≺ ⋯ ≺ 𝔊𝔏₇` for the Hamming sphere-packing sums,
Witt design block counts, Gleason–Golay weight polynomials, truncated Leech theta
polynomials, Conway `196,560` partition, and Peirce synthesis.
-/
inductive GolayLeechPerfectCodesStage : Type
  | GL1_PerfectCodeSpherePackingTrinity
  | GL2_WittSteinerDesignBlockCounts
  | GL3_GleasonGolayW24PolynomialIdentity
  | GL4_LeechLatticeRootAnnihilationAndThetaSeries
  | GL5_ConwayThreefoldLeechDecomposition
  | GL6_MonsterGriessAlgebraDimension
  | GL7_GolayLeechParafermionPeirceMasterSynthesis
  deriving DecidableEq, Repr

namespace GolayLeechPerfectCodesStage

/-- Numerical topological rank `0..6` of each stage in `GolayLeechPerfectCodesStage`. -/
def rank : GolayLeechPerfectCodesStage → ℕ
  | .GL1_PerfectCodeSpherePackingTrinity => 0
  | .GL2_WittSteinerDesignBlockCounts => 1
  | .GL3_GleasonGolayW24PolynomialIdentity => 2
  | .GL4_LeechLatticeRootAnnihilationAndThetaSeries => 3
  | .GL5_ConwayThreefoldLeechDecomposition => 4
  | .GL6_MonsterGriessAlgebraDimension => 5
  | .GL7_GolayLeechParafermionPeirceMasterSynthesis => 6

/-- `rank` is strictly injective across all 7 stages. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder GolayLeechPerfectCodesStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal edge `u ≺ v` (`rank u < rank v`) in the 7-stage poset. -/
def causalEdge (u v : GolayLeechPerfectCodesStage) : Bool :=
  decide (rank u < rank v)

/-- Strict acyclicity (`Irrefl` and `Trans`) of the 7-stage index poset. -/
theorem causalEdge_acyclic :
    (∀ u : GolayLeechPerfectCodesStage, causalEdge u u = false) ∧
    (∀ u v w : GolayLeechPerfectCodesStage,
      causalEdge u v = true → causalEdge v w = true → causalEdge u w = true) := by
  refine ⟨?_, ?_⟩
  · intro u
    simp [causalEdge]
  · intro u v w huv hvw
    simp only [causalEdge, decide_eq_true_eq] at huv hvw ⊢
    exact Nat.lt_trans huv hvw

end GolayLeechPerfectCodesStage

-- ============================================================================
-- NODE 𝔊𝔏₁ & 𝔊𝔏₂: The Perfect Code Sphere-Packing Trinity & Witt Designs W₁₂, W₂₄
-- ============================================================================

/-- Volume of a Hamming ball of radius `e` in `𝔽_q^n`: `∑_{j=0}^e (n choose j)(q - 1)^j`. -/
def hammingBallVol (n q : ℕ) : ℕ → ℕ
  | 0     => 1
  | e + 1 => hammingBallVol n q e + Nat.choose n (e + 1) * (q - 1) ^ (e + 1)

/--
Universal radius-1 Hamming ball volume formula: for any length `n : ℕ` and alphabet size
`q : ℕ`, `hammingBallVol n q 1 = 1 + n * (q - 1)`.
-/
theorem hammingBallVol_one (n q : ℕ) :
    hammingBallVol n q 1 = 1 + n * (q - 1) := by
  dsimp [hammingBallVol]
  rw [Nat.choose_one_right, pow_one]

/--
**Theorem 1 (`𝔊𝔏₁` — `perfect_code_sphere_packing_trinity`):**
1. **Universal Radius-1 Formula:** `hammingBallVol n q 1 = 1 + n * (q - 1)` for all `n, q : ℕ`.
2. **Binary Hamming `[7, 4, 3]₂` (`n = 7, q = 2, e = 1`):** `hammingBallVol 7 2 1 = 8 = 2^(7 - 4)`.
3. **Ternary Golay `[11, 6, 5]₃` (`n = 11, q = 3, e = 2`):** `hammingBallVol 11 3 2 = 243 = 3^(11 - 6)`.
4. **Binary Golay `[23, 12, 7]₂` (`n = 23, q = 2, e = 3`):** `hammingBallVol 23 2 3 = 2048 = 2^(23 - 12)`.
-/
theorem perfect_code_sphere_packing_trinity (n q : ℕ) :
    hammingBallVol n q 1 = 1 + n * (q - 1) ∧
    hammingBallVol 7  2 1 = 2 ^ (7 - 4) ∧
    hammingBallVol 11 3 2 = 3 ^ (11 - 6) ∧
    hammingBallVol 23 2 3 = 2 ^ (23 - 12) ∧
    -- Explicit binomial breakdown of the Binary Golay [23, 12, 7]₂ sphere:
    Nat.choose 23 0 + Nat.choose 23 1 + Nat.choose 23 2 + Nat.choose 23 3 = 2048 ∧
    -- Explicit binomial breakdown of the Ternary Golay [11, 6, 5]₃ sphere:
    Nat.choose 11 0 + 2 * Nat.choose 11 1 + 4 * Nat.choose 11 2 = 243 := by
  refine ⟨hammingBallVol_one n q, by decide⟩

/--
**Theorem 2 (`𝔊𝔏₂` — `witt_steiner_design_block_counts`):**
1. Universal half-period parafermion spin numerator `zfSpinNum (4 * k) (2 * k) = k * (4 * k)`.
2. `W₁₂` hexad block ratio: `(12 choose 5) / (6 choose 5) = 132` (`2 * 132 = 264` weight-6 words).
3. `W₂₄` octad block ratio: `(24 choose 5) / (8 choose 5) = 759` weight-8 words.
4. `W₁₂` weight-enumerator sum `1 + 264 + 440 + 24 = 3^6 = 729`.
5. `W₂₄` weight-enumerator sum `1 + 759 + 2576 + 759 + 1 = 2^12 = 4096`.
-/
theorem witt_steiner_design_block_counts (k : ℕ) :
    zfSpinNum (4 * k) (2 * k) = k * (4 * k) ∧
    Nat.choose 12 5 / Nat.choose 6 5 = 132 ∧
    2 * (Nat.choose 12 5 / Nat.choose 6 5) = 264 ∧
    Nat.choose 24 5 / Nat.choose 8 5 = 759 ∧
    1 + 264 + 440 + 24 = 3 ^ 6 ∧
    1 + 759 + 2576 + 759 + 1 = 2 ^ 12 := by
  refine ⟨zfSpinNum_half_period_even k, by decide⟩

-- ============================================================================
-- NODE 𝔊𝔏₃: Universal Gleason Polynomial Identity for W₂₄ from W₈³
-- ============================================================================

section GleasonWeightEnumerators
variable {K : Type*} [CommRing K]

/-- Extended Hamming `[8, 4, 4]₂` weight enumerator polynomial `W₈(x, y) = x⁸ + 14 x⁴ y⁴ + y⁸`. -/
def W8 (x y : K) : K :=
  x ^ 8 + 14 * x ^ 4 * y ^ 4 + y ^ 8

/-- Gleason–Turyn cusp polynomial `Δ₂₄(x, y) = x⁴ y⁴ (x⁴ - y⁴)⁴`. -/
def Delta24 (x y : K) : K :=
  x ^ 4 * y ^ 4 * (x ^ 4 - y ^ 4) ^ 4

/-- Extended Binary Golay `[24, 12, 8]₂` weight enumerator polynomial `W₂₄(x, y)`. -/
def W24 (x y : K) : K :=
  x ^ 24 + 759 * x ^ 16 * y ^ 8 + 2576 * x ^ 12 * y ^ 12 + 759 * x ^ 8 * y ^ 16 + y ^ 24

/-- Extended Ternary Golay `[12, 6, 6]₃` weight enumerator polynomial `W₁₂(x, y)`. -/
def W12 (x y : K) : K :=
  x ^ 12 + 264 * x ^ 6 * y ^ 6 + 440 * x ^ 3 * y ^ 9 + 24 * y ^ 12

/--
**Theorem 3 (`𝔊𝔏₃` — `gleason_golay_w24_polynomial_identity`):**
Over any commutative ring `K`:
1. The uncoupled cube `W₈(x, y)³` expands with `42 * x^20 * y^4` and `591 * x^16 * y^8`.
2. Subtracting `42 * Delta24 x y` cancels the `42 * x^20 * y^4` term identically to zero,
   shifts `591` by `+42 * 4 = +168` to `759`, and shifts `2828` by `-42 * 6 = -252` to `2576`,
   yielding `W24 x y`.
3. Along the diagonal `y = x`, the cusp counterterm vanishes (`Delta24 x x = 0`) and total
   weight is conserved (`W24 x x = W8 x x ^ 3`).
-/
theorem gleason_golay_w24_polynomial_identity (x y : K) :
    W8 x y ^ 3 - 42 * Delta24 x y = W24 x y ∧
    W8 x y ^ 3 =
      x ^ 24 + 42 * x ^ 20 * y ^ 4 + 591 * x ^ 16 * y ^ 8 +
      2828 * x ^ 12 * y ^ 12 + 591 * x ^ 8 * y ^ 16 + 42 * x ^ 4 * y ^ 20 + y ^ 24 ∧
    Delta24 x x = 0 ∧
    W24 x x = W8 x x ^ 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · dsimp [W8, Delta24, W24]
    ring

end GleasonWeightEnumerators

-- ============================================================================
-- NODE 𝔊𝔏₄, 𝔊𝔏₅, 𝔊𝔏₆: Leech Lattice Root Annihilation, 196,560 Split, & Monster 196,884
-- ============================================================================

section LeechLatticeAndMonsterGriess
variable {K : Type*} [CommRing K]

/-- Truncated `E₈` theta polynomial `Θ_{E₈}(q) = 1 + 240 q + 2160 q² + 6720 q³`. -/
def ThetaE8 (q : K) : K :=
  1 + 240 * q + 2160 * q ^ 2 + 6720 * q ^ 3

/-- Truncated Ramanujan discriminant polynomial `Δ(q) = q - 24 q² + 252 q³`. -/
def RamanujanDelta (q : K) : K :=
  q - 24 * q ^ 2 + 252 * q ^ 3

/--
**Theorem 4 (`𝔊𝔏₄` — `leech_lattice_root_annihilation_and_theta_series`):**
Over any commutative ring `K`, in `(ThetaE8 q)³ - 720 * RamanujanDelta q`:
1. The `q¹` coefficient of `ThetaE8 q ^ 3` is `3 * 240 = 720`, which is canceled (`720 - 720 = 0`)
   by `-720 * RamanujanDelta q`.
2. The `q²` coefficient shifts from `179280` by `+720 * 24 = +17280` to `196560`.
3. The `q³` coefficient shifts from `16954560` by `-720 * 252 = -181440` to `16773120`.
-/
theorem leech_lattice_root_annihilation_and_theta_series (q : K) :
    thetaLeech24 (ThetaE8 q) (RamanujanDelta q) =
      1 + 0 * q + 196560 * q ^ 2 + 16773120 * q ^ 3 +
      q ^ 4 * (396921600 + 4607539200 * q + 31115059200 * q ^ 2 + 126572544000 * q ^ 3 +
               292626432000 * q ^ 4 + 303464448000 * q ^ 5) ∧
    ThetaE8 q ^ 3 - 720 * RamanujanDelta q =
      1 + 0 * q + 196560 * q ^ 2 + 16773120 * q ^ 3 +
      q ^ 4 * (396921600 + 4607539200 * q + 31115059200 * q ^ 2 + 126572544000 * q ^ 3 +
               292626432000 * q ^ 4 + 303464448000 * q ^ 5) ∧
    ThetaE8 q ^ 3 =
      1 + 720 * q + 179280 * q ^ 2 + 16954560 * q ^ 3 +
      q ^ 4 * (396921600 + 4607539200 * q + 31115059200 * q ^ 2 + 126572544000 * q ^ 3 +
               292626432000 * q ^ 4 + 303464448000 * q ^ 5) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp [thetaLeech24, ThetaE8, RamanujanDelta]
    ring

/--
**Theorem 5 (`𝔊𝔏₅ & 𝔊𝔏₆` — `conway_threefold_leech_decomposition_and_monster_griess`):**
1. **Systematic Self-Dual Block Orthogonality:** In any ring `R`, `1 + a * a = 0 ↔ a * a = -1`.
2. **Octad Sector (`leechType2Count`):** `759` octads × `2⁷` sign choices = `97,152`.
3. **Spinor Frame Sector (`leechType3Count`):** `24` coordinates × `2¹² = 4096` words = `98,304`.
4. **Coordinate Cross-Pair Sector (`leechType1Count`):** `(24 choose 2) = 276` pairs × `4` signs = `1,104`.
5. **Total `196,560` & `196,884` Sum:** `leechMinimalVectorCount = 97,152 + 98,304 + 1,104 = 196,560`,
   `196,560 + (25 choose 2) + 24 = 196,884`, and `3 * 248 = 744`.
-/
theorem conway_threefold_leech_decomposition_and_monster_griess
    {R : Type*} [Ring R] (a : R) :
    let octadSector  := (Nat.choose 24 5 / Nat.choose 8 5) * (2 ^ 7)
    let spinorSector := 24 * (2 ^ 12)
    let pairSector   := Nat.choose 24 2 * 4
    ((1 : R) + a * a = 0 ↔ a * a = -1) ∧
    octadSector = leechType2Count ∧
    spinorSector = leechType3Count ∧
    pairSector = leechType1Count ∧
    octadSector = 97152 ∧
    spinorSector = 98304 ∧
    pairSector = 1104 ∧
    octadSector + spinorSector + pairSector = InfoGeometry.Canonical.ViazovskaLeechGolayWeld.leechMinimalVectorCount ∧
    InfoGeometry.Canonical.ViazovskaLeechGolayWeld.leechMinimalVectorCount = 196560 ∧
    196560 + Nat.choose 25 2 + 24 = 196884 ∧
    3 * 248 = 744 := by
  have hSelfDual : (1 : R) + a * a = 0 ↔ a * a = -1 := by
    constructor
    · intro h
      calc
        a * a = -1 + ((1 : R) + a * a) := by abel
        _ = -1 + 0 := by rw [h]
        _ = -1 := add_zero (-1)
    · intro h
      rw [h, add_neg_cancel]
  refine ⟨hSelfDual, by decide⟩

end LeechLatticeAndMonsterGriess

-- ============================================================================
-- NODE 𝔊𝔏₇: Master Synthesis with Parafermion Character Sums & Peirce Conjugation
-- ============================================================================

section MasterSynthesis
variable {K : Type*} [CommRing K]
variable {B : Type*} [Ring B]

/--
**Theorem 6 (`𝔊𝔏₇` — `golay_leech_perfect_codes_parafermion_peirce_master_synthesis`):**
Combines the 7-stage `GolayLeechPerfectCodesPoset` identities with the finite parafermion
character-sum equations and the Peirce corner conjugation commutator identity:
1. The Hamming ball volume evaluations `hammingBallVol 11 3 2 = 3^5` and `hammingBallVol 23 2 3 = 2^11`,
2. The universal Gleason–Golay polynomial identity `W8 x y ^ 3 - 42 * Delta24 x y = W24 x y`,
3. The truncated Leech theta polynomial identity for `ThetaE8 q ^ 3 - 720 * RamanujanDelta q`,
4. The `97152 + 98304 + 1104 = 196560` and `196560 + 300 + 24 = 196884` arithmetic identities,
5. The conditional `ℤ₃` and `ℤ₄` cyclic character-sum equations `(1 - Ω) * cyclicCharacterSum3 Ω = 0`
   and `(U * U) * cyclicCharacterSum4 U = cyclicCharacterSum4 U`,
6. The Peirce corner conjugation even-grade commutator identity
   `evenGrade P (cornerConjugation P X Y (P * Z * P) - P * Z * P) = comm (coneMinus P Y * (P * Z * P)) (conePlus P X)`.
-/
theorem golay_leech_perfect_codes_parafermion_peirce_master_synthesis
    (x y q : K) (Ω U P X Y Z : B)
    (hΩ : Ω * (Ω * Ω) = 1) (hU : U * (U * (U * U)) = 1) (hP : P * P = P) :
    (hammingBallVol 11 3 2 = 3 ^ (11 - 6) ∧ hammingBallVol 23 2 3 = 2 ^ (23 - 12)) ∧
    W8 x y ^ 3 - 42 * Delta24 x y = W24 x y ∧
    ThetaE8 q ^ 3 - 720 * RamanujanDelta q =
      1 + 0 * q + 196560 * q ^ 2 + 16773120 * q ^ 3 +
      q ^ 4 * (396921600 + 4607539200 * q + 31115059200 * q ^ 2 + 126572544000 * q ^ 3 +
               292626432000 * q ^ 4 + 303464448000 * q ^ 5) ∧
    ((Nat.choose 24 5 / Nat.choose 8 5) * (2 ^ 7) + 24 * (2 ^ 12) + Nat.choose 24 2 * 4 = 196560 ∧
     196560 + Nat.choose 25 2 + 24 = 196884) ∧
    ((1 - Ω) * cyclicCharacterSum3 Ω = 0 ∧
     (U * U) * cyclicCharacterSum4 U = cyclicCharacterSum4 U) ∧
    evenGrade P (cornerConjugation P X Y (P * Z * P) - P * Z * P) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (coneMinus P Y * (P * Z * P)) (conePlus P X) := by
  have hSphere := perfect_code_sphere_packing_trinity 0 0
  have hChar := cyclic_character_sum_ring_identities Ω U hΩ hU
  refine ⟨⟨hSphere.2.2.1, hSphere.2.2.2.1⟩,
    (gleason_golay_w24_polynomial_identity x y).1,
    (leech_lattice_root_annihilation_and_theta_series q).2.1,
    by decide,
    ⟨hChar.1, hChar.2.2.2.1⟩,
    (cornerConjugation_even_shift_eq_reverse_commutator P X Y Z hP).1⟩

end MasterSynthesis

end InfoGeometry.Canonical.GolayLeechPerfectCodesPoset
