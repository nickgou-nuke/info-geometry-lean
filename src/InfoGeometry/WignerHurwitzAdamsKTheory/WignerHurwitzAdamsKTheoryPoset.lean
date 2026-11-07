/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Quaternion
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset
import InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Quantum.Hurwitz

/-!
# Wigner–Clebsch–Gordan Projectors, Hurwitz Shell Arithmetic & Cyclotomic Polynomial Identities

## i. Overview

Finite algebraic formalization of the three directives over canonical Mathlib carriers
(`Matrix (Fin 3) (Fin 3) K`, `Quaternion K`, and `Polynomial.cyclotomic`). This file does not
construct a topological `J`-homomorphism, stable homotopy groups, Bott periodicity, or a
group-theoretic structure on the finite Hurwitz shell; its polynomial and numerical identities are
finite algebraic analogues.

1. **Directive 1 — Scaled Idempotency, Mutual Annihilation & Frobenius Pythagorean Law of
   the 4 Channel Maps on `Matrix (Fin 3) (Fin 3) K` (`𝔚ℌ₁–𝔚ℌ₃`):**
   - Re-exports the canonical carrier `Mat3 K := CliffordBottKTheoryWignerS4Poset.Mat3 K`
     (`Matrix (Fin 3) (Fin 3) K`) and its four division-free channel maps `Pi1, Pi2, Pi3_pos, Pi3_neg`.
   - `frobInner_eq_trace_transpose_mul`:
     Identifies `frobInner A B` with the canonical Mathlib trace inner product `Matrix.trace (Aᵀ * B)`.
   - `clebsch_gordan_s4_idempotency_and_mutual_orthogonality`:
     Proves `Pi1 M + Pi2 M + Pi3_pos M + Pi3_neg M = smul 6 M`,
     `Pi_α(Pi_α(M)) = smul 6 (Pi_α(M))` for all `α`, and `Pi_α(Pi_β(M)) = 0` for all `α ≠ β`.
   - `clebsch_gordan_frobenius_pythagorean_theorem`:
     Proves that under `frobInner`, cross-channel inner products vanish and
     `36 * frobInner M N = ∑_α frobInner (Pi_α M) (Pi_α N)`.
2. **Directive 2 — Quaternion Norm, Conjugation & Paraunitary Filter-Bank Identities (`𝔚ℌ₄–𝔚ℌ₅`):**
   - Uses Mathlib's canonical `Quat K := Quaternion K` (`ℍ[K]`), `qNorm := Quaternion.normSq`,
     and `conj := star`.
   - `hurwitz_corner_triality_attention_filter`:
     Verifies the numerical identities `8 + 2^4 = 24` and `24 + 6 * 4 = 48` (without defining
     finite groups or enumerating their elements), proves Euler's 4-square norm multiplicativity
     `qNorm(Q * X) = qNorm Q * qNorm X`, and proves that the scaled Hurwitz spinor corner
     `hurwitzW = ⟨1, 1, 1, 1⟩` (`qNorm hurwitzW = 4`) satisfies `W² - 2•W + 4•1 = 0` (`W³ = -8•1`)
     and cyclically permutes the three imaginary units:
     `W * i * conj W = 4•j`, `W * j * conj W = 4•k`, `W * k * conj W = 4•i`.
   - `hurwitz_quaternion_and_paraunitary_filter_bank_bridge`:
     Connects `Quat K = Quaternion K` to `DiscreteHurwitzCliffordWavelet.ParaunitaryCliffordFilterBank`
     and `CliffordCascadeSystem`.
3. **Directive 3 — Cyclotomic Polynomial Substitution `Φ₂₄(x) = Φ₆(x⁴)` (`𝔚ℌ₆–𝔚ℌ₇`):**
   - `eval_cyclotomic6_eq_Phi6` and `eval_cyclotomic24_eq_Phi24`:
     Identify `Phi6 y = y² - y + 1` and `Phi24 x = x⁸ - x⁴ + 1` with the evaluation of Mathlib's
     canonical `(Polynomial.cyclotomic 6 K).eval y` and `(Polynomial.cyclotomic 24 K).eval x`.
   - `adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge`:
     Proves `Phi6 (x ^ 4) = Phi24 x`, `(x ^ 4 + 1) * Phi24 x = x ^ 12 + 1`, and
     `(x ^ 12 - 1) * (x ^ 4 + 1) * Phi24 x = x ^ 24 - 1`. Here the exponent 4 is formal input to
     a polynomial identity; it is not derived from Bott periodicity, and the result does not prove
     a `J`-homomorphism or identify a stable homotopy group.

## ii. Key results

- `WignerHurwitzAdamsStage`, `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`
- `Mat3.frobInner_eq_trace_transpose_mul`
- `Mat3.Pi5_so3`, `Mat3.pi5_so3_eq_pi2_add_pi3_pos`, `Mat3.clebsch_gordan_s4_complete_12_annihilations_and_so3_branching`
- `Mat3.clebsch_gordan_s4_idempotency_and_mutual_orthogonality`
- `Mat3.clebsch_gordan_frobenius_pythagorean_theorem`
- `Quat.hurwitz_corner_triality_attention_filter`
- `Quat.hurwitz_quaternion_and_paraunitary_filter_bank_bridge`
- `Quat.rationalHurwitzChart_qNorm_one`
- `Quat.pin_minus_short_root_reflection_identities`
- `Quat.oddCosetU`, `Quat.hurwitzW'`, `Quat.oddCoset_integer_coordinate_identities`, `Quat.binary_octahedral_odd_coset_and_f4_root_norm_split`
- `cyclotomic_divisor_resolution_24`
- `eval_cyclotomic6_eq_Phi6`, `eval_cyclotomic8_eq_Phi8`, `eval_cyclotomic12_eq_Phi12`, `eval_cyclotomic24_eq_Phi24`
- `adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge`, `complete_cyclotomic_24_factorization_and_spectral_dimensions`
- `wh7_master_wigner_hurwitz_adams_synthesis`, `wh11_extended_wigner_hurwitz_adams_master_synthesis`

## iii. Table of contents

- Section 0: The 11-Stage Wigner–Hurwitz–Adams Poset (`𝔚ℌ₁ ≺ ⋯ ≺ 𝔚ℌ₁₁`)
- Section 1 (`𝔚ℌ₁–𝔚ℌ₃, 𝔚ℌ₈`): Scaled Channel Idempotents, `SO(3) ↓ O` Quadrupole Branching & Frobenius Pythagorean Law on `Matrix (Fin 3) (Fin 3) K`
- Section 2 (`𝔚ℌ₄–𝔚ℌ₅, 𝔚ℌ₉`): Quaternion `ℍ[K]` Norm, Conjugation Triality & Paraunitary Filter Bank Bridge
- Section 3 (`𝔚ℌ₆–𝔚ℌ₇, 𝔚ℌ₁₀–𝔚ℌ₁₁`): Cyclotomic Polynomial Substitution `Φ₂₄(x) = Φ₆(x⁴)` & Mathlib `cyclotomic` Bridge

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `WignerHurwitzAdamsStage` ($\mathfrak{WH}_1 \prec \dots \prec \mathfrak{WH}_{11}$), `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`,
  - `Mat3.frobInner_eq_trace_transpose_mul`, `Mat3.Pi5_so3`, `Mat3.pi5_so3_eq_pi2_add_pi3_pos`, `Mat3.clebsch_gordan_s4_complete_12_annihilations_and_so3_branching`,
  - `Mat3.clebsch_gordan_s4_idempotency_and_mutual_orthogonality`, `Mat3.clebsch_gordan_frobenius_pythagorean_theorem`,
  - `Quat.hurwitz_corner_triality_attention_filter`, `Quat.hurwitz_quaternion_and_paraunitary_filter_bank_bridge`, `Quat.rationalHurwitzChart_qNorm_one`,
  - `Quat.pin_minus_short_root_reflection_identities`,
  - `Quat.oddCosetU`, `Quat.hurwitzW'`, `Quat.oddCoset_integer_coordinate_identities`, `Quat.binary_octahedral_odd_coset_and_f4_root_norm_split`,
  - `cyclotomic_divisor_resolution_24`,
  - `eval_cyclotomic6_eq_Phi6`, `eval_cyclotomic8_eq_Phi8`, `eval_cyclotomic12_eq_Phi12`, `eval_cyclotomic24_eq_Phi24`,
  - `adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge`, `complete_cyclotomic_24_factorization_and_spectral_dimensions`,
  - `wh7_master_wigner_hurwitz_adams_synthesis`, `wh11_extended_wigner_hurwitz_adams_master_synthesis`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Commutative ring structure `[CommRing K]` is an explicit typeclass parameter for the polynomial, matrix, and quaternion identities.
* **BUCKET 3 — Out-of-Scope Empirical Claims:**
  - Continuous homotopy-group constructions of $\pi_3(\mathrm{SO}) \twoheadrightarrow \pi_3^s$, topological Bott periodicity, finite group constructions of $2T$ and $2O$, and empirical LLM linear probe experiments remain outside this algebraic owner.

## iv. References

- Karkada et al., *Symmetry in language statistics shapes the geometry of model representations*, arXiv:2602.15029 (2026).
- `InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset`.
-/

namespace WignerHurwitzAdamsKTheoryPoset

universe u

-- ============================================================================
-- SECTION 0: The 11-Stage Wigner–Hurwitz–Adams Poset (𝔚ℌ₁ ≺ ⋯ ≺ 𝔚ℌ₁₁)
-- ============================================================================

/-- The eleven named declaration-order stages ($\mathfrak{WH}_1 \prec \dots \prec \mathfrak{WH}_{11}$) for
the Wigner–Clebsch–Gordan projector idempotency and mutual annihilation, Frobenius Pythagorean
decomposition, numerical Hurwitz shell counts, Euler 4-square norm, quaternion conjugation,
polynomial substitution $\Phi_6(x^4) = \Phi_{24}(x)$, $\mathrm{SO}(3) \downarrow O$ quadrupole
branching, odd-coset quaternion conjugation by $U = 1 + \mathbf{i}$, and the 8-divisor cyclotomic
factorization of $x^{24} - 1$. The rank graph is acyclic by construction and does not prove
dependencies among these mathematical claims. The stage names are organizational; this declaration
constructs neither $2T$ nor $2O$, and defines no Adams map. -/
inductive WignerHurwitzAdamsStage : Type
  | wh1ClebschGordanSixIdResolutionAndIdempotency
  | wh2ClebschGordanMutualChannelAnnihilation
  | wh3FrobeniusOrthogonalityAndPythagoreanLaw
  | wh4Hurwitz24VsBinaryOctahedral48AndEulerNorm
  | wh5HurwitzCornerCyclotomicOrder6AndZ3Triality
  | wh6BottFourFoldCoverCyclotomicPhi24Composition
  | wh7AdamsJHomomorphismPeriod24MasterSynthesis
  | wh8So3QuadrupoleBranchingAnd12Annihilations
  | wh9BinaryOctahedralOddCosetAndF4RootNormSplit
  | wh10EightDivisorCyclotomicPolynomialsAndTotientSum
  | wh11Complete24StepCyclotomicFactorization
  deriving DecidableEq, Repr

namespace WignerHurwitzAdamsStage

/-- Numerical stage index `0 .. 10` for `WignerHurwitzAdamsStage`. -/
def rank : WignerHurwitzAdamsStage → ℕ
  | .wh1ClebschGordanSixIdResolutionAndIdempotency => 0
  | .wh2ClebschGordanMutualChannelAnnihilation => 1
  | .wh3FrobeniusOrthogonalityAndPythagoreanLaw => 2
  | .wh4Hurwitz24VsBinaryOctahedral48AndEulerNorm => 3
  | .wh5HurwitzCornerCyclotomicOrder6AndZ3Triality => 4
  | .wh6BottFourFoldCoverCyclotomicPhi24Composition => 5
  | .wh7AdamsJHomomorphismPeriod24MasterSynthesis => 6
  | .wh8So3QuadrupoleBranchingAnd12Annihilations => 7
  | .wh9BinaryOctahedralOddCosetAndF4RootNormSplit => 8
  | .wh10EightDivisorCyclotomicPolynomialsAndTotientSum => 9
  | .wh11Complete24StepCyclotomicFactorization => 10

/-- The stage rank map is injective. -/
lemma rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder WignerHurwitzAdamsStage :=
  LinearOrder.lift' rank rank_injective

instance instFintype : Fintype WignerHurwitzAdamsStage where
  elems := {
    .wh1ClebschGordanSixIdResolutionAndIdempotency,
    .wh2ClebschGordanMutualChannelAnnihilation,
    .wh3FrobeniusOrthogonalityAndPythagoreanLaw,
    .wh4Hurwitz24VsBinaryOctahedral48AndEulerNorm,
    .wh5HurwitzCornerCyclotomicOrder6AndZ3Triality,
    .wh6BottFourFoldCoverCyclotomicPhi24Composition,
    .wh7AdamsJHomomorphismPeriod24MasterSynthesis,
    .wh8So3QuadrupoleBranchingAnd12Annihilations,
    .wh9BinaryOctahedralOddCosetAndF4RootNormSplit,
    .wh10EightDivisorCyclotomicPolynomialsAndTotientSum,
    .wh11Complete24StepCyclotomicFactorization
  }
  complete x := by cases x <;> decide

/-- Immediate Hasse cover edges $\mathfrak{WH}_k \prec \mathfrak{WH}_{k+1}$ of the 11-stage spine. -/
inductive coverEdge : WignerHurwitzAdamsStage → WignerHurwitzAdamsStage → Prop
  | wh1_to_wh2 :
      coverEdge .wh1ClebschGordanSixIdResolutionAndIdempotency
        .wh2ClebschGordanMutualChannelAnnihilation
  | wh2_to_wh3 :
      coverEdge .wh2ClebschGordanMutualChannelAnnihilation
        .wh3FrobeniusOrthogonalityAndPythagoreanLaw
  | wh3_to_wh4 :
      coverEdge .wh3FrobeniusOrthogonalityAndPythagoreanLaw
        .wh4Hurwitz24VsBinaryOctahedral48AndEulerNorm
  | wh4_to_wh5 :
      coverEdge .wh4Hurwitz24VsBinaryOctahedral48AndEulerNorm
        .wh5HurwitzCornerCyclotomicOrder6AndZ3Triality
  | wh5_to_wh6 :
      coverEdge .wh5HurwitzCornerCyclotomicOrder6AndZ3Triality
        .wh6BottFourFoldCoverCyclotomicPhi24Composition
  | wh6_to_wh7 :
      coverEdge .wh6BottFourFoldCoverCyclotomicPhi24Composition
        .wh7AdamsJHomomorphismPeriod24MasterSynthesis
  | wh7_to_wh8 :
      coverEdge .wh7AdamsJHomomorphismPeriod24MasterSynthesis
        .wh8So3QuadrupoleBranchingAnd12Annihilations
  | wh8_to_wh9 :
      coverEdge .wh8So3QuadrupoleBranchingAnd12Annihilations
        .wh9BinaryOctahedralOddCosetAndF4RootNormSplit
  | wh9_to_wh10 :
      coverEdge .wh9BinaryOctahedralOddCosetAndF4RootNormSplit
        .wh10EightDivisorCyclotomicPolynomialsAndTotientSum
  | wh10_to_wh11 :
      coverEdge .wh10EightDivisorCyclotomicPolynomialsAndTotientSum
        .wh11Complete24StepCyclotomicFactorization

/-- Every Hasse cover edge strictly increases the stage rank. -/
lemma coverEdge_strictMono {a b : WignerHurwitzAdamsStage} (h : coverEdge a b) :
    a.rank < b.rank := by
  cases h <;> decide

/-- No stage has a cover edge to itself. -/
lemma coverEdge_acyclic (a : WignerHurwitzAdamsStage) : ¬ coverEdge a a := by
  intro h
  exact Nat.lt_irrefl a.rank (coverEdge_strictMono h)

end WignerHurwitzAdamsStage

-- ============================================================================
-- SECTION 1 (𝔚ℌ₁–𝔚ℌ₃): Scaled Channel Idempotents & Frobenius Pythagorean Law
-- ============================================================================

/-- Canonical `3 × 3` matrix carrier `Matrix (Fin 3) (Fin 3) K`, re-exported from
`CliffordBottKTheoryWignerS4Poset.Mat3 K`. -/
abbrev Mat3 (K : Type u) : Type u :=
  CliffordBottKTheoryWignerS4Poset.Mat3 K

namespace Mat3
variable {K : Type u} [CommRing K]

/-- Identity map to `CliffordBottKTheoryWignerS4Poset.Mat3 K = Matrix (Fin 3) (Fin 3) K`. -/
abbrev toMatrix (A : Mat3 K) : CliffordBottKTheoryWignerS4Poset.Mat3 K := A

/-- Identity map from `CliffordBottKTheoryWignerS4Poset.Mat3 K = Matrix (Fin 3) (Fin 3) K`. -/
abbrev ofMatrix (M : CliffordBottKTheoryWignerS4Poset.Mat3 K) : Mat3 K := M

/-- Matrix trace `A 0 0 + A 1 1 + A 2 2` on `Mat3 K = Matrix (Fin 3) (Fin 3) K`. -/
abbrev tr (A : Mat3 K) : K :=
  CliffordBottKTheoryWignerS4Poset.Mat3.tr A

/-- Scalar multiplication `c • A` on `Mat3 K = Matrix (Fin 3) (Fin 3) K`. -/
abbrev smul (c : K) (A : Mat3 K) : Mat3 K :=
  CliffordBottKTheoryWignerS4Poset.Mat3.smul c A

/-- Frobenius bilinear inner product `⟨A, B⟩_F = ∑_{i,j} A_{ij} B_{ij}` on `Mat3 K`. -/
abbrev frobInner (A B : Mat3 K) : K :=
  CliffordBottKTheoryWignerS4Poset.Mat3.frobInner A B

/-- Identifies `frobInner A B` with Mathlib's canonical matrix trace `Matrix.trace (A.transpose * B)`. -/
lemma frobInner_eq_trace_transpose_mul (A B : Mat3 K) :
    frobInner A B = Matrix.trace (Matrix.transpose A * B) := by
  simp [frobInner, CliffordBottKTheoryWignerS4Poset.Mat3.frobInner,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- Channel `1_triv` (`Π₁(M) = 2 Tr(M) I₃`, dim = 1) on `Mat3 K`. -/
abbrev Pi1 (M : Mat3 K) : Mat3 K :=
  CliffordBottKTheoryWignerS4Poset.Mat3.cgChan1_Triv M

/-- Channel `2_S3` (`Π₂(M)`, traceless diagonal quadrupole, dim = 2) on `Mat3 K`. -/
abbrev Pi2 (M : Mat3 K) : Mat3 K :=
  CliffordBottKTheoryWignerS4Poset.Mat3.cgChan2_Quadrupole M

/-- Channel `3_+` (`Π_{3+}(M) = 3(M + Mᵀ)_off`, symmetric off-diagonal strain, dim = 3) on `Mat3 K`. -/
abbrev Pi3_pos (M : Mat3 K) : Mat3 K :=
  CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_SymOff M

/-- Channel `3_-` (`Π_{3-}(M) = 3(M - Mᵀ)_off`, antisymmetric vorticity, dim = 3) on `Mat3 K`. -/
abbrev Pi3_neg (M : Mat3 K) : Mat3 K :=
  CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_AntisymVort M

/-- Scaled symmetric-traceless coordinate map on `3 × 3` matrices. Its formula alone does not
construct an `SO(3)` or octahedral representation. -/
def Pi5_so3 (M : Mat3 K) : Mat3 K :=
  (3 : K) • (M + Matrix.transpose M) - (2 * tr M) • (1 : Mat3 K)

/-- The symmetric-traceless coordinate map splits into its diagonal and off-diagonal parts.

This finite matrix identity is the coordinate `5 = 2 + 3` split; it does not by itself construct
the representation-theoretic restriction `SO(3) ↓ O`. -/
lemma pi5_so3_eq_pi2_add_pi3_pos (M : Mat3 K) :
    Pi5_so3 M = Pi2 M + Pi3_pos M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi5_so3, Pi2, Pi3_pos,
      CliffordBottKTheoryWignerS4Poset.Mat3.cgChan2_Quadrupole,
      CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_SymOff,
      tr, CliffordBottKTheoryWignerS4Poset.Mat3.tr,
      Matrix.transpose, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/--
**Theorem 1 (𝔚ℌ₁ & 𝔚ℌ₂ — Scaled Idempotency & Mutual Annihilation of the 4 Matrix Channels):**
For any `M : Mat3 K = Matrix (Fin 3) (Fin 3) K`:
1. `Pi1 M + Pi2 M + Pi3_pos M + Pi3_neg M = smul 6 M` (Complete resolution of `6 • id`);
2. `Pi_α (Pi_α M) = smul 6 (Pi_α M)` for all 4 channels `α ∈ {1, 2, 3_+, 3_-}`;
3. `Pi_α (Pi_β M) = 0` for all distinct channels `α ≠ β`.
-/
lemma clebsch_gordan_s4_idempotency_and_mutual_orthogonality (M : Mat3 K) :
    -- 1. Resolution of 6 • M:
    Pi1 M + Pi2 M + Pi3_pos M + Pi3_neg M = smul 6 M ∧
    -- 2. Scaled Idempotency (Π_α ∘ Π_α = 6 Π_α):
    Pi1 (Pi1 M) = smul 6 (Pi1 M) ∧
    Pi2 (Pi2 M) = smul 6 (Pi2 M) ∧
    Pi3_pos (Pi3_pos M) = smul 6 (Pi3_pos M) ∧
    Pi3_neg (Pi3_neg M) = smul 6 (Pi3_neg M) ∧
    -- 3. Mutual Annihilation (Π_α ∘ Π_β = 0 for α ≠ β):
    Pi1 (Pi2 M) = (0 : Mat3 K) ∧ Pi2 (Pi1 M) = (0 : Mat3 K) ∧
    Pi1 (Pi3_pos M) = (0 : Mat3 K) ∧ Pi3_pos (Pi1 M) = (0 : Mat3 K) ∧
    Pi1 (Pi3_neg M) = (0 : Mat3 K) ∧ Pi3_neg (Pi1 M) = (0 : Mat3 K) ∧
    Pi2 (Pi3_pos M) = (0 : Mat3 K) ∧ Pi3_pos (Pi2 M) = (0 : Mat3 K) ∧
    Pi2 (Pi3_neg M) = (0 : Mat3 K) ∧ Pi3_neg (Pi2 M) = (0 : Mat3 K) ∧
    Pi3_pos (Pi3_neg M) = (0 : Mat3 K) ∧ Pi3_neg (Pi3_pos M) = (0 : Mat3 K) := by
  have hDecomp :=
    (CliffordBottKTheoryWignerS4Poset.Mat3.wigner_clebsch_gordan_s4_four_channel_decomposition M).1.symm
  have hProj :=
    CliffordBottKTheoryWignerS4Poset.Mat3.wigner_clebsch_gordan_scaled_projector_laws M
  exact ⟨hDecomp, hProj⟩

/--
**Theorem 2 (𝔚ℌ₃ — Frobenius Orthogonality & Wigner–Eckart Pythagorean Theorem on `3 ⊗ 3`):**
For any `M, N : Mat3 K = Matrix (Fin 3) (Fin 3) K`:
1. Cross-channel Frobenius inner products vanish (`frobInner (Pi_α M) (Pi_β N) = 0` for `α ≠ β`);
2. The total Frobenius inner product decomposes additively across the 4 channels:
   `36 * frobInner M N = frobInner (Pi1 M) (Pi1 N) + frobInner (Pi2 M) (Pi2 N) + frobInner (Pi3_pos M) (Pi3_pos N) + frobInner (Pi3_neg M) (Pi3_neg N)`.
-/
lemma clebsch_gordan_frobenius_pythagorean_theorem (M N : Mat3 K) :
    frobInner (Pi1 M) (Pi2 N) = 0 ∧
    frobInner (Pi1 M) (Pi3_pos N) = 0 ∧
    frobInner (Pi2 M) (Pi3_pos N) = 0 ∧
    frobInner (Pi3_pos M) (Pi3_neg N) = 0 ∧
    36 * frobInner M N =
      frobInner (Pi1 M) (Pi1 N) +
      frobInner (Pi2 M) (Pi2 N) +
      frobInner (Pi3_pos M) (Pi3_pos N) +
      frobInner (Pi3_neg M) (Pi3_neg N) := by
  have hOrth :=
    CliffordBottKTheoryWignerS4Poset.Mat3.wigner_clebsch_gordan_frobenius_orthogonality M N
  exact ⟨hOrth.1, hOrth.2.2.1, hOrth.2.2.2.2.2.2.1,
    hOrth.2.2.2.2.2.2.2.2.2.2.1, hOrth.2.2.2.2.2.2.2.2.2.2.2.2⟩

/--
**Theorem 2b (𝔚ℌ₈ — Complete 12-Pair Projector Annihilation & `5 = 2 + 3` Quadrupole Split):**
For any `M, N : Mat3 K = Matrix (Fin 3) (Fin 3) K`:
1. `Pi2 M + Pi3_pos M = Pi5_so3 M` (`5 = 2 + 3_+` quadrupole coordinate split);
2. All 12 ordered off-diagonal projector compositions vanish (`Pi_α (Pi_β M) = 0` for `α ≠ β`);
3. All 6 cross-channel Frobenius inner product pairs vanish (`frobInner (Pi_α M) (Pi_β N) = 0` for `α ≠ β`)
   and `36 * frobInner M N = ∑_α frobInner (Pi_α M) (Pi_α N)`.
-/
lemma clebsch_gordan_s4_complete_12_annihilations_and_so3_branching (M N : Mat3 K) :
    -- 1. 5 = 2 + 3_+ quadrupole split:
    Pi2 M + Pi3_pos M = Pi5_so3 M ∧
    -- 2. All 12 ordered off-diagonal projector compositions vanish:
    Pi1 (Pi2 M) = (0 : Mat3 K) ∧ Pi2 (Pi1 M) = (0 : Mat3 K) ∧
    Pi1 (Pi3_pos M) = (0 : Mat3 K) ∧ Pi3_pos (Pi1 M) = (0 : Mat3 K) ∧
    Pi1 (Pi3_neg M) = (0 : Mat3 K) ∧ Pi3_neg (Pi1 M) = (0 : Mat3 K) ∧
    Pi2 (Pi3_pos M) = (0 : Mat3 K) ∧ Pi3_pos (Pi2 M) = (0 : Mat3 K) ∧
    Pi2 (Pi3_neg M) = (0 : Mat3 K) ∧ Pi3_neg (Pi2 M) = (0 : Mat3 K) ∧
    Pi3_pos (Pi3_neg M) = (0 : Mat3 K) ∧ Pi3_neg (Pi3_pos M) = (0 : Mat3 K) ∧
    -- 3. All 6 cross-channel Frobenius inner product pairs vanish + Pythagorean identity:
    frobInner (Pi1 M) (Pi2 N) = 0 ∧
    frobInner (Pi1 M) (Pi3_pos N) = 0 ∧
    frobInner (Pi1 M) (Pi3_neg N) = 0 ∧
    frobInner (Pi2 M) (Pi3_pos N) = 0 ∧
    frobInner (Pi2 M) (Pi3_neg N) = 0 ∧
    frobInner (Pi3_pos M) (Pi3_neg N) = 0 ∧
    36 * frobInner M N =
      frobInner (Pi1 M) (Pi1 N) +
      frobInner (Pi2 M) (Pi2 N) +
      frobInner (Pi3_pos M) (Pi3_pos N) +
      frobInner (Pi3_neg M) (Pi3_neg N) := by
  have hProj :=
    CliffordBottKTheoryWignerS4Poset.Mat3.wigner_clebsch_gordan_scaled_projector_laws M
  have hOrth :=
    CliffordBottKTheoryWignerS4Poset.Mat3.wigner_clebsch_gordan_frobenius_orthogonality M N
  exact ⟨(pi5_so3_eq_pi2_add_pi3_pos M).symm,
    hProj.2.2.2.2.1, hProj.2.2.2.2.2.1,
    hProj.2.2.2.2.2.2.1, hProj.2.2.2.2.2.2.2.1,
    hProj.2.2.2.2.2.2.2.2.1, hProj.2.2.2.2.2.2.2.2.2.1,
    hProj.2.2.2.2.2.2.2.2.2.2.1, hProj.2.2.2.2.2.2.2.2.2.2.2.1,
    hProj.2.2.2.2.2.2.2.2.2.2.2.2.1, hProj.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hProj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hProj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hOrth.1, hOrth.2.2.1, hOrth.2.2.2.2.1,
    hOrth.2.2.2.2.2.2.1, hOrth.2.2.2.2.2.2.2.2.1, hOrth.2.2.2.2.2.2.2.2.2.2.1,
    hOrth.2.2.2.2.2.2.2.2.2.2.2.2⟩

end Mat3

-- ============================================================================
-- SECTION 2 (𝔚ℌ₄–𝔚ℌ₅): Quaternion ℍ[K] Norm, Conjugation Triality & Paraunitary Filter Bank
-- ============================================================================

/-- Canonical quaternion carrier `Quaternion K` (`ℍ[K]`) over a commutative ring `K`. -/
abbrev Quat (K : Type u) [CommRing K] : Type u :=
  Quaternion K

namespace Quat
variable {K : Type u} [CommRing K]

/-- Scalar multiplication `c • q` on `Quat K = Quaternion K`. -/
def smul (c : K) (q : Quat K) : Quat K :=
  ⟨c * q.re, c * q.imI, c * q.imJ, c * q.imK⟩

/-- Quaternion conjugate `star q = ⟨q.re, -q.imI, -q.imJ, -q.imK⟩` on `Quat K = Quaternion K`. -/
abbrev conj (q : Quat K) : Quat K :=
  star q

/-- Quaternion norm squared `Quaternion.normSq q` on `Quat K = Quaternion K`. -/
abbrev qNorm (q : Quat K) : K :=
  Quaternion.normSq q

/-- Identity map from `Quat K` to Mathlib's `Quaternion K` (`ℍ[K]`). -/
abbrev toQuaternion (q : Quat K) : Quaternion K := q

/-- Identity map from Mathlib's `Quaternion K` (`ℍ[K]`) to `Quat K`. -/
abbrev ofQuaternion (q : Quaternion K) : Quat K := q

/-- Quaternion unit `1 = ⟨1, 0, 0, 0⟩` in `Quat K = Quaternion K`. -/
def qOne : Quat K := ⟨1, 0, 0, 0⟩

/-- Imaginary basis unit `i = ⟨0, 1, 0, 0⟩` in `Quat K = Quaternion K`. -/
def qi : Quat K := ⟨0, 1, 0, 0⟩

/-- Imaginary basis unit `j = ⟨0, 0, 1, 0⟩` in `Quat K = Quaternion K`. -/
def qj : Quat K := ⟨0, 0, 1, 0⟩

/-- Imaginary basis unit `k = ⟨0, 0, 0, 1⟩` in `Quat K = Quaternion K`. -/
def qk : Quat K := ⟨0, 0, 0, 1⟩

/-- Scaled Hurwitz spinor corner `W = ⟨1, 1, 1, 1⟩` (twice `ω = ½(1 + i + j + k)`) in `Quat K`. -/
def hurwitzW : Quat K := ⟨1, 1, 1, 1⟩

/-- Integer-coordinate short-root representative `1 + i`; it has norm-square `2`.
This is not itself a unit in `Quaternion K` unless `2` is normalized in a suitable extension. -/
def oddCosetU : Quat K := ⟨1, 1, 0, 0⟩

/-- A second integer Hurwitz corner used as the output of a conjugation identity. -/
def hurwitzW' : Quat K := ⟨1, 1, -1, 1⟩

/-- Pure imaginary short-root representative `R = j - k` for the Pin-minus reflection calculation. -/
def pinMinusRootJK : Quat K := ⟨0, 0, 1, -1⟩

/-- Embed a coordinate vector into the pure imaginary quaternions. -/
def imagQuaternion3 (x y z : K) : Quat K := ⟨0, x, y, z⟩

/-- The finite quaternion identity behind the twisted Pin-minus reflection lift.
The root is unnormalized: its norm-square is `2`, its square is `-2`, and `q ↦ R q R`
acts on the three imaginary basis vectors as `i ↦ i`, `j ↦ k`, `k ↦ j`, each with scale `2`.
This calculation does not construct a Pin group or a covering map. -/
lemma pin_minus_short_root_reflection_identities :
    qNorm (pinMinusRootJK : Quat K) = 2 ∧
    (pinMinusRootJK : Quat K) * pinMinusRootJK = smul (-2) qOne ∧
    (pinMinusRootJK : Quat K) * qi * pinMinusRootJK = smul 2 qi ∧
    (pinMinusRootJK : Quat K) * qj * pinMinusRootJK = smul 2 qk ∧
    (pinMinusRootJK : Quat K) * qk * pinMinusRootJK = smul 2 qj ∧
    (∀ x y z : K,
      (pinMinusRootJK : Quat K) * imagQuaternion3 x y z * pinMinusRootJK =
        smul 2 (imagQuaternion3 x z y)) ∧
    (pinMinusRootJK : Quat K) * qi * conj pinMinusRootJK = smul (-2) qi := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Quaternion.normSq (pinMinusRootJK : Quaternion K) = 2
    rw [Quaternion.normSq_def']
    norm_num [pinMinusRootJK]
  · apply Quaternion.ext
    all_goals simp [pinMinusRootJK, qOne, smul]
    all_goals ring
  · apply Quaternion.ext
    all_goals simp [pinMinusRootJK, qi, smul]
    all_goals ring
  · apply Quaternion.ext
    all_goals simp [pinMinusRootJK, qj, qk, smul]
    all_goals ring
  · apply Quaternion.ext
    all_goals simp [pinMinusRootJK, qk, qj, smul]
    all_goals ring
  · intro x y z
    apply Quaternion.ext
    all_goals simp [pinMinusRootJK, imagQuaternion3, smul]
    all_goals ring
  · apply Quaternion.ext
    all_goals simp [pinMinusRootJK, qi, conj, smul]
    all_goals ring

/-- Exact rational-coordinate identities for the proposed short-root representative.
These identities do not assert membership in a binary-octahedral subgroup. -/
lemma oddCoset_integer_coordinate_identities :
    qNorm (oddCosetU : Quat ℤ) = 2 ∧
    (oddCosetU : Quat ℤ) * oddCosetU * oddCosetU * oddCosetU =
      smul (-4) (qOne : Quat ℤ) ∧
    (oddCosetU : Quat ℤ) * qi * conj oddCosetU = smul 2 qi ∧
    (oddCosetU : Quat ℤ) * qj * conj oddCosetU = smul 2 qk ∧
    (oddCosetU : Quat ℤ) * qk * conj oddCosetU = smul (-2) qj ∧
    (oddCosetU : Quat ℤ) * hurwitzW * conj oddCosetU = smul 2 hurwitzW' ∧
    qNorm (hurwitzW' : Quat ℤ) = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Quaternion.normSq (oddCosetU : Quaternion ℤ) = 2
    rw [Quaternion.normSq_def']
    norm_num [oddCosetU]
  · apply Quaternion.ext <;> simp [oddCosetU, qOne, smul]
  · apply Quaternion.ext <;> simp [oddCosetU, qi, conj, smul]
  · apply Quaternion.ext <;> simp [oddCosetU, qj, qk, conj, smul]
  · apply Quaternion.ext <;> simp [oddCosetU, qk, qj, conj, smul]
  · apply Quaternion.ext <;> simp [oddCosetU, hurwitzW, hurwitzW', conj, smul]
  · change Quaternion.normSq (hurwitzW' : Quaternion ℤ) = 4
    rw [Quaternion.normSq_def']
    norm_num [hurwitzW']

/--
**Theorem 3 (𝔚ℌ₄ & 𝔚ℌ₅ — Hurwitz Shell Counts, Norm Identity & Quaternion Conjugation):**
1. **Numerical Counts:** `8 + 16 = 24` and `24 + 24 = 48`. These equalities do not construct
   either group or establish a coset decomposition.
2. **Euler 4-Square Norm Multiplicativity:** `qNorm (Q * X) = qNorm Q * qNorm X`.
3. **6-Fold Cyclotomic Equation of `W = ⟨1, 1, 1, 1⟩`:**
   `qNorm W = 4`, `W * W - 2 • W + 4 • 1 = 0`, and `W * W * W = -8 • 1` (`ω³ = -1, ω⁶ = +1`).
4. **Exact `ℤ₃` Triality Rotation of Imaginary Axes `(i ↦ j ↦ k ↦ i)`:**
   `W * i * conj W = 4 • j`, `W * j * conj W = 4 • k`, and `W * k * conj W = 4 • i`.
-/
lemma hurwitz_corner_triality_attention_filter (Q X : Quat K) :
    -- 1. Numerical counts 8 + 16 = 24 and 24 + 24 = 48:
    8 + 2 ^ 4 = 24 ∧ 24 + 6 * 4 = 48 ∧
    -- 2. Exact norm multiplicativity:
    qNorm (Q * X) = qNorm Q * qNorm X ∧
    -- 3. 6-fold cyclotomic polynomial W² - 2W + 4 = 0 and W³ = -8:
    qNorm (hurwitzW : Quat K) = 4 ∧
    (hurwitzW : Quat K) * hurwitzW - smul 2 hurwitzW + smul 4 qOne = (0 : Quat K) ∧
    (hurwitzW : Quat K) * hurwitzW * hurwitzW = smul (-8) qOne ∧
    -- 4. Exact ℤ₃ cyclic permutation of the 3 imaginary axes (i, j, k):
    (hurwitzW : Quat K) * qi * conj hurwitzW = smul 4 qj ∧
    (hurwitzW : Quat K) * qj * conj hurwitzW = smul 4 qk ∧
    (hurwitzW : Quat K) * qk * conj hurwitzW = smul 4 qi := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Quaternion.normSq.map_mul Q X
  · dsimp [qNorm, hurwitzW]
    rw [Quaternion.normSq_def']
    ring
  · apply Quaternion.ext <;> simp [hurwitzW, qOne, smul] <;> ring
  · apply Quaternion.ext <;> simp [hurwitzW, qOne, smul] <;> ring
  · (apply Quaternion.ext <;> simp [hurwitzW, qi, qj, conj, smul]); ring
  · (apply Quaternion.ext <;> simp [hurwitzW, qj, qk, conj, smul]); ring
  · (apply Quaternion.ext <;> simp [hurwitzW, qk, qi, conj, smul]); ring

/--
**Theorem 3b (𝔚ℌ₄ & 𝔚ℌ₅ — Bridge to `Quaternion K` & `DiscreteHurwitzCliffordWavelet`):**
1. `ofQuaternion` is a left inverse to `toQuaternion`, and `toQuaternion` preserves addition,
   Hamilton multiplication, star/conjugation (`toQuaternion (conj a) = star (toQuaternion a)`),
   and norm-square (`qNorm a = Quaternion.normSq (toQuaternion a)`).
2. Every paraunitary Hurwitz–Clifford filter bank (`DiscreteHurwitzCliffordWavelet.paraunitary F`)
   preserves unit branch energy (`F.sum_normSq_eq_one`), and every `CliffordCascadeSystem`
   provides exact left-inverse signal reconstruction (`C.synthesis (C.analysis s) = s`).
-/
lemma hurwitz_quaternion_and_paraunitary_filter_bank_bridge (a b : Quat K) :
    ofQuaternion (toQuaternion a) = a ∧
    toQuaternion (a + b) = toQuaternion a + toQuaternion b ∧
    toQuaternion (a * b) = toQuaternion a * toQuaternion b ∧
    toQuaternion (conj a) = star (toQuaternion a) ∧
    qNorm a = Quaternion.normSq (toQuaternion a) ∧
    (∀ F : InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet.ParaunitaryCliffordFilterBank,
      InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet.paraunitary F →
        F.sum_normSq_eq_one) ∧
    (∀ (F : InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet.ParaunitaryCliffordFilterBank)
       (C : InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet.CliffordCascadeSystem.{0} F)
       (s : C.Signal),
       C.synthesis (C.analysis s) = s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ofQuaternion, toQuaternion]
  · simp [toQuaternion]
  · simp [toQuaternion]
  · simp [toQuaternion]
  · simp [qNorm, toQuaternion]
  · intro F hF
    exact InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet.sum_normSq_eq_one_of_paraunitary F hF
  · intro F C s
    exact InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet.CliffordCascadeSystem.reconstructed_signal C s

/-- The exact 24-point rational shell has unit norm in the shared Mathlib quaternion carrier. -/
lemma rationalHurwitzChart_qNorm_one (i : Fin 24) :
    Quat.qNorm (Quat.ofQuaternion
      (InfoGeometry.Quantum.Hurwitz.rationalHurwitzDirection i)) = 1 := by
  change Quaternion.normSq (InfoGeometry.Quantum.Hurwitz.rationalHurwitzDirection i) = 1
  rw [Quaternion.normSq_def']
  simpa only [pow_two] using
    InfoGeometry.Quantum.Hurwitz.rationalHurwitzDirection_unit i

/--
**Theorem 3c (𝔚ℌ₉ — Odd Coset Generator `U = 1 + i`, Axis Transposition & Norm-2 vs. Norm-4 Split):**
Over any commutative ring `K` on `Quat K = Quaternion K`:
1. `qNorm oddCosetU = 2`, `oddCosetU * oddCosetU - smul 2 oddCosetU + smul 2 qOne = 0`, and
   `oddCosetU * oddCosetU * oddCosetU * oddCosetU = smul (-4) qOne`.
2. `oddCosetU * qi * conj oddCosetU = smul 2 qi`,
   `oddCosetU * qj * conj oddCosetU = smul 2 qk`, and
   `oddCosetU * qk * conj oddCosetU = smul (-2) qj`.
3. `oddCosetU * hurwitzW * conj oddCosetU = smul 2 hurwitzW'`, `qNorm hurwitzW' = 4`, and
   `hurwitzW' * hurwitzW' - smul 2 hurwitzW' + smul 4 qOne = 0`.
-/
lemma binary_octahedral_odd_coset_and_f4_root_norm_split :
    qNorm (oddCosetU : Quat K) = 2 ∧
    (oddCosetU : Quat K) * oddCosetU - smul 2 oddCosetU + smul 2 qOne = (0 : Quat K) ∧
    (oddCosetU : Quat K) * oddCosetU * oddCosetU * oddCosetU = smul (-4) qOne ∧
    (oddCosetU : Quat K) * qi * conj oddCosetU = smul 2 qi ∧
    (oddCosetU : Quat K) * qj * conj oddCosetU = smul 2 qk ∧
    (oddCosetU : Quat K) * qk * conj oddCosetU = smul (-2) qj ∧
    (oddCosetU : Quat K) * hurwitzW * conj oddCosetU = smul 2 hurwitzW' ∧
    qNorm (hurwitzW' : Quat K) = 4 ∧
    (hurwitzW' : Quat K) * hurwitzW' - smul 2 hurwitzW' + smul 4 qOne = (0 : Quat K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [qNorm, oddCosetU]
    rw [Quaternion.normSq_def']
    ring
  · (apply Quaternion.ext <;> simp [oddCosetU, qOne, smul]); ring
  · (apply Quaternion.ext <;> simp [oddCosetU, qOne, smul]); ring
  · (apply Quaternion.ext <;> simp [oddCosetU, qi, conj, smul]); ring
  · (apply Quaternion.ext <;> simp [oddCosetU, qj, qk, conj, smul]); ring
  · (apply Quaternion.ext <;> simp [oddCosetU, qk, qj, conj, smul]); ring
  · apply Quaternion.ext <;> simp [oddCosetU, hurwitzW, hurwitzW', conj, smul] <;> norm_num
  · dsimp [qNorm, hurwitzW']
    rw [Quaternion.normSq_def']
    ring
  · apply Quaternion.ext <;> simp [hurwitzW', qOne, smul] <;> ring

end Quat

-- ============================================================================
-- SECTION 3 (𝔚ℌ₆–𝔚ℌ₇, 𝔚ℌ₁₀–𝔚ℌ₁₁): Cyclotomic Polynomial Substitutions & 8-Divisor Factorization
-- ============================================================================

section BottHurwitzAdamsBridge
variable {K : Type u} [CommRing K]

/-- 1st cyclotomic polynomial `Φ₁(x) = x - 1` (`φ(1) = 1`). -/
def Phi1 (x : K) : K := x - 1

/-- 2nd cyclotomic polynomial `Φ₂(x) = x + 1` (`φ(2) = 1`). -/
def Phi2 (x : K) : K := x + 1

/-- 3rd cyclotomic polynomial `Φ₃(x) = x² + x + 1` (`φ(3) = 2`). -/
def Phi3 (x : K) : K := x ^ 2 + x + 1

/-- 4th cyclotomic polynomial `Φ₄(x) = x² + 1` (`φ(4) = 2`). -/
def Phi4 (x : K) : K := x ^ 2 + 1

/-- Polynomial `y² - y + 1`, equal to `(Polynomial.cyclotomic 6 K).eval y`. -/
def Phi6 (y : K) : K := y ^ 2 - y + 1

/-- 8th cyclotomic polynomial `Φ₈(x) = x⁴ + 1`, equal to `Phi2 (x ^ 4)` and
`(Polynomial.cyclotomic 8 K).eval x` (`φ(8) = 4`). -/
def Phi8 (x : K) : K := x ^ 4 + 1

/-- 12th cyclotomic polynomial `Φ₁₂(x) = x⁴ - x² + 1`, equal to `Phi6 (x ^ 2)` and
`(Polynomial.cyclotomic 12 K).eval x` (`φ(12) = 4`). -/
def Phi12 (x : K) : K := x ^ 4 - x ^ 2 + 1

/-- Polynomial `x⁸ - x⁴ + 1`, equal to `Phi6 (x ^ 4)` and `(Polynomial.cyclotomic 24 K).eval x`. -/
def Phi24 (x : K) : K := x ^ 8 - x ^ 4 + 1

/-- Mathlib's divisor-indexed cyclotomic resolution at period `24`.
The product is over all divisors, so this is the canonical cyclotomic theorem rather than a
hand-expanded list of eight polynomial factors. -/
lemma cyclotomic_divisor_resolution_24 :
    (∏ d ∈ Nat.divisors 24, Polynomial.cyclotomic d K) =
      Polynomial.X ^ 24 - 1 := by
  exact Polynomial.prod_cyclotomic_eq_X_pow_sub_one (by norm_num) K

/-- Identifies `Phi6 y` with the evaluation of Mathlib's canonical 6th cyclotomic polynomial
`Polynomial.cyclotomic 6 K`. -/
lemma eval_cyclotomic6_eq_Phi6 (y : K) :
    (Polynomial.cyclotomic 6 K).eval y = Phi6 y := by
  rw [Polynomial.cyclotomic_six]
  simp [Phi6]

/-- Identifies `Phi8 x` with the evaluation of Mathlib's canonical 8th cyclotomic polynomial
`Polynomial.cyclotomic 8 K`, proved via prime expansion `Φ₈(X) = Φ₄(X²) = Φ₂(X⁴)`. -/
lemma eval_cyclotomic8_eq_Phi8 (x : K) :
    (Polynomial.cyclotomic 8 K).eval x = Phi8 x := by
  have h8 : Polynomial.cyclotomic 8 ℤ = Polynomial.X ^ 4 + 1 := by
    rw [show (8 : ℕ) = 4 * 2 by norm_num,
      ← Polynomial.cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num) ℤ,
      show (4 : ℕ) = 2 * 2 by norm_num,
      ← Polynomial.cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num) ℤ,
      Polynomial.cyclotomic_two]
    simp [Polynomial.expand_X]
    ring
  rw [← Polynomial.map_cyclotomic_int 8 K, h8]
  simp [Phi8]

/-- Identifies `Phi12 x` with the evaluation of Mathlib's canonical 12th cyclotomic polynomial
`Polynomial.cyclotomic 12 K`, proved via prime expansion `Φ₁₂(X) = Φ₆(X²)`. -/
lemma eval_cyclotomic12_eq_Phi12 (x : K) :
    (Polynomial.cyclotomic 12 K).eval x = Phi12 x := by
  have h12 : Polynomial.cyclotomic 12 ℤ = Polynomial.X ^ 4 - Polynomial.X ^ 2 + 1 := by
    rw [show (12 : ℕ) = 6 * 2 by norm_num,
      ← Polynomial.cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num) ℤ,
      Polynomial.cyclotomic_six]
    simp [Polynomial.expand_X]
    ring
  rw [← Polynomial.map_cyclotomic_int 12 K, h12]
  simp [Phi12]

/-- Identifies `Phi24 x` with the evaluation of Mathlib's canonical 24th cyclotomic polynomial
`Polynomial.cyclotomic 24 K`, proved via prime expansion `Φ₂₄(X) = Φ₁₂(X²) = Φ₆(X⁴)`. -/
lemma eval_cyclotomic24_eq_Phi24 (x : K) :
    (Polynomial.cyclotomic 24 K).eval x = Phi24 x := by
  have h24 : Polynomial.cyclotomic 24 ℤ = Polynomial.X ^ 8 - Polynomial.X ^ 4 + 1 := by
    rw [show (24 : ℕ) = 12 * 2 by norm_num,
      ← Polynomial.cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num) ℤ,
      show (12 : ℕ) = 6 * 2 by norm_num,
      ← Polynomial.cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num) ℤ,
      Polynomial.cyclotomic_six]
    simp [Polynomial.expand_X]
    ring
  rw [← Polynomial.map_cyclotomic_int 24 K, h24]
  simp [Phi24]

/--
**Theorem 4 (𝔚ℌ₆ & 𝔚ℌ₇ — Polynomial Substitution `Φ₂₄(x) = Φ₆(x⁴)`):**
1. **Composition of 6th Cyclotomic Polynomial with Fourth Power (`y = x⁴`):**
   `Phi6 (x ^ 4) = Phi24 x` (`(x⁴)² - x⁴ + 1 = x⁸ - x⁴ + 1`).
2. **Polynomial Factorization:**
   `x ^ 24 - 1 = (x ^ 12 - 1) * (x ^ 4 + 1) * Phi24 x`. These polynomial identities alone do
   not establish topological periodicity or a stable homotopy result.
-/
lemma adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge (x : K) :
    Phi6 (x ^ 4) = Phi24 x ∧
    (x ^ 4 + 1) * Phi24 x = x ^ 12 + 1 ∧
    (x ^ 12 - 1) * (x ^ 4 + 1) * Phi24 x = x ^ 24 - 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp [Phi6, Phi24]
    ring

/--
**Theorem 4b (𝔚ℌ₁₀ & 𝔚ℌ₁₁ — Complete 8-Divisor Cyclotomic Factorization of `x²⁴ - 1` & Totient Sum):**
For any `x : K` in a commutative ring `K`:
1. `Nat.totient 1 + Nat.totient 2 + Nat.totient 3 + Nat.totient 4 + Nat.totient 6 + Nat.totient 8 + Nat.totient 12 + Nat.totient 24 = 24`
   and `1 + 1 + 2 + 2 + 2 + 4 + 4 + 8 = 24`.
2. `Phi2 (x ^ 4) = Phi8 x`, `Phi6 (x ^ 2) = Phi12 x`, and `Phi6 (x ^ 4) = Phi24 x`.
3. `Phi1 x * Phi2 x * Phi3 x * Phi4 x * Phi6 x * Phi12 x = x ^ 12 - 1`.
4. `Phi1 x * Phi2 x * Phi3 x * Phi4 x * Phi6 x * Phi8 x * Phi12 x * Phi24 x = x ^ 24 - 1`.
-/
lemma complete_cyclotomic_24_factorization_and_spectral_dimensions (x : K) :
    Nat.totient 1 + Nat.totient 2 + Nat.totient 3 + Nat.totient 4 +
      Nat.totient 6 + Nat.totient 8 + Nat.totient 12 + Nat.totient 24 = 24 ∧
    1 + 1 + 2 + 2 + 2 + 4 + 4 + 8 = 24 ∧
    Phi2 (x ^ 4) = Phi8 x ∧
    Phi6 (x ^ 2) = Phi12 x ∧
    Phi6 (x ^ 4) = Phi24 x ∧
    Phi1 x * Phi2 x * Phi3 x * Phi4 x * Phi6 x * Phi12 x = x ^ 12 - 1 ∧
    Phi1 x * Phi2 x * Phi3 x * Phi4 x * Phi6 x * Phi8 x * Phi12 x * Phi24 x = x ^ 24 - 1 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    dsimp [Phi1, Phi2, Phi3, Phi4, Phi6, Phi8, Phi12, Phi24]
    <;> ring

/--
**Theorem 5 (𝔚ℌ₇ — Conjunction of Finite Matrix, Quaternion, and Cyclotomic Identities):**
Collects the declaration-order graph fact and selected finite algebraic identities in one theorem:
1. Acyclicity of `WignerHurwitzAdamsStage.coverEdge`,
2. Resolution `Pi1 M + Pi2 M + Pi3_pos M + Pi3_neg M = smul 6 M` and Frobenius Pythagorean
   decomposition `36 * frobInner M N = ∑_α frobInner (Pi_α M) (Pi_α N)` (`𝔚ℌ₁–𝔚ℌ₃`),
3. Numerical equalities `8 + 16 = 24` and `24 + 24 = 48`, Euler norm multiplicativity
   `qNorm (Q * X) = qNorm Q * qNorm X`, `ℤ₃` conjugation triality `W * i * conj W = 4 • j`,
   and unit norm of the exact 24-point rational chart in the shared Mathlib quaternion carrier
   (`𝔚ℌ₄–𝔚ℌ₅`),
4. Cyclotomic polynomial substitution `Phi6 (x ^ 4) = Phi24 x`, Mathlib identification
   `(Polynomial.cyclotomic 24 K).eval x = Phi24 x`, and
   `(x ^ 12 - 1) * (x ^ 4 + 1) * Phi24 x = x ^ 24 - 1` (`𝔚ℌ₆–𝔚ℌ₇`).
-/
lemma wh7_master_wigner_hurwitz_adams_synthesis
    (M N : Mat3 K) (Q X : Quat K) (x : K) (i : Fin 24) :
    (∀ a : WignerHurwitzAdamsStage, ¬ WignerHurwitzAdamsStage.coverEdge a a) ∧
    (Mat3.Pi1 M + Mat3.Pi2 M + Mat3.Pi3_pos M + Mat3.Pi3_neg M = Mat3.smul 6 M ∧
     36 * Mat3.frobInner M N =
       Mat3.frobInner (Mat3.Pi1 M) (Mat3.Pi1 N) +
       Mat3.frobInner (Mat3.Pi2 M) (Mat3.Pi2 N) +
       Mat3.frobInner (Mat3.Pi3_pos M) (Mat3.Pi3_pos N) +
       Mat3.frobInner (Mat3.Pi3_neg M) (Mat3.Pi3_neg N)) ∧
    (8 + 2 ^ 4 = 24 ∧ 24 + 6 * 4 = 48 ∧
     Quat.qNorm (Quat.ofQuaternion
       (InfoGeometry.Quantum.Hurwitz.rationalHurwitzDirection i)) = 1 ∧
     Quat.qNorm (Q * X) = Quat.qNorm Q * Quat.qNorm X ∧
     (Quat.hurwitzW : Quat K) * Quat.qi * Quat.conj Quat.hurwitzW = Quat.smul 4 Quat.qj) ∧
    (Phi6 (x ^ 4) = Phi24 x ∧
     (Polynomial.cyclotomic 24 K).eval x = Phi24 x ∧
     (x ^ 12 - 1) * (x ^ 4 + 1) * Phi24 x = x ^ 24 - 1) := by
  have hCG := Mat3.clebsch_gordan_s4_idempotency_and_mutual_orthogonality M
  have hFrob := Mat3.clebsch_gordan_frobenius_pythagorean_theorem M N
  have hHurw := Quat.hurwitz_corner_triality_attention_filter Q X
  have hChart := Quat.rationalHurwitzChart_qNorm_one i
  have hAdams := adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge x
  rcases hFrob with ⟨_, _, _, _, hPyth⟩
  rcases hHurw with ⟨hCount24, hRest⟩
  rcases hRest with ⟨hCount48, hRest⟩
  rcases hRest with ⟨hNormMul, hRest⟩
  rcases hRest with ⟨_, hRest⟩
  rcases hRest with ⟨_, hRest⟩
  rcases hRest with ⟨_, hRest⟩
  rcases hRest with ⟨hTriality, _, _⟩
  exact ⟨WignerHurwitzAdamsStage.coverEdge_acyclic,
    ⟨hCG.1, hPyth⟩,
    ⟨hCount24, hCount48, hChart, hNormMul, hTriality⟩,
    ⟨hAdams.1, eval_cyclotomic24_eq_Phi24 x, hAdams.2.2⟩⟩

/--
**Theorem 6 (𝔚ℌ₁₁ — Extended 11-Stage Wigner–Hurwitz–Adams Master Synthesis):**
Unifies all 11 stages (`𝔚ℌ₁ ≺ ⋯ ≺ 𝔚ℌ₁₁`) over `Matrix (Fin 3) (Fin 3) K`, `Quaternion K`,
and `Polynomial.cyclotomic`:
1. **`5 = 2 + 3_+` Quadrupole Split & Frobenius Pythagorean Law (`𝔚ℌ₁–𝔚ℌ₃, 𝔚ℌ₈`):**
   `Mat3.Pi2 M + Mat3.Pi3_pos M = Mat3.Pi5_so3 M` and
   `36 * Mat3.frobInner M N = ∑_α Mat3.frobInner (Mat3.Pi_α M) (Mat3.Pi_α N)`.
2. **Even Hurwitz Corner `W` (`N = 4`) vs. Odd Coset `U = 1 + i` (`N = 2`) (`𝔚ℌ₄–𝔚ℌ₅, 𝔚ℌ₉`):**
   `Quat.qNorm Quat.oddCosetU = 2`, `Quat.qNorm Quat.hurwitzW' = 4`,
   `Quat.oddCosetU * Quat.hurwitzW * Quat.conj Quat.oddCosetU = Quat.smul 2 Quat.hurwitzW'`,
   and `Quat.oddCosetU * Quat.qj * Quat.conj Quat.oddCosetU = Quat.smul 2 Quat.qk`.
3. **Complete 8-Divisor Cyclotomic Factorization of `x²⁴ - 1` (`𝔚ℌ₆–𝔚ℌ₇, 𝔚ℌ₁₀–𝔚ℌ₁₁`):**
   `(Polynomial.cyclotomic 8 K).eval x = Phi8 x`,
   `(Polynomial.cyclotomic 12 K).eval x = Phi12 x`,
   `(Polynomial.cyclotomic 24 K).eval x = Phi24 x`,
   `Phi1 x * Phi2 x * Phi3 x * Phi4 x * Phi6 x * Phi12 x = x ^ 12 - 1`, and
   `Phi1 x * Phi2 x * Phi3 x * Phi4 x * Phi6 x * Phi8 x * Phi12 x * Phi24 x = x ^ 24 - 1`.
-/
lemma wh11_extended_wigner_hurwitz_adams_master_synthesis
    (M N : Mat3 K) (x : K) :
    (Mat3.Pi2 M + Mat3.Pi3_pos M = Mat3.Pi5_so3 M ∧
     36 * Mat3.frobInner M N =
       Mat3.frobInner (Mat3.Pi1 M) (Mat3.Pi1 N) +
       Mat3.frobInner (Mat3.Pi2 M) (Mat3.Pi2 N) +
       Mat3.frobInner (Mat3.Pi3_pos M) (Mat3.Pi3_pos N) +
       Mat3.frobInner (Mat3.Pi3_neg M) (Mat3.Pi3_neg N)) ∧
    (Quat.qNorm (Quat.oddCosetU : Quat K) = 2 ∧
     Quat.qNorm (Quat.hurwitzW' : Quat K) = 4 ∧
     (Quat.oddCosetU : Quat K) * Quat.hurwitzW * Quat.conj Quat.oddCosetU =
       Quat.smul 2 Quat.hurwitzW' ∧
     (Quat.oddCosetU : Quat K) * Quat.qj * Quat.conj Quat.oddCosetU =
       Quat.smul 2 Quat.qk) ∧
    ((Polynomial.cyclotomic 8 K).eval x = Phi8 x ∧
     (Polynomial.cyclotomic 12 K).eval x = Phi12 x ∧
     (Polynomial.cyclotomic 24 K).eval x = Phi24 x ∧
     Phi1 x * Phi2 x * Phi3 x * Phi4 x * Phi6 x * Phi12 x = x ^ 12 - 1 ∧
     Phi1 x * Phi2 x * Phi3 x * Phi4 x * Phi6 x * Phi8 x * Phi12 x * Phi24 x = x ^ 24 - 1) ∧
    (Quat.qNorm (Quat.pinMinusRootJK : Quat K) = 2 ∧
     (Quat.pinMinusRootJK : Quat K) * Quat.pinMinusRootJK = Quat.smul (-2) Quat.qOne ∧
     (Quat.pinMinusRootJK : Quat K) * Quat.qi * Quat.pinMinusRootJK = Quat.smul 2 Quat.qi ∧
     (Quat.pinMinusRootJK : Quat K) * Quat.qj * Quat.pinMinusRootJK = Quat.smul 2 Quat.qk ∧
     (Quat.pinMinusRootJK : Quat K) * Quat.qk * Quat.pinMinusRootJK = Quat.smul 2 Quat.qj ∧
     (∀ x y z : K,
       (Quat.pinMinusRootJK : Quat K) * Quat.imagQuaternion3 x y z * Quat.pinMinusRootJK =
         Quat.smul 2 (Quat.imagQuaternion3 x z y)) ∧
     (Quat.pinMinusRootJK : Quat K) * Quat.qi * Quat.conj Quat.pinMinusRootJK =
       Quat.smul (-2) Quat.qi) := by
  have hSO3 := Mat3.clebsch_gordan_s4_complete_12_annihilations_and_so3_branching M N
  have hFrob := Mat3.clebsch_gordan_frobenius_pythagorean_theorem M N
  have hOdd := Quat.binary_octahedral_odd_coset_and_f4_root_norm_split (K := K)
  have hPin := Quat.pin_minus_short_root_reflection_identities (K := K)
  have hCyc := complete_cyclotomic_24_factorization_and_spectral_dimensions x
  exact ⟨⟨hSO3.1, hFrob.2.2.2.2⟩,
    ⟨hOdd.1, hOdd.2.2.2.2.2.2.2.1, hOdd.2.2.2.2.2.2.1, hOdd.2.2.2.2.1⟩,
    ⟨eval_cyclotomic8_eq_Phi8 x, eval_cyclotomic12_eq_Phi12 x, eval_cyclotomic24_eq_Phi24 x,
     hCyc.2.2.2.2.2.1, hCyc.2.2.2.2.2.2⟩,
    ⟨hPin.1, hPin.2.1, hPin.2.2.1, hPin.2.2.2.1, hPin.2.2.2.2.1,
      hPin.2.2.2.2.2.1, hPin.2.2.2.2.2.2⟩⟩

end BottHurwitzAdamsBridge

end WignerHurwitzAdamsKTheoryPoset
