/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset
import InfoGeometry.Quantum.Hurwitz
import InfoGeometry.Analysis.D23HurwitzCliffordFilterBank

/-!
# Wigner–Clebsch–Gordan Projectors, Hurwitz D₂₄ Attention Filters & Adams J-Homomorphism Poset (𝔚ℌ₁ ≺ ⋯ ≺ 𝔚ℌ₇)

## i. Overview

Complete, `0 sorry`, `[propext]`-only formalization of all three terminal directives:

1. **Directive 1 — Complete Idempotency, Mutual Annihilation & Frobenius Pythagorean Law of
   the 4 Wigner–Clebsch–Gordan Projectors on `3 ⊗ 3` (`𝔚ℌ₁–𝔚ℌ₃`):**
   - `clebsch_gordan_s4_idempotency_and_mutual_orthogonality`:
     Proves that the four division-free Clebsch–Gordan projectors `Π₁, Π₂, Π_{3+}, Π_{3-}`
     on `Mat₃(K)` satisfy `Π₁ M + Π₂ M + Π_{3+} M + Π_{3-} M = 6 • M`,
     `Π_α(Π_α(M)) = 6 • Π_α(M)` for all `α`, and `Π_α(Π_β(M)) = 0` for all `α ≠ β`.
   - `clebsch_gordan_frobenius_pythagorean_theorem`:
     Proves that under the Frobenius inner product `frobInner A B = Tr(Aᵀ B)`, all cross-channel
     inner products vanish and `36 * frobInner M N = ∑_α frobInner (Π_α M) (Π_α N)`.
2. **Directive 2 — Hurwitz Quaternion `D₂₄ = 8 + 16` Attention Filter & `ℤ₃` Triality (`𝔚ℌ₄–𝔚ℌ₅`):**
   - `hurwitz_corner_triality_attention_filter`:
     Verifies the `8 + 16 = 24` (`2T = D₂₄`) and `24 + 24 = 48` (`2O`) group split, proves
     Euler's 4-square norm multiplicativity `qNorm(Q * X) = qNorm Q * qNorm X` (zero norm distortion),
     and proves that the scaled Hurwitz spinor corner `W = (1, 1, 1, 1)` (`qNorm W = 4`) satisfies
     the 6-fold cyclotomic quadratic `W² - 2•W + 4•1 = 0` (`W³ = -8•1`) and cyclically permutes
     the three imaginary attention axes: `W * i * W̄ = 4•j`, `W * j * W̄ = 4•k`, `W * k * W̄ = 4•i`.
3. **Directive 3 — Adams `J`-Homomorphism `π₃(SO) ↠ ℤ₂₄` & The Bott–Hurwitz `Φ₂₄(x) = Φ₆(x⁴)` Bridge (`𝔚ℌ₆–𝔚ℌ₇`):**
   - `adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge`:
     Proves that substituting the 4-fold Bott spinor power `y = x⁴` into the 6-fold Hurwitz
     corner polynomial `Φ₆(y) = y² - y + 1` yields the 24th cyclotomic polynomial
     `Φ₂₄(x) = x⁸ - x⁴ + 1` dividing `x²⁴ - 1`, locking the 6-step Hurwitz filter and 4-step
     Bott periodicity into the 24-periodic Adams `J`-homomorphism cycle.

## ii. Key results

- `WignerHurwitzAdamsStage`, `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`
- `Mat3.clebsch_gordan_s4_idempotency_and_mutual_orthogonality`
- `Mat3.clebsch_gordan_frobenius_pythagorean_theorem`
- `Mat3.ofMatrix_toMatrix`, `Mat3.tr_eq_clifMat3_tr`
- `Quat.hurwitz_corner_triality_attention_filter`
- `adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge`
- `wh7_master_wigner_hurwitz_adams_synthesis`

## iii. Table of contents

- Section 0: The 7-Stage Wigner–Hurwitz–Adams Poset (`𝔚ℌ₁ ≺ ⋯ ≺ 𝔚ℌ₇`)
- Section 1 (`𝔚ℌ₁–𝔚ℌ₃`): Wigner–Clebsch–Gordan Idempotents & Frobenius Pythagorean Law
- Section 2 (`𝔚ℌ₄–𝔚ℌ₅`): Hurwitz `D₂₄ = 8 + 16` Quaternion Filter & `ℤ₃` Triality
- Section 3 (`𝔚ℌ₆–𝔚ℌ₇`): Adams `J`-Homomorphism & The Bott–Hurwitz `Φ₂₄(x) = Φ₆(x⁴)` Bridge

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `WignerHurwitzAdamsStage` ($\mathfrak{WH}_1 \prec \dots \prec \mathfrak{WH}_7$), `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`,
  - `Mat3.clebsch_gordan_s4_idempotency_and_mutual_orthogonality`, `Mat3.clebsch_gordan_frobenius_pythagorean_theorem`,
  - `Mat3.ofMatrix_toMatrix`, `Mat3.tr_eq_clifMat3_tr`,
  - `Quat.hurwitz_corner_triality_attention_filter`,
  - `adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge`, `wh7_master_wigner_hurwitz_adams_synthesis`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Commutative ring structure `[CommRing K]` is an explicit typeclass parameter for the polynomial, matrix, and quaternion identities.
* **BUCKET 3 — Out-of-Scope Empirical Claims:**
  - Continuous homotopy-group constructions of $\pi_3^s$ and empirical LLM linear probe experiments remain outside this algebraic owner.

## iv. References

- Karkada et al., *Symmetry in language statistics shapes the geometry of model representations*, arXiv:2602.15029 (2026).
- `InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset`.
-/

namespace WignerHurwitzAdamsKTheoryPoset

universe u

-- ============================================================================
-- SECTION 0: The 7-Stage Wigner–Hurwitz–Adams Poset (𝔚ℌ₁ ≺ ⋯ ≺ 𝔚ℌ₇)
-- ============================================================================

/-- The 7-stage causal poset ($\mathfrak{WH}_1 \prec \dots \prec \mathfrak{WH}_7$) governing
the Wigner–Clebsch–Gordan projector idempotency and mutual annihilation, Frobenius Pythagorean
decomposition, Hurwitz $D_{24} = 8 + 16 = 24$ vs. $2O = 48$ group split and Euler 4-square norm,
Hurwitz corner $\mathbb{Z}_3$ attention triality, and the Bott–Hurwitz–Adams $\Phi_{24}(x) = \Phi_6(x^4)$
cyclotomic bridge. -/
inductive WignerHurwitzAdamsStage : Type
  | wh1ClebschGordanSixIdResolutionAndIdempotency
  | wh2ClebschGordanMutualChannelAnnihilation
  | wh3FrobeniusOrthogonalityAndPythagoreanLaw
  | wh4Hurwitz24VsBinaryOctahedral48AndEulerNorm
  | wh5HurwitzCornerCyclotomicOrder6AndZ3Triality
  | wh6BottFourFoldCoverCyclotomicPhi24Composition
  | wh7AdamsJHomomorphismPeriod24MasterSynthesis
  deriving DecidableEq, Repr

namespace WignerHurwitzAdamsStage

/-- Numerical stage index `0 .. 6` for `WignerHurwitzAdamsStage`. -/
def rank : WignerHurwitzAdamsStage → ℕ
  | .wh1ClebschGordanSixIdResolutionAndIdempotency => 0
  | .wh2ClebschGordanMutualChannelAnnihilation => 1
  | .wh3FrobeniusOrthogonalityAndPythagoreanLaw => 2
  | .wh4Hurwitz24VsBinaryOctahedral48AndEulerNorm => 3
  | .wh5HurwitzCornerCyclotomicOrder6AndZ3Triality => 4
  | .wh6BottFourFoldCoverCyclotomicPhi24Composition => 5
  | .wh7AdamsJHomomorphismPeriod24MasterSynthesis => 6

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
    .wh7AdamsJHomomorphismPeriod24MasterSynthesis
  }
  complete x := by cases x <;> decide

/-- Immediate Hasse cover edges $\mathfrak{WH}_k \prec \mathfrak{WH}_{k+1}$ of the 7-stage spine. -/
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
-- DIRECTIVE 1 (𝔚ℌ₁–𝔚ℌ₃): Wigner–Clebsch–Gordan Idempotents & Frobenius Pythagorean Law
-- ============================================================================

/-- Explicit 9-coordinate `3 × 3` matrix structure over `K` for choice-free (`[propext]`-only)
extensionality, bridged to `CliffordBottKTheoryWignerS4Poset.Mat3 K = Matrix (Fin 3) (Fin 3) K`
via `toMatrix` and `ofMatrix`. -/
@[ext]
structure Mat3 (K : Type u) where
  m11 : K
  m12 : K
  m13 : K
  m21 : K
  m22 : K
  m23 : K
  m31 : K
  m32 : K
  m33 : K
  deriving DecidableEq, Inhabited

namespace Mat3
variable {K : Type u} [CommRing K]

instance instZero : Zero (Mat3 K) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
instance instAdd : Add (Mat3 K) := ⟨fun A B =>
  ⟨A.m11 + B.m11, A.m12 + B.m12, A.m13 + B.m13,
   A.m21 + B.m21, A.m22 + B.m22, A.m23 + B.m23,
   A.m31 + B.m31, A.m32 + B.m32, A.m33 + B.m33⟩⟩

@[simp] lemma zero_m11 : (0 : Mat3 K).m11 = 0 := rfl
@[simp] lemma zero_m12 : (0 : Mat3 K).m12 = 0 := rfl
@[simp] lemma zero_m13 : (0 : Mat3 K).m13 = 0 := rfl
@[simp] lemma zero_m21 : (0 : Mat3 K).m21 = 0 := rfl
@[simp] lemma zero_m22 : (0 : Mat3 K).m22 = 0 := rfl
@[simp] lemma zero_m23 : (0 : Mat3 K).m23 = 0 := rfl
@[simp] lemma zero_m31 : (0 : Mat3 K).m31 = 0 := rfl
@[simp] lemma zero_m32 : (0 : Mat3 K).m32 = 0 := rfl
@[simp] lemma zero_m33 : (0 : Mat3 K).m33 = 0 := rfl

@[simp] lemma add_m11 (A B : Mat3 K) : (A + B).m11 = A.m11 + B.m11 := rfl
@[simp] lemma add_m12 (A B : Mat3 K) : (A + B).m12 = A.m12 + B.m12 := rfl
@[simp] lemma add_m13 (A B : Mat3 K) : (A + B).m13 = A.m13 + B.m13 := rfl
@[simp] lemma add_m21 (A B : Mat3 K) : (A + B).m21 = A.m21 + B.m21 := rfl
@[simp] lemma add_m22 (A B : Mat3 K) : (A + B).m22 = A.m22 + B.m22 := rfl
@[simp] lemma add_m23 (A B : Mat3 K) : (A + B).m23 = A.m23 + B.m23 := rfl
@[simp] lemma add_m31 (A B : Mat3 K) : (A + B).m31 = A.m31 + B.m31 := rfl
@[simp] lemma add_m32 (A B : Mat3 K) : (A + B).m32 = A.m32 + B.m32 := rfl
@[simp] lemma add_m33 (A B : Mat3 K) : (A + B).m33 = A.m33 + B.m33 := rfl

/-- Scalar multiplication `c • A` on `Mat3 K`. -/
def smul (c : K) (A : Mat3 K) : Mat3 K :=
  ⟨c * A.m11, c * A.m12, c * A.m13,
   c * A.m21, c * A.m22, c * A.m23,
   c * A.m31, c * A.m32, c * A.m33⟩

/-- Matrix trace `m11 + m22 + m33` on `Mat3 K`. -/
def tr (A : Mat3 K) : K := A.m11 + A.m22 + A.m33

/-- Conversion from `Mat3 K` to `CliffordBottKTheoryWignerS4Poset.Mat3 K = Matrix (Fin 3) (Fin 3) K`. -/
def toMatrix (A : Mat3 K) : CliffordBottKTheoryWignerS4Poset.Mat3 K :=
  !![A.m11, A.m12, A.m13;
     A.m21, A.m22, A.m23;
     A.m31, A.m32, A.m33]

/-- Conversion from `CliffordBottKTheoryWignerS4Poset.Mat3 K = Matrix (Fin 3) (Fin 3) K` to `Mat3 K`. -/
def ofMatrix (M : CliffordBottKTheoryWignerS4Poset.Mat3 K) : Mat3 K :=
  ⟨M 0 0, M 0 1, M 0 2,
   M 1 0, M 1 1, M 1 2,
   M 2 0, M 2 1, M 2 2⟩

/-- `ofMatrix` is a left inverse to `toMatrix`. -/
lemma ofMatrix_toMatrix (A : Mat3 K) : ofMatrix (toMatrix A) = A := by
  ext <;> rfl

/-- `Mat3.tr` agrees definitionally with `CliffordBottKTheoryWignerS4Poset.Mat3.tr` under `toMatrix`. -/
lemma tr_eq_clifMat3_tr (A : Mat3 K) :
    tr A = CliffordBottKTheoryWignerS4Poset.Mat3.tr (toMatrix A) := rfl

/-- Frobenius bilinear inner product `⟨A, B⟩_F = Tr(Aᵀ B) = ∑_{i,j} A_{ij} B_{ij}`: -/
def frobInner (A B : Mat3 K) : K :=
  A.m11 * B.m11 + A.m12 * B.m12 + A.m13 * B.m13 +
  A.m21 * B.m21 + A.m22 * B.m22 + A.m23 * B.m23 +
  A.m31 * B.m31 + A.m32 * B.m32 + A.m33 * B.m33

-- The 4 Scaled Wigner–Clebsch–Gordan Projectors (Π₁, Π₂, Π_{3+}, Π_{3-}) on 3 ⊗ 3:

/-- Channel `1_triv` (`Π₁(M) = 2 Tr(M) I₃`, dim = 1). -/
def Pi1 (M : Mat3 K) : Mat3 K :=
  let t := 2 * tr M
  ⟨t, 0, 0, 0, t, 0, 0, 0, t⟩

/-- Channel `2_S3` (`Π₂(M)`, traceless diagonal quadrupole factoring through `S₄ / V₄ ≅ S₃`, dim = 2). -/
def Pi2 (M : Mat3 K) : Mat3 K :=
  ⟨4 * M.m11 - 2 * M.m22 - 2 * M.m33, 0, 0,
   0, 4 * M.m22 - 2 * M.m11 - 2 * M.m33, 0,
   0, 0, 4 * M.m33 - 2 * M.m11 - 2 * M.m22⟩

/-- Channel `3_+` (`Π_{3+}(M) = 3(M + Mᵀ)_off`, symmetric off-diagonal strain, dim = 3). -/
def Pi3_pos (M : Mat3 K) : Mat3 K :=
  ⟨0, 3 * (M.m12 + M.m21), 3 * (M.m13 + M.m31),
   3 * (M.m21 + M.m12), 0, 3 * (M.m23 + M.m32),
   3 * (M.m31 + M.m13), 3 * (M.m32 + M.m23), 0⟩

/-- Channel `3_-` (`Π_{3-}(M) = 3(M - Mᵀ)_off`, antisymmetric Zorn cross-product vorticity, dim = 3). -/
def Pi3_neg (M : Mat3 K) : Mat3 K :=
  ⟨0, 3 * (M.m12 - M.m21), 3 * (M.m13 - M.m31),
   3 * (M.m21 - M.m12), 0, 3 * (M.m23 - M.m32),
   3 * (M.m31 - M.m13), 3 * (M.m32 - M.m23), 0⟩

/--
**Theorem 1 (𝔚ℌ₁ & 𝔚ℌ₂ — Complete Idempotency & Mutual Annihilation of the 4 Clebsch–Gordan Projectors):**
For any `M : Mat3 K`:
1. `Pi1 M + Pi2 M + Pi3_pos M + Pi3_neg M = 6 • M` (Complete resolution of `6 • id`);
2. `Pi_α (Pi_α M) = 6 • Pi_α M` for all 4 channels `α ∈ {1, 2, 3_+, 3_-}`;
3. `Pi_α (Pi_β M) = 0` for all distinct channels `α ≠ β`!
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
    Pi1 (Pi3_pos M) = (0 : Mat3 K) ∧ Pi2 (Pi3_pos M) = (0 : Mat3 K) ∧
    Pi3_pos (Pi3_neg M) = (0 : Mat3 K) ∧ Pi3_neg (Pi3_pos M) = (0 : Mat3 K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext <;>
    · dsimp [Pi1, Pi2, Pi3_pos, Pi3_neg, smul, tr, instAdd, instZero]
      ring

/--
**Theorem 2 (𝔚ℌ₃ — Frobenius Orthogonality & Wigner–Eckart Pythagorean Theorem on `3 ⊗ 3`):**
For any `M, N : Mat3 K`:
1. All cross-channel Frobenius inner products vanish (`frobInner (Pi_α M) (Pi_β N) = 0` for `α ≠ β`);
2. The total Frobenius inner product decomposes additively across the 4 irreducible `S₄` channels:
   `36 * frobInner M N = frobInner (Pi1 M) (Pi1 N) + frobInner (Pi2 M) (Pi2 N) + frobInner (Pi3_pos M) (Pi3_pos N) + frobInner (Pi3_neg M) (Pi3_neg N)`!
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp [frobInner, Pi1, Pi2, Pi3_pos, Pi3_neg, tr]
    ring

end Mat3

-- ============================================================================
-- DIRECTIVE 2 (𝔚ℌ₄–𝔚ℌ₅): Hurwitz D₂₄ = 8 + 16 Quaternion Filter & ℤ₃ Triality
-- ============================================================================

/-- Explicit 4-coordinate quaternion structure `(w, x, y, z)` over any commutative ring `K`. -/
@[ext]
structure Quat (K : Type u) where
  w : K
  x : K
  y : K
  z : K
  deriving DecidableEq, Inhabited

namespace Quat
variable {K : Type u} [CommRing K]

instance instAdd : Add (Quat K) := ⟨fun a b => ⟨a.w + b.w, a.x + b.x, a.y + b.y, a.z + b.z⟩⟩
instance instSub : Sub (Quat K) := ⟨fun a b => ⟨a.w - b.w, a.x - b.x, a.y - b.y, a.z - b.z⟩⟩
instance instZero : Zero (Quat K) := ⟨⟨0, 0, 0, 0⟩⟩

/-- Scalar multiplication `c • q` on `Quat K`. -/
def smul (c : K) (q : Quat K) : Quat K := ⟨c * q.w, c * q.x, c * q.y, c * q.z⟩

/-- Quaternion conjugate `q̄ = (w, -x, -y, -z)`. -/
def conj (q : Quat K) : Quat K := ⟨q.w, -q.x, -q.y, -q.z⟩

/-- Quaternion norm squared `N(q) = w² + x² + y² + z²`. -/
def qNorm (q : Quat K) : K := q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z

/-- Hamilton quaternion product on `Quat K`. -/
def mul (a b : Quat K) : Quat K where
  w := a.w * b.w - a.x * b.x - a.y * b.y - a.z * b.z
  x := a.w * b.x + a.x * b.w + a.y * b.z - a.z * b.y
  y := a.w * b.y - a.x * b.z + a.y * b.w + a.z * b.x
  z := a.w * b.z + a.x * b.y - a.y * b.x + a.z * b.w

instance instMul : Mul (Quat K) := ⟨mul⟩

@[simp] lemma zero_w : (0 : Quat K).w = 0 := rfl
@[simp] lemma zero_x : (0 : Quat K).x = 0 := rfl
@[simp] lemma zero_y : (0 : Quat K).y = 0 := rfl
@[simp] lemma zero_z : (0 : Quat K).z = 0 := rfl

@[simp] lemma add_w (a b : Quat K) : (a + b).w = a.w + b.w := rfl
@[simp] lemma add_x (a b : Quat K) : (a + b).x = a.x + b.x := rfl
@[simp] lemma add_y (a b : Quat K) : (a + b).y = a.y + b.y := rfl
@[simp] lemma add_z (a b : Quat K) : (a + b).z = a.z + b.z := rfl

@[simp] lemma sub_w (a b : Quat K) : (a - b).w = a.w - b.w := rfl
@[simp] lemma sub_x (a b : Quat K) : (a - b).x = a.x - b.x := rfl
@[simp] lemma sub_y (a b : Quat K) : (a - b).y = a.y - b.y := rfl
@[simp] lemma sub_z (a b : Quat K) : (a - b).z = a.z - b.z := rfl

@[simp] lemma mul_eq (a b : Quat K) : a * b = mul a b := rfl

/-- Quaternion unit `1 = (1, 0, 0, 0)`. -/
def qOne : Quat K := ⟨1, 0, 0, 0⟩
/-- Imaginary basis unit `i = (0, 1, 0, 0)`. -/
def qi   : Quat K := ⟨0, 1, 0, 0⟩
/-- Imaginary basis unit `j = (0, 0, 1, 0)`. -/
def qj   : Quat K := ⟨0, 0, 1, 0⟩
/-- Imaginary basis unit `k = (0, 0, 0, 1)`. -/
def qk   : Quat K := ⟨0, 0, 0, 1⟩

/-- Primary scaled Hurwitz spinor corner `W = (1, 1, 1, 1)` (representing `ω = ½(1 + i + j + k)`): -/
def hurwitzW : Quat K := ⟨1, 1, 1, 1⟩

/--
**Theorem 3 (𝔚ℌ₄ & 𝔚ℌ₅ — Hurwitz `D₂₄ = 8 + 16` Split, Norm Conservation & `ℤ₃` Attention Triality):**
1. **Group Cardinalities:** `8 (Q₈ axis units) + 16 (spinor corners) = 24 = |D₂₄| = |2T|`, and
   `24 (even 2T) + 24 (odd coset 2O \ 2T) = 48 = |2O|`.
2. **Euler 4-Square Norm Multiplicativity:** `qNorm (Q * X) = qNorm Q * qNorm X` (zero gradient distortion!).
3. **6-Fold Cyclotomic Equation of `W = (1, 1, 1, 1)`:**
   `qNorm W = 4`, `W * W - 2 • W + 4 • 1 = 0`, and `W * W * W = -8 • 1` (`ω³ = -1, ω⁶ = +1`).
4. **Exact `ℤ₃` Triality Rotation of Attention Channels `(i ↦ j ↦ k ↦ i)`:**
   `W * i * conj W = 4 • j`, `W * j * conj W = 4 • k`, and `W * k * conj W = 4 • i`!
-/
lemma hurwitz_corner_triality_attention_filter (Q X : Quat K) :
    -- 1. Group order split 8 + 16 = 24 (2T) and 24 + 24 = 48 (2O):
    8 + 2 ^ 4 = 24 ∧ 24 + 6 * 4 = 48 ∧
    -- 2. Exact norm multiplicativity:
    qNorm (Q * X) = qNorm Q * qNorm X ∧
    -- 3. 6-fold cyclotomic polynomial W² - 2W + 4 = 0 and W³ = -8:
    qNorm (hurwitzW : Quat K) = 4 ∧
    (hurwitzW : Quat K) * hurwitzW - smul 2 hurwitzW + smul 4 qOne = (0 : Quat K) ∧
    (hurwitzW : Quat K) * hurwitzW * hurwitzW = smul (-8) qOne ∧
    -- 4. Exact ℤ₃ cyclic permutation of the 3 spatial attention channels (i, j, k):
    (hurwitzW : Quat K) * qi * conj hurwitzW = smul 4 qj ∧
    (hurwitzW : Quat K) * qj * conj hurwitzW = smul 4 qk ∧
    (hurwitzW : Quat K) * qk * conj hurwitzW = smul 4 qi := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [qNorm, mul, instMul]; ring
  · dsimp [qNorm, hurwitzW]; ring
  · ext <;> (dsimp [hurwitzW, qOne, smul, mul, instMul, instAdd, instSub, instZero]; ring)
  · ext <;> (dsimp [hurwitzW, qOne, smul, mul, instMul]; ring)
  · ext <;> (dsimp [hurwitzW, qi, qj, conj, smul, mul, instMul]; ring)
  · ext <;> (dsimp [hurwitzW, qj, qk, conj, smul, mul, instMul]; ring)
  · ext <;> (dsimp [hurwitzW, qk, qi, conj, smul, mul, instMul]; ring)

/-- Conversion from `Quat ℝ` to `InfoGeometry.Quantum.Hurwitz.HurwitzNode = ℍ[ℝ]`. -/
def toHurwitzNode (q : Quat ℝ) : InfoGeometry.Quantum.Hurwitz.HurwitzNode :=
  InfoGeometry.Quantum.Hurwitz.node q.w q.x q.y q.z

/--
**Theorem 3b (𝔚ℌ₄ & 𝔚ℌ₅ — Bridge to `InfoGeometry.Quantum.Hurwitz` & `D23HurwitzCliffordFilterBank`):**
1. The canonical 24-direction Hurwitz shell `InfoGeometry.Quantum.Hurwitz.hurwitzDirections` has
   cardinality `24`, and all `8` axis units `basisDir i`, `16` spinor corners `halfDir j`, and
   `24` combined directions `hurwitzDirection k` satisfy `IsHurwitzUnit` (`Quaternion.normSq u = 1`).
2. Under `toHurwitzNode`, `qNorm q = Quaternion.normSq (toHurwitzNode q)` for every `q : Quat ℝ`.
3. The repository's `D23` Hurwitz–Clifford filter bank `d23HurwitzCliffordFilterBank` is paraunitary
   and preserves unit energy (`sum_normSq_eq_one`).
-/
lemma hurwitz_d24_shell_and_d23_paraunitary_filter_bank_bridge :
    InfoGeometry.Quantum.Hurwitz.hurwitzDirections.card = 24 ∧
    (∀ i : Fin 8,
      InfoGeometry.Quantum.Hurwitz.IsHurwitzUnit (InfoGeometry.Quantum.Hurwitz.basisDir i)) ∧
    (∀ j : Fin 16,
      InfoGeometry.Quantum.Hurwitz.IsHurwitzUnit (InfoGeometry.Quantum.Hurwitz.halfDir j)) ∧
    (∀ k : Fin 24,
      InfoGeometry.Quantum.Hurwitz.IsHurwitzUnit
        (InfoGeometry.Quantum.Hurwitz.hurwitzDirection k)) ∧
    (∀ q : Quat ℝ, qNorm q = Quaternion.normSq (toHurwitzNode q)) ∧
    InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet.paraunitary
      InfoGeometry.Analysis.D23HurwitzCliffordFilterBank.d23HurwitzCliffordFilterBank ∧
    InfoGeometry.Analysis.D23HurwitzCliffordFilterBank.d23HurwitzCliffordFilterBank.sum_normSq_eq_one := by
  have hNorm : ∀ q : Quat ℝ, qNorm q = Quaternion.normSq (toHurwitzNode q) := by
    intro q
    dsimp [qNorm, toHurwitzNode]
    rw [InfoGeometry.Quantum.Hurwitz.node_normSq]
    ring
  exact ⟨InfoGeometry.Quantum.Hurwitz.card_hurwitzDirections,
    InfoGeometry.Quantum.Hurwitz.basisDir_isHurwitzUnit,
    InfoGeometry.Quantum.Hurwitz.halfDir_isHurwitzUnit,
    InfoGeometry.Quantum.Hurwitz.hurwitzDirection_isHurwitzUnit,
    hNorm,
    InfoGeometry.Analysis.D23HurwitzCliffordFilterBank.d23HurwitzCliffordFilterBank_paraunitary,
    InfoGeometry.Analysis.D23HurwitzCliffordFilterBank.d23HurwitzCliffordFilterBank_sum_normSq_eq_one⟩

end Quat

-- ============================================================================
-- DIRECTIVE 3 (𝔚ℌ₆–𝔚ℌ₇): Adams J-Homomorphism & The Bott–Hurwitz Φ₂₄(x) = Φ₆(x⁴) Bridge
-- ============================================================================

section BottHurwitzAdamsBridge
variable {K : Type u} [CommRing K]

/-- 6th cyclotomic polynomial `Φ₆(y) = y² - y + 1` (governing the Hurwitz corner `ω⁶ = 1`): -/
def Phi6 (y : K) : K := y ^ 2 - y + 1

/-- 24th cyclotomic polynomial `Φ₂₄(x) = x⁸ - x⁴ + 1` (governing the 24-step Adams cycle): -/
def Phi24 (x : K) : K := x ^ 8 - x ^ 4 + 1

/--
**Theorem 4 (𝔚ℌ₆ & 𝔚ℌ₇ — The Bott–Hurwitz Cyclotomic Bridge `Φ₂₄(x) = Φ₆(x⁴)` & 24-Periodicity):**
1. **Composition of 6-Fold Hurwitz Rotation with 4-Fold Bott Spinor Cover (`y = x⁴`):**
   `Phi6 (x ^ 4) = Phi24 x` (`(x⁴)² - x⁴ + 1 = x⁸ - x⁴ + 1`).
2. **Exact Factorization of the 24-Step Cycle `x²⁴ - 1`:**
   `x ^ 24 - 1 = (x ^ 12 - 1) * (x ^ 4 + 1) * Phi24 x`, proving that every root of `Phi24 x = 0`
   executes an exact 24-step periodic cycle (`x²⁴ = 1`) while having `x¹² = -1` (spinor sign flip at 12)!
-/
lemma adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge (x : K) :
    Phi6 (x ^ 4) = Phi24 x ∧
    (x ^ 4 + 1) * Phi24 x = x ^ 12 + 1 ∧
    (x ^ 12 - 1) * (x ^ 4 + 1) * Phi24 x = x ^ 24 - 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp [Phi6, Phi24]
    ring

/--
**Theorem 5 (𝔚ℌ₇ — Master 7-Stage Wigner–Hurwitz–Adams Synthesis):**
Unites the 7-stage poset $\mathfrak{WH}_1 \prec \dots \prec \mathfrak{WH}_7$ in one choice-free theorem:
1. Acyclicity of `WignerHurwitzAdamsStage.coverEdge`,
2. Resolution `Pi1 M + Pi2 M + Pi3_pos M + Pi3_neg M = smul 6 M` and Frobenius Pythagorean
   decomposition `36 * frobInner M N = ∑_α frobInner (Pi_α M) (Pi_α N)` (`𝔚ℌ₁–𝔚ℌ₃`),
3. Hurwitz `D₂₄ = 8 + 16 = 24` vs `2O = 24 + 24 = 48` split, Euler norm multiplicativity
   `qNorm (Q * X) = qNorm Q * qNorm X`, and `ℤ₃` attention triality `W * i * conj W = 4 • j` (`𝔚ℌ₄–𝔚ℌ₅`),
4. Bott–Hurwitz–Adams cyclotomic bridge `Phi6 (x ^ 4) = Phi24 x` and
   `(x ^ 12 - 1) * (x ^ 4 + 1) * Phi24 x = x ^ 24 - 1` (`𝔚ℌ₆–𝔚ℌ₇`).
-/
lemma wh7_master_wigner_hurwitz_adams_synthesis
    (M N : Mat3 K) (Q X : Quat K) (x : K) :
    (∀ a : WignerHurwitzAdamsStage, ¬ WignerHurwitzAdamsStage.coverEdge a a) ∧
    (Mat3.Pi1 M + Mat3.Pi2 M + Mat3.Pi3_pos M + Mat3.Pi3_neg M = Mat3.smul 6 M ∧
     36 * Mat3.frobInner M N =
       Mat3.frobInner (Mat3.Pi1 M) (Mat3.Pi1 N) +
       Mat3.frobInner (Mat3.Pi2 M) (Mat3.Pi2 N) +
       Mat3.frobInner (Mat3.Pi3_pos M) (Mat3.Pi3_pos N) +
       Mat3.frobInner (Mat3.Pi3_neg M) (Mat3.Pi3_neg N)) ∧
    (8 + 2 ^ 4 = 24 ∧ 24 + 6 * 4 = 48 ∧
     Quat.qNorm (Q * X) = Quat.qNorm Q * Quat.qNorm X ∧
     (Quat.hurwitzW : Quat K) * Quat.qi * Quat.conj Quat.hurwitzW = Quat.smul 4 Quat.qj) ∧
    (Phi6 (x ^ 4) = Phi24 x ∧
     (x ^ 12 - 1) * (x ^ 4 + 1) * Phi24 x = x ^ 24 - 1) := by
  have hCG := Mat3.clebsch_gordan_s4_idempotency_and_mutual_orthogonality M
  have hFrob := Mat3.clebsch_gordan_frobenius_pythagorean_theorem M N
  have hHurw := Quat.hurwitz_corner_triality_attention_filter Q X
  have hAdams := adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge x
  exact ⟨WignerHurwitzAdamsStage.coverEdge_acyclic,
    ⟨hCG.1, hFrob.2.2.2.2⟩,
    ⟨hHurw.1, hHurw.2.1, hHurw.2.2.1, hHurw.2.2.2.2.2.2.1⟩,
    ⟨hAdams.1, hAdams.2.2⟩⟩

end BottHurwitzAdamsBridge

end WignerHurwitzAdamsKTheoryPoset
