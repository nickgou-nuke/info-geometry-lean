/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential

/-!
# Alexei Kitaev Lecture 1 — Local Bulk Energy Gaps, Universal Invertibility & Ω-Spectrum Poset (𝔎𝔏₁ ≺ ⋯ ≺ 𝔎𝔏₇)

## i. Overview

Finite algebraic and ring-theoretic formalization of the 7-stage causal poset ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$)
motivated by Alexei Kitaev's Lecture 1 on condensed-matter-inspired $K$-theory. This module proves
the noncommutative ring identities for ground-state fiber convexity, spectral-annulus midpoint
centering, square-first vs. truncate-first Peirce collar excursion, and $2 \times 2$ block-matrix
universal anticommutation over any ring `[Ring B]` or commutative ring `[CommRing K]`. It does not
construct infinite-dimensional topological classifying spaces $\mathbb{C}\mathbb{P}^\infty$,
Lipschitz loop spaces $\Omega A_{d+1}$, or continuous homotopy equivalences $A_d \simeq KO_{d-2}$.

* **Node `𝔎𝔏₁` (`convex_hamiltonian_fiber_ground_state_invariance`):**
  Proves that if `H₀ * P₀ = 0` and `H₁ * P₀ = 0`, then for any parameter `t`, the affine combination
  `((1 - t) * H₀ + t * H₁) * P₀ = 0` also annihilates `P₀`.
* **Node `𝔎𝔏₂` (`spectral_gap_annulus_midpoint_centering`):**
  Proves over any commutative ring `K` that
  `(b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2 = 4 * (Q - a_sq) * (b_sq - Q)`.
* **Node `𝔎𝔏₃` (`square_first_local_bulk_gap_collar_healing` & `n_plus_minus_eq_centralizer_cones`):**
  Proves over any `[Ring B]` that for an idempotent `P * P = P`, the difference between the
  square-first projection `SquareFirstBulkOp P A μ₀ = P * (-(A * A) - μ₀) * P` and the
  truncate-first projection `TruncateFirstBulkOp P A μ₀ = -(P * A * P)² - P * μ₀ * P` is the
  two-hop Peirce collar excursion `- (N_plus P A * N_minus P A)`, bridged directly to
  `InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential.conePlus` and `coneMinus`.
* **Node `𝔎𝔏₄–𝔎𝔏₇` (`Block2.universal_invertibility_anticommuting_homotopy` & `kl7_master_kitaev_local_gap_omega_spectrum_synthesis`):**
  Proves that for any `A : B` (without commutation hypotheses on `A`), the $2 \times 2$ block
  matrices `doubledSys A = [[0, A], [A, 0]]` and `baseDecoupler = [[0, 1], [-1, 0]]` satisfy
  `doubledSys A * baseDecoupler + baseDecoupler * doubledSys A = 0`, and that for scalars `c, s`
  commuting with `A` and each other, `RotorXY A c s * RotorXY A c s = diag(c² A² - s², c² A² - s²)`,
  together with the dimer re-association cancellation `(A - A₀) + (A₀ - A₀) + (A₀ - A₀) = A - A₀`.

## ii. Key results

- `KitaevLocalGapStage`, `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`
- `convex_hamiltonian_fiber_ground_state_invariance`
- `spectral_gap_annulus_midpoint_centering`
- `n_plus_minus_eq_centralizer_cones`
- `square_first_local_bulk_gap_collar_healing`
- `Block2.universal_invertibility_anticommuting_homotopy`
- `kl7_master_kitaev_local_gap_omega_spectrum_synthesis`

## iii. Table of contents

- Section 0: The 7-Stage Kitaev Local-Gap Poset (`𝔎𝔏₁ ≺ ⋯ ≺ 𝔎𝔏₇`)
- Section 1 (`𝔎𝔏₁–𝔎𝔏₂`): Affine Ground-State Fiber Invariance & Spectral Annulus Centering
- Section 2 (`𝔎𝔏₃`): Square-First Local Bulk Gap vs. Truncate-First Collar Excursion
- Section 3 (`𝔎𝔏₄–𝔎𝔏₇`): Universal $2 \times 2$ Anticommuting Rotor & Dimer Cancellation

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `KitaevLocalGapStage` ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$), `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`,
  - `convex_hamiltonian_fiber_ground_state_invariance`, `spectral_gap_annulus_midpoint_centering`,
  - `n_plus_minus_eq_centralizer_cones`, `square_first_local_bulk_gap_collar_healing`,
  - `Block2.universal_invertibility_anticommuting_homotopy`, `kl7_master_kitaev_local_gap_omega_spectrum_synthesis`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Ring identities hold over `[Ring B]` under explicit hypotheses (`h0 : H0 * P0 = 0`, `h1 : H1 * P0 = 0`, `hP : P * P = P`, `hc : c * A = A * c`, `hs : s * A = A * s`, `hcs : c * s = s * c`).
* **BUCKET 3 — Out-of-Scope Topological / Analytic Claims:**
  - Continuous homotopy equivalences $B_0 \simeq \mathbb{C}\mathbb{P}^\infty$, $A_d \simeq \Omega A_{d+1} \simeq KO_{d-2}$, and operator-norm bounds on infinite lattices remain outside this algebraic owner.

## iv. References

- A. Kitaev, *Periodic table for topological insulators and superconductors*, AIP Conf. Proc. 1134, 22–30 (2009).
- `InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential`.
-/

namespace KitaevLocalGapOmegaSpectrumPoset

universe u

-- ============================================================================
-- SECTION 0: The 7-Stage Kitaev Local-Gap Poset (𝔎𝔏₁ ≺ ⋯ ≺ 𝔎𝔏₇)
-- ============================================================================

/-- The 7-stage causal poset ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$) organizing
affine ground-state fiber invariance, spectral-annulus midpoint centering, square-first Peirce
collar excursion healing, universal $2 \times 2$ block anticommutation, gap-preserving rotor
squaring, and dimer re-association cancellation. -/
inductive KitaevLocalGapStage : Type
  | kl1ConvexHamiltonianFiberGroundStateInvariance
  | kl2SpectralGapAnnulusMidpointCentering
  | kl3SquareFirstLocalBulkGapCollarHealing
  | kl4UniversalBlockAnticommutatorIdentity
  | kl5GapPreservingHomotopyRotorSquare
  | kl6DimerPeierlsSuspensionReassociation
  | kl7OmegaSpectrumAlgebraicMasterSynthesis
  deriving DecidableEq, Repr

namespace KitaevLocalGapStage

/-- Numerical stage index `0 .. 6` for `KitaevLocalGapStage`. -/
def rank : KitaevLocalGapStage → ℕ
  | .kl1ConvexHamiltonianFiberGroundStateInvariance => 0
  | .kl2SpectralGapAnnulusMidpointCentering => 1
  | .kl3SquareFirstLocalBulkGapCollarHealing => 2
  | .kl4UniversalBlockAnticommutatorIdentity => 3
  | .kl5GapPreservingHomotopyRotorSquare => 4
  | .kl6DimerPeierlsSuspensionReassociation => 5
  | .kl7OmegaSpectrumAlgebraicMasterSynthesis => 6

/-- The stage rank map is injective. -/
lemma rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder KitaevLocalGapStage :=
  LinearOrder.lift' rank rank_injective

instance instFintype : Fintype KitaevLocalGapStage where
  elems := {
    .kl1ConvexHamiltonianFiberGroundStateInvariance,
    .kl2SpectralGapAnnulusMidpointCentering,
    .kl3SquareFirstLocalBulkGapCollarHealing,
    .kl4UniversalBlockAnticommutatorIdentity,
    .kl5GapPreservingHomotopyRotorSquare,
    .kl6DimerPeierlsSuspensionReassociation,
    .kl7OmegaSpectrumAlgebraicMasterSynthesis
  }
  complete := by intro x; cases x <;> decide

/-- Directed Hasse covering relation on `KitaevLocalGapStage`. -/
inductive coverEdge : KitaevLocalGapStage → KitaevLocalGapStage → Prop
  | kl1_to_kl2 :
      coverEdge .kl1ConvexHamiltonianFiberGroundStateInvariance
        .kl2SpectralGapAnnulusMidpointCentering
  | kl2_to_kl3 :
      coverEdge .kl2SpectralGapAnnulusMidpointCentering
        .kl3SquareFirstLocalBulkGapCollarHealing
  | kl3_to_kl4 :
      coverEdge .kl3SquareFirstLocalBulkGapCollarHealing
        .kl4UniversalBlockAnticommutatorIdentity
  | kl4_to_kl5 :
      coverEdge .kl4UniversalBlockAnticommutatorIdentity
        .kl5GapPreservingHomotopyRotorSquare
  | kl5_to_kl6 :
      coverEdge .kl5GapPreservingHomotopyRotorSquare
        .kl6DimerPeierlsSuspensionReassociation
  | kl6_to_kl7 :
      coverEdge .kl6DimerPeierlsSuspensionReassociation
        .kl7OmegaSpectrumAlgebraicMasterSynthesis

/-- Every covering edge strictly increases stage order (`a < b`). -/
lemma coverEdge_strictMono {a b : KitaevLocalGapStage} (h : coverEdge a b) :
    a < b := by
  cases h <;> decide

/-- No stage covers itself. -/
lemma coverEdge_acyclic (a : KitaevLocalGapStage) : ¬ coverEdge a a := by
  intro h
  have := coverEdge_strictMono h
  exact lt_irrefl a this

end KitaevLocalGapStage

-- ============================================================================
-- NODE 𝔎𝔏₁ & 𝔎𝔏₂: Contractible 0D Hamiltonian Fibers & Spectral Gap Centering
-- ============================================================================

section ZeroDimFiberAndGapCentering
variable {B : Type u} [Ring B]

/--
**Theorem 1 (𝔎𝔏₁ — Affine Ground-State Annihilation Invariance):**
If two operators `H₀, H₁` annihilate a ground-state projector `P₀` (`H₀ * P₀ = 0` and
`H₁ * P₀ = 0`), then for any interpolation element `t`, the affine combination
`H(t) = (1 - t) * H₀ + t * H₁` also annihilates `P₀` (`((1 - t) * H₀ + t * H₁) * P₀ = 0`).
-/
theorem convex_hamiltonian_fiber_ground_state_invariance
    (H0 H1 P0 t : B) (h0 : H0 * P0 = 0) (h1 : H1 * P0 = 0) :
    ((1 - t) * H0 + t * H1) * P0 = 0 := by
  calc ((1 - t) * H0 + t * H1) * P0
    _ = (1 - t) * (H0 * P0) + t * (H1 * P0) := by simp only [add_mul, mul_assoc]
    _ = 0 := by rw [h0, h1, mul_zero, mul_zero, add_zero]

/--
**Theorem 2 (𝔎𝔏₂ — Spectral Annulus Midpoint Centering Identity):**
In any commutative ring `K` (scaled by `4` to avoid division by `2`), the quadratic product
`4 * (Q - a_sq) * (b_sq - Q)` equals the centered difference of squares
`(b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2`.
-/
theorem spectral_gap_annulus_midpoint_centering
    {K : Type u} [CommRing K] (Q a_sq b_sq : K) :
    (b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2 =
      4 * (Q - a_sq) * (b_sq - Q) := by
  ring

end ZeroDimFiberAndGapCentering

-- ============================================================================
-- NODE 𝔎𝔏₃: Square-First Local Bulk Gap vs. Truncate-First Boundary Failure
-- ============================================================================

section SquareFirstLocalBulkGap
variable {B : Type u} [Ring B]

/-- Upper-right Peirce off-diagonal collar transition `P * A * (1 - P)`. -/
def N_plus  (P A : B) : B := P * A * (1 - P)

/-- Lower-left Peirce off-diagonal collar transition `(1 - P) * A * P`. -/
def N_minus (P A : B) : B := (1 - P) * A * P

/-- `N_plus`, `N_minus`, and their reversed sum agree with `PeirceSpine.conePlus`, `coneMinus`, and `oddGrade`. -/
lemma n_plus_minus_eq_centralizer_cones (P A : B) :
    N_plus P A = InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A ∧
    N_minus P A = InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P A ∧
    N_minus P A + N_plus P A =
      InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade P A := by
  refine ⟨rfl, rfl, ?_⟩
  dsimp only [N_plus, N_minus,
    InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade]
  abel

/-- Square-first local bulk gap operator `P * (-(A * A) - μ₀) * P` on the interior projector `P`. -/
def SquareFirstBulkOp (P A μ0 : B) : B :=
  P * (- (A * A) - μ0) * P

/-- Naive truncate-first operator `-(P * A * P)² - P * μ₀ * P` cutting `A` before squaring. -/
def TruncateFirstBulkOp (P A μ0 : B) : B :=
  - ((P * A * P) * (P * A * P)) - P * μ0 * P

/-- Left-multiplication absorption for an idempotent `P * P = P`. -/
lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/--
**Theorem 3 (𝔎𝔏₃ — Square-First Collar Healing vs. Truncate-First Spurious Edge Modes):**
For any interior projector `P * P = P` and operator `A`:
1. **Exact Collar Healing Identity:**
   `SquareFirstBulkOp P A μ₀ - TruncateFirstBulkOp P A μ₀ = - (N_plus P A * N_minus P A)`.
2. **Unit-Gapped Interior Bulk (`P * (A * A) * P = -P`):**
   If `P * (A * A) * P = -P`, then `SquareFirstBulkOp P A 1 = 0`, whereas
   `TruncateFirstBulkOp P A 1 = N_plus P A * N_minus P A`.
-/
theorem square_first_local_bulk_gap_collar_healing
    (P A μ0 : B) (hP : P * P = P) :
    -- 1. Universal difference between Square-First and Truncate-First:
    SquareFirstBulkOp P A μ0 - TruncateFirstBulkOp P A μ0 =
      - (N_plus P A * N_minus P A) ∧
    -- 2. When the interior bulk has unit gap (P A² P = -P), Square-First has 0 defect:
    (P * (A * A) * P = -P →
      SquareFirstBulkOp P A 1 = 0 ∧
      TruncateFirstBulkOp P A 1 = N_plus P A * N_minus P A) := by
  have h_diff : SquareFirstBulkOp P A μ0 - TruncateFirstBulkOp P A μ0 =
      - (N_plus P A * N_minus P A) := by
    dsimp only [SquareFirstBulkOp, TruncateFirstBulkOp, N_plus, N_minus]
    simp only [sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, proj_idem hP]
    abel
  refine ⟨h_diff, ?_⟩
  intro h_unit_gap
  have h_sq_zero : SquareFirstBulkOp P A 1 = 0 := by
    dsimp [SquareFirstBulkOp]
    calc P * (-(A * A) - 1) * P
      _ = - (P * (A * A) * P) - P * P := by
          simp only [sub_mul, mul_sub, neg_mul, mul_neg, mul_one, mul_assoc]
      _ = - (-P) - P := by rw [h_unit_gap, hP]
      _ = 0 := by abel
  have h_trunc : TruncateFirstBulkOp P A 1 = N_plus P A * N_minus P A := by
    have h2 : SquareFirstBulkOp P A 1 - TruncateFirstBulkOp P A 1 =
        - (N_plus P A * N_minus P A) := by
      dsimp only [SquareFirstBulkOp, TruncateFirstBulkOp, N_plus, N_minus]
      simp only [sub_mul, mul_sub, one_mul, mul_one,
                 neg_mul, mul_neg, mul_assoc, proj_idem hP]
      abel
    rw [h_sq_zero, zero_sub, neg_inj] at h2
    exact h2
  exact ⟨h_sq_zero, h_trunc⟩

end SquareFirstLocalBulkGap

-- ============================================================================
-- NODE 𝔎𝔏₄, 𝔎𝔏₅, 𝔎𝔏₆, 𝔎𝔏₇: Universal Invertibility Rotor & Dimer Peierls Cancellation
-- ============================================================================

/-- Explicit $2 \times 2$ block matrix carrier over any ring `B`. -/
@[ext]
structure Block2 (B : Type u) where
  b11 : B
  b12 : B
  b21 : B
  b22 : B
  deriving DecidableEq, Inhabited

namespace Block2
variable {B : Type u} [Ring B]

instance instZero : Zero (Block2 B) := ⟨⟨0, 0, 0, 0⟩⟩
instance instAdd  : Add  (Block2 B) := ⟨fun X Y => ⟨X.b11 + Y.b11, X.b12 + Y.b12, X.b21 + Y.b21, X.b22 + Y.b22⟩⟩
instance instSub  : Sub  (Block2 B) := ⟨fun X Y => ⟨X.b11 - Y.b11, X.b12 - Y.b12, X.b21 - Y.b21, X.b22 - Y.b22⟩⟩

/-- Block matrix multiplication on `Block2 B`. -/
def mul (X Y : Block2 B) : Block2 B where
  b11 := X.b11 * Y.b11 + X.b12 * Y.b21
  b12 := X.b11 * Y.b12 + X.b12 * Y.b22
  b21 := X.b21 * Y.b11 + X.b22 * Y.b21
  b22 := X.b21 * Y.b12 + X.b22 * Y.b22

instance instMul : Mul (Block2 B) := ⟨mul⟩

@[simp] lemma zero_b11 : (0 : Block2 B).b11 = 0 := rfl
@[simp] lemma zero_b12 : (0 : Block2 B).b12 = 0 := rfl
@[simp] lemma zero_b21 : (0 : Block2 B).b21 = 0 := rfl
@[simp] lemma zero_b22 : (0 : Block2 B).b22 = 0 := rfl

@[simp] lemma add_b11 (X Y : Block2 B) : (X + Y).b11 = X.b11 + Y.b11 := rfl
@[simp] lemma add_b12 (X Y : Block2 B) : (X + Y).b12 = X.b12 + Y.b12 := rfl
@[simp] lemma add_b21 (X Y : Block2 B) : (X + Y).b21 = X.b21 + Y.b21 := rfl
@[simp] lemma add_b22 (X Y : Block2 B) : (X + Y).b22 = X.b22 + Y.b22 := rfl

@[simp] lemma mul_eq (X Y : Block2 B) : X * Y = mul X Y := rfl

/-- Hadamard-rotated doubled system `X(A) = [[0, A], [A, 0]]`. -/
def doubledSys (A : B) : Block2 B :=
  ⟨0, A,
   A, 0⟩

/-- Universal skew-symmetric basepoint decoupler `Y = [[0, 1], [-1, 0]]`. -/
def baseDecoupler : Block2 B :=
  ⟨ 0, 1,
   -1, 0⟩

/-- Homotopy rotor `RotorXY A c s = [[0, c * A + s], [c * A - s, 0]]`. -/
def RotorXY (A c s : B) : Block2 B :=
  ⟨0,         c * A + s,
   c * A - s, 0⟩

/--
**Theorem 4 (𝔎𝔏₄–𝔎𝔏₇ — Universal Invertibility Anticommuting Rotor & Dimer Cancellation):**
For any operator `A ∈ B` (without commutation assumptions on `A` for the anticommutator):
1. `doubledSys A` and `baseDecoupler` strictly anticommute:
   `doubledSys A * baseDecoupler + baseDecoupler * doubledSys A = 0`.
2. For scalars `c, s` commuting with `A` and each other, `RotorXY A c s` has diagonal square
   `⟨c * c * (A * A) - s * s, 0, 0, c * c * (A * A) - s * s⟩`.
3. Dimer cascade re-association `(A - A₀) + (A₀ - A₀) + (A₀ - A₀) = A - A₀` cancels adjacent trivial pairs.
-/
theorem universal_invertibility_anticommuting_homotopy
    (A A0 c s : B) (hc : c * A = A * c) (hs : s * A = A * s) (hcs : c * s = s * c) :
    -- 1. Universal anticommutation {X(A), Y} = 0 for ALL A ∈ B:
    doubledSys A * baseDecoupler + baseDecoupler * doubledSys A = (0 : Block2 B) ∧
    -- 2. Exact gap-preserving square of the homotopy rotor:
    RotorXY A c s * RotorXY A c s =
      ⟨c * c * (A * A) - s * s, 0,
       0, c * c * (A * A) - s * s⟩ ∧
    -- 3. Dimer cascade re-association cancels background pairs (A₀ - A₀):
    (A - A0) + (A0 - A0) + (A0 - A0) = A - A0 := by
  have h_quad : (c * A + s) * (c * A - s) = c * c * (A * A) - s * s := by
    calc (c * A + s) * (c * A - s)
      _ = c * (A * c) * A - c * A * s + s * c * A - s * s := by
          simp only [add_mul, mul_sub, mul_assoc]; abel
      _ = c * c * (A * A) - c * (A * s) + c * s * A - s * s := by
          rw [← hc, ← hcs]; simp only [mul_assoc]
      _ = c * c * (A * A) - s * s := by
          rw [← hs]; simp only [mul_assoc]; abel
  have h_quad2 : (c * A - s) * (c * A + s) = c * c * (A * A) - s * s := by
    calc (c * A - s) * (c * A + s)
      _ = c * (A * c) * A + c * A * s - s * c * A - s * s := by
          simp only [sub_mul, mul_add, mul_assoc]; abel
      _ = c * c * (A * A) + c * (A * s) - c * s * A - s * s := by
          rw [← hc, ← hcs]; simp only [mul_assoc]
      _ = c * c * (A * A) - s * s := by
          rw [← hs]; simp only [mul_assoc]; abel
  refine ⟨?_, ?_, by abel⟩
  · ext <;>
    · dsimp only [doubledSys, baseDecoupler, mul_eq, add_b11, add_b12, add_b21, add_b22,
        zero_b11, zero_b12, zero_b21, zero_b22, mul]
      simp only [mul_zero, zero_mul, mul_one, one_mul, mul_neg, neg_mul]
      abel
  · ext <;>
    · dsimp only [RotorXY, mul_eq, mul]
      simp only [zero_mul, mul_zero, add_zero, zero_add]
      try (first | exact h_quad | exact h_quad2)

end Block2

/--
**Theorem 5 (𝔎𝔏₇ — Master 7-Stage Kitaev Local-Gap & Invertibility Synthesis):**
Combines all 7 stages ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$) in a single theorem:
1. Acyclicity of `KitaevLocalGapStage.coverEdge`,
2. Affine ground-state fiber invariance `((1 - t) * H₀ + t * H₁) * P₀ = 0` (`𝔎𝔏₁`) and
   midpoint annulus centering `(b_sq - a_sq)² - (2 * Q - (a_sq + b_sq))² = 4 * (Q - a_sq) * (b_sq - Q)` (`𝔎𝔏₂`),
3. Square-first vs. truncate-first Peirce collar identity
   `SquareFirstBulkOp P A μ₀ - TruncateFirstBulkOp P A μ₀ = - (N_plus P A * N_minus P A)` (`𝔎𝔏₃`),
4. Universal $2 \times 2$ anticommutator `doubledSys A * baseDecoupler + baseDecoupler * doubledSys A = 0`,
   rotor square `RotorXY A c s * RotorXY A c s`, and dimer cancellation `(A - A₀) + (A₀ - A₀) + (A₀ - A₀) = A - A₀` (`𝔎𝔏₄–𝔎𝔏₇`).
-/
theorem kl7_master_kitaev_local_gap_omega_spectrum_synthesis
    {B : Type u} [Ring B] {K : Type u} [CommRing K]
    (H0 H1 P0 t P A A0 μ0 c s : B)
    (h0 : H0 * P0 = 0) (h1 : H1 * P0 = 0) (hP : P * P = P)
    (hc : c * A = A * c) (hs : s * A = A * s) (hcs : c * s = s * c)
    (Q a_sq b_sq : K) :
    (∀ a : KitaevLocalGapStage, ¬ KitaevLocalGapStage.coverEdge a a) ∧
    (((1 - t) * H0 + t * H1) * P0 = 0 ∧
     (b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2 = 4 * (Q - a_sq) * (b_sq - Q)) ∧
    (SquareFirstBulkOp P A μ0 - TruncateFirstBulkOp P A μ0 =
       - (N_plus P A * N_minus P A) ∧
     N_plus P A = InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A ∧
     N_minus P A = InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P A) ∧
    (Block2.doubledSys A * Block2.baseDecoupler +
       Block2.baseDecoupler * Block2.doubledSys A = (0 : Block2 B) ∧
     Block2.RotorXY A c s * Block2.RotorXY A c s =
       ⟨c * c * (A * A) - s * s, 0,
        0, c * c * (A * A) - s * s⟩ ∧
     (A - A0) + (A0 - A0) + (A0 - A0) = A - A0) := by
  have hFib := convex_hamiltonian_fiber_ground_state_invariance H0 H1 P0 t h0 h1
  have hAnn := spectral_gap_annulus_midpoint_centering Q a_sq b_sq
  have hGap := square_first_local_bulk_gap_collar_healing P A μ0 hP
  have hCones := n_plus_minus_eq_centralizer_cones P A
  have hInv := Block2.universal_invertibility_anticommuting_homotopy A A0 c s hc hs hcs
  exact ⟨KitaevLocalGapStage.coverEdge_acyclic,
    ⟨hFib, hAnn⟩,
    ⟨hGap.1, hCones.1, hCones.2.1⟩,
    hInv⟩

end KitaevLocalGapOmegaSpectrumPoset
