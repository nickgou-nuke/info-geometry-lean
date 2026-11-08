/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential

/-!
# Alexei Kitaev Lecture 1 — Local Bulk Energy Gaps, Universal Invertibility & Ω-Spectrum Poset (𝔎𝔏₁ ≺ ⋯ ≺ 𝔎𝔏₁₁)

## i. Overview

Finite algebraic and ring-theoretic formalization of the 11-stage causal poset ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_{11}$)
motivated by Alexei Kitaev's Lecture 1 on condensed-matter-inspired $K$-theory. This module proves
the noncommutative ring identities for ground-state fiber convexity, spectral-annulus midpoint
centering, square-first vs. truncate-first Peirce collar excursion, $2 \times 2$ block-matrix
universal anticommutation (both Hadamard-rotated and direct unrotated), concrete $4$-Majorana
open Kitaev chain collar healing, and the algebraic powers of a $2 \times 2$ Brown–Gauss matrix
over `[Ring B]`. These matrix powers are not a formalization of the Fidkowski–Kitaev
classification or an Arf–Brown–Kervaire invariant. It does
not construct infinite-dimensional topological classifying spaces $\mathbb{C}\mathbb{P}^\infty$,
Lipschitz loop spaces $\Omega A_{d+1}$, or continuous homotopy equivalences $A_d \simeq KO_{d-2}$.

* **Node `𝔎𝔏₁` (`convex_hamiltonian_fiber_ground_state_invariance`):**
  Proves that if `H₀ * P₀ = 0` and `H₁ * P₀ = 0`, then for any parameter `t`, the affine combination
  `((1 - t) * H₀ + t * H₁) * P₀ = 0` also annihilates `P₀`.
* **Node `𝔎𝔏₂` (`energy_gap_annulus_midpoint_centering`):**
  Proves over any commutative ring `K` that
  `(b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2 = 4 * (Q - a_sq) * (b_sq - Q)`.
* **Node `𝔎𝔏₃` (`square_first_local_bulk_gap_collar_healing` & `n_plus_minus_eq_centralizer_cones`):**
  Proves over any `[Ring B]` that for an idempotent `P * P = P`, the difference between the
  square-first projection `SquareFirstBulkOp P A μ₀ = P * (-(A * A) - μ₀) * P` and the
  truncate-first projection `TruncateFirstBulkOp P A μ₀ = -(P * A * P)² - P * μ₀ * P` is the
  two-hop Peirce collar excursion `- (N_plus P A * N_minus P A)`, bridged directly to
  `InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential.conePlus` and `coneMinus`.
* **Node `𝔎𝔏₄–𝔎𝔏₈` (`Block2.universal_invertibility_anticommuting_homotopy` & `Block2.universal_unrotated_and_hadamard_invertibility_rotor`):**
  Over the canonical $2 \times 2$ matrix carrier `Block2 B := Matrix (Fin 2) (Fin 2) B`, proves that
  for any `A : B` (without commutation hypotheses on `A`), `baseDecoupler = !![0, 1; -1, 0]`
  anticommutes with both `doubledSys A = !![0, A; A, 0]` and the unrotated `diagSys A = !![A, 0; 0, -A]`,
  `hadamard2 * diagSys A * hadamard2 = doubledSys (A + A)`, and both `RotorXY A c s` and
  `DirectRotor A c s` square to `mk2 (c² A² - s²) 0 0 (c² A² - s²)`.
* **Node `𝔎𝔏₉–𝔎𝔏₁₀` (`Mat4.open_kitaev_majorana_chain_square_first_healing`):**
  Over `Mat4 K := Matrix (Fin 4) (Fin 4) K`, instantiates the open 2-site ($4$-Majorana) topological
  Kitaev chain `kitaevChainA` with unpaired outer boundary zero modes $(c_1, c_4)$ and inter-site
  dimer bond $(c_2, c_3)$, proving that truncate-first across `projCut2` severs the bond while the
  2-hop collar excursion `N_plus projCut2 kitaevChainA * N_minus projCut2 kitaevChainA = -projCut2`
  heals `SquareFirstBulkOp projCut2 kitaevChainA 1 = 0`.
* **Node `𝔎𝔏₁₁` (`Block2.brown_gauss_matrix_power_identities`):**
  Proves over `[Ring B]` that `baseDecoupler * baseDecoupler = -1` while
  `brownGaussU = !![1, 1; -1, 1]` satisfies `brownGaussU² = 2 • baseDecoupler`,
  `brownGaussU⁴ = (-4) • 1`, and `brownGaussU⁸ = 16 • 1`.

## ii. Key results

- `KitaevLocalGapStage`, `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`
- `convex_hamiltonian_fiber_ground_state_invariance`
- `energy_gap_annulus_midpoint_centering`
- `n_plus_minus_eq_centralizer_cones`
- `square_first_local_bulk_gap_collar_healing`
- `Block2`, `Block2.mk2`, `Block2.doubledSys_baseDecoupler_noncomm`,
  `Block2.doubledSysOne_baseDecoupler_anticomm`,
  `Block2.universal_invertibility_anticommuting_homotopy`,
  `Block2.unit_gap_rotor_preservation_and_pole_endpoints`,
  `Block2.universal_unrotated_and_hadamard_invertibility_rotor`,
  `Block2.brown_gauss_matrix_power_identities`
- `Mat4`, `Mat4.trivChainA_kitaevChainA_noncomm`, `Mat4.mat4_grading12_swap12_anticomm`,
  `Mat4.open_kitaev_majorana_chain_square_first_healing`
- `kl7_master_kitaev_local_gap_omega_spectrum_synthesis`

## iii. Table of contents

- Section 0: The 11-Stage Kitaev Local-Gap Poset (`𝔎𝔏₁ ≺ ⋯ ≺ 𝔎𝔏₁₁`)
- Section 1 (`𝔎𝔏₁–𝔎𝔏₂`): Affine Ground-State Fiber Invariance & Spectral Annulus Centering
- Section 2 (`𝔎𝔏₃`): Square-First Local Bulk Gap vs. Truncate-First Collar Excursion
- Section 3 (`𝔎𝔏₄–𝔎𝔏₈` & `𝔎𝔏₁₁`): Universal $2 \times 2$ Anticommuting Rotors, Hadamard Similarity & Brown–Gauss Matrix Powers
- Section 4 (`𝔎𝔏₉–𝔎𝔏₁₀`): Concrete $4$-Majorana Open Kitaev Chain & Square-First Collar Healing

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `KitaevLocalGapStage` ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_{11}$), `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`,
  - `convex_hamiltonian_fiber_ground_state_invariance`, `energy_gap_annulus_midpoint_centering`,
  - `n_plus_minus_eq_centralizer_cones`, `square_first_local_bulk_gap_collar_healing`,
  - `Block2.doubledSys_baseDecoupler_noncomm`, `Block2.doubledSysOne_baseDecoupler_anticomm`, `Block2.universal_invertibility_anticommuting_homotopy`, `Block2.unit_gap_rotor_preservation_and_pole_endpoints`, `Block2.universal_unrotated_and_hadamard_invertibility_rotor`, `Block2.brown_gauss_matrix_power_identities`,
  - `Mat4.trivChainA_kitaevChainA_noncomm`, `Mat4.mat4_grading12_swap12_anticomm`, `Mat4.open_kitaev_majorana_chain_square_first_healing`,
  - `kl7_master_kitaev_local_gap_omega_spectrum_synthesis`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Ring identities hold over `[Ring B]` under explicit hypotheses (`h0 : H0 * P0 = 0`, `h1 : H1 * P0 = 0`, `hP : P * P = P`, `hc : c * A = A * c`, `hs : s * A = A * s`, `hcs : c * s = s * c`).
* **BUCKET 3 — Out-of-Scope Topological / Analytic Claims:**
  - Continuous homotopy equivalences $B_0 \simeq \mathbb{C}\mathbb{P}^\infty$, $A_d \simeq \Omega A_{d+1} \simeq KO_{d-2}$, and operator-norm bounds on infinite lattices remain outside this algebraic owner.

## iv. References

- A. Kitaev, *Periodic table for topological insulators and superconductors*, AIP Conf. Proc. 1134, 22–30 (2009).
- L. Fidkowski and A. Kitaev, *Topological phases of fermions in one dimension*, Phys. Rev. B 83, 075103 (2011).
- `InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential`.
-/

namespace KitaevLocalGapOmegaSpectrumPoset

open Matrix

universe u

-- ============================================================================
-- SECTION 0: The 11-Stage Kitaev Local-Gap Poset (𝔎𝔏₁ ≺ ⋯ ≺ 𝔎𝔏₁₁)
-- ============================================================================

/-- The 11-stage causal poset ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_{11}$) organizing
affine ground-state fiber invariance, spectral-annulus midpoint centering, square-first Peirce
collar excursion healing, universal $2 \times 2$ block anticommutation, gap-preserving rotor
squaring, dimer re-association cancellation, direct unrotated rotor & Hadamard similarity,
concrete $4$-Majorana open Kitaev chain collar healing, and the 8-fold Brown–Gauss matrix cycle. -/
inductive KitaevLocalGapStage : Type
  | kl1ConvexHamiltonianFiberGroundStateInvariance
  | kl2SpectralGapAnnulusMidpointCentering
  | kl3SquareFirstLocalBulkGapCollarHealing
  | kl4UniversalBlockAnticommutatorIdentity
  | kl5GapPreservingHomotopyRotorSquare
  | kl6DimerPeierlsSuspensionReassociation
  | kl7OmegaSpectrumAlgebraicMasterSynthesis
  | kl8DirectUnrotatedRotorAndHadamardSimilarity
  | kl9FourMajoranaOpenKitaevChainBoundaryZeroModes
  | kl10FourMajoranaSquareFirstCollarHealing
  | kl11BrownGaussMatrixPowerIdentities
  deriving DecidableEq, Repr

namespace KitaevLocalGapStage

/-- Numerical stage index `0 .. 10` for `KitaevLocalGapStage`. -/
def rank : KitaevLocalGapStage → ℕ
  | .kl1ConvexHamiltonianFiberGroundStateInvariance => 0
  | .kl2SpectralGapAnnulusMidpointCentering => 1
  | .kl3SquareFirstLocalBulkGapCollarHealing => 2
  | .kl4UniversalBlockAnticommutatorIdentity => 3
  | .kl5GapPreservingHomotopyRotorSquare => 4
  | .kl6DimerPeierlsSuspensionReassociation => 5
  | .kl7OmegaSpectrumAlgebraicMasterSynthesis => 6
  | .kl8DirectUnrotatedRotorAndHadamardSimilarity => 7
  | .kl9FourMajoranaOpenKitaevChainBoundaryZeroModes => 8
  | .kl10FourMajoranaSquareFirstCollarHealing => 9
  | .kl11BrownGaussMatrixPowerIdentities => 10

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
    .kl7OmegaSpectrumAlgebraicMasterSynthesis,
    .kl8DirectUnrotatedRotorAndHadamardSimilarity,
    .kl9FourMajoranaOpenKitaevChainBoundaryZeroModes,
    .kl10FourMajoranaSquareFirstCollarHealing,
    .kl11BrownGaussMatrixPowerIdentities
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
  | kl7_to_kl8 :
      coverEdge .kl7OmegaSpectrumAlgebraicMasterSynthesis
        .kl8DirectUnrotatedRotorAndHadamardSimilarity
  | kl8_to_kl9 :
      coverEdge .kl8DirectUnrotatedRotorAndHadamardSimilarity
        .kl9FourMajoranaOpenKitaevChainBoundaryZeroModes
  | kl9_to_kl10 :
      coverEdge .kl9FourMajoranaOpenKitaevChainBoundaryZeroModes
        .kl10FourMajoranaSquareFirstCollarHealing
  | kl10_to_kl11 :
      coverEdge .kl10FourMajoranaSquareFirstCollarHealing
        .kl11BrownGaussMatrixPowerIdentities

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
    _ = (1 - t) * (H0 * P0) + t * (H1 * P0) := by noncomm_ring
    _ = 0 := by rw [h0, h1, mul_zero, mul_zero, add_zero]

/--
**Theorem 2 (𝔎𝔏₂ — Spectral Annulus Midpoint Centering Identity):**
In any commutative ring `K` (scaled by `4` to avoid division by `2`), the quadratic product
`4 * (Q - a_sq) * (b_sq - Q)` equals the centered difference of squares
`(b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2`.
-/
theorem energy_gap_annulus_midpoint_centering
    {K : Type u} [CommRing K] (Q a_sq b_sq : K) :
    (b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2 =
      4 * (Q - a_sq) * (b_sq - Q) := by
  have hDiffSq :
      (b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2 =
        ((b_sq - a_sq) + (2 * Q - (a_sq + b_sq))) *
          ((b_sq - a_sq) - (2 * Q - (a_sq + b_sq))) := by
    ring
  have hLeft : (b_sq - a_sq) + (2 * Q - (a_sq + b_sq)) = 2 * (Q - a_sq) := by
    ring
  have hRight : (b_sq - a_sq) - (2 * Q - (a_sq + b_sq)) = 2 * (b_sq - Q) := by
    ring
  rw [hDiffSq, hLeft, hRight]
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

/-- `N_plus`, `N_minus`, and their sum agree with `PeirceSpine.conePlus`, `coneMinus`, and `oddGrade`. -/
lemma n_plus_minus_eq_centralizer_cones (P A : B) :
    N_plus P A = InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A ∧
    N_minus P A = InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P A ∧
    N_plus P A + N_minus P A =
      InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade P A := by
  dsimp [N_plus, N_minus, InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
    InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
    InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade]
  refine ⟨rfl, rfl, ?_⟩
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
    SquareFirstBulkOp P A μ0 - TruncateFirstBulkOp P A μ0 =
      - (N_plus P A * N_minus P A) ∧
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
      _ = - (P * (A * A) * P) - P * P := by noncomm_ring
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

/-- Canonical $2 \times 2$ block matrix carrier `Matrix (Fin 2) (Fin 2) B` over any ring `B`. -/
abbrev Block2 (B : Type u) : Type u := Matrix (Fin 2) (Fin 2) B

namespace Block2
variable {B : Type u} [Ring B]

/-- Explicit $2 \times 2$ block matrix constructor `!![b11, b12; b21, b22]`. -/
def mk2 (b11 b12 b21 b22 : B) : Block2 B :=
  !![b11, b12; b21, b22]

/-- Hadamard-rotated doubled system `X(A) = [[0, A], [A, 0]]`. -/
def doubledSys (A : B) : Block2 B :=
  !![0, A; A, 0]

/-- Canonical unit-operator specialization `X₁ = doubledSys 1 = !![0, 1; 1, 0]` over `B`. -/
def doubledSysOne : Block2 B :=
  !![0, 1; 1, 0]

/-- Universal skew-symmetric basepoint decoupler `Y = [[0, 1], [-1, 0]]`. -/
def baseDecoupler : Block2 B :=
  !![0, 1; -1, 0]

/-- Homotopy rotor `RotorXY A c s = [[0, c * A + s], [c * A - s, 0]]`. -/
def RotorXY (A c s : B) : Block2 B :=
  !![0, c * A + s; c * A - s, 0]

/-- Unnormalized $2 \times 2$ Hadamard matrix over `ℤ`. -/
def hadamard2Z : Block2 ℤ :=
  !![1, 1; 1, -1]

/-- Universal skew-symmetric basepoint decoupler over `ℤ`. -/
def baseDecouplerZ : Block2 ℤ :=
  !![0, 1; -1, 0]

/-- Explicit non-commutativity witness for `hadamard2Z` and `baseDecouplerZ` over `ℤ`. -/
lemma doubledSys_baseDecoupler_noncomm :
    hadamard2Z * baseDecouplerZ ≠ baseDecouplerZ * hadamard2Z := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  revert h00
  decide

/-- Closed anticommutator witness `{X₁, Y} = 0` on `Block2 B = Matrix (Fin 2) (Fin 2) B`. -/
lemma doubledSysOne_baseDecoupler_anticomm :
    (doubledSysOne : Block2 B) * baseDecoupler + baseDecoupler * doubledSysOne = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [doubledSysOne, baseDecoupler]

/--
**Theorem 4 (𝔎𝔏₄–𝔎𝔏₇ — Universal Invertibility Anticommuting Rotor & Dimer Cancellation):**
For any operator `A ∈ B` (without commutation assumptions on `A` for the anticommutator):
1. `doubledSys A` and `baseDecoupler` strictly anticommute:
   `doubledSys A * baseDecoupler + baseDecoupler * doubledSys A = 0`.
2. For scalars `c, s` commuting with `A` and each other, `RotorXY A c s` has diagonal square
   `mk2 (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s)`.
3. Dimer cascade re-association `(A - A₀) + (A₀ - A₀) + (A₀ - A₀) = A - A₀` cancels adjacent trivial pairs.
-/
theorem universal_invertibility_anticommuting_homotopy
    (A A0 c s : B) (hc : c * A = A * c) (hs : s * A = A * s) (hcs : c * s = s * c) :
    doubledSys A * baseDecoupler + baseDecoupler * doubledSys A = 0 ∧
    RotorXY A c s * RotorXY A c s =
      mk2 (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s) ∧
    (A - A0) + (A0 - A0) + (A0 - A0) = A - A0 := by
  have h_quad : (c * A + s) * (c * A - s) = c * c * (A * A) - s * s := by
    calc (c * A + s) * (c * A - s)
      _ = c * (A * c) * A - c * A * s + s * c * A - s * s := by noncomm_ring
      _ = c * c * (A * A) - c * (A * s) + c * s * A - s * s := by
          rw [← hc, ← hcs]; simp only [mul_assoc]
      _ = c * c * (A * A) - s * s := by
          rw [← hs]; simp only [mul_assoc]; abel
  have h_quad2 : (c * A - s) * (c * A + s) = c * c * (A * A) - s * s := by
    calc (c * A - s) * (c * A + s)
      _ = c * (A * c) * A + c * A * s - s * c * A - s * s := by noncomm_ring
      _ = c * c * (A * A) + c * (A * s) - c * s * A - s * s := by
          rw [← hc, ← hcs]; simp only [mul_assoc]
      _ = c * c * (A * A) - s * s := by
          rw [← hs]; simp only [mul_assoc]; abel
  refine ⟨?_, ?_, by abel⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [doubledSys, baseDecoupler]
  · ext i j
    fin_cases i <;> fin_cases j <;>
    · simp [RotorXY, mk2, Matrix.mul_apply, Fin.sum_univ_two]
      try (first | exact h_quad | exact h_quad2)

/--
**Theorem 4b (𝔎𝔏₅–𝔎𝔏₆ — Unit-Gap Homotopy Invariance, Pole Specialization & Peierls Domain-Wall Sum):**
For any `A, c, s : B` with `hc : c * A = A * c`, `hs : s * A = A * s`, `hcs : c * s = s * c`:
1. **Exact Unit-Gap Preservation Along the Homotopy Path:**
   If `A * A = -1` (flattened unit-gap skew-adjoint Hamiltonian) and `c * c + s * s = 1`
   (Pythagorean rotor parameters), then `RotorXY A c s * RotorXY A c s = mk2 (-1) 0 0 (-1)`.
2. **Equator (`(1, 0)`) and Pole (`(0, ±1)`) Endpoints:**
   `RotorXY A 1 0 = doubledSys A`, `RotorXY A 0 1 = baseDecoupler`,
   `RotorXY A 0 1 * RotorXY A 0 1 = mk2 (-1) 0 0 (-1)`, and
   `RotorXY A 0 (-1) * RotorXY A 0 (-1) = mk2 (-1) 0 0 (-1)`.
3. **Peierls Domain-Wall Cancellation & 45°-Midpoint Square:**
   `RotorXY A 0 1 + RotorXY A 0 (-1) = 0` and
   `RotorXY A 1 1 * RotorXY A 1 1 = mk2 (A * A - 1) 0 0 (A * A - 1)`.
-/
theorem unit_gap_rotor_preservation_and_pole_endpoints
    (A c s : B) (hc : c * A = A * c) (hs : s * A = A * s) (hcs : c * s = s * c) :
    (A * A = -1 → c * c + s * s = 1 →
      RotorXY A c s * RotorXY A c s = mk2 (-1) 0 0 (-1)) ∧
    RotorXY A 1 0 = doubledSys A ∧
    RotorXY A 0 1 = baseDecoupler ∧
    RotorXY A 0 1 * RotorXY A 0 1 = mk2 (-1) 0 0 (-1) ∧
    RotorXY A 0 (-1) * RotorXY A 0 (-1) = mk2 (-1) 0 0 (-1) ∧
    RotorXY A 0 1 + RotorXY A 0 (-1) = (0 : Block2 B) ∧
    RotorXY A 1 1 * RotorXY A 1 1 = mk2 (A * A - 1) 0 0 (A * A - 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hA hcs1
    rw [(universal_invertibility_anticommuting_homotopy A 0 c s hc hs hcs).2.1, hA]
    have h_neg : c * c * (-1 : B) - s * s = -1 := by
      calc c * c * (-1 : B) - s * s
        _ = - (c * c + s * s) := by noncomm_ring
        _ = -1 := by rw [hcs1]
    rw [h_neg]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [RotorXY, doubledSys]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [RotorXY, baseDecoupler]
  · have h01 := (universal_invertibility_anticommuting_homotopy A 0 0 1
      (by simp) (by simp) (by simp)).2.1
    simpa using h01
  · have h0m1 := (universal_invertibility_anticommuting_homotopy A 0 0 (-1)
      (by simp) (by simp) (by simp)).2.1
    simpa using h0m1
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [RotorXY]
  · have h11 := (universal_invertibility_anticommuting_homotopy A 0 1 1
      (by simp) (by simp) (by simp)).2.1
    simpa using h11

/-- Unrotated block-diagonal doubled system `diagSys A = [[A, 0], [0, -A]]`. -/
def diagSys (A : B) : Block2 B :=
  !![A, 0; 0, -A]

/-- Unnormalized $2 \times 2$ Hadamard matrix `H = [[1, 1], [1, -1]]` over any ring `B`. -/
def hadamard2 : Block2 B :=
  !![1, 1; 1, -1]

/-- Direct unrotated homotopy rotor `DirectRotor A c s = [[c * A, s], [-s, -(c * A)]]`. -/
def DirectRotor (A c s : B) : Block2 B :=
  !![c * A, s; -s, -(c * A)]

/--
**Theorem 4c (𝔎𝔏₈ — Direct Unrotated Anticommutation, Division-Free Hadamard Conjugation & Rotor Square):**
For any operator `A ∈ B` (without commutation hypotheses on `A` for the anticommutators or Hadamard conjugation):
1. `doubledSys A` and `baseDecoupler` strictly anticommute:
   `doubledSys A * baseDecoupler + baseDecoupler * doubledSys A = 0`.
2. The unrotated block-diagonal system `diagSys A = [[A, 0], [0, -A]]` also strictly anticommutes
   with `baseDecoupler = [[0, 1], [-1, 0]]`:
   `diagSys A * baseDecoupler + baseDecoupler * diagSys A = 0`.
3. Division-free Hadamard similarity conjugates `diagSys A` to `doubledSys (A + A)` with
   `hadamard2 * hadamard2 = mk2 2 0 0 2`.
4. For scalars `c, s` commuting with `A` and each other, both `RotorXY A c s` and `DirectRotor A c s`
   have identical diagonal square `mk2 (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s)`.
-/
theorem universal_unrotated_and_hadamard_invertibility_rotor
    (A c s : B) (hc : c * A = A * c) (hs : s * A = A * s) (hcs : c * s = s * c) :
    doubledSys A * baseDecoupler + baseDecoupler * doubledSys A = 0 ∧
    diagSys A * baseDecoupler + baseDecoupler * diagSys A = 0 ∧
    (hadamard2 * diagSys A * hadamard2 = doubledSys (A + A) ∧
     (hadamard2 : Block2 B) * hadamard2 = mk2 2 0 0 2) ∧
    RotorXY A c s * RotorXY A c s =
      mk2 (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s) ∧
    DirectRotor A c s * DirectRotor A c s =
      mk2 (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s) := by
  have hInv := universal_invertibility_anticommuting_homotopy A 0 c s hc hs hcs
  have h_d00 : c * A * (c * A) + -(s * s) = c * c * (A * A) - s * s := by
    calc c * A * (c * A) + -(s * s)
      _ = c * (A * c) * A - s * s := by noncomm_ring
      _ = c * c * (A * A) - s * s := by rw [← hc]; simp only [mul_assoc]
  have h_d01 : c * A * s + -(s * (c * A)) = 0 := by
    calc c * A * s + -(s * (c * A))
      _ = c * (A * s) - s * c * A := by noncomm_ring
      _ = c * s * A - c * s * A := by rw [← hs, ← hcs]; simp only [mul_assoc]
      _ = 0 := by abel
  have h_d10 : -(s * (c * A)) + c * A * s = 0 := by
    calc -(s * (c * A)) + c * A * s
      _ = - (s * c * A) + c * (A * s) := by noncomm_ring
      _ = - (c * s * A) + c * s * A := by rw [← hs, ← hcs]; simp only [mul_assoc]
      _ = 0 := by abel
  have h_d11 : -(s * s) + c * A * (c * A) = c * c * (A * A) - s * s := by
    calc -(s * s) + c * A * (c * A)
      _ = c * (A * c) * A - s * s := by noncomm_ring
      _ = c * c * (A * A) - s * s := by rw [← hc]; simp only [mul_assoc]
  refine ⟨hInv.1, ?_, ⟨?_, ?_⟩, hInv.2.1, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagSys, baseDecoupler]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamard2, diagSys, doubledSys]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamard2, mk2, one_add_one_eq_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
    · simp [DirectRotor, mk2, Matrix.mul_apply, Fin.sum_univ_two]
      try (first | exact h_d00 | exact h_d01 | exact h_d10 | exact h_d11)

/-- Brown–Gauss matrix `U = 1 + Y = [[1, 1], [-1, 1]]` over any ring `B`. -/
def brownGaussU : Block2 B :=
  !![1, 1; -1, 1]

/- The following identities concern only the unnormalized matrix `U`. In
particular, the first identity is only the square of a matrix generator; it
does not assert a two-chain mass term or a free-fermion invariant. They
are not a construction of the free-fermion classification, an ABK invariant,
or the Fidkowski–Kitaev interacting classification map. -/
/-- The unnormalized Brown–Gauss matrix `U = [[1,1],[-1,1]]` satisfies the
algebraic power identities `U²=2Y`, `U⁴=-4I`, and `U⁸=16I`. These identities
alone do not imply a Pin-minus bordism or interacting classification result. -/
theorem brown_gauss_matrix_power_identities :
    (baseDecoupler : Block2 B) * baseDecoupler = -1 ∧
    (brownGaussU : Block2 B) * brownGaussU = (2 : B) • (baseDecoupler : Block2 B) ∧
    ((brownGaussU : Block2 B) * brownGaussU) * (brownGaussU * brownGaussU) =
      (-4 : B) • (1 : Block2 B) ∧
    (((brownGaussU : Block2 B) * brownGaussU) * (brownGaussU * brownGaussU)) *
      (((brownGaussU : Block2 B) * brownGaussU) * (brownGaussU * brownGaussU)) =
      (16 : B) • (1 : Block2 B) := by
  have hY2 : (baseDecoupler : Block2 B) * baseDecoupler = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [baseDecoupler]
  have hU2 : (brownGaussU : Block2 B) * brownGaussU = (2 : B) • (baseDecoupler : Block2 B) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [brownGaussU, baseDecoupler, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;>
      norm_num
  have hU4 : ((brownGaussU : Block2 B) * brownGaussU) * (brownGaussU * brownGaussU) =
      (-4 : B) • (1 : Block2 B) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [brownGaussU, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;>
      norm_num
  have hU8 : (((brownGaussU : Block2 B) * brownGaussU) * (brownGaussU * brownGaussU)) *
      (((brownGaussU : Block2 B) * brownGaussU) * (brownGaussU * brownGaussU)) =
      (16 : B) • (1 : Block2 B) := by
    rw [hU4]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.one_apply, smul_eq_mul] <;>
      norm_num
  exact ⟨hY2, hU2, hU4, hU8⟩

end Block2

-- ============================================================================
-- SECTION 4 (𝔎𝔏₉–𝔎𝔏₁₀): Concrete 4-Majorana Open Kitaev Chain & Collar Healing
-- ============================================================================

/-- Canonical $4 \times 4$ Majorana matrix carrier `Matrix (Fin 4) (Fin 4) K` over a ring `K`. -/
abbrev Mat4 (K : Type u) : Type u := Matrix (Fin 4) (Fin 4) K

namespace Mat4
variable {K : Type u} [CommRing K]

/-- $4 \times 4$ identity matrix `I₄` in `Mat4 K`. -/
def I4 : Mat4 K :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- `I4` coincides with the ring identity `(1 : Mat4 K)`. -/
lemma I4_eq_one : (I4 : Mat4 K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [I4]

/-- Trivial intra-site dimerized 4-Majorana chain pairing `(c₁, c₂)` and `(c₃, c₄)`. -/
def trivChainA : Mat4 K :=
  !![ 0,  1,  0,  0;
     -1,  0,  0,  0;
      0,  0,  0,  1;
      0,  0, -1,  0]

/-- Open 2-site topological Kitaev chain pairing `(c₂, c₃)` with dangling edge zero modes `c₁, c₄`. -/
def kitaevChainA : Mat4 K :=
  !![0,  0,  0,  0;
     0,  0,  1,  0;
     0, -1,  0,  0;
     0,  0,  0,  0]

/-- Interior projector onto the full inter-site bulk dimer `{c₂, c₃}`. -/
def projBulk23 : Mat4 K :=
  !![0, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0]

/-- Single-Majorana projector onto `{c₂}` cutting right across the inter-site dimer bond `(c₂, c₃)`. -/
def projCut2 : Mat4 K :=
  !![0, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Outer boundary zero-mode defect `diag(-1, 0, 0, -1)` supported purely on `{c₁, c₄}`. -/
def edgeZeroModeDefect : Mat4 K :=
  !![-1, 0, 0,  0;
      0, 0, 0,  0;
      0, 0, 0,  0;
      0, 0, 0, -1]

/-- Explicit non-commutativity witness for `trivChainA` and `kitaevChainA` over `ℤ`. -/
lemma trivChainA_kitaevChainA_noncomm :
    (trivChainA : Mat4 ℤ) * kitaevChainA ≠ kitaevChainA * trivChainA := by
  intro h
  have h02 := congr_fun (congr_fun h 0) 2
  revert h02
  decide

/-- Grading witness `diag(1, -1, 0, 0)` on `Mat4 K`. -/
def mat4Grading12 : Mat4 K :=
  !![1,  0, 0, 0;
     0, -1, 0, 0;
     0,  0, 0, 0;
     0,  0, 0, 0]

/-- Swap witness between indices `0` and `1` on `Mat4 K`. -/
def mat4Swap12 : Mat4 K :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Closed anticommutator witness on `Mat4 K = Matrix (Fin 4) (Fin 4) K`. -/
lemma mat4_grading12_swap12_anticomm :
    (mat4Grading12 : Mat4 K) * mat4Swap12 + mat4Swap12 * mat4Grading12 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat4Grading12, mat4Swap12]

/--
**Theorem 5a (𝔎𝔏₉–𝔎𝔏₁₀ — Open 4-Majorana Kitaev Chain Boundary Zero Modes & Square-First Collar Healing):**
Over any commutative ring `K`:
1. **Trivial Chain is Globally Gapped:**
   `- ((trivChainA : Mat4 K) * trivChainA) - I4 = 0`.
2. **Open Topological Kitaev Chain Fails Global Gap on Outer Boundary Zero Modes `{c₁, c₄}`:**
   `- ((kitaevChainA : Mat4 K) * kitaevChainA) - I4 = edgeZeroModeDefect`.
3. **Square-First Local Bulk Gap Vanishes on the Full Bulk Dimer `{c₂, c₃}`:**
   `projBulk23 * projBulk23 = projBulk23`,
   `projBulk23 * (- (kitaevChainA * kitaevChainA) - I4) * projBulk23 = 0`, and
   `SquareFirstBulkOp (projBulk23 : Mat4 K) kitaevChainA 1 = 0`.
4. **Truncate-First Across the Inter-Site Cut (`projCut2`) Severs the Dimer Bond:**
   `projCut2 * projCut2 = projCut2`, `projCut2 * kitaevChainA * projCut2 = 0`, and
   `TruncateFirstBulkOp (projCut2 : Mat4 K) kitaevChainA 1 = -projCut2`.
5. **2-Hop Collar Excursion Restores the Severed Inter-Site Bond:**
   `N_plus (projCut2 : Mat4 K) kitaevChainA * N_minus projCut2 kitaevChainA = -projCut2`.
6. **Square-First Across the Cut Heals the Bond While Filtering Outer Edge Modes:**
   `projCut2 * (- (kitaevChainA * kitaevChainA) - I4) * projCut2 = 0` and
   `SquareFirstBulkOp (projCut2 : Mat4 K) kitaevChainA 1 = 0`.
-/
theorem open_kitaev_majorana_chain_square_first_healing :
    - ((trivChainA : Mat4 K) * trivChainA) - I4 = 0 ∧
    - ((kitaevChainA : Mat4 K) * kitaevChainA) - I4 = edgeZeroModeDefect ∧
    ((projBulk23 : Mat4 K) * projBulk23 = projBulk23 ∧
     (projBulk23 : Mat4 K) * (- (kitaevChainA * kitaevChainA) - I4) * projBulk23 = 0 ∧
     SquareFirstBulkOp (projBulk23 : Mat4 K) kitaevChainA 1 = 0) ∧
    ((projCut2 : Mat4 K) * projCut2 = projCut2 ∧
     (projCut2 : Mat4 K) * kitaevChainA * projCut2 = 0 ∧
     TruncateFirstBulkOp (projCut2 : Mat4 K) kitaevChainA 1 = -projCut2) ∧
    N_plus (projCut2 : Mat4 K) kitaevChainA * N_minus projCut2 kitaevChainA = -projCut2 ∧
    ((projCut2 : Mat4 K) * (- (kitaevChainA * kitaevChainA) - I4) * projCut2 = 0 ∧
     SquareFirstBulkOp (projCut2 : Mat4 K) kitaevChainA 1 = 0) := by
  have hTriv : - ((trivChainA : Mat4 K) * trivChainA) - I4 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [trivChainA, I4]
  have hKit : - ((kitaevChainA : Mat4 K) * kitaevChainA) - I4 = edgeZeroModeDefect := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kitaevChainA, I4, edgeZeroModeDefect]
  have hBulkIdem : (projBulk23 : Mat4 K) * projBulk23 = projBulk23 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projBulk23, Matrix.mul_apply, Fin.sum_univ_four]
  have hBulkMat :
      (projBulk23 : Mat4 K) * (- (kitaevChainA * kitaevChainA) - I4) * projBulk23 = 0 := by
    rw [hKit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projBulk23, edgeZeroModeDefect, Matrix.mul_apply, Fin.sum_univ_four]
  have hBulkSq : SquareFirstBulkOp (projBulk23 : Mat4 K) kitaevChainA 1 = 0 := by
    dsimp [SquareFirstBulkOp]
    rw [← I4_eq_one]
    exact hBulkMat
  have hCutIdem : (projCut2 : Mat4 K) * projCut2 = projCut2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projCut2, Matrix.mul_apply, Fin.sum_univ_four]
  have hCutPAP : (projCut2 : Mat4 K) * kitaevChainA * projCut2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projCut2, kitaevChainA, Matrix.mul_apply, Fin.sum_univ_four]
  have hCutTrunc : TruncateFirstBulkOp (projCut2 : Mat4 K) kitaevChainA 1 = -projCut2 := by
    dsimp [TruncateFirstBulkOp]
    rw [hCutPAP, zero_mul, neg_zero, zero_sub, mul_one, hCutIdem]
  have hCutMat :
      (projCut2 : Mat4 K) * (- (kitaevChainA * kitaevChainA) - I4) * projCut2 = 0 := by
    rw [hKit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projCut2, edgeZeroModeDefect, Matrix.mul_apply, Fin.sum_univ_four]
  have hCutSq : SquareFirstBulkOp (projCut2 : Mat4 K) kitaevChainA 1 = 0 := by
    dsimp [SquareFirstBulkOp]
    rw [← I4_eq_one]
    exact hCutMat
  have hCollar :
      N_plus (projCut2 : Mat4 K) kitaevChainA * N_minus projCut2 kitaevChainA = -projCut2 := by
    have hHeal := (square_first_local_bulk_gap_collar_healing
      (projCut2 : Mat4 K) kitaevChainA 1 hCutIdem).1
    rw [hCutSq, hCutTrunc, zero_sub, neg_inj] at hHeal
    exact hHeal.symm
  exact ⟨hTriv, hKit, ⟨hBulkIdem, hBulkMat, hBulkSq⟩,
    ⟨hCutIdem, hCutPAP, hCutTrunc⟩, hCollar, ⟨hCutMat, hCutSq⟩⟩

end Mat4

/--
**Theorem 5 (𝔎𝔏₁–𝔎𝔏₁₁ — Master 11-Stage Kitaev Local-Gap, 4-Majorana Collar Healing & Invertibility Synthesis):**
Combines all 11 stages ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_{11}$) in a single theorem:
1. Acyclicity of `KitaevLocalGapStage.coverEdge`,
2. Affine ground-state fiber invariance `((1 - t) * H₀ + t * H₁) * P₀ = 0` (`𝔎𝔏₁`) and
   midpoint annulus centering `(b_sq - a_sq)² - (2 * Q - (a_sq + b_sq))² = 4 * (Q - a_sq) * (b_sq - Q)` (`𝔎𝔏₂`),
3. Square-first vs. truncate-first Peirce collar identity
   `SquareFirstBulkOp P A μ₀ - TruncateFirstBulkOp P A μ₀ = - (N_plus P A * N_minus P A)` (`𝔎𝔏₃`),
4. Universal $2 \times 2$ anticommutators (`{doubledSys A, baseDecoupler} = 0` and
   `{diagSys A, baseDecoupler} = 0`), division-free Hadamard similarity
   `hadamard2 * diagSys A * hadamard2 = doubledSys (A + A)`, rotor squares (`RotorXY` and `DirectRotor`),
   unit-gap homotopy preservation, pole endpoints, and dimer cancellation (`𝔎𝔏₄–𝔎𝔏₈`),
5. Concrete 4-Majorana open Kitaev chain boundary zero-mode defect, truncate-first bond severance,
   2-hop collar excursion, square-first healing, and 8-fold Brown–Gauss matrix powers (`𝔎𝔏₉–𝔎𝔏₁₁`).
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
       Block2.baseDecoupler * Block2.doubledSys A = 0 ∧
     Block2.diagSys A * Block2.baseDecoupler +
       Block2.baseDecoupler * Block2.diagSys A = 0 ∧
     Block2.hadamard2 * Block2.diagSys A * Block2.hadamard2 = Block2.doubledSys (A + A) ∧
     Block2.RotorXY A c s * Block2.RotorXY A c s =
       Block2.mk2 (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s) ∧
     Block2.DirectRotor A c s * Block2.DirectRotor A c s =
       Block2.mk2 (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s) ∧
     (A * A = -1 → c * c + s * s = 1 →
       Block2.RotorXY A c s * Block2.RotorXY A c s = Block2.mk2 (-1) 0 0 (-1)) ∧
     Block2.RotorXY A 0 1 + Block2.RotorXY A 0 (-1) = (0 : Block2 B) ∧
     (A - A0) + (A0 - A0) + (A0 - A0) = A - A0) ∧
    (- ((Mat4.kitaevChainA : Mat4 K) * Mat4.kitaevChainA) - Mat4.I4 =
       Mat4.edgeZeroModeDefect ∧
     TruncateFirstBulkOp (Mat4.projCut2 : Mat4 K) Mat4.kitaevChainA 1 = -Mat4.projCut2 ∧
     N_plus (Mat4.projCut2 : Mat4 K) Mat4.kitaevChainA *
       N_minus Mat4.projCut2 Mat4.kitaevChainA = -Mat4.projCut2 ∧
     SquareFirstBulkOp (Mat4.projCut2 : Mat4 K) Mat4.kitaevChainA 1 = 0 ∧
     (((Block2.brownGaussU : Block2 B) * Block2.brownGaussU) *
        (Block2.brownGaussU * Block2.brownGaussU)) *
       (((Block2.brownGaussU : Block2 B) * Block2.brownGaussU) *
        (Block2.brownGaussU * Block2.brownGaussU)) =
       (16 : B) • (1 : Block2 B)) := by
  have hFib := convex_hamiltonian_fiber_ground_state_invariance H0 H1 P0 t h0 h1
  have hAnn := energy_gap_annulus_midpoint_centering Q a_sq b_sq
  have hGap := square_first_local_bulk_gap_collar_healing P A μ0 hP
  have hCones := n_plus_minus_eq_centralizer_cones P A
  have hInv := Block2.universal_invertibility_anticommuting_homotopy A A0 c s hc hs hcs
  have hUnrot := Block2.universal_unrotated_and_hadamard_invertibility_rotor A c s hc hs hcs
  have hUnit := Block2.unit_gap_rotor_preservation_and_pole_endpoints A c s hc hs hcs
  have hMaj := Mat4.open_kitaev_majorana_chain_square_first_healing (K := K)
  have hBrown := Block2.brown_gauss_matrix_power_identities (B := B)
  exact ⟨KitaevLocalGapStage.coverEdge_acyclic,
    ⟨hFib, hAnn⟩,
    ⟨hGap.1, hCones.1, hCones.2.1⟩,
    ⟨hInv.1, hUnrot.2.1, hUnrot.2.2.1.1, hInv.2.1, hUnrot.2.2.2.2,
     hUnit.1, hUnit.2.2.2.2.2.1, hInv.2.2⟩,
    ⟨hMaj.2.1, hMaj.2.2.2.1.2.2, hMaj.2.2.2.2.1, hMaj.2.2.2.2.2.2, hBrown.2.2.2⟩⟩

end KitaevLocalGapOmegaSpectrumPoset
