/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential
import InfoGeometry.Canonical.PfaffianFour

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
- `ims_single_double_commutator_identity`,
  `ims_partition_of_unity_and_active_patch_double_commutator_sum`
- `Block2`, `Block2.mk2`, `Block2.doubledSys_baseDecoupler_noncomm`,
  `Block2.doubledSysOne_baseDecoupler_anticomm`,
  `Block2.universal_invertibility_anticommuting_homotopy`,
  `Block2.unit_gap_rotor_preservation_and_pole_endpoints`,
  `Block2.universal_unrotated_and_hadamard_invertibility_rotor`,
  `Block2.brown_gauss_matrix_power_identities`
- `Mat4`, `Mat4.trivChainA_kitaevChainA_noncomm`, `Mat4.mat4_grading12_swap12_anticomm`,
  `Mat4.open_kitaev_majorana_chain_square_first_healing`,
  `Mat4.bdi_parameterized_majorana_pfaffian_and_phase_sign_flip`,
  `Mat4.bdi_chiral_zero_mode_index_and_mod8_fidkowski_kitaev_reduction`,
  `Mat4.d3_dirac_clifford_mass_circle_and_kramers_trs_z2_blocking`,
  `Mat4.twistor_plucker_klein_quadric_and_kitaev_mass_gap_regulator`,
  `Mat4.z4_parafermion_binary_carry_clock_shift_weyl_algebra`
- `z4_ring_binary_carry_and_peirce_tetraktys_weyl_algebra`,
  `z4_peirce_braid_brown_gauss_and_nilpotent_unipotent_gate`
- `kl7_master_kitaev_local_gap_omega_spectrum_synthesis`

## iii. Table of contents

- Section 0: The 11-Stage Kitaev Local-Gap Poset (`𝔎𝔏₁ ≺ ⋯ ≺ 𝔎𝔏₁₁`)
- Section 1 (`𝔎𝔏₁–𝔎𝔏₂`): Affine Ground-State Fiber Invariance & Spectral Annulus Centering
- Section 2 (`𝔎𝔏₃`): Square-First Local Bulk Gap, Collar Excursion & Active-Patch IMS Double-Commutator Sum
- Section 3 (`𝔎𝔏₄–𝔎𝔏₈` & `𝔎𝔏₁₁`): Universal $2 \times 2$ Anticommuting Rotors, Hadamard Similarity & Brown–Gauss Matrix Powers
- Section 4 (`𝔎𝔏₉–𝔎𝔏₁₀`): Concrete $4$-Majorana Open Kitaev Chain, Parameterized Pfaffian Sign Flip, BDI Chiral Stack Index, 3D Kramers TRS Blocking, Twistor Plücker–Klein Quadric & `ℤ₄` Parafermion Binary-Carry / Peirce Braid Laws

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `KitaevLocalGapStage` ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_{11}$), `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`,
  - `convex_hamiltonian_fiber_ground_state_invariance`, `energy_gap_annulus_midpoint_centering`,
  - `n_plus_minus_eq_centralizer_cones`, `square_first_local_bulk_gap_collar_healing`,
  - `ims_single_double_commutator_identity`, `ims_partition_of_unity_and_active_patch_double_commutator_sum`,
  - `Block2.doubledSys_baseDecoupler_noncomm`, `Block2.doubledSysOne_baseDecoupler_anticomm`, `Block2.universal_invertibility_anticommuting_homotopy`, `Block2.unit_gap_rotor_preservation_and_pole_endpoints`, `Block2.universal_unrotated_and_hadamard_invertibility_rotor`, `Block2.brown_gauss_matrix_power_identities`,
  - `Mat4.trivChainA_kitaevChainA_noncomm`, `Mat4.mat4_grading12_swap12_anticomm`, `Mat4.open_kitaev_majorana_chain_square_first_healing`,
  - `Mat4.bdi_parameterized_majorana_pfaffian_and_phase_sign_flip`, `Mat4.bdi_chiral_zero_mode_index_and_mod8_fidkowski_kitaev_reduction`,
  - `Mat4.d3_dirac_clifford_mass_circle_and_kramers_trs_z2_blocking`, `Mat4.twistor_plucker_klein_quadric_and_kitaev_mass_gap_regulator`, `Mat4.z4_parafermion_binary_carry_clock_shift_weyl_algebra`,
  - `z4_ring_binary_carry_and_peirce_tetraktys_weyl_algebra`, `z4_peirce_braid_brown_gauss_and_nilpotent_unipotent_gate`, `kl7_master_kitaev_local_gap_omega_spectrum_synthesis`.
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

/-- **Single-Weight Noncommutative IMS Double-Commutator Identity:**
In any associative ring `[Ring B]`, for any weight `χ : B` and operator `M : B`:
$$\chi * \chi * M + M * (\chi * \chi) - (2 : \mathbb{Z}) \bullet (\chi * M * \chi) =
  \mathrm{comm}\;\chi\;(\mathrm{comm}\;\chi\;M).$$ -/
lemma ims_single_double_commutator_identity (χ M : B) :
    χ * χ * M + M * (χ * χ) - (2 : ℤ) • (χ * M * χ) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm χ
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm χ M) := by
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  rw [two_zsmul]
  noncomm_ring

/-- **Global Partition-of-Unity & Active-Patch IMS Double-Commutator Sum:**
For any finite index type `ι` (`[Fintype ι]`), weight family `χ : ι → B`, and operator `M : B`
with quadratic partition of unity `(∑ b : ι, χ b * χ b) = 1`, and any active patch subset
`active : Finset ι` outside which the double commutators vanish:
1. `(2 : ℤ) • M - (2 : ℤ) • (∑ b : ι, χ b * M * χ b) = ∑ b : ι, comm (χ b) (comm (χ b) M)`,
2. `(2 : ℤ) • M - (2 : ℤ) • (∑ b : ι, χ b * M * χ b) = ∑ b ∈ active, comm (χ b) (comm (χ b) M)`. -/
theorem ims_partition_of_unity_and_active_patch_double_commutator_sum
    {ι : Type*} [Fintype ι]
    (χ : ι → B) (M : B) (hPart : (∑ b : ι, χ b * χ b) = 1)
    (active : Finset ι)
    (hZeroOffActive : ∀ b : ι, b ∉ active →
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M) = 0) :
    ((2 : ℤ) • M - (2 : ℤ) • (∑ b : ι, χ b * M * χ b) =
      ∑ b : ι, InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)) ∧
    ((2 : ℤ) • M - (2 : ℤ) • (∑ b : ι, χ b * M * χ b) =
      ∑ b ∈ active, InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)) := by
  have hSum :
      (2 : ℤ) • M - (2 : ℤ) • (∑ b : ι, χ b * M * χ b) =
        ∑ b : ι, InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M) := by
    have hPointwise :
        (∑ b : ι, InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)) =
          ∑ b : ι, (χ b * χ b * M + M * (χ b * χ b) - (2 : ℤ) • (χ b * M * χ b)) := by
      refine Finset.sum_congr rfl ?_
      intro b _
      exact (ims_single_double_commutator_identity (χ b) M).symm
    rw [hPointwise, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hPart, one_mul, mul_one,
      ← two_zsmul M, ← Finset.smul_sum]
  have hActive :
      (∑ b ∈ active, InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)) =
      ∑ b : ι, InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M) := by
    refine Finset.sum_subset (Finset.subset_univ active) ?_
    intro b _ hbNot
    exact hZeroOffActive b hbNot
  exact ⟨hSum, hSum.trans hActive.symm⟩

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

/-- Primal $e$-flat Plabic unipotent shear `ℰ_+(t) = I + t N_+ = [[1, t], [0, 1]]` in `Block2 B`. -/
def shearPlus (t : B) : Block2 B :=
  mk2 1 t 0 1

/-- Dual $m$-flat Plabic unipotent shear `ℰ_-(s) = I + s N_- = [[1, 0], [s, 1]]` in `Block2 B`. -/
def shearMinus (s : B) : Block2 B :=
  mk2 1 0 s 1

/-- Paired Amari–DeWitt Gaussian `𝒢_+(t, s) = ℰ_+(t) ℰ_-(s) = [[1 + t s, t], [s, 1]]` in `Block2 B`. -/
def gaussianTP2 (t s : B) : Block2 B :=
  mk2 (1 + t * s) t s 1

/-- Unnormalized Positive Grassmannian Projector `P̃_+(t, s) = [[1, t], [s, t s]]` in `Block2 B`. -/
def posGrassProj (t s : B) : Block2 B :=
  mk2 1 t s (t * s)

/-- $2 \times 2$ determinant `det₂(M) = M₀₀ M₁₁ - M₀₁ M₁₀` for `M : Block2 K` over `[CommRing K]`. -/
def det2 {K : Type u} [CommRing K] (M : Block2 K) : K :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

/--
**Theorem 3f (`positive_grassmannian_gaussian_tp2_and_homogeneous_projector`):**
Total Positivity ($\mathrm{TP}_2$) of the paired DeWitt–Amari Gaussian `gaussianTP2 t s` and
trace-normalized idempotency of the positive Grassmannian projector `posGrassProj t s`:
1. **Universal Algebraic Factorization & Unit Determinant (`[CommRing K]`):**
   - `shearPlus tK * shearMinus sK = gaussianTP2 tK sK`,
   - `det2 (gaussianTP2 tK sK) = 1`,
   - `posGrassProj tK sK * posGrassProj tK sK = (1 + tK * sK) • posGrassProj tK sK`.
2. **Strict Total Positivity Over `ℤ` (`0 < t ∧ 0 < s`):**
   Whenever `0 < t` and `0 < s`, all four $1 \times 1$ minors and the $2 \times 2$ determinant of
   `gaussianTP2 t s` are strictly positive (`> 0`), and all four entries of `posGrassProj t s` are
   strictly positive (`> 0`).
-/
theorem positive_grassmannian_gaussian_tp2_and_homogeneous_projector
    {K : Type u} [CommRing K] (tK sK : K) (t s : ℤ) (ht : 0 < t) (hs : 0 < s) :
    shearPlus tK * shearMinus sK = gaussianTP2 tK sK ∧
    det2 (gaussianTP2 tK sK) = 1 ∧
    posGrassProj tK sK * posGrassProj tK sK = (1 + tK * sK) • posGrassProj tK sK ∧
    0 < gaussianTP2 t s 0 0 ∧
    0 < gaussianTP2 t s 0 1 ∧
    0 < gaussianTP2 t s 1 0 ∧
    0 < gaussianTP2 t s 1 1 ∧
    0 < det2 (gaussianTP2 t s) ∧
    0 < posGrassProj t s 1 1 := by
  have hts : 0 < t * s := Int.mul_pos ht hs
  have hFact : shearPlus tK * shearMinus sK = gaussianTP2 tK sK := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shearPlus, shearMinus, gaussianTP2, mk2, Matrix.mul_apply, Fin.sum_univ_two]
  have hDet : det2 (gaussianTP2 tK sK) = 1 := by
    simp [det2, gaussianTP2, mk2]
  have hProj : posGrassProj tK sK * posGrassProj tK sK = (1 + tK * sK) • posGrassProj tK sK := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [posGrassProj, mk2, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;>
      ring
  have hG00 : 0 < gaussianTP2 t s 0 0 := by simp [gaussianTP2, mk2]; omega
  have hG01 : 0 < gaussianTP2 t s 0 1 := by simpa [gaussianTP2, mk2] using ht
  have hG10 : 0 < gaussianTP2 t s 1 0 := by simpa [gaussianTP2, mk2] using hs
  have hG11 : 0 < gaussianTP2 t s 1 1 := by simp [gaussianTP2, mk2]
  have hGDet : 0 < det2 (gaussianTP2 t s) := by simp [det2, gaussianTP2, mk2]
  have hP11 : 0 < posGrassProj t s 1 1 := by simpa [posGrassProj, mk2] using hts
  exact ⟨hFact, hDet, hProj, hG00, hG01, hG10, hG11, hGDet, hP11⟩

/-- Conformal Peirce corner idempotent `P_conf = [[1, 0], [0, 0]]` in `Block2 B`. -/
def cornerIdem : Block2 B :=
  mk2 1 0 0 0

/-- Upper-right Peirce corner embedding `[[0, X], [0, 0]]` in `Block2 B`. -/
def cornerEmbed (X : B) : Block2 B :=
  mk2 0 X 0 0

/-- Diagonal stabilizer embedding `[[M, 0], [0, M]]` in `Block2 B` preserving the Peirce corner. -/
def lorentzDiag (M : B) : Block2 B :=
  mk2 M 0 0 M

/--
**Theorem 3f' (`peirce_corner_embed_and_diagonal_lorentz_action`):**
In `Block2 B` over any `[Ring B]`, the upper-right Peirce corner `cornerEmbed X = [[0, X], [0, 0]]`
determined by `cornerIdem = [[1, 0], [0, 0]]` is an Abelian nilpotent module preserved by the
diagonal stabilizer action `lorentzDiag M = [[M, 0], [0, M]]`:
1. `cornerIdem * cornerIdem = cornerIdem`,
2. `N_plus cornerIdem (cornerEmbed X) = cornerEmbed X`,
3. `cornerEmbed (X + Y) = cornerEmbed X + cornerEmbed Y` and `cornerEmbed X * cornerEmbed Y = 0`,
4. `lorentzDiag M * cornerEmbed X - cornerEmbed X * lorentzDiag M = cornerEmbed (M * X - X * M)`.
-/
theorem peirce_corner_embed_and_diagonal_lorentz_action (M X Y : B) :
    (cornerIdem : Block2 B) * cornerIdem = cornerIdem ∧
    N_plus (cornerIdem : Block2 B) (cornerEmbed X) = cornerEmbed X ∧
    cornerEmbed (X + Y) = cornerEmbed X + cornerEmbed Y ∧
    cornerEmbed X * cornerEmbed Y = 0 ∧
    lorentzDiag M * cornerEmbed X - cornerEmbed X * lorentzDiag M =
      cornerEmbed (M * X - X * M) := by
  have hIdem : (cornerIdem : Block2 B) * cornerIdem = cornerIdem := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerIdem, mk2, Matrix.mul_apply, Fin.sum_univ_two]
  have hCorner : N_plus (cornerIdem : Block2 B) (cornerEmbed X) = cornerEmbed X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [N_plus, cornerIdem, cornerEmbed, mk2, Matrix.mul_apply, Fin.sum_univ_two]
  have hAdd : cornerEmbed (X + Y) = cornerEmbed X + cornerEmbed Y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerEmbed, mk2]
  have hMul : cornerEmbed X * cornerEmbed Y = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerEmbed, mk2, Matrix.mul_apply, Fin.sum_univ_two]
  have hAct :
      lorentzDiag M * cornerEmbed X - cornerEmbed X * lorentzDiag M =
        cornerEmbed (M * X - X * M) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lorentzDiag, cornerEmbed, mk2]
  exact ⟨hIdem, hCorner, hAdd, hMul, hAct⟩

/-- Rank-1 real Majorana-twistor momentum matrix `P(λ) = λ λᵀ = [[λ₁², λ₁ λ₂], [λ₂ λ₁, λ₂²]]`
in `Block2 B`. -/
def twistorMomentum2 (lam1 lam2 : B) : Block2 B :=
  mk2 (lam1 * lam1) (lam1 * lam2) (lam2 * lam1) (lam2 * lam2)

/--
**Theorem 3g (`real_twistor_susy_null_and_massive_momentum_factorization`):**
Real Penrose–Witten twistor factorization of massless null and massive 4-momenta (`𝔖𝔓₅–𝔖𝔓₇`):
1. **1-Twistor Massless Light-Cone Identity (`P = λ λᵀ`):**
   For any `lam1, lam2 : K`, `det2 (twistorMomentum2 lam1 lam2) = 0` and the DeWitt components
   `2 p₀ = lam1² + lam2²`, `2 p₁ = lam1² - lam2²`, `2 p₂ = 2 lam1 lam2` satisfy the exact light-cone law
   `(lam1 ^ 2 + lam2 ^ 2) ^ 2 - (lam1 ^ 2 - lam2 ^ 2) ^ 2 - (2 * lam1 * lam2) ^ 2 = 0`.
2. **2-Twistor Massive Casimir Identity (`P = λ λᵀ + μ μᵀ`):**
   Summing two real twistors `λ = (lam1, lam2)` and `μ = (mu1, mu2)` yields the invariant mass squared
   as the square of the symplectic 2-bracket `⟨λ μ⟩ = lam1 * mu2 - lam2 * mu1`:
   `det2 (twistorMomentum2 lam1 lam2 + twistorMomentum2 mu1 mu2) = (lam1 * mu2 - lam2 * mu1) ^ 2` and
   `(lam1 ^ 2 + mu1 ^ 2) * (lam2 ^ 2 + mu2 ^ 2) - (lam1 * lam2 + mu1 * mu2) ^ 2 = (lam1 * mu2 - lam2 * mu1) ^ 2`.
3. **Witten Positive Energy (`2 p₀ ≥ 0`) & Nonnegative Mass Squared (`m² ≥ 0`) Over `ℤ`:**
   For any `l₁, l₂, m₁, m₂ : ℤ`, `0 ≤ l₁ ^ 2 + l₂ ^ 2` and
   `0 ≤ det2 (twistorMomentum2 l₁ l₂ + twistorMomentum2 m₁ m₂)`.
-/
theorem real_twistor_susy_null_and_massive_momentum_factorization
    {K : Type u} [CommRing K] (lam1 lam2 mu1 mu2 : K) (l1 l2 m1 m2 : ℤ) :
    (det2 (twistorMomentum2 lam1 lam2) = 0 ∧
     (lam1 ^ 2 + lam2 ^ 2) ^ 2 - (lam1 ^ 2 - lam2 ^ 2) ^ 2 - (2 * lam1 * lam2) ^ 2 = 0) ∧
    (det2 (twistorMomentum2 lam1 lam2 + twistorMomentum2 mu1 mu2) =
       (lam1 * mu2 - lam2 * mu1) ^ 2 ∧
     (lam1 ^ 2 + mu1 ^ 2) * (lam2 ^ 2 + mu2 ^ 2) - (lam1 * lam2 + mu1 * mu2) ^ 2 =
       (lam1 * mu2 - lam2 * mu1) ^ 2) ∧
    (0 ≤ l1 ^ 2 + l2 ^ 2 ∧
     0 ≤ det2 (twistorMomentum2 l1 l2 + twistorMomentum2 m1 m2)) := by
  have hNullDet : det2 (twistorMomentum2 lam1 lam2) = 0 := by
    change (lam1 * lam1) * (lam2 * lam2) - (lam1 * lam2) * (lam2 * lam1) = 0
    ring
  have hNullCone :
      (lam1 ^ 2 + lam2 ^ 2) ^ 2 - (lam1 ^ 2 - lam2 ^ 2) ^ 2 - (2 * lam1 * lam2) ^ 2 = 0 := by
    ring
  have hMassDet :
      det2 (twistorMomentum2 lam1 lam2 + twistorMomentum2 mu1 mu2) =
        (lam1 * mu2 - lam2 * mu1) ^ 2 := by
    change ((lam1 * lam1 + mu1 * mu1) * (lam2 * lam2 + mu2 * mu2) -
      (lam1 * lam2 + mu1 * mu2) * (lam2 * lam1 + mu2 * mu1)) =
      (lam1 * mu2 - lam2 * mu1) ^ 2
    ring
  have hMassPoly :
      (lam1 ^ 2 + mu1 ^ 2) * (lam2 ^ 2 + mu2 ^ 2) - (lam1 * lam2 + mu1 * mu2) ^ 2 =
        (lam1 * mu2 - lam2 * mu1) ^ 2 := by
    ring
  have hPosE : 0 ≤ l1 ^ 2 + l2 ^ 2 := add_nonneg (sq_nonneg l1) (sq_nonneg l2)
  have hMassDetZ :
      det2 (twistorMomentum2 l1 l2 + twistorMomentum2 m1 m2) = (l1 * m2 - l2 * m1) ^ 2 := by
    change ((l1 * l1 + m1 * m1) * (l2 * l2 + m2 * m2) -
      (l1 * l2 + m1 * m2) * (l2 * l1 + m2 * m1)) =
      (l1 * m2 - l2 * m1) ^ 2
    ring
  have hPosMass : 0 ≤ det2 (twistorMomentum2 l1 l2 + twistorMomentum2 m1 m2) := by
    rw [hMassDetZ]
    exact sq_nonneg (l1 * m2 - l2 * m1)
  exact ⟨⟨hNullDet, hNullCone⟩, ⟨hMassDet, hMassPoly⟩, ⟨hPosE, hPosMass⟩⟩

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

/-- Division-free 3-parameter $4 \times 4$ Majorana matrix `A₄(μ, t₊, t₋)` in `Mat4 K`,
where `μ` is the intra-site pairing `(c₁, c₂)` and `(c₃, c₄)`, `t₊ = t + Δ` is the inter-site
dimer bond `(c₂, c₃)`, and `t₋ = t - Δ` is the complementary bond `(c₁, c₄)`. -/
def majoranaParamA (μ tPlus tMinus : K) : Mat4 K :=
  !![ 0,       μ,      0, tMinus;
     -μ,       0,  tPlus,      0;
      0,  -tPlus,      0,      μ;
  -tMinus,     0,     -μ,      0]

/-- Closed (antiperiodic) topological sweet-spot 4-Majorana chain `majoranaParamA 0 1 (-1)`,
coupling `(c₂, c₃)` with `+1` and `(c₁, c₄)` with `-1`. -/
def closedTopChainA : Mat4 K :=
  !![0,  0,  0, -1;
     0,  0,  1,  0;
     0, -1,  0,  0;
     1,  0,  0,  0]

/-- Sublattice-swapped open 2-site Kitaev chain `majoranaParamA 0 0 1`, coupling `(c₁, c₄)`
and leaving `(c₂, c₃)` as unpaired zero modes. -/
def kitaevChainSublatticeSwapA : Mat4 K :=
  !![ 0, 0, 0, 1;
      0, 0, 0, 0;
      0, 0, 0, 0;
     -1, 0, 0, 0]

/-- Canonical BDI chiral sublattice grading `Γ_BDI = diag(1, -1, 1, -1)` on `Mat4 K`. -/
def bdiChiralGamma : Mat4 K :=
  !![1,  0, 0,  0;
     0, -1, 0,  0;
     0,  0, 1,  0;
     0,  0, 0, -1]

/-- Left-unit-cell projector `diag(1, 1, 0, 0)` onto `{c₁, c₂}` on `Mat4 K`. -/
def projLeftCell : Mat4 K :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Polynomial $4 \times 4$ Pfaffian `A₀₁ A₂₃ - A₀₂ A₁₃ + A₀₃ A₁₂` on `Mat4 K`. -/
def pfaffianMat4 (A : Mat4 K) : K :=
  A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2

/--
**Theorem 5b (`bdi_parameterized_majorana_pfaffian_and_phase_sign_flip`):**
Over any commutative ring `K`:
1. **Endpoint Specializations:**
   `majoranaParamA 1 0 0 = trivChainA`, `majoranaParamA 0 1 0 = kitaevChainA`,
   `majoranaParamA 0 1 (-1) = closedTopChainA`, and
   `majoranaParamA 0 0 1 = kitaevChainSublatticeSwapA`.
2. **Universal Skew-Symmetry & BDI Chiral Anticommutation:**
   `(majoranaParamA μ tPlus tMinus).transpose = -majoranaParamA μ tPlus tMinus`,
   `bdiChiralGamma * bdiChiralGamma = I4`, and
   `bdiChiralGamma * majoranaParamA μ tPlus tMinus + majoranaParamA μ tPlus tMinus * bdiChiralGamma = 0`.
3. **Canonical `Pfaffian.skew4` Bridge & Determinant–Pfaffian Square Law:**
   `majoranaParamA μ tPlus tMinus = InfoGeometry.Canonical.Pfaffian.skew4 μ 0 tMinus tPlus 0 μ`,
   `pfaffianMat4 (majoranaParamA μ tPlus tMinus) = μ ^ 2 + tPlus * tMinus`, and
   `(majoranaParamA μ tPlus tMinus).det = (pfaffianMat4 (majoranaParamA μ tPlus tMinus)) ^ 2`.
4. **Trivial vs. Closed Topological vs. Open Topological Pfaffian Sign Dichotomy:**
   - `pfaffianMat4 trivChainA = 1` and `- (trivChainA * trivChainA) - I4 = 0`,
   - `pfaffianMat4 closedTopChainA = -1` and `- (closedTopChainA * closedTopChainA) - I4 = 0`,
   - `pfaffianMat4 kitaevChainA = 0` and `pfaffianMat4 kitaevChainSublatticeSwapA = 0`.
-/
theorem bdi_parameterized_majorana_pfaffian_and_phase_sign_flip (μ tPlus tMinus : K) :
    ((majoranaParamA (1 : K) 0 0 : Mat4 K) = trivChainA ∧
     (majoranaParamA (0 : K) 1 0 : Mat4 K) = kitaevChainA ∧
     (majoranaParamA (0 : K) 1 (-1) : Mat4 K) = closedTopChainA ∧
     (majoranaParamA (0 : K) 0 1 : Mat4 K) = kitaevChainSublatticeSwapA) ∧
    ((majoranaParamA μ tPlus tMinus).transpose = -majoranaParamA μ tPlus tMinus ∧
     (bdiChiralGamma : Mat4 K) * bdiChiralGamma = I4 ∧
     bdiChiralGamma * majoranaParamA μ tPlus tMinus +
       majoranaParamA μ tPlus tMinus * bdiChiralGamma = 0) ∧
    (majoranaParamA μ tPlus tMinus =
       InfoGeometry.Canonical.Pfaffian.skew4 μ 0 tMinus tPlus 0 μ ∧
     pfaffianMat4 (majoranaParamA μ tPlus tMinus) = μ ^ 2 + tPlus * tMinus ∧
     (majoranaParamA μ tPlus tMinus).det =
       (pfaffianMat4 (majoranaParamA μ tPlus tMinus)) ^ 2) ∧
    ((pfaffianMat4 (trivChainA : Mat4 K) = 1 ∧
      - ((trivChainA : Mat4 K) * trivChainA) - I4 = 0) ∧
     (pfaffianMat4 (closedTopChainA : Mat4 K) = -1 ∧
      - ((closedTopChainA : Mat4 K) * closedTopChainA) - I4 = 0) ∧
     (pfaffianMat4 (kitaevChainA : Mat4 K) = 0 ∧
      pfaffianMat4 (kitaevChainSublatticeSwapA : Mat4 K) = 0)) := by
  have hSpec1 : (majoranaParamA (1 : K) 0 0 : Mat4 K) = trivChainA := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [majoranaParamA, trivChainA]
  have hSpec2 : (majoranaParamA (0 : K) 1 0 : Mat4 K) = kitaevChainA := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [majoranaParamA, kitaevChainA]
  have hSpec3 : (majoranaParamA (0 : K) 1 (-1) : Mat4 K) = closedTopChainA := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [majoranaParamA, closedTopChainA]
  have hSpec4 : (majoranaParamA (0 : K) 0 1 : Mat4 K) = kitaevChainSublatticeSwapA := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [majoranaParamA, kitaevChainSublatticeSwapA]
  have hSkew : (majoranaParamA μ tPlus tMinus).transpose = -majoranaParamA μ tPlus tMinus := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [majoranaParamA]
  have hGammaSq : (bdiChiralGamma : Mat4 K) * bdiChiralGamma = I4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [bdiChiralGamma, I4]
  have hGammaAnti :
      bdiChiralGamma * majoranaParamA μ tPlus tMinus +
        majoranaParamA μ tPlus tMinus * bdiChiralGamma = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [bdiChiralGamma, majoranaParamA]
  have hSkew4 : majoranaParamA μ tPlus tMinus =
      InfoGeometry.Canonical.Pfaffian.skew4 μ 0 tMinus tPlus 0 μ := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [majoranaParamA, InfoGeometry.Canonical.Pfaffian.skew4]
  have hPf : pfaffianMat4 (majoranaParamA μ tPlus tMinus) = μ ^ 2 + tPlus * tMinus := by
    simp [pfaffianMat4, majoranaParamA]
    ring
  have hPfBridge : pfaffianMat4 (majoranaParamA μ tPlus tMinus) =
      InfoGeometry.Canonical.Pfaffian.pfaffian4 μ 0 tMinus tPlus 0 μ := by
    simp [pfaffianMat4, majoranaParamA, InfoGeometry.Canonical.Pfaffian.pfaffian4]
  have hDet : (majoranaParamA μ tPlus tMinus).det =
      (pfaffianMat4 (majoranaParamA μ tPlus tMinus)) ^ 2 := by
    rw [hPfBridge, hSkew4]
    exact (InfoGeometry.Canonical.Pfaffian.pfaffian4_sq_eq_det μ 0 tMinus tPlus 0 μ).symm
  have hTrivPf : pfaffianMat4 (trivChainA : Mat4 K) = 1 := by
    simp [pfaffianMat4, trivChainA]
  have hTrivGap : - ((trivChainA : Mat4 K) * trivChainA) - I4 = 0 :=
    (open_kitaev_majorana_chain_square_first_healing (K := K)).1
  have hClosedPf : pfaffianMat4 (closedTopChainA : Mat4 K) = -1 := by
    simp [pfaffianMat4, closedTopChainA]
  have hClosedGap : - ((closedTopChainA : Mat4 K) * closedTopChainA) - I4 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [closedTopChainA, I4]
  have hKitPf : pfaffianMat4 (kitaevChainA : Mat4 K) = 0 := by
    simp [pfaffianMat4, kitaevChainA]
  have hSwapPf : pfaffianMat4 (kitaevChainSublatticeSwapA : Mat4 K) = 0 := by
    simp [pfaffianMat4, kitaevChainSublatticeSwapA]
  exact ⟨⟨hSpec1, hSpec2, hSpec3, hSpec4⟩, ⟨hSkew, hGammaSq, hGammaAnti⟩,
    ⟨hSkew4, hPf, hDet⟩, ⟨⟨hTrivPf, hTrivGap⟩, ⟨hClosedPf, hClosedGap⟩, ⟨hKitPf, hSwapPf⟩⟩⟩

/-- Left-unit-cell BDI chiral zero-mode index `Tr(Γ_BDI P_left (I₄ + A²) P_left)` on `Mat4 K`. -/
def bdiLeftZeroModeIndex (A : Mat4 K) : K :=
  Matrix.trace (bdiChiralGamma * projLeftCell * (I4 + A * A) * projLeftCell)

/-- Total two-boundary BDI chiral zero-mode trace `Tr(Γ_BDI (I₄ + A²))` on `Mat4 K`. -/
def bdiTotalZeroModeTrace (A : Mat4 K) : K :=
  Matrix.trace (bdiChiralGamma * (I4 + A * A))

/-- Additive BDI chiral zero-mode index of a finite stack of 4-Majorana chains `List (Mat4 K)`. -/
def bdiStackIndex (stack : List (Mat4 K)) : K :=
  (stack.map bdiLeftZeroModeIndex).sum

/-- Explicit finite stack of 4-Majorana BDI chains realizing any integer `z : ℤ`. -/
def bdiStackOfInt : ℤ → List (Mat4 K)
  | Int.ofNat n => List.replicate n kitaevChainA
  | Int.negSucc n => List.replicate (n + 1) kitaevChainSublatticeSwapA

/-- Left-unit-cell BDI chiral index of `trivChainA` is `0`. -/
lemma bdiLeftZeroModeIndex_trivChainA :
    bdiLeftZeroModeIndex (trivChainA : Mat4 K) = 0 := by
  simp [bdiLeftZeroModeIndex, bdiChiralGamma, projLeftCell, I4, trivChainA,
    Matrix.trace, Fin.sum_univ_four]

/-- Left-unit-cell BDI chiral index of `closedTopChainA` is `0`. -/
lemma bdiLeftZeroModeIndex_closedTopChainA :
    bdiLeftZeroModeIndex (closedTopChainA : Mat4 K) = 0 := by
  simp [bdiLeftZeroModeIndex, bdiChiralGamma, projLeftCell, I4, closedTopChainA,
    Matrix.trace, Fin.sum_univ_four]

/-- Left-unit-cell BDI chiral index of `kitaevChainA` is `+1` (unpaired `c₁` mode). -/
lemma bdiLeftZeroModeIndex_kitaevChainA :
    bdiLeftZeroModeIndex (kitaevChainA : Mat4 K) = 1 := by
  simp [bdiLeftZeroModeIndex, bdiChiralGamma, projLeftCell, I4, kitaevChainA,
    Matrix.trace, Fin.sum_univ_four]

/-- Left-unit-cell BDI chiral index of `kitaevChainSublatticeSwapA` is `-1` (unpaired `c₂` mode). -/
lemma bdiLeftZeroModeIndex_kitaevChainSublatticeSwapA :
    bdiLeftZeroModeIndex (kitaevChainSublatticeSwapA : Mat4 K) = -1 := by
  simp [bdiLeftZeroModeIndex, bdiChiralGamma, projLeftCell, I4, kitaevChainSublatticeSwapA,
    Matrix.trace, Fin.sum_univ_four]

/-- `bdiStackIndex` is additive under stack concatenation. -/
lemma bdiStackIndex_append (s₁ s₂ : List (Mat4 K)) :
    bdiStackIndex (s₁ ++ s₂) = bdiStackIndex s₁ + bdiStackIndex s₂ := by
  simp [bdiStackIndex, List.map_append, List.sum_append]

/-- `bdiStackIndex` on `bdiStackOfInt z` evaluates to `(z : K)` for every `z : ℤ`. -/
lemma bdiStackIndex_bdiStackOfInt (z : ℤ) :
    bdiStackIndex (bdiStackOfInt z : List (Mat4 K)) = (z : K) := by
  cases z with
  | ofNat n =>
    dsimp [bdiStackOfInt, bdiStackIndex]
    simp [bdiLeftZeroModeIndex_kitaevChainA]
  | negSucc n =>
    dsimp [bdiStackOfInt, bdiStackIndex]
    simp [bdiLeftZeroModeIndex_kitaevChainSublatticeSwapA, Int.cast_negSucc]

/-- Fidkowski–Kitaev mod-8 reduction of the BDI stack chiral zero-mode index. -/
def bdiStackIndexMod8 (stack : List (Mat4 ℤ)) : ZMod 8 :=
  Int.castRingHom (ZMod 8) (bdiStackIndex stack)

/-- Class-D mod-2 Majorana parity reduction of the BDI stack chiral zero-mode index. -/
def bdiStackIndexMod2 (stack : List (Mat4 ℤ)) : ZMod 2 :=
  Int.castRingHom (ZMod 2) (bdiStackIndex stack)

/--
**Theorem 5c (`bdi_chiral_zero_mode_index_and_mod8_fidkowski_kitaev_reduction`):**
Constructive Hamiltonian-level BDI chiral zero-mode index and its mod-8 / mod-2 reductions:
1. **Two-Boundary Chiral Cancellation vs. Left-Boundary Quantization:**
   - `bdiTotalZeroModeTrace trivChainA = 0`, `bdiTotalZeroModeTrace kitaevChainA = 0`, and
     `bdiTotalZeroModeTrace kitaevChainSublatticeSwapA = 0` (the `+1` and `-1` edge modes cancel globally),
   - `bdiLeftZeroModeIndex trivChainA = 0`, `bdiLeftZeroModeIndex closedTopChainA = 0`,
     `bdiLeftZeroModeIndex kitaevChainA = 1`, and `bdiLeftZeroModeIndex kitaevChainSublatticeSwapA = -1`.
2. **Additive Stack Homomorphism & Universal Integer Realization (`bdiStackOfInt`):**
   - `bdiStackIndex (s₁ ++ s₂) = bdiStackIndex s₁ + bdiStackIndex s₂`,
   - `bdiStackIndex (bdiStackOfInt z) = (z : K)` for every `z : ℤ`,
   - `Function.Surjective (bdiStackIndex (K := ℤ))`.
3. **Fidkowski–Kitaev Mod-8 Reduction & 8-Chain Periodicity:**
   - `bdiStackIndexMod8 (st₁ ++ st₂) = bdiStackIndexMod8 st₁ + bdiStackIndexMod8 st₂`,
   - `Function.Surjective bdiStackIndexMod8`,
   - `bdiStackIndex (List.replicate 8 (kitaevChainA : Mat4 ℤ)) = 8` while
     `bdiStackIndexMod8 (List.replicate 8 (kitaevChainA : Mat4 ℤ)) = 0`,
   - `bdiStackIndexMod8 (bdiStackOfInt z) = 0 ↔ (8 : ℤ) ∣ z`.
4. **Class-D Parity Factorization (`ℤ → ZMod 8 → ZMod 2`):**
   - `ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) (bdiStackIndexMod8 st₁) = bdiStackIndexMod2 st₁`.
-/
theorem bdi_chiral_zero_mode_index_and_mod8_fidkowski_kitaev_reduction
    (s₁ s₂ : List (Mat4 K)) (st₁ st₂ : List (Mat4 ℤ)) (z : ℤ) :
    ((bdiTotalZeroModeTrace (trivChainA : Mat4 K) = 0 ∧
      bdiTotalZeroModeTrace (kitaevChainA : Mat4 K) = 0 ∧
      bdiTotalZeroModeTrace (kitaevChainSublatticeSwapA : Mat4 K) = 0) ∧
     (bdiLeftZeroModeIndex (trivChainA : Mat4 K) = 0 ∧
      bdiLeftZeroModeIndex (closedTopChainA : Mat4 K) = 0 ∧
      bdiLeftZeroModeIndex (kitaevChainA : Mat4 K) = 1 ∧
      bdiLeftZeroModeIndex (kitaevChainSublatticeSwapA : Mat4 K) = -1)) ∧
    (bdiStackIndex (s₁ ++ s₂) = bdiStackIndex s₁ + bdiStackIndex s₂ ∧
     bdiStackIndex (bdiStackOfInt z : List (Mat4 K)) = (z : K) ∧
     Function.Surjective (bdiStackIndex (K := ℤ))) ∧
    (bdiStackIndexMod8 (st₁ ++ st₂) = bdiStackIndexMod8 st₁ + bdiStackIndexMod8 st₂ ∧
     Function.Surjective bdiStackIndexMod8 ∧
     bdiStackIndex (List.replicate 8 (kitaevChainA : Mat4 ℤ)) = 8 ∧
     bdiStackIndexMod8 (List.replicate 8 (kitaevChainA : Mat4 ℤ)) = 0 ∧
     (bdiStackIndexMod8 (bdiStackOfInt z) = 0 ↔ (8 : ℤ) ∣ z)) ∧
    (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) (bdiStackIndexMod8 st₁) =
       bdiStackIndexMod2 st₁) := by
  have hTotTriv : bdiTotalZeroModeTrace (trivChainA : Mat4 K) = 0 := by
    simp [bdiTotalZeroModeTrace, bdiChiralGamma, I4, trivChainA, Matrix.trace, Fin.sum_univ_four]
  have hTotKit : bdiTotalZeroModeTrace (kitaevChainA : Mat4 K) = 0 := by
    simp [bdiTotalZeroModeTrace, bdiChiralGamma, I4, kitaevChainA, Matrix.trace, Fin.sum_univ_four]
  have hTotSwap : bdiTotalZeroModeTrace (kitaevChainSublatticeSwapA : Mat4 K) = 0 := by
    simp [bdiTotalZeroModeTrace, bdiChiralGamma, I4, kitaevChainSublatticeSwapA,
      Matrix.trace, Fin.sum_univ_four]
  have hSurjZ : Function.Surjective (bdiStackIndex (K := ℤ)) := by
    intro m
    refine ⟨bdiStackOfInt m, ?_⟩
    simpa using bdiStackIndex_bdiStackOfInt (K := ℤ) m
  have hMod8Add : bdiStackIndexMod8 (st₁ ++ st₂) = bdiStackIndexMod8 st₁ + bdiStackIndexMod8 st₂ := by
    unfold bdiStackIndexMod8
    rw [bdiStackIndex_append, map_add]
  have hSurjMod8 : Function.Surjective bdiStackIndexMod8 := by
    intro w
    rcases ZMod.intCast_surjective w with ⟨m, rfl⟩
    refine ⟨bdiStackOfInt m, ?_⟩
    unfold bdiStackIndexMod8
    rw [bdiStackIndex_bdiStackOfInt (K := ℤ) m]
    simp
  have hEightZ : bdiStackIndex (List.replicate 8 (kitaevChainA : Mat4 ℤ)) = 8 := by
    change bdiStackIndex (bdiStackOfInt 8 : List (Mat4 ℤ)) = (8 : ℤ)
    exact bdiStackIndex_bdiStackOfInt (K := ℤ) 8
  have hEightMod8 : bdiStackIndexMod8 (List.replicate 8 (kitaevChainA : Mat4 ℤ)) = 0 := by
    unfold bdiStackIndexMod8
    rw [hEightZ]
    decide
  have hDvd8 : bdiStackIndexMod8 (bdiStackOfInt z) = 0 ↔ (8 : ℤ) ∣ z := by
    unfold bdiStackIndexMod8
    rw [bdiStackIndex_bdiStackOfInt (K := ℤ) z]
    simpa using ZMod.intCast_zmod_eq_zero_iff_dvd z 8
  have hMod2Factor :
      ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) (bdiStackIndexMod8 st₁) =
        bdiStackIndexMod2 st₁ := by
    unfold bdiStackIndexMod8 bdiStackIndexMod2
    have hcomp :
        (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)).comp (Int.castRingHom (ZMod 8)) =
          Int.castRingHom (ZMod 2) := RingHom.ext_int _ _
    exact congrArg (fun f : ℤ →+* ZMod 2 => f (bdiStackIndex st₁)) hcomp
  exact ⟨⟨⟨hTotTriv, hTotKit, hTotSwap⟩,
          ⟨bdiLeftZeroModeIndex_trivChainA, bdiLeftZeroModeIndex_closedTopChainA,
           bdiLeftZeroModeIndex_kitaevChainA, bdiLeftZeroModeIndex_kitaevChainSublatticeSwapA⟩⟩,
    ⟨bdiStackIndex_append s₁ s₂, bdiStackIndex_bdiStackOfInt z, hSurjZ⟩,
    ⟨hMod8Add, hSurjMod8, hEightZ, hEightMod8, hDvd8⟩,
    hMod2Factor⟩

/-- First 3D real symmetric kinetic Dirac generator `Γ₁ = σ_z ⊗ I₂ = diag(1, 1, -1, -1)` in `Mat4 K`. -/
def diracGamma1 : Mat4 K :=
  !![1, 0,  0,  0;
     0, 1,  0,  0;
     0, 0, -1,  0;
     0, 0,  0, -1]

/-- Second 3D real symmetric kinetic Dirac generator `Γ₂ = σ_x ⊗ σ_z` in `Mat4 K`. -/
def diracGamma2 : Mat4 K :=
  !![0,  0, 1,  0;
     0,  0, 0, -1;
     1,  0, 0,  0;
     0, -1, 0,  0]

/-- Third 3D real symmetric kinetic Dirac generator `Γ₃ = σ_x ⊗ σ_x` in `Mat4 K`. -/
def diracGamma3 : Mat4 K :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- First 3D skew-symmetric Dirac mass / Kramers TRS generator `M₁ = σ_x ⊗ J` in `Mat4 K`. -/
def diracMass1 : Mat4 K :=
  !![ 0, 0,  0, 1;
      0, 0, -1, 0;
      0, 1,  0, 0;
     -1, 0,  0, 0]

/-- Second 3D skew-symmetric Dirac mass / Kramers TRS generator `M₂ = J ⊗ I₂` in `Mat4 K`. -/
def diracMass2 : Mat4 K :=
  !![ 0,  0, 1, 0;
      0,  0, 0, 1;
     -1,  0, 0, 0;
      0, -1, 0, 0]

/-- Tensor product of two $2 \times 2$ skew-symmetric blocks `J ⊗ J` in `Mat4 K`
(symmetric involution `(J ⊗ J)² = +I₄` that commutes with `Γ₂, Γ₃`). -/
def diracJTensorJ : Mat4 K :=
  !![0,  0,  0, 1;
     0,  0, -1, 0;
     0, -1,  0, 0;
     1,  0,  0, 0]

/-- Continuous 2-parameter Class-D Dirac mass combination `c • M₁ + s • M₂` in `Mat4 K`. -/
def diracMassRotor (c s : K) : Mat4 K :=
  c • diracMass1 + s • diracMass2

/-- The three 3D real Dirac kinetic generators `diracGamma1`, `diracGamma2`, `diracGamma3` are
symmetric, square to `+I₄`, and pairwise anticommute. -/
lemma d3_dirac_kinetic_clifford_triplet :
    ((diracGamma1 : Mat4 K).transpose = diracGamma1 ∧
     (diracGamma2 : Mat4 K).transpose = diracGamma2 ∧
     (diracGamma3 : Mat4 K).transpose = diracGamma3) ∧
    ((diracGamma1 : Mat4 K) * diracGamma1 = I4 ∧
     (diracGamma2 : Mat4 K) * diracGamma2 = I4 ∧
     (diracGamma3 : Mat4 K) * diracGamma3 = I4) ∧
    ((diracGamma1 : Mat4 K) * diracGamma2 + diracGamma2 * diracGamma1 = 0 ∧
     (diracGamma1 : Mat4 K) * diracGamma3 + diracGamma3 * diracGamma1 = 0 ∧
     (diracGamma2 : Mat4 K) * diracGamma3 + diracGamma3 * diracGamma2 = 0) := by
  have hG1T : (diracGamma1 : Mat4 K).transpose = diracGamma1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma1]
  have hG2T : (diracGamma2 : Mat4 K).transpose = diracGamma2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma2]
  have hG3T : (diracGamma3 : Mat4 K).transpose = diracGamma3 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma3]
  have hG1Sq : (diracGamma1 : Mat4 K) * diracGamma1 = I4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma1, I4]
  have hG2Sq : (diracGamma2 : Mat4 K) * diracGamma2 = I4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma2, I4]
  have hG3Sq : (diracGamma3 : Mat4 K) * diracGamma3 = I4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma3, I4]
  have hG12 : (diracGamma1 : Mat4 K) * diracGamma2 + diracGamma2 * diracGamma1 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma1, diracGamma2]
  have hG13 : (diracGamma1 : Mat4 K) * diracGamma3 + diracGamma3 * diracGamma1 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma1, diracGamma3]
  have hG23 : (diracGamma2 : Mat4 K) * diracGamma3 + diracGamma3 * diracGamma2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma2, diracGamma3]
  exact ⟨⟨hG1T, hG2T, hG3T⟩, ⟨hG1Sq, hG2Sq, hG3Sq⟩, ⟨hG12, hG13, hG23⟩⟩

/-- Skew-symmetry, `-I₄` square, and anticommutation of `diracMass1 = σ_x ⊗ J` and `diracMass2 = J ⊗ I₂`
with `diracGamma1`, `diracGamma2`, `diracGamma3`. -/
lemma d3_dirac_mass1_mass2_anticomm_and_sq :
    ((diracMass1 : Mat4 K).transpose = -diracMass1 ∧
     (diracMass2 : Mat4 K).transpose = -diracMass2 ∧
     (diracMass1 : Mat4 K) * diracMass1 = -I4 ∧
     (diracMass2 : Mat4 K) * diracMass2 = -I4) ∧
    ((diracGamma1 : Mat4 K) * diracMass1 + diracMass1 * diracGamma1 = 0 ∧
     (diracGamma2 : Mat4 K) * diracMass1 + diracMass1 * diracGamma2 = 0 ∧
     (diracGamma3 : Mat4 K) * diracMass1 + diracMass1 * diracGamma3 = 0) := by
  have hM1T : (diracMass1 : Mat4 K).transpose = -diracMass1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracMass1]
  have hM2T : (diracMass2 : Mat4 K).transpose = -diracMass2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracMass2]
  have hM1Sq : (diracMass1 : Mat4 K) * diracMass1 = -I4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracMass1, I4]
  have hM2Sq : (diracMass2 : Mat4 K) * diracMass2 = -I4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracMass2, I4]
  have hG1M1 : (diracGamma1 : Mat4 K) * diracMass1 + diracMass1 * diracGamma1 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma1, diracMass1]
  have hG2M1 : (diracGamma2 : Mat4 K) * diracMass1 + diracMass1 * diracGamma2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma2, diracMass1]
  have hG3M1 : (diracGamma3 : Mat4 K) * diracMass1 + diracMass1 * diracGamma3 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma3, diracMass1]
  exact ⟨⟨hM1T, hM2T, hM1Sq, hM2Sq⟩, ⟨hG1M1, hG2M1, hG3M1⟩⟩

/-- Anticommutation of `diracMass2 = J ⊗ I₂` with `diracGamma1..3` and `diracMass1`. -/
lemma d3_dirac_mass2_anticomm :
    ((diracGamma1 : Mat4 K) * diracMass2 + diracMass2 * diracGamma1 = 0 ∧
     (diracGamma2 : Mat4 K) * diracMass2 + diracMass2 * diracGamma2 = 0 ∧
     (diracGamma3 : Mat4 K) * diracMass2 + diracMass2 * diracGamma3 = 0) ∧
    (diracMass1 : Mat4 K) * diracMass2 + diracMass2 * diracMass1 = 0 := by
  have hG1M2 : (diracGamma1 : Mat4 K) * diracMass2 + diracMass2 * diracGamma1 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma1, diracMass2]
  have hG2M2 : (diracGamma2 : Mat4 K) * diracMass2 + diracMass2 * diracGamma2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma2, diracMass2]
  have hG3M2 : (diracGamma3 : Mat4 K) * diracMass2 + diracMass2 * diracGamma3 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma3, diracMass2]
  have hM12 : (diracMass1 : Mat4 K) * diracMass2 + diracMass2 * diracMass1 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracMass1, diracMass2]
  exact ⟨⟨hG1M2, hG2M2, hG3M2⟩, hM12⟩

/-- The tensor product of two skew-symmetric $2 \times 2$ blocks `diracJTensorJ = J ⊗ J` is symmetric,
squares to `+I₄`, and commutes with `diracGamma2` and `diracGamma3`. -/
lemma d3_dirac_jtensorj_relations :
    (diracJTensorJ : Mat4 K).transpose = diracJTensorJ ∧
    (diracJTensorJ : Mat4 K) * diracJTensorJ = I4 ∧
    (diracGamma2 : Mat4 K) * diracJTensorJ - diracJTensorJ * diracGamma2 = 0 ∧
    (diracGamma3 : Mat4 K) * diracJTensorJ - diracJTensorJ * diracGamma3 = 0 := by
  have hJJT : (diracJTensorJ : Mat4 K).transpose = diracJTensorJ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracJTensorJ]
  have hJJSq : (diracJTensorJ : Mat4 K) * diracJTensorJ = I4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracJTensorJ, I4]
  have hG2JJ : (diracGamma2 : Mat4 K) * diracJTensorJ - diracJTensorJ * diracGamma2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma2, diracJTensorJ]
  have hG3JJ : (diracGamma3 : Mat4 K) * diracJTensorJ - diracJTensorJ * diracGamma3 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracGamma3, diracJTensorJ]
  exact ⟨hJJT, hJJSq, hG2JJ, hG3JJ⟩

/-- Class-D $S^1$ mass rotor square and Kramers TRS ($T = M_1$) commutator blocking the $M_2$ channel. -/
lemma d3_dirac_mass_rotor_and_kramers_blocking (c s : K) :
    (diracMassRotor c s * diracMassRotor c s = - ((c ^ 2 + s ^ 2) • (I4 : Mat4 K)) ∧
     diracMassRotor 1 0 = (diracMass1 : Mat4 K) ∧
     diracMassRotor (-1) 0 = -(diracMass1 : Mat4 K) ∧
     diracMassRotor 0 1 = (diracMass2 : Mat4 K)) ∧
    diracMassRotor c s * diracMass1 - diracMass1 * diracMassRotor c s =
      (2 * s) • ((diracMass2 : Mat4 K) * diracMass1) ∧
    ((diracMass2 : Mat4 K) * diracMass1) * (diracMass2 * diracMass1) = -I4 := by
  have hRotSq : diracMassRotor c s * diracMassRotor c s = - ((c ^ 2 + s ^ 2) • (I4 : Mat4 K)) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [diracMassRotor, diracMass1, diracMass2, I4, Matrix.mul_apply, Fin.sum_univ_four] <;>
      ring
  have hRot10 : diracMassRotor (1 : K) 0 = (diracMass1 : Mat4 K) := by
    simp [diracMassRotor]
  have hRotNeg10 : diracMassRotor (-1 : K) 0 = -(diracMass1 : Mat4 K) := by
    simp [diracMassRotor]
  have hRot01 : diracMassRotor (0 : K) 1 = (diracMass2 : Mat4 K) := by
    simp [diracMassRotor]
  have hRotComm :
      diracMassRotor c s * diracMass1 - diracMass1 * diracMassRotor c s =
        (2 * s) • ((diracMass2 : Mat4 K) * diracMass1) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [diracMassRotor, diracMass1, diracMass2] <;>
      ring
  have hM21Sq : ((diracMass2 : Mat4 K) * diracMass1) * (diracMass2 * diracMass1) = -I4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diracMass1, diracMass2, I4]
  exact ⟨⟨hRotSq, hRot10, hRotNeg10, hRot01⟩, hRotComm, hM21Sq⟩

/--
**Theorem 5d (`d3_dirac_clifford_mass_circle_and_kramers_trs_z2_blocking`):**
Algebraic resolution of the 3D Dirac Clifford algebra $\mathcal{C}\ell(3, 2) \cong \mathrm{Mat}_4(K)$,
the Class-D $S^1$ mass-rotor connectedness, and the Kramers time-reversal ($T^2 = -I$) $\mathbb{Z}_2$
mass-channel blocking in `Mat4 K` and `Block2 (Mat4 K)`:
1. **Symmetric Kinetic Clifford Triplet ($\Gamma_1, \Gamma_2, \Gamma_3$):**
   `diracGamma1`, `diracGamma2`, `diracGamma3` are symmetric (`Γₐᵀ = Γₐ`), square to `+I₄`, and
   pairwise anticommute (`Γₐ Γ_b + Γ_b Γₐ = 0` for `a ≠ b`).
2. **Socratic Resolution of `σ_x ⊗ J` (`diracMass1`) vs. `J ⊗ J` (`diracJTensorJ`):**
   - Both `diracMass1 = σ_x ⊗ J` and `diracMass2 = J ⊗ I₂` are skew-symmetric (`Mᵀ = -M`), square to
     `-I₄`, anticommute with **all three** kinetic generators `diracGamma1`, `diracGamma2`, `diracGamma3`
     (including `diracGamma2 * diracMass1 + diracMass1 * diracGamma2 = 0` because `[σ_x, σ_x] = 0` and
     `{σ_z, J} = 0`), and anticommute with each other (`diracMass1 * diracMass2 + diracMass2 * diracMass1 = 0`).
   - By contrast, `diracJTensorJ = J ⊗ J` is **symmetric** (`diracJTensorJᵀ = diracJTensorJ`), squares to
     `+I₄`, and **commutes** with `diracGamma2` and `diracGamma3` (`diracGamma2 * diracJTensorJ - diracJTensorJ * diracGamma2 = 0`).
3. **Class-D $S^1$ Mass Rotor vs. Kramers TRS ($T = M_1$, $T^2 = -I_4$) Mass Blocking:**
   - For any `c, s : K`, `diracMassRotor c s = c • M₁ + s • M₂` anticommutes with `Γ₁, Γ₂, Γ₃` and satisfies
     `diracMassRotor c s * diracMassRotor c s = - ((c ^ 2 + s ^ 2) • I4)`.
   - Under Kramers TRS `T = diracMass1` (`T² = -I₄`, `{Γₐ, T} = 0`), `M₁` commutes with `T`
     (`diracMass1 * diracMass1 - diracMass1 * diracMass1 = 0`) while `M₂` **anticommutes** with `T`
     (`diracMass2 * diracMass1 + diracMass1 * diracMass2 = 0`), so the commutator of the general mass rotor with `T` is
     `diracMassRotor c s * diracMass1 - diracMass1 * diracMassRotor c s = (2 * s) • (diracMass2 * diracMass1)`,
     blocking the `M₂` rotation channel and isolating the $\mathbb{Z}_2$ mass axis `c • M₁`.
4. **8×8 Real Lifting in `Block2 (Mat4 K)`:**
   With `Γ̃ₐ = Block2.diagSys Γₐ = diag(Γₐ, -Γₐ)` ($a = 1, 2, 3$), the $8 \times 8$ skew-symmetric Kramers operator
   `T̃ = Block2.baseDecoupler = [[0, I₄], [-I₄, 0]]` satisfies `T̃² = mk2 (-1) 0 0 (-1)` and anticommutes with all three `Γ̃ₐ`,
   while `Block2.mk2 M₁ 0 0 M₁` commutes with `T̃`.
-/
theorem d3_dirac_clifford_mass_circle_and_kramers_trs_z2_blocking (c s : K) :
    (((diracGamma1 : Mat4 K).transpose = diracGamma1 ∧
      (diracGamma2 : Mat4 K).transpose = diracGamma2 ∧
      (diracGamma3 : Mat4 K).transpose = diracGamma3) ∧
     ((diracGamma1 : Mat4 K) * diracGamma1 = I4 ∧
      (diracGamma2 : Mat4 K) * diracGamma2 = I4 ∧
      (diracGamma3 : Mat4 K) * diracGamma3 = I4) ∧
     ((diracGamma1 : Mat4 K) * diracGamma2 + diracGamma2 * diracGamma1 = 0 ∧
      (diracGamma1 : Mat4 K) * diracGamma3 + diracGamma3 * diracGamma1 = 0 ∧
      (diracGamma2 : Mat4 K) * diracGamma3 + diracGamma3 * diracGamma2 = 0)) ∧
    (((diracMass1 : Mat4 K).transpose = -diracMass1 ∧
      (diracMass2 : Mat4 K).transpose = -diracMass2 ∧
      (diracMass1 : Mat4 K) * diracMass1 = -I4 ∧
      (diracMass2 : Mat4 K) * diracMass2 = -I4) ∧
     ((diracGamma1 : Mat4 K) * diracMass1 + diracMass1 * diracGamma1 = 0 ∧
      (diracGamma2 : Mat4 K) * diracMass1 + diracMass1 * diracGamma2 = 0 ∧
      (diracGamma3 : Mat4 K) * diracMass1 + diracMass1 * diracGamma3 = 0) ∧
     ((diracGamma1 : Mat4 K) * diracMass2 + diracMass2 * diracGamma1 = 0 ∧
      (diracGamma2 : Mat4 K) * diracMass2 + diracMass2 * diracGamma2 = 0 ∧
      (diracGamma3 : Mat4 K) * diracMass2 + diracMass2 * diracGamma3 = 0) ∧
     (diracMass1 : Mat4 K) * diracMass2 + diracMass2 * diracMass1 = 0 ∧
     ((diracJTensorJ : Mat4 K).transpose = diracJTensorJ ∧
      (diracJTensorJ : Mat4 K) * diracJTensorJ = I4 ∧
      (diracGamma2 : Mat4 K) * diracJTensorJ - diracJTensorJ * diracGamma2 = 0 ∧
      (diracGamma3 : Mat4 K) * diracJTensorJ - diracJTensorJ * diracGamma3 = 0)) ∧
    ((diracMassRotor c s * diracMassRotor c s = - ((c ^ 2 + s ^ 2) • (I4 : Mat4 K)) ∧
      diracMassRotor 1 0 = (diracMass1 : Mat4 K) ∧
      diracMassRotor (-1) 0 = -(diracMass1 : Mat4 K) ∧
      diracMassRotor 0 1 = (diracMass2 : Mat4 K)) ∧
     diracMassRotor c s * diracMass1 - diracMass1 * diracMassRotor c s =
       (2 * s) • ((diracMass2 : Mat4 K) * diracMass1) ∧
     ((diracMass2 : Mat4 K) * diracMass1) * (diracMass2 * diracMass1) = -I4) ∧
    ((Block2.baseDecoupler : Block2 (Mat4 K)) * Block2.baseDecoupler =
       Block2.mk2 (-1) 0 0 (-1) ∧
     Block2.diagSys (diracGamma1 : Mat4 K) * Block2.baseDecoupler +
       Block2.baseDecoupler * Block2.diagSys diracGamma1 = 0 ∧
     Block2.diagSys (diracGamma2 : Mat4 K) * Block2.baseDecoupler +
       Block2.baseDecoupler * Block2.diagSys diracGamma2 = 0 ∧
     Block2.diagSys (diracGamma3 : Mat4 K) * Block2.baseDecoupler +
       Block2.baseDecoupler * Block2.diagSys diracGamma3 = 0 ∧
     Block2.mk2 (diracMass1 : Mat4 K) 0 0 diracMass1 * Block2.baseDecoupler -
       Block2.baseDecoupler * Block2.mk2 diracMass1 0 0 diracMass1 = 0) := by
  have hM12 := d3_dirac_mass1_mass2_anticomm_and_sq (K := K)
  have hM2 := d3_dirac_mass2_anticomm (K := K)
  have hB8Sq :
      (Block2.baseDecoupler : Block2 (Mat4 K)) * Block2.baseDecoupler =
        Block2.mk2 (-1) 0 0 (-1) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Block2.baseDecoupler, Block2.mk2]
  have hB8 :
      Block2.mk2 (diracMass1 : Mat4 K) 0 0 diracMass1 * Block2.baseDecoupler -
        Block2.baseDecoupler * Block2.mk2 diracMass1 0 0 diracMass1 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Block2.baseDecoupler, Block2.mk2]
  exact ⟨d3_dirac_kinetic_clifford_triplet,
    ⟨hM12.1, hM12.2, hM2.1, hM2.2, d3_dirac_jtensorj_relations⟩,
    d3_dirac_mass_rotor_and_kramers_blocking c s,
    ⟨hB8Sq,
     (Block2.universal_unrotated_and_hadamard_invertibility_rotor
       (diracGamma1 : Mat4 K) 0 0 (by simp) (by simp) (by simp)).2.1,
     (Block2.universal_unrotated_and_hadamard_invertibility_rotor
       (diracGamma2 : Mat4 K) 0 0 (by simp) (by simp) (by simp)).2.1,
     (Block2.universal_unrotated_and_hadamard_invertibility_rotor
       (diracGamma3 : Mat4 K) 0 0 (by simp) (by simp) (by simp)).2.1,
     hB8⟩⟩

/-- Decomposable $4 \times 4$ bitwistor Plücker wedge matrix `(v ∧ w)_{ij} = v_i w_j - v_j w_i`
representing a 2-plane in $\mathrm{Gr}(2, 4)$ inside `Mat4 K`. -/
def bitwistorWedge (v w : Fin 4 → K) : Mat4 K :=
  fun i j => v i * w j - v j * w i

/-- Every decomposable bitwistor `v ∧ w` in $\mathrm{Gr}(2, 4)$ lies on the Plücker–Klein quadric:
its $4 \times 4$ Pfaffian `p₀₁ p₂₃ - p₀₂ p₁₃ + p₀₃ p₁₂` vanishes identically. -/
lemma bitwistorWedge_pfaffianMat4_eq_zero (v w : Fin 4 → K) :
    pfaffianMat4 (bitwistorWedge v w) = 0 := by
  simp [pfaffianMat4, bitwistorWedge]
  ring

/-- Every decomposable bitwistor `v ∧ w` in $\mathrm{Gr}(2, 4)$ has vanishing $4 \times 4$ determinant
(massless null-ray / propagator pole), derived directly from `pfaffian4_sq_eq_det` and the
Plücker–Klein quadric identity `pfaffianMat4 (bitwistorWedge v w) = 0`. -/
lemma bitwistorWedge_det_eq_zero (v w : Fin 4 → K) :
    (bitwistorWedge v w).det = 0 := by
  have hSkew4 :
      bitwistorWedge v w =
        InfoGeometry.Canonical.Pfaffian.skew4
          (bitwistorWedge v w 0 1) (bitwistorWedge v w 0 2) (bitwistorWedge v w 0 3)
          (bitwistorWedge v w 1 2) (bitwistorWedge v w 1 3) (bitwistorWedge v w 2 3) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [bitwistorWedge, InfoGeometry.Canonical.Pfaffian.skew4]
  have hPfBridge :
      pfaffianMat4 (bitwistorWedge v w) =
        InfoGeometry.Canonical.Pfaffian.pfaffian4
          (bitwistorWedge v w 0 1) (bitwistorWedge v w 0 2) (bitwistorWedge v w 0 3)
          (bitwistorWedge v w 1 2) (bitwistorWedge v w 1 3) (bitwistorWedge v w 2 3) := by
    simp [pfaffianMat4, InfoGeometry.Canonical.Pfaffian.pfaffian4]
  have hDet :
      (bitwistorWedge v w).det = (pfaffianMat4 (bitwistorWedge v w)) ^ 2 := by
    rw [hPfBridge]
    conv_lhs => rw [hSkew4]
    exact (InfoGeometry.Canonical.Pfaffian.pfaffian4_sq_eq_det
      (bitwistorWedge v w 0 1) (bitwistorWedge v w 0 2) (bitwistorWedge v w 0 3)
      (bitwistorWedge v w 1 2) (bitwistorWedge v w 1 3) (bitwistorWedge v w 2 3)).symm
  rw [hDet, bitwistorWedge_pfaffianMat4_eq_zero, zero_pow (by decide)]

/--
**Theorem 5e (`twistor_plucker_klein_quadric_and_kitaev_mass_gap_regulator`):**
Unifies the $\mathrm{Gr}(2, 4)$ Plücker–Klein quadric with the $4 \times 4$ Majorana Pfaffian and the
Kitaev mass-gap regulator over any `[CommRing K]`:
1. **Massless Decomposable Bitwistor ($\mathrm{Gr}(2, 4)$ Klein Quadric Pole):**
   For any two 4-twistors `v, w : Fin 4 → K`, `bitwistorWedge v w` is skew-symmetric, satisfies the
   Plücker–Klein quadric equation `pfaffianMat4 (bitwistorWedge v w) = 0`, and has singular determinant
   `(bitwistorWedge v w).det = 0`.
2. **Kitaev Majorana Mass-Gap Deformation Off the Klein Quadric:**
   Adding the Kitaev pairing parameters `majoranaParamA μ tPlus tMinus` shifts the Klein-quadric /
   Pfaffian invariant to `pfaffianMat4 (majoranaParamA μ tPlus tMinus) = μ ^ 2 + tPlus * tMinus` and
   lifts the determinant to `(majoranaParamA μ tPlus tMinus).det = (μ ^ 2 + tPlus * tMinus) ^ 2`:
   - On the gapless open boundary sweet spots (`kitaevChainA` and `kitaevChainSublatticeSwapA`),
     `pfaffianMat4 = 0` and `det = 0` (boundary zero modes remain on the Klein quadric);
   - On the gapped trivial (`trivChainA`, `Pf = +1`) and closed topological (`closedTopChainA`, `Pf = -1`)
     bulk phases, `det = 1` and `-A² = I₄`, removing the massless determinant pole.
-/
theorem twistor_plucker_klein_quadric_and_kitaev_mass_gap_regulator
    (v w : Fin 4 → K) (μ tPlus tMinus : K) :
    ((bitwistorWedge v w).transpose = -bitwistorWedge v w ∧
     pfaffianMat4 (bitwistorWedge v w) = 0 ∧
     (bitwistorWedge v w).det = 0) ∧
    (pfaffianMat4 (majoranaParamA μ tPlus tMinus) = μ ^ 2 + tPlus * tMinus ∧
     (majoranaParamA μ tPlus tMinus).det = (μ ^ 2 + tPlus * tMinus) ^ 2 ∧
     (trivChainA : Mat4 K).det = 1 ∧
     (closedTopChainA : Mat4 K).det = 1) := by
  have hSkew : (bitwistorWedge v w).transpose = -bitwistorWedge v w := by
    ext i j; simp [bitwistorWedge]
  have hPf := bdi_parameterized_majorana_pfaffian_and_phase_sign_flip μ tPlus tMinus
  have hDetParam : (majoranaParamA μ tPlus tMinus).det = (μ ^ 2 + tPlus * tMinus) ^ 2 := by
    rw [hPf.2.2.1.2.2, hPf.2.2.1.2.1]
  have hDetTriv : (trivChainA : Mat4 K).det = 1 := by
    have h1 := bdi_parameterized_majorana_pfaffian_and_phase_sign_flip (1 : K) 0 0
    have h2 : (majoranaParamA (1 : K) 0 0).det = ((1 : K) ^ 2 + 0 * 0) ^ 2 := by
      rw [h1.2.2.1.2.2, h1.2.2.1.2.1]
    rw [h1.1.1] at h2
    simpa using h2
  have hDetClosed : (closedTopChainA : Mat4 K).det = 1 := by
    have h1 := bdi_parameterized_majorana_pfaffian_and_phase_sign_flip (0 : K) 1 (-1)
    have h2 : (majoranaParamA (0 : K) 1 (-1)).det = ((0 : K) ^ 2 + 1 * (-1)) ^ 2 := by
      rw [h1.2.2.1.2.2, h1.2.2.1.2.1]
    rw [h1.1.2.2.1] at h2
    simpa using h2
  exact ⟨⟨hSkew, bitwistorWedge_pfaffianMat4_eq_zero v w, bitwistorWedge_det_eq_zero v w⟩,
    ⟨hPf.2.2.1.2.1, hDetParam, hDetTriv, hDetClosed⟩⟩

-- ============================================================================
-- SECTION 4f: ℤ₄ Parafermion Binary-Carry Shift τ & Phase-Graded Clock σ (Weyl Algebra)
-- ============================================================================

/-- LSB chiral involution `S₂ = I₂ ⊗ Z = diag(1, -1, 1, -1)` in `Mat4 K`. -/
def pauliZ1 : Mat4 K :=
  !![1,  0, 0,  0;
     0, -1, 0,  0;
     0,  0, 1,  0;
     0,  0, 0, -1]

/-- LSB flip `Φ₂ = I₂ ⊗ X` in `Mat4 K`. -/
def pauliX1 : Mat4 K :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- MSB chiral involution `S₁ = Z ⊗ I₂ = diag(1, 1, -1, -1)` in `Mat4 K`. -/
def pauliZ2 : Mat4 K :=
  !![1, 0,  0,  0;
     0, 1,  0,  0;
     0, 0, -1,  0;
     0, 0,  0, -1]

/-- MSB flip `Φ₁ = X ⊗ I₂` in `Mat4 K`. -/
def pauliX2 : Mat4 K :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- The `ℤ₄` parafermion binary-carry shift operator `τ` in `Mat4 K`, constructed from
two `ℤ₂` Pauli pairs via a CNOT / binary-carry twist `((I₄ + Z₁)/2 + X₂(I₄ - Z₁)/2) X₁`.
Satisfies `τ² = X₂ = Φ₁`, `τ⁴ = I₄`, and `τ σ(i_K) = i_K σ(i_K) τ` when `i_K² = -1`. -/
def z4ShiftTau : Mat4 K :=
  !![0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0]

/-- The inverse / adjoint `ℤ₄` binary-carry shift `τ† = τ³` in `Mat4 K`, given by
`X₁ ((I₄ + Z₁)/2 + X₂(I₄ - Z₁)/2)`. Satisfies `σ(i_K) τ† = i_K τ† σ(i_K)` when `i_K² = -1`. -/
def z4ShiftTauAdj : Mat4 K :=
  !![0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0]

/-- The `ℤ₄` parafermion phase-graded clock operator `σ(i_K) = diag(1, i_K, -1, -i_K)` in `Mat4 K`,
synthesized from `Z₂ ((I₄ + Z₁)/2 + i_K (I₄ - Z₁)/2)`. When `i_K² = -1`, satisfies
`σ(i_K)² = Z₁ = S₂` and `σ(i_K)⁴ = I₄`. -/
def z4ClockSigma (i_K : K) : Mat4 K :=
  !![1,   0,  0,    0;
     0, i_K,  0,    0;
     0,   0, -1,    0;
     0,   0,  0, -i_K]

/-- Helper lemma: division-free CNOT / binary-carry synthesis of `z4ShiftTau` and `z4ShiftTauAdj`,
their mutual inversion `τ τ† = I₄`, and order-4 carry laws `τ² = pauliX2`, `τ⁴ = I₄`. -/
lemma z4_binary_carry_synthesis_and_tau_powers :
    (2 : K) • (z4ShiftTau : Mat4 K) =
      ((I4 + pauliZ1) + pauliX2 * (I4 - pauliZ1)) * pauliX1 ∧
    (2 : K) • (z4ShiftTauAdj : Mat4 K) =
      pauliX1 * ((I4 + pauliZ1) + pauliX2 * (I4 - pauliZ1)) ∧
    (z4ShiftTau : Mat4 K) * z4ShiftTau = pauliX2 ∧
    ((z4ShiftTau : Mat4 K) * z4ShiftTau) * (z4ShiftTau * z4ShiftTau) = I4 ∧
    (z4ShiftTau : Mat4 K) * z4ShiftTauAdj = I4 ∧
    (z4ShiftTauAdj : Mat4 K) * z4ShiftTau = I4 := by
  have hSyn1 :
      (2 : K) • (z4ShiftTau : Mat4 K) =
        ((I4 + pauliZ1) + pauliX2 * (I4 - pauliZ1)) * pauliX1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [z4ShiftTau, I4, pauliZ1, pauliX1, pauliX2] <;> ring
  have hSyn2 :
      (2 : K) • (z4ShiftTauAdj : Mat4 K) =
        pauliX1 * ((I4 + pauliZ1) + pauliX2 * (I4 - pauliZ1)) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [z4ShiftTauAdj, I4, pauliZ1, pauliX1, pauliX2] <;> ring
  have hTau2 : (z4ShiftTau : Mat4 K) * z4ShiftTau = pauliX2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [z4ShiftTau, pauliX2]
  have hTau4 : ((z4ShiftTau : Mat4 K) * z4ShiftTau) * (z4ShiftTau * z4ShiftTau) = I4 := by
    rw [hTau2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX2, I4]
  have hInvR : (z4ShiftTau : Mat4 K) * z4ShiftTauAdj = I4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [z4ShiftTau, z4ShiftTauAdj, I4]
  have hInvL : (z4ShiftTauAdj : Mat4 K) * z4ShiftTau = I4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [z4ShiftTau, z4ShiftTauAdj, I4]
  exact ⟨hSyn1, hSyn2, hTau2, hTau4, hInvR, hInvL⟩

/-- Helper lemma: division-free controlled-phase synthesis of `z4ClockSigma i_K`, its square
and fourth power under `i_K * i_K = -1`, and the `ℤ₄` Weyl braiding relations
`τ σ = i_K σ τ` and `σ τ† = i_K τ† σ`. -/
lemma z4_clock_powers_and_weyl_braiding (i_K : K) :
    (2 : K) • z4ClockSigma i_K =
      pauliZ2 * ((I4 + pauliZ1) + i_K • (I4 - pauliZ1)) ∧
    (i_K * i_K = -1 →
      z4ClockSigma i_K * z4ClockSigma i_K = pauliZ1 ∧
      (z4ClockSigma i_K * z4ClockSigma i_K) * (z4ClockSigma i_K * z4ClockSigma i_K) = I4 ∧
      z4ShiftTau * z4ClockSigma i_K = i_K • (z4ClockSigma i_K * z4ShiftTau) ∧
      z4ClockSigma i_K * z4ShiftTauAdj = i_K • (z4ShiftTauAdj * z4ClockSigma i_K)) := by
  have hSyn :
      (2 : K) • z4ClockSigma i_K =
        pauliZ2 * ((I4 + pauliZ1) + i_K • (I4 - pauliZ1)) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [z4ClockSigma, pauliZ2, pauliZ1, I4] <;> ring
  refine ⟨hSyn, ?_⟩
  intro hi
  have hSig2 : z4ClockSigma i_K * z4ClockSigma i_K = pauliZ1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [z4ClockSigma, pauliZ1] <;> simp [hi]
  have hSig4 :
      (z4ClockSigma i_K * z4ClockSigma i_K) * (z4ClockSigma i_K * z4ClockSigma i_K) = I4 := by
    rw [hSig2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ1, I4]
  have hWeyl1 : z4ShiftTau * z4ClockSigma i_K = i_K • (z4ClockSigma i_K * z4ShiftTau) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [z4ShiftTau, z4ClockSigma] <;> simp [hi]
  have hWeyl2 : z4ClockSigma i_K * z4ShiftTauAdj = i_K • (z4ShiftTauAdj * z4ClockSigma i_K) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [z4ShiftTauAdj, z4ClockSigma] <;> simp [hi]
  exact ⟨hSig2, hSig4, hWeyl1, hWeyl2⟩

/--
**Theorem 5f (`z4_parafermion_binary_carry_clock_shift_weyl_algebra`):**
Resolves the Socratic distinction between two `ℤ₂` Majorana/Pauli pairs (`(√2)² = 2`) and one
genuine `ℤ₄` parafermion pair (`√4 = 2`) over `Mat4 K`:
1. **Non-Clifford Binary-Carry & Controlled-Phase Synthesis:**
   `2 • τ = ((I₄ + Z₁) + X₂(I₄ - Z₁)) X₁`, `2 • τ† = X₁ ((I₄ + Z₁) + X₂(I₄ - Z₁))`, and
   `2 • σ(i_K) = Z₂ ((I₄ + Z₁) + i_K • (I₄ - Z₁))`.
2. **Exact Order-4 Carry & Phase-Grading Laws:**
   `τ² = pauliX2` (`Φ₁`), `τ⁴ = I₄`, `τ τ† = τ† τ = I₄`, and whenever `i_K² = -1`,
   `σ(i_K)² = pauliZ1` (`S₂`) and `σ(i_K)⁴ = I₄`.
3. **Exact `ℤ₄` Parafermion Weyl Braiding Relation:**
   Whenever `i_K² = -1`, `τ σ(i_K) = i_K • (σ(i_K) τ)` and `σ(i_K) τ† = i_K • (τ† σ(i_K))`.
-/
theorem z4_parafermion_binary_carry_clock_shift_weyl_algebra (i_K : K) :
    ((2 : K) • (z4ShiftTau : Mat4 K) =
       ((I4 + pauliZ1) + pauliX2 * (I4 - pauliZ1)) * pauliX1 ∧
     (2 : K) • (z4ShiftTauAdj : Mat4 K) =
       pauliX1 * ((I4 + pauliZ1) + pauliX2 * (I4 - pauliZ1)) ∧
     (z4ShiftTau : Mat4 K) * z4ShiftTau = pauliX2 ∧
     ((z4ShiftTau : Mat4 K) * z4ShiftTau) * (z4ShiftTau * z4ShiftTau) = I4 ∧
     (z4ShiftTau : Mat4 K) * z4ShiftTauAdj = I4 ∧
     (z4ShiftTauAdj : Mat4 K) * z4ShiftTau = I4) ∧
    ((2 : K) • z4ClockSigma i_K =
       pauliZ2 * ((I4 + pauliZ1) + i_K • (I4 - pauliZ1)) ∧
     (i_K * i_K = -1 →
       z4ClockSigma i_K * z4ClockSigma i_K = pauliZ1 ∧
       (z4ClockSigma i_K * z4ClockSigma i_K) * (z4ClockSigma i_K * z4ClockSigma i_K) = I4 ∧
       z4ShiftTau * z4ClockSigma i_K = i_K • (z4ClockSigma i_K * z4ShiftTau) ∧
       z4ClockSigma i_K * z4ShiftTauAdj = i_K • (z4ShiftTauAdj * z4ClockSigma i_K))) := by
  have hTau := z4_binary_carry_synthesis_and_tau_powers (K := K)
  have hSig := z4_clock_powers_and_weyl_braiding i_K
  refine ⟨⟨hTau.1, hTau.2.1, ?_, hTau.2.2.2.1, hTau.2.2.2.2.1, hTau.2.2.2.2.2⟩, hSig⟩
  rw [hTau.2.2.1]

/-- Exact division-free LSB Peirce idempotent `P₂ = I₂ ⊗ diag(1, 0) = diag(1, 0, 1, 0)` in `Mat4 K`.
Satisfies `P₂² = P₂`, `(2 : K) • P₂ - I₄ = pauliZ1`, and `pauliX1 * P₂ = (I₄ - P₂) * pauliX1`
with zero division by `2`. -/
def peirceP2 : Mat4 K :=
  !![1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0]

/-- Exact division-free integer 8th root of unity (`ζ_real`) in `Mat4 K`, constructed from the
DeWitt Split Tetractys binary carry `P₂ Φ₂ + (I₄ - P₂) J₁ Φ₂` where `P₂ = peirceP2`,
`Φ₂ = pauliX1`, and `J₁ = diracMass2 = J ⊗ I₂`. Eliminates both scalar `i ∈ ℂ` and `√2`,
and satisfies `ζ_real² = diracMass2`, `ζ_real⁴ = -I₄`, `ζ_real⁸ = +I₄`, and symplectic/orthogonal
invariance `ζ_realᵀ diracMass2 ζ_real = diracMass2` over any `[CommRing K]` (including `ℤ`). -/
def zetaRealMat4 : Mat4 K :=
  !![ 0, 1, 0, 0;
      0, 0, 1, 0;
      0, 0, 0, 1;
     -1, 0, 0, 0]

/-- Real moment curve `Z(t) = (1, t, t², t³)` in `Fin 4 → K`. -/
def momentCurveVec (t : K) : Fin 4 → K :=
  ![1, t, t ^ 2, t ^ 3]

/-- First row `[1, 0, -t₁, -(t₁ t₃ + t₄)]` of the canonical unipotent boundary-measurement
matrix `C(t₁, t₂, t₃, t₄)` in the positive Grassmannian $\mathrm{Gr}_+(2, 4)$. -/
def gr24PosRow1 (t1 t3 t4 : K) : Fin 4 → K :=
  ![1, 0, -t1, -(t1 * t3 + t4)]

/-- Second row `[0, 1, t₂, t₂ t₃]` of the canonical unipotent boundary-measurement matrix
`C(t₁, t₂, t₃, t₄)` in the positive Grassmannian $\mathrm{Gr}_+(2, 4)$. -/
def gr24PosRow2 (t2 t3 : K) : Fin 4 → K :=
  ![0, 1, t2, t2 * t3]

/--
**Theorem 5f'' (`dewitt_tetractys_mat4_zeta8_and_sp4_invariance`):**
Concrete `Mat4 K` realization of the division-free integer 8th root of unity `zetaRealMat4`
and its $\mathrm{Sp}(4, K) \cap \mathrm{O}(4, K)$ symplectic-orthogonal invariance:
1. **Division-Free Peirce Binary-Carry Synthesis:**
   `peirceP2 * peirceP2 = peirceP2`, `pauliX1 * peirceP2 = (I4 - peirceP2) * pauliX1`, and
   `peirceP2 * pauliX1 + (I4 - peirceP2) * diracMass2 * pauliX1 = zetaRealMat4`.
2. **Exact Cyclotomic Hierarchy ($\zeta_{\text{real}}^2 = J_1$, $\zeta_{\text{real}}^4 = -I_4$, $\zeta_{\text{real}}^8 = +I_4$):**
   `zetaRealMat4 * zetaRealMat4 = diracMass2`,
   `(zetaRealMat4 * zetaRealMat4) * (zetaRealMat4 * zetaRealMat4) = -I4`, and
   `(((zetaRealMat4 * zetaRealMat4) * (zetaRealMat4 * zetaRealMat4)) *
     ((zetaRealMat4 * zetaRealMat4) * (zetaRealMat4 * zetaRealMat4))) = I4`.
3. **Symplectic $\mathrm{Sp}(4, K)$ & Orthogonal $\mathrm{O}(4, K)$ Invariance:**
   `zetaRealMat4.transpose * zetaRealMat4 = I4` and
   `zetaRealMat4.transpose * diracMass2 * zetaRealMat4 = diracMass2`.
-/
theorem dewitt_tetractys_mat4_zeta8_and_sp4_invariance :
    ((peirceP2 : Mat4 K) * peirceP2 = peirceP2 ∧
     (pauliX1 : Mat4 K) * peirceP2 = (I4 - peirceP2) * pauliX1 ∧
     (peirceP2 : Mat4 K) * pauliX1 + (I4 - peirceP2) * diracMass2 * pauliX1 = zetaRealMat4) ∧
    ((zetaRealMat4 : Mat4 K) * zetaRealMat4 = diracMass2 ∧
     ((zetaRealMat4 : Mat4 K) * zetaRealMat4) * (zetaRealMat4 * zetaRealMat4) = -I4 ∧
     (((zetaRealMat4 : Mat4 K) * zetaRealMat4) * (zetaRealMat4 * zetaRealMat4)) *
       (((zetaRealMat4 : Mat4 K) * zetaRealMat4) * (zetaRealMat4 * zetaRealMat4)) = I4) ∧
    ((zetaRealMat4 : Mat4 K).transpose * zetaRealMat4 = I4 ∧
     (zetaRealMat4 : Mat4 K).transpose * diracMass2 * zetaRealMat4 = diracMass2) := by
  have hP2 : (peirceP2 : Mat4 K) * peirceP2 = peirceP2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [peirceP2]
  have hSwap : (pauliX1 : Mat4 K) * peirceP2 = (I4 - peirceP2) * pauliX1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX1, peirceP2, I4]
  have hSyn :
      (peirceP2 : Mat4 K) * pauliX1 + (I4 - peirceP2) * diracMass2 * pauliX1 = zetaRealMat4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [peirceP2, pauliX1, I4, diracMass2, zetaRealMat4]
  have hSq : (zetaRealMat4 : Mat4 K) * zetaRealMat4 = diracMass2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [zetaRealMat4, diracMass2]
  have hPow4 :
      ((zetaRealMat4 : Mat4 K) * zetaRealMat4) * (zetaRealMat4 * zetaRealMat4) = -I4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [zetaRealMat4, I4]
  have hPow8 :
      (((zetaRealMat4 : Mat4 K) * zetaRealMat4) * (zetaRealMat4 * zetaRealMat4)) *
        (((zetaRealMat4 : Mat4 K) * zetaRealMat4) * (zetaRealMat4 * zetaRealMat4)) = I4 := by
    rw [hPow4]
    ext i j; fin_cases i <;> fin_cases j <;> simp [I4]
  have hOrth : (zetaRealMat4 : Mat4 K).transpose * zetaRealMat4 = I4 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [zetaRealMat4, I4, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
  have hSymp : (zetaRealMat4 : Mat4 K).transpose * diracMass2 * zetaRealMat4 = diracMass2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [zetaRealMat4, diracMass2, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
  exact ⟨⟨hP2, hSwap, hSyn⟩, ⟨hSq, hPow4, hPow8⟩, ⟨hOrth, hSymp⟩⟩

/--
**Theorem 5f''' (`moment_curve_amplituhedron_vandermonde_and_gr24_positivity`):**
Unifies the 3-term Grassmann–Plücker syzygy on $\mathrm{Gr}(2, 4)$, strict Plücker positivity of the
unipotent boundary-measurement matrix $C(t_1, t_2, t_3, t_4) \in \mathrm{Gr}_+(2, 4)$, and the
4-variable Vandermonde factorization & strict positivity of the Amplituhedron scattering foam on
the ordered real moment curve $Z(t) = (1, t, t^2, t^3)$:
1. **Universal 3-Term Grassmann–Plücker Syzygy ($\Delta_{02}\Delta_{13} = \Delta_{01}\Delta_{23} + \Delta_{03}\Delta_{12}$):**
   For any `u, v : Fin 4 → K`,
   `bitwistorWedge u v 0 2 * bitwistorWedge u v 1 3 =
     bitwistorWedge u v 0 1 * bitwistorWedge u v 2 3 +
     bitwistorWedge u v 0 3 * bitwistorWedge u v 1 2`.
2. **Unipotent $\mathrm{Gr}_+(2, 4)$ Plücker Coordinates:**
   For `W := bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3)`:
   `W 0 1 = 1`, `W 0 2 = t2`, `W 0 3 = t2 * t3`, `W 1 2 = t1`, `W 1 3 = t1 * t3 + t4`, and
   `W 2 3 = t2 * t4`.
3. **Moment-Curve Amplituhedron Vandermonde Factorization & Ordered Positivity ($t_0 < t_1 < t_2 < t_3$):**
   - While each single moment-curve ray has zero Pfaffian on the Klein quadric
     (`pfaffianMat4 (bitwistorWedge (momentCurveVec t0) (momentCurveVec t1)) = 0`), the Pfaffian of
     the sum of two colliding rays equals the 6-factor Vandermonde product:
     `pfaffianMat4 (bitwistorWedge (momentCurveVec t0) (momentCurveVec t1) +
       bitwistorWedge (momentCurveVec t2) (momentCurveVec t3)) =
       (t1 - t0) * (t2 - t0) * (t3 - t0) * (t2 - t1) * (t3 - t1) * (t3 - t2)`.
   - Whenever `a0 < a1`, `a1 < a2`, and `a2 < a3` in `ℤ`,
     `0 < pfaffianMat4 (bitwistorWedge (momentCurveVec a0) (momentCurveVec a1) +
       bitwistorWedge (momentCurveVec a2) (momentCurveVec a3))`.
-/
theorem moment_curve_amplituhedron_vandermonde_and_gr24_positivity
    (u v : Fin 4 → K) (t0 t1 t2 t3 t4 : K) (a0 a1 a2 a3 : ℤ)
    (h01 : a0 < a1) (h12 : a1 < a2) (h23 : a2 < a3) :
    (bitwistorWedge u v 0 2 * bitwistorWedge u v 1 3 =
       bitwistorWedge u v 0 1 * bitwistorWedge u v 2 3 +
       bitwistorWedge u v 0 3 * bitwistorWedge u v 1 2) ∧
    (bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 0 1 = 1 ∧
     bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 0 2 = t2 ∧
     bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 0 3 = t2 * t3 ∧
     bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 1 2 = t1 ∧
     bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 1 3 = t1 * t3 + t4 ∧
     bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 2 3 = t2 * t4) ∧
    (pfaffianMat4 (bitwistorWedge (momentCurveVec t0) (momentCurveVec t1) +
        bitwistorWedge (momentCurveVec t2) (momentCurveVec t3)) =
      (t1 - t0) * (t2 - t0) * (t3 - t0) * (t2 - t1) * (t3 - t1) * (t3 - t2) ∧
     0 < pfaffianMat4 (bitwistorWedge (momentCurveVec a0) (momentCurveVec a1) +
        bitwistorWedge (momentCurveVec a2) (momentCurveVec a3))) := by
  have hSyz :
      bitwistorWedge u v 0 2 * bitwistorWedge u v 1 3 =
        bitwistorWedge u v 0 1 * bitwistorWedge u v 2 3 +
        bitwistorWedge u v 0 3 * bitwistorWedge u v 1 2 := by
    simp [bitwistorWedge]
    ring
  have hGr01 : bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 0 1 = 1 := by
    simp [bitwistorWedge, gr24PosRow1, gr24PosRow2]
  have hGr02 : bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 0 2 = t2 := by
    simp [bitwistorWedge, gr24PosRow1, gr24PosRow2]
  have hGr03 : bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 0 3 = t2 * t3 := by
    simp [bitwistorWedge, gr24PosRow1, gr24PosRow2]
  have hGr12 : bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 1 2 = t1 := by
    simp [bitwistorWedge, gr24PosRow1, gr24PosRow2]
  have hGr13 : bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 1 3 = t1 * t3 + t4 := by
    simp [bitwistorWedge, gr24PosRow1, gr24PosRow2]
  have hGr23 : bitwistorWedge (gr24PosRow1 t1 t3 t4) (gr24PosRow2 t2 t3) 2 3 = t2 * t4 := by
    simp [bitwistorWedge, gr24PosRow1, gr24PosRow2]
    ring
  have hVanK :
      pfaffianMat4 (bitwistorWedge (momentCurveVec t0) (momentCurveVec t1) +
        bitwistorWedge (momentCurveVec t2) (momentCurveVec t3)) =
        (t1 - t0) * (t2 - t0) * (t3 - t0) * (t2 - t1) * (t3 - t1) * (t3 - t2) := by
    simp [pfaffianMat4, bitwistorWedge, momentCurveVec]
    ring
  have hVanZ :
      pfaffianMat4 (bitwistorWedge (momentCurveVec a0) (momentCurveVec a1) +
        bitwistorWedge (momentCurveVec a2) (momentCurveVec a3)) =
        (a1 - a0) * (a2 - a0) * (a3 - a0) * (a2 - a1) * (a3 - a1) * (a3 - a2) := by
    simp [pfaffianMat4, bitwistorWedge, momentCurveVec]
    ring
  have hPos :
      0 < pfaffianMat4 (bitwistorWedge (momentCurveVec a0) (momentCurveVec a1) +
        bitwistorWedge (momentCurveVec a2) (momentCurveVec a3)) := by
    rw [hVanZ]
    have h02 : a0 < a2 := lt_trans h01 h12
    have h03 : a0 < a3 := lt_trans h02 h23
    have h13 : a1 < a3 := lt_trans h12 h23
    have d10 : 0 < a1 - a0 := Int.sub_pos.mpr h01
    have d20 : 0 < a2 - a0 := Int.sub_pos.mpr h02
    have d30 : 0 < a3 - a0 := Int.sub_pos.mpr h03
    have d21 : 0 < a2 - a1 := Int.sub_pos.mpr h12
    have d31 : 0 < a3 - a1 := Int.sub_pos.mpr h13
    have d32 : 0 < a3 - a2 := Int.sub_pos.mpr h23
    exact Int.mul_pos
      (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos d10 d20) d30) d21) d31) d32
  exact ⟨hSyz, ⟨hGr01, hGr02, hGr03, hGr12, hGr13, hGr23⟩, ⟨hVanK, hPos⟩⟩

end Mat4

-- ============================================================================
-- SECTION 4g: Fateev–Zamolodchikov / Jones–Fendley ℤ₄ Braid Operator via Orthogonal
--             Peirce Idempotents, Brown–Gauss Sum (c₋ = 1), & η⁴ = 0 Unipotent Gate
-- ============================================================================

section Z4ParafermionBraidAndUnipotentGate

variable {B : Type u} [Ring B]

/-- Division-free binary-carry shift operator `2 τ = ((1 + S₂) + Φ₁ (1 - S₂)) Φ₂` in any `[Ring B]`,
built from two commuting `ℤ₂` Pauli/Peirce pairs `(S₁, Φ₁)` and `(S₂, Φ₂)`. -/
def tauCarry2 (S₂ Φ₁ Φ₂ : B) : B :=
  ((1 + S₂) + Φ₁ * (1 - S₂)) * Φ₂

/-- Division-free phase-graded clock operator `2 σ = S₁ ((1 + S₂) + J (1 - S₂))` in any `[Ring B]`,
with an internal operator-valued complex structure `J` (`J² = -1`). -/
def sigmaClock2 (S₁ S₂ J : B) : B :=
  S₁ * ((1 + S₂) + J * (1 - S₂))

/--
**Theorem 5f' (`z4_ring_binary_carry_and_peirce_tetraktys_weyl_algebra`):**
Universal noncommutative ring formulation of the Peirce Tetraktys internal Clifford $\mathcal{C}\ell(1, 1)$
and complex-structure laws (`PF1`) together with the `ℤ₄` binary-carry shift `tauCarry2 S₂ Φ₁ Φ₂`
and phase-graded clock `sigmaClock2 S₁ S₂ J` projector decompositions in `[Ring B]`:
1. **Peirce Tetraktys Internal Clifford $\mathcal{C}\ell(1, 1)$ & Complex Structure (`PF1`):**
   For any idempotent `P * P = P` and corner operators `A, C : B`:
   - `genPhi P A C * genPhi P A C = genV P A C`,
   - `genJ P A C * genJ P A C = -genV P A C`,
   - `genPhi P A C * genJ P A C + genJ P A C * genPhi P A C = 0`,
   - When the Jordan mass is normalized to the unit (`genV P A C = 1`), `genPhi P A C` is an
     involution (`genPhi² = 1`) and `genJ P A C` is an internal square root of `-1` (`genJ² = -1`).
2. **Binary-Carry Shift & Phase-Graded Clock Projector Decomposition:**
   `tauCarry2 S₂ Φ₁ Φ₂ = (1 + S₂) * Φ₂ + Φ₁ * (1 - S₂) * Φ₂` and
   `sigmaClock2 S₁ S₂ J = S₁ * (1 + S₂) + S₁ * J * (1 - S₂)`.
-/
theorem z4_ring_binary_carry_and_peirce_tetraktys_weyl_algebra
    (P A C S₁ S₂ Φ₁ Φ₂ J : B) (hP : P * P = P) :
    (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C *
       InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C =
       InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A C ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C *
       InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C =
       -InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A C ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C *
       InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C +
     InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C *
       InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C = 0 ∧
     (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A C = 1 →
       InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C *
         InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C = 1 ∧
       InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C *
         InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C = -1)) ∧
    tauCarry2 S₂ Φ₁ Φ₂ = (1 + S₂) * Φ₂ + Φ₁ * (1 - S₂) * Φ₂ ∧
    sigmaClock2 S₁ S₂ J = S₁ * (1 + S₂) + S₁ * J * (1 - S₂) := by
  have hPP := InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus_mul_conePlus hP A A
  have hMM := InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus_mul_coneMinus hP C C
  have hPhiSq :
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C *
        InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C =
        InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A C := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
      InfoGeometry.OperatorAlgebra.PeirceSpine.genV
      InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm
    calc
      (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A +
         InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) *
        (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A +
         InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A *
          InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A +
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C *
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C +
        (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A *
           InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C +
         InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C *
           InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A) := by noncomm_ring
      _ = InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A *
            InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C +
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C *
            InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A := by
        rw [hPP, hMM]; abel
  have hTet :
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C *
        InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C =
        -InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A C := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.genJ
      InfoGeometry.OperatorAlgebra.PeirceSpine.genV
      InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm
    calc
      (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A -
         InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) *
        (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A -
         InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A *
          InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A +
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C *
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C -
        (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A *
           InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C +
         InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C *
           InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A) := by noncomm_ring
      _ = -(InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A *
              InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C +
            InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C *
              InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A) := by
        rw [hPP, hMM]; abel
  have hAntiPhiJ :
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C *
        InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C +
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C *
        InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C = 0 := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ
    calc
      (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A +
         InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) *
        (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A -
         InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) +
      (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A -
         InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) *
        (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A +
         InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) =
        (2 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A *
          InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A) -
        (2 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C *
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) := by noncomm_ring
      _ = 0 := by rw [hPP, hMM, smul_zero, sub_zero]
  have hTauDecomp : tauCarry2 S₂ Φ₁ Φ₂ = (1 + S₂) * Φ₂ + Φ₁ * (1 - S₂) * Φ₂ := by
    dsimp [tauCarry2]; noncomm_ring
  have hSigDecomp : sigmaClock2 S₁ S₂ J = S₁ * (1 + S₂) + S₁ * J * (1 - S₂) := by
    dsimp [sigmaClock2]; noncomm_ring
  exact ⟨⟨hPhiSq, hTet, hAntiPhiJ, fun hV => ⟨by rw [hPhiSq, hV], by rw [hTet, hV]⟩⟩,
    hTauDecomp, hSigDecomp⟩

/-- Unnormalized odd-parity Peirce projector `P_-^{(2)}(X) = 1 - X²` (projected onto `X² = -1`). -/
def z4PeirceOdd2 (X : B) : B := 1 - X * X

/-- Unnormalized even-parity Peirce projector `P_+^{(2)}(X) = 1 + X²` (projected onto `X² = +1`). -/
def z4PeirceEven2 (X : B) : B := 1 + X * X

/-- Division-free 4-term Fateev–Zamolodchikov / Jones–Fendley `ℤ₄` parafermion braid generator
`2 U(X) = 1 + ζ X - X² + ζ X³`. -/
def z4BraidU2 (X ζ : B) : B :=
  1 + ζ * X - X * X + ζ * (X * (X * X))

/-- The 4-term `ℤ₄` quadratic Brown–Gauss sum `G₄(ζ) = ∑_{m=0}^3 ζ^{m²} = 1 + ζ + ζ⁴ + ζ⁹`. -/
def z4BrownGaussSum (ζ : B) : B :=
  1 + ζ + (ζ * ζ) * (ζ * ζ) + (((ζ * ζ) * (ζ * ζ)) * ((ζ * ζ) * (ζ * ζ))) * ζ

/-- The degree-3 truncated geometric / unipotent exponential gate `𝓔₄(x) = 1 + x + x² + x³`. -/
def unipotentGate4 (x : B) : B :=
  1 + x + x * x + x * (x * x)

/--
**Theorem 5g (`z4_peirce_braid_brown_gauss_and_nilpotent_unipotent_gate`):**
In any associative ring `[Ring B]`:
1. **Fateev–Zamolodchikov / Jones–Fendley `ℤ₄` Braid to 2-Sector Peirce Reduction:**
   - The 4-term `ℤ₄` braid generator `z4BraidU2 X ζ = 1 + ζ X - X² + ζ X³` collapses identically
     to the two-sector Peirce decomposition `(1 - X²) + ζ X (1 + X²)`.
   - Whenever `X⁴ = 1` (`(X * X) * (X * X) = 1`):
     - `z4PeirceOdd2 X` and `z4PeirceEven2 X` are orthogonal quasi-idempotents:
       `(1 - X²)² = 2 • (1 - X²)`, `(1 + X²)² = 2 • (1 + X²)`, and
       `(1 - X²)(1 + X²) = (1 + X²)(1 - X²) = 0`;
     - On the even sector `1 + X²`, the inverse cube `X³` equals `X`:
       `X * (X * X) * (1 + X²) = X * (1 + X²)`;
     - `z4BraidU2 X ζ` acts as `2 • id` on the odd sector (`z4BraidU2 X ζ * (1 - X²) = 2 • (1 - X²)`)
       and as `2 ζ X` on the even sector (`z4BraidU2 X ζ * (1 + X²) = 2 • (ζ * X * (1 + X²))`);
     - The unscaled sector squares sum to `4 • 1`:
       `(1 - X²) * (1 - X²) + (X * (1 + X²)) * (X * (1 + X²)) = (4 : ℤ) • (1 : B)`.
2. **`ℤ₄` Quadratic Brown–Gauss Sum & Chiral Central Charge `c₋ = 1`:**
   Whenever `ζ⁴ = -1` (`(ζ * ζ) * (ζ * ζ) = -1`, the 8th cyclotomic equation `Φ₈(ζ) = 0`),
   the `m = 0` and `m = 2` terms cancel (`1 + ζ⁴ = 0`) while `m = 1` and `m = 3` constructively
   interfere (`ζ + ζ⁹ = 2 • ζ`), yielding `z4BrownGaussSum ζ = (2 : ℤ) • ζ`
   (i.e. `G₄(ζ) / √4 = ζ = e^{2πi c₋ / 8}` with chiral central charge `c₋ = 1`).
3. **Nilpotent `η⁴ = 0` Unipotent Gate `𝓔₄(η)` & Cyclotomic Factorization `Φ₂(x)Φ₄(x)`:**
   For every `x : B`, `unipotentGate4 x = (1 + x) * (1 + x * x) = (1 + x * x) * (1 + x)` and
   `(1 - x) * unipotentGate4 x = unipotentGate4 x * (1 - x) = 1 - (x * x) * (x * x)`; hence
   whenever `x⁴ = 0` (`(x * x) * (x * x) = 0`), `unipotentGate4 x` is the exact two-sided inverse
   of `1 - x`.
-/
theorem z4_peirce_braid_brown_gauss_and_nilpotent_unipotent_gate
    (X ζ x : B) :
    (z4BraidU2 X ζ = z4PeirceOdd2 X + ζ * X * z4PeirceEven2 X ∧
     ((X * X) * (X * X) = 1 →
       z4PeirceOdd2 X * z4PeirceOdd2 X = (2 : ℤ) • z4PeirceOdd2 X ∧
       z4PeirceEven2 X * z4PeirceEven2 X = (2 : ℤ) • z4PeirceEven2 X ∧
       z4PeirceOdd2 X * z4PeirceEven2 X = 0 ∧
       z4PeirceEven2 X * z4PeirceOdd2 X = 0 ∧
       X * (X * X) * z4PeirceEven2 X = X * z4PeirceEven2 X ∧
       z4BraidU2 X ζ * z4PeirceOdd2 X = (2 : ℤ) • z4PeirceOdd2 X ∧
       z4BraidU2 X ζ * z4PeirceEven2 X = (2 : ℤ) • (ζ * X * z4PeirceEven2 X) ∧
       z4PeirceOdd2 X * z4PeirceOdd2 X +
         (X * z4PeirceEven2 X) * (X * z4PeirceEven2 X) = (4 : ℤ) • (1 : B))) ∧
    ((ζ * ζ) * (ζ * ζ) = -1 → z4BrownGaussSum ζ = (2 : ℤ) • ζ) ∧
    (unipotentGate4 x = (1 + x) * (1 + x * x) ∧
     unipotentGate4 x = (1 + x * x) * (1 + x) ∧
     (1 - x) * unipotentGate4 x = 1 - (x * x) * (x * x) ∧
     unipotentGate4 x * (1 - x) = 1 - (x * x) * (x * x) ∧
     ((x * x) * (x * x) = 0 →
       (1 - x) * unipotentGate4 x = 1 ∧ unipotentGate4 x * (1 - x) = 1)) := by
  have hBraidDecomp : z4BraidU2 X ζ = z4PeirceOdd2 X + ζ * X * z4PeirceEven2 X := by
    dsimp [z4BraidU2, z4PeirceOdd2, z4PeirceEven2]
    simp only [mul_add, mul_one, mul_assoc]
    abel
  refine ⟨⟨hBraidDecomp, ?_⟩, ?_, ?_⟩
  · intro hX4
    have hOddSq : z4PeirceOdd2 X * z4PeirceOdd2 X = (2 : ℤ) • z4PeirceOdd2 X := by
      dsimp [z4PeirceOdd2]
      simp only [sub_mul, mul_sub, one_mul, mul_one, hX4, two_zsmul]
      abel
    have hEvenSq : z4PeirceEven2 X * z4PeirceEven2 X = (2 : ℤ) • z4PeirceEven2 X := by
      dsimp [z4PeirceEven2]
      simp only [add_mul, mul_add, one_mul, mul_one, hX4, two_zsmul]
      abel
    have hOrthOE : z4PeirceOdd2 X * z4PeirceEven2 X = 0 := by
      dsimp [z4PeirceOdd2, z4PeirceEven2]
      simp only [sub_mul, mul_add, one_mul, mul_one, hX4]
      abel
    have hOrthEO : z4PeirceEven2 X * z4PeirceOdd2 X = 0 := by
      dsimp [z4PeirceOdd2, z4PeirceEven2]
      simp only [add_mul, mul_sub, one_mul, mul_one, hX4]
      abel
    have hCubeEven : X * (X * X) * z4PeirceEven2 X = X * z4PeirceEven2 X := by
      dsimp [z4PeirceEven2]
      have hX5 : X * (X * X) * (X * X) = X := by
        rw [mul_assoc X (X * X) (X * X), hX4, mul_one]
      simp only [mul_add, mul_one, hX5]
      abel
    have hActOdd : z4BraidU2 X ζ * z4PeirceOdd2 X = (2 : ℤ) • z4PeirceOdd2 X := by
      rw [hBraidDecomp, add_mul, mul_assoc (ζ * X), hOrthEO, mul_zero, add_zero, hOddSq]
    have hActEven : z4BraidU2 X ζ * z4PeirceEven2 X = (2 : ℤ) • (ζ * X * z4PeirceEven2 X) := by
      rw [hBraidDecomp, add_mul, hOrthOE, zero_add, mul_assoc (ζ * X), hEvenSq,
        two_zsmul, mul_add, two_zsmul]
    have hUnitSum :
        z4PeirceOdd2 X * z4PeirceOdd2 X +
          (X * z4PeirceEven2 X) * (X * z4PeirceEven2 X) = (4 : ℤ) • (1 : B) := by
      dsimp [z4PeirceOdd2, z4PeirceEven2]
      have hX1X3 : X * (X * (X * X)) = 1 := by
        calc
          X * (X * (X * X)) = (X * X) * (X * X) := by simp only [mul_assoc]
          _ = 1 := hX4
      have hX3X : X * (X * X) * X = 1 := by
        calc
          X * (X * X) * X = (X * X) * (X * X) := by simp only [mul_assoc]
          _ = 1 := hX4
      have hX3X3 : X * (X * X) * (X * (X * X)) = X * X := by
        calc
          X * (X * X) * (X * (X * X)) = ((X * X) * (X * X)) * (X * X) := by
            simp only [mul_assoc]
          _ = 1 * (X * X) := by rw [hX4]
          _ = X * X := one_mul (X * X)
      have hFour : (4 : ℤ) • (1 : B) = 1 + 1 + 1 + 1 := by
        change ((2 + 2 : ℤ) • (1 : B)) = 1 + 1 + 1 + 1
        rw [add_zsmul, two_zsmul]
        abel
      simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one,
        hX4, hX1X3, hX3X, hX3X3, hFour]
      abel
    exact ⟨hOddSq, hEvenSq, hOrthOE, hOrthEO, hCubeEven, hActOdd, hActEven, hUnitSum⟩
  · intro hZeta4
    dsimp [z4BrownGaussSum]
    simp only [hZeta4, neg_mul_neg, one_mul, two_zsmul]
    abel
  · have hFact1 : unipotentGate4 x = (1 + x) * (1 + x * x) := by
      dsimp [unipotentGate4]
      simp only [add_mul, mul_add, one_mul, mul_one]
      abel
    have hFact2 : unipotentGate4 x = (1 + x * x) * (1 + x) := by
      dsimp [unipotentGate4]
      simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc]
      abel
    have hTelL : (1 - x) * unipotentGate4 x = 1 - (x * x) * (x * x) := by
      dsimp [unipotentGate4]
      simp only [sub_mul, mul_add, one_mul, mul_one, mul_assoc]
      abel
    have hTelR : unipotentGate4 x * (1 - x) = 1 - (x * x) * (x * x) := by
      dsimp [unipotentGate4]
      simp only [mul_sub, add_mul, one_mul, mul_one, mul_assoc]
      abel
    refine ⟨hFact1, hFact2, hTelL, hTelR, ?_⟩
    intro hNil4
    rw [hTelL, hTelR, hNil4, sub_zero]
    exact ⟨rfl, rfl⟩

/-- Division-free integer 8th root of unity `ζ_real = P₂ Φ₂ + (1 - P₂) J₁ Φ₂` in any `[Ring B]`,
constructed from a Peirce idempotent `P₂² = P₂`, its bridge involution `Φ₂² = 1` swapping `P₂` and
`1 - P₂` (`Φ₂ P₂ = (1 - P₂) Φ₂`), and a commuting endogenous bivector `J₁² = -1`. -/
def zetaRealCarry (P₂ Φ₂ J₁ : B) : B :=
  P₂ * Φ₂ + (1 - P₂) * J₁ * Φ₂

/-- The endogenous elliptic bivector `J = S_P * Φ` of the DeWitt Split Tetractys in any `[Ring B]`,
formed as the product of the hyperbolic chiral involution `S_P` (`S_P² = 1`) and the Peirce bridge
involution `Φ` (`Φ² = 1`). -/
def tetractysJ (S_P Φ : B) : B :=
  S_P * Φ

/--
**Theorem 5h (`dewitt_tetractys_division_free_zeta8_and_sl2_triad`):**
Universal noncommutative ring formalization of the DeWitt Split Tetractys division-free 8th root of
unity `zetaRealCarry P₂ Φ₂ J₁` and the Row 1–4 $\mathfrak{sl}_2(\mathbb{R}) \cong \mathfrak{so}(2, 1)$
commutator triad over any `[Ring B]`:
1. **Division-Free Integer 8th Root of Unity (`zetaRealCarry P₂ Φ₂ J₁`):**
   Whenever `P₂ * P₂ = P₂`, `Φ₂ * Φ₂ = 1`, `Φ₂ * P₂ = (1 - P₂) * Φ₂`, `J₁ * J₁ = -1`,
   `J₁ * P₂ = P₂ * J₁`, and `J₁ * Φ₂ = Φ₂ * J₁`:
   - `Φ₂ * (1 - P₂) = P₂ * Φ₂`,
   - `zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁ = J₁` ($\zeta_{\text{real}}^2 = J_1$),
   - `(zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) * (zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) = -1` ($\zeta_{\text{real}}^4 = -1$),
   - `(((zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) * (zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁)) * ((zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) * (zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁))) = 1` ($\zeta_{\text{real}}^8 = +1$),
   - `z4BrownGaussSum (zetaRealCarry P₂ Φ₂ J₁) = (2 : ℤ) • zetaRealCarry P₂ Φ₂ J₁`.
2. **DeWitt Tetractys Row 3 $\mathfrak{sl}_2(\mathbb{R})$ Lie Bracket Triad:**
   Whenever `S_P * S_P = 1`, `Φ * Φ = 1`, and `Φ * S_P = -(S_P * Φ)`, the endogenous bivector
   `J := tetractysJ S_P Φ = S_P * Φ` satisfies:
   - `tetractysJ S_P Φ * tetractysJ S_P Φ = -1` ($J^2 = -1$),
   - `tetractysJ S_P Φ * Φ = S_P`, `Φ * tetractysJ S_P Φ = -S_P`, `S_P * tetractysJ S_P Φ = Φ`, and `tetractysJ S_P Φ * S_P = -Φ`,
   - `S_P * Φ - Φ * S_P = (2 : ℤ) • tetractysJ S_P Φ` ($[S_P, \Phi] = 2J$),
   - `tetractysJ S_P Φ * Φ - Φ * tetractysJ S_P Φ = (2 : ℤ) • S_P` ($[J, \Phi] = 2 S_P$, equivalently $[\Phi, J] = -2 S_P$),
   - `tetractysJ S_P Φ * S_P - S_P * tetractysJ S_P Φ = -((2 : ℤ) • Φ)` ($[J, S_P] = -2\Phi$).
-/
theorem dewitt_tetractys_division_free_zeta8_and_sl2_triad
    (P₂ Φ₂ J₁ S_P Φ : B)
    (hP2 : P₂ * P₂ = P₂) (hPhi2 : Φ₂ * Φ₂ = 1) (hSwap : Φ₂ * P₂ = (1 - P₂) * Φ₂)
    (hJ1 : J₁ * J₁ = -1) (hJ1P2 : J₁ * P₂ = P₂ * J₁) (hJ1Phi2 : J₁ * Φ₂ = Φ₂ * J₁)
    (hSP : S_P * S_P = 1) (hPhi : Φ * Φ = 1) (hAnti : Φ * S_P = -(S_P * Φ)) :
    (Φ₂ * (1 - P₂) = P₂ * Φ₂ ∧
     zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁ = J₁ ∧
     (zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) *
       (zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) = -1 ∧
     (((zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) *
         (zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁)) *
        ((zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) *
         (zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁))) = 1 ∧
     z4BrownGaussSum (zetaRealCarry P₂ Φ₂ J₁) = (2 : ℤ) • zetaRealCarry P₂ Φ₂ J₁) ∧
    (tetractysJ S_P Φ * tetractysJ S_P Φ = -1 ∧
     tetractysJ S_P Φ * Φ = S_P ∧
     Φ * tetractysJ S_P Φ = -S_P ∧
     S_P * tetractysJ S_P Φ = Φ ∧
     tetractysJ S_P Φ * S_P = -Φ ∧
     S_P * Φ - Φ * S_P = (2 : ℤ) • tetractysJ S_P Φ ∧
     tetractysJ S_P Φ * Φ - Φ * tetractysJ S_P Φ = (2 : ℤ) • S_P ∧
     tetractysJ S_P Φ * S_P - S_P * tetractysJ S_P Φ = -((2 : ℤ) • Φ)) := by
  have hSwapComp : Φ₂ * (1 - P₂) = P₂ * Φ₂ := by
    calc
      Φ₂ * (1 - P₂) = Φ₂ - Φ₂ * P₂ := by noncomm_ring
      _ = Φ₂ - (1 - P₂) * Φ₂ := by rw [hSwap]
      _ = P₂ * Φ₂ := by noncomm_ring
  have hP2Comp : P₂ * (1 - P₂) = 0 := by
    calc
      P₂ * (1 - P₂) = P₂ - P₂ * P₂ := by noncomm_ring
      _ = P₂ - P₂ := by rw [hP2]
      _ = 0 := sub_self P₂
  have hCompP2 : (1 - P₂) * P₂ = 0 := by
    calc
      (1 - P₂) * P₂ = P₂ - P₂ * P₂ := by noncomm_ring
      _ = P₂ - P₂ := by rw [hP2]
      _ = 0 := sub_self P₂
  have hCompSq : (1 - P₂) * (1 - P₂) = 1 - P₂ := by
    calc
      (1 - P₂) * (1 - P₂) = 1 - P₂ - (P₂ - P₂ * P₂) := by noncomm_ring
      _ = 1 - P₂ - (P₂ - P₂) := by rw [hP2]
      _ = 1 - P₂ := by abel
  have hJ1Comp : J₁ * (1 - P₂) = (1 - P₂) * J₁ := by
    calc
      J₁ * (1 - P₂) = J₁ - J₁ * P₂ := by noncomm_ring
      _ = J₁ - P₂ * J₁ := by rw [hJ1P2]
      _ = (1 - P₂) * J₁ := by noncomm_ring
  have hT1 : (P₂ * Φ₂) * (P₂ * Φ₂) = 0 := by
    calc
      (P₂ * Φ₂) * (P₂ * Φ₂) = P₂ * (Φ₂ * P₂) * Φ₂ := by noncomm_ring
      _ = P₂ * ((1 - P₂) * Φ₂) * Φ₂ := by rw [hSwap]
      _ = (P₂ * (1 - P₂)) * (Φ₂ * Φ₂) := by noncomm_ring
      _ = 0 * 1 := by rw [hP2Comp, hPhi2]
      _ = 0 := by simp
  have hT2 : (P₂ * Φ₂) * ((1 - P₂) * J₁ * Φ₂) = P₂ * J₁ := by
    calc
      (P₂ * Φ₂) * ((1 - P₂) * J₁ * Φ₂) = P₂ * (Φ₂ * (1 - P₂)) * J₁ * Φ₂ := by noncomm_ring
      _ = P₂ * (P₂ * Φ₂) * J₁ * Φ₂ := by rw [hSwapComp]
      _ = (P₂ * P₂) * (Φ₂ * J₁) * Φ₂ := by noncomm_ring
      _ = P₂ * (J₁ * Φ₂) * Φ₂ := by rw [hP2, ← hJ1Phi2]
      _ = P₂ * J₁ * (Φ₂ * Φ₂) := by noncomm_ring
      _ = P₂ * J₁ * 1 := by rw [hPhi2]
      _ = P₂ * J₁ := by simp
  have hT3 : ((1 - P₂) * J₁ * Φ₂) * (P₂ * Φ₂) = (1 - P₂) * J₁ := by
    calc
      ((1 - P₂) * J₁ * Φ₂) * (P₂ * Φ₂) = (1 - P₂) * J₁ * (Φ₂ * P₂) * Φ₂ := by noncomm_ring
      _ = (1 - P₂) * J₁ * ((1 - P₂) * Φ₂) * Φ₂ := by rw [hSwap]
      _ = (1 - P₂) * (J₁ * (1 - P₂)) * (Φ₂ * Φ₂) := by noncomm_ring
      _ = (1 - P₂) * ((1 - P₂) * J₁) * 1 := by rw [hJ1Comp, hPhi2]
      _ = ((1 - P₂) * (1 - P₂)) * J₁ := by noncomm_ring
      _ = (1 - P₂) * J₁ := by rw [hCompSq]
  have hT4 : ((1 - P₂) * J₁ * Φ₂) * ((1 - P₂) * J₁ * Φ₂) = 0 := by
    calc
      ((1 - P₂) * J₁ * Φ₂) * ((1 - P₂) * J₁ * Φ₂) =
        (1 - P₂) * J₁ * (Φ₂ * (1 - P₂)) * J₁ * Φ₂ := by noncomm_ring
      _ = (1 - P₂) * J₁ * (P₂ * Φ₂) * J₁ * Φ₂ := by rw [hSwapComp]
      _ = (1 - P₂) * (J₁ * P₂) * Φ₂ * J₁ * Φ₂ := by noncomm_ring
      _ = (1 - P₂) * (P₂ * J₁) * Φ₂ * J₁ * Φ₂ := by rw [hJ1P2]
      _ = ((1 - P₂) * P₂) * (J₁ * Φ₂ * J₁ * Φ₂) := by noncomm_ring
      _ = 0 * (J₁ * Φ₂ * J₁ * Φ₂) := by rw [hCompP2]
      _ = 0 := by simp
  have hZetaSq : zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁ = J₁ := by
    dsimp [zetaRealCarry]
    calc
      (P₂ * Φ₂ + (1 - P₂) * J₁ * Φ₂) * (P₂ * Φ₂ + (1 - P₂) * J₁ * Φ₂) =
        (P₂ * Φ₂) * (P₂ * Φ₂) +
        (P₂ * Φ₂) * ((1 - P₂) * J₁ * Φ₂) +
        ((1 - P₂) * J₁ * Φ₂) * (P₂ * Φ₂) +
        ((1 - P₂) * J₁ * Φ₂) * ((1 - P₂) * J₁ * Φ₂) := by noncomm_ring
      _ = 0 + P₂ * J₁ + (1 - P₂) * J₁ + 0 := by rw [hT1, hT2, hT3, hT4]
      _ = J₁ := by noncomm_ring
  have hZetaPow4 :
      (zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) *
        (zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) = -1 := by
    rw [hZetaSq, hJ1]
  have hZetaPow8 :
      (((zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) *
          (zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁)) *
         ((zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁) *
          (zetaRealCarry P₂ Φ₂ J₁ * zetaRealCarry P₂ Φ₂ J₁))) = 1 := by
    rw [hZetaPow4, neg_mul_neg, one_mul]
  have hGauss :
      z4BrownGaussSum (zetaRealCarry P₂ Φ₂ J₁) = (2 : ℤ) • zetaRealCarry P₂ Φ₂ J₁ :=
    (z4_peirce_braid_brown_gauss_and_nilpotent_unipotent_gate P₂ (zetaRealCarry P₂ Φ₂ J₁) P₂).2.1
      hZetaPow4
  have hJSq : tetractysJ S_P Φ * tetractysJ S_P Φ = -1 := by
    dsimp [tetractysJ]
    calc
      (S_P * Φ) * (S_P * Φ) = S_P * (Φ * S_P) * Φ := by noncomm_ring
      _ = S_P * (-(S_P * Φ)) * Φ := by rw [hAnti]
      _ = -(S_P * S_P) * (Φ * Φ) := by noncomm_ring
      _ = -1 * 1 := by rw [hSP, hPhi]
      _ = -1 := by noncomm_ring
  have hJPhi : tetractysJ S_P Φ * Φ = S_P := by
    dsimp [tetractysJ]
    calc
      (S_P * Φ) * Φ = S_P * (Φ * Φ) := by noncomm_ring
      _ = S_P * 1 := by rw [hPhi]
      _ = S_P := mul_one S_P
  have hPhiJ : Φ * tetractysJ S_P Φ = -S_P := by
    dsimp [tetractysJ]
    calc
      Φ * (S_P * Φ) = (Φ * S_P) * Φ := by noncomm_ring
      _ = -(S_P * Φ) * Φ := by rw [hAnti]
      _ = -S_P * (Φ * Φ) := by noncomm_ring
      _ = -S_P * 1 := by rw [hPhi]
      _ = -S_P := by noncomm_ring
  have hSPJ : S_P * tetractysJ S_P Φ = Φ := by
    dsimp [tetractysJ]
    calc
      S_P * (S_P * Φ) = (S_P * S_P) * Φ := by noncomm_ring
      _ = 1 * Φ := by rw [hSP]
      _ = Φ := one_mul Φ
  have hJSP : tetractysJ S_P Φ * S_P = -Φ := by
    dsimp [tetractysJ]
    calc
      (S_P * Φ) * S_P = S_P * (Φ * S_P) := by noncomm_ring
      _ = S_P * (-(S_P * Φ)) := by rw [hAnti]
      _ = -(S_P * S_P) * Φ := by noncomm_ring
      _ = -1 * Φ := by rw [hSP]
      _ = -Φ := by noncomm_ring
  have hComm1 : S_P * Φ - Φ * S_P = (2 : ℤ) • tetractysJ S_P Φ := by
    dsimp [tetractysJ]
    rw [hAnti, two_zsmul]
    abel
  have hComm2 : tetractysJ S_P Φ * Φ - Φ * tetractysJ S_P Φ = (2 : ℤ) • S_P := by
    rw [hJPhi, hPhiJ, two_zsmul]
    abel
  have hComm3 : tetractysJ S_P Φ * S_P - S_P * tetractysJ S_P Φ = -((2 : ℤ) • Φ) := by
    rw [hJSP, hSPJ, two_zsmul]
    abel
  exact ⟨⟨hSwapComp, hZetaSq, hZetaPow4, hZetaPow8, hGauss⟩,
    ⟨hJSq, hJPhi, hPhiJ, hSPJ, hJSP, hComm1, hComm2, hComm3⟩⟩

/--
**Theorem 5i (`tetractys_two_bit_10_plus_6_symplectic_and_chevalley_peirce_ladder`):**
Completes Row 4 of the DeWitt Split Tetractys and the two-bit $\mathcal{C}\ell(1,1) \otimes \mathcal{C}\ell(1,1)$
$\mathfrak{sp}(4, \mathbb{R})$ / Chevalley–Peirce nilpotent structure in `[Ring B]`:
1. **Pythagorean Tetractys & Two-Bit $16 = 10 \oplus 6$ Split:**
   `1 + 2 + 3 + 4 = 10`, `3 * 3 + 1 * 1 = 10`, `3 * 1 + 1 * 3 = 6`, and
   `(3 * 3 + 1 * 1) + (3 * 1 + 1 * 3) = 16`.
2. **Real Double-Bivector Boost Law & Symplectic Defining Relation:**
   - Whenever `J₁ * J₁ = -1`, `J₂ * J₂ = -1`, and `J₁ * J₂ = J₂ * J₁`, their product `J₁ * J₂` is a
     real hyperbolic involution `(J₁ * J₂) * (J₁ * J₂) = 1`;
   - Whenever `Ω * Ω = -1`, `X = Ω * S` satisfies `Ω * (Ω * S) + (- (S * Ω)) * Ω = 0`.
3. **Row 4 Nilpotent Chevalley–Peirce $\mathfrak{sl}_2(\mathbb{R})$ Ladder & First-Order Unipotent Bridges:**
   For any idempotent `P * P = P` and corner operators `A, C : B`, with grading involution
   `S_P = P - (1 - P)` and nilpotent rays `N_+ = conePlus P A`, `N_- = coneMinus P C`:
   - `(P - (1 - P)) * (P - (1 - P)) = 1`,
   - `(1 + conePlus P A) * (1 - conePlus P A) = 1` and
     `(1 + coneMinus P C) * (1 - coneMinus P C) = 1` (exact first-order unipotent inversion),
   - `(P - (1 - P)) * conePlus P A - conePlus P A * (P - (1 - P)) = (2 : ℤ) • conePlus P A`
     ($[S_P, N_+] = +2 N_+$),
   - `(P - (1 - P)) * coneMinus P C - coneMinus P C * (P - (1 - P)) = -((2 : ℤ) • coneMinus P C)`
     ($[S_P, N_-] = -2 N_-$).
-/
theorem tetractys_two_bit_10_plus_6_symplectic_and_chevalley_peirce_ladder
    (P A C J₁ J₂ Ω S : B) (hP : P * P = P)
    (hJ1 : J₁ * J₁ = -1) (hJ2 : J₂ * J₂ = -1) (hComm : J₁ * J₂ = J₂ * J₁)
    (hΩ : Ω * Ω = -1) :
    (1 + 2 + 3 + 4 = 10 ∧
     3 * 3 + 1 * 1 = 10 ∧
     3 * 1 + 1 * 3 = 6 ∧
     (3 * 3 + 1 * 1) + (3 * 1 + 1 * 3) = 16) ∧
    ((J₁ * J₂) * (J₁ * J₂) = 1 ∧
     Ω * (Ω * S) + (- (S * Ω)) * Ω = 0) ∧
    ((P - (1 - P)) * (P - (1 - P)) = 1 ∧
     (1 + InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A) *
       (1 - InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A) = 1 ∧
     (1 + InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) *
       (1 - InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) = 1 ∧
     (P - (1 - P)) * InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A -
       InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A * (P - (1 - P)) =
       (2 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A ∧
     (P - (1 - P)) * InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C -
       InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C * (P - (1 - P)) =
       -((2 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C)) := by
  have hBoost : (J₁ * J₂) * (J₁ * J₂) = 1 := by
    calc
      (J₁ * J₂) * (J₁ * J₂) = J₁ * (J₂ * J₁) * J₂ := by simp only [mul_assoc]
      _ = (J₁ * J₁) * (J₂ * J₂) := by rw [← hComm]; simp only [mul_assoc]
      _ = 1 := by rw [hJ1, hJ2, neg_mul_neg, one_mul]
  have hSymp : Ω * (Ω * S) + (- (S * Ω)) * Ω = 0 := by
    calc
      Ω * (Ω * S) + (- (S * Ω)) * Ω = (Ω * Ω) * S - S * (Ω * Ω) := by
        simp only [neg_mul, mul_assoc]; abel
      _ = (-1) * S - S * (-1) := by rw [hΩ]
      _ = 0 := by simp only [neg_mul, mul_neg, one_mul, mul_one]; abel
  have hSPSq : (P - (1 - P)) * (P - (1 - P)) = 1 := by
    calc
      (P - (1 - P)) * (P - (1 - P)) = 1 + (4 : ℤ) • (P * P - P) := by noncomm_ring
      _ = 1 := by rw [hP, sub_self, smul_zero, add_zero]
  have hPP := InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus_mul_conePlus hP A A
  have hMM := InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus_mul_coneMinus hP C C
  have hUnipPlus :
      (1 + InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A) *
        (1 - InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A) = 1 := by
    calc
      (1 + InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A) *
        (1 - InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A) =
        1 - InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A *
          InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A := by noncomm_ring
      _ = 1 := by rw [hPP, sub_zero]
  have hUnipMinus :
      (1 + InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) *
        (1 - InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) = 1 := by
    calc
      (1 + InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) *
        (1 - InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) =
        1 - InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C *
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C := by noncomm_ring
      _ = 1 := by rw [hMM, sub_zero]
  have hP_Nplus :
      P * InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A =
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus
    calc
      P * (P * A * (1 - P)) = (P * P) * A * (1 - P) := by noncomm_ring
      _ = P * A * (1 - P) := by rw [hP]
  have hNplus_P : InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A * P = 0 := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus
    calc
      (P * A * (1 - P)) * P = P * A * (P - P * P) := by noncomm_ring
      _ = P * A * (P - P) := by rw [hP]
      _ = 0 := by noncomm_ring
  have hP_Nminus : P * InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C = 0 := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus
    calc
      P * ((1 - P) * C * P) = (P - P * P) * C * P := by noncomm_ring
      _ = (P - P) * C * P := by rw [hP]
      _ = 0 := by noncomm_ring
  have hNminus_P :
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C * P =
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus
    calc
      ((1 - P) * C * P) * P = (1 - P) * C * (P * P) := by noncomm_ring
      _ = (1 - P) * C * P := by rw [hP]
  have hChevPlus :
      (P - (1 - P)) * InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A -
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A * (P - (1 - P)) =
        (2 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A := by
    calc
      (P - (1 - P)) * InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A -
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A * (P - (1 - P)) =
        (2 : ℤ) • (P * InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A) -
        (2 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A * P) := by noncomm_ring
      _ = (2 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A := by
        rw [hP_Nplus, hNplus_P, smul_zero, sub_zero]
  have hChevMinus :
      (P - (1 - P)) * InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C -
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C * (P - (1 - P)) =
        -((2 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) := by
    calc
      (P - (1 - P)) * InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C -
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C * (P - (1 - P)) =
        (2 : ℤ) • (P * InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) -
        (2 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C * P) := by noncomm_ring
      _ = -((2 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) := by
        rw [hP_Nminus, hNminus_P, smul_zero, zero_sub]
  exact ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨hBoost, hSymp⟩,
    ⟨hSPSq, hUnipPlus, hUnipMinus, hChevPlus, hChevMinus⟩⟩

/-- Endogenous timelike Tetractys generator `γ⁰ = J₁ = S₁ Φ₁` (`(γ⁰)² = -1`). -/
def tetractysGamma0 (S1 Φ1 : B) : B :=
  tetractysJ S1 Φ1

/-- Endogenous first spacelike Tetractys generator `γ¹ = S₁` (`(γ¹)² = +1`). -/
def tetractysGamma1 (S1 : B) : B :=
  S1

/-- Endogenous second spacelike Tetractys generator `γ² = Φ₁ S₂` (`(γ²))² = +1`). -/
def tetractysGamma2 (Φ1 S2 : B) : B :=
  Φ1 * S2

/-- Endogenous third spacelike Tetractys generator `γ³ = Φ₁ Φ₂` (`(γ³)² = +1`). -/
def tetractysGamma3 (Φ1 Φ2 : B) : B :=
  Φ1 * Φ2

/-- Endogenous 4D Tetractys Feynman slash operator
`tetractysSlash S₁ Φ₁ S₂ Φ₂ p₀ p₁ p₂ p₃ = p₀ • γ⁰ + p₁ • γ¹ + p₂ • γ² + p₃ • γ³`
constructed purely from the two-bit DeWitt Split Tetractys in any ring `B`. -/
def tetractysSlash (S1 Φ1 S2 Φ2 : B) (p0 p1 p2 p3 : ℤ) : B :=
  p0 • tetractysGamma0 S1 Φ1 + p1 • tetractysGamma1 S1 +
    p2 • tetractysGamma2 Φ1 S2 + p3 • tetractysGamma3 Φ1 Φ2

/-- Endogenous Tetractys Lorentz boost `K₀₁ = γ⁰ γ¹` (`= -Φ₁`). -/
def tetractysBoost01 (S1 Φ1 : B) : B :=
  tetractysGamma0 S1 Φ1 * tetractysGamma1 S1

/-- Endogenous Tetractys Lorentz boost `K₀₂ = γ⁰ γ²` (`= S₁ S₂`). -/
def tetractysBoost02 (S1 Φ1 S2 : B) : B :=
  tetractysGamma0 S1 Φ1 * tetractysGamma2 Φ1 S2

/-- Endogenous Tetractys Lorentz boost `K₀₃ = γ⁰ γ³` (`= S₁ Φ₂`). -/
def tetractysBoost03 (S1 Φ1 Φ2 : B) : B :=
  tetractysGamma0 S1 Φ1 * tetractysGamma3 Φ1 Φ2

/-- Endogenous Tetractys spatial rotation `J₁₂ = γ¹ γ²` (`= J₁ S₂`). -/
def tetractysRot12 (S1 Φ1 S2 : B) : B :=
  tetractysGamma1 S1 * tetractysGamma2 Φ1 S2

/-- Endogenous Tetractys spatial rotation `J₂₃ = γ² γ³` (`= J₂`). -/
def tetractysRot23 (Φ1 S2 Φ2 : B) : B :=
  tetractysGamma2 Φ1 S2 * tetractysGamma3 Φ1 Φ2

/-- Endogenous Tetractys spatial rotation `J₃₁ = γ³ γ¹` (`= -J₁ Φ₂`). -/
def tetractysRot31 (S1 Φ1 Φ2 : B) : B :=
  tetractysGamma3 Φ1 Φ2 * tetractysGamma1 S1

/-- Four-dimensional spacetime translation module in the nilpotent Peirce corner `N_+(P, -)`
constructed directly from the two-bit DeWitt Split Tetractys `(S₁, Φ₁, S₂, Φ₂)` in any ring `B`. -/
def tetractysCornerTranslation4 (P S1 Φ1 S2 Φ2 : B) (p0 p1 p2 p3 : ℤ) : B :=
  N_plus P (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3)

/--
**Theorem 4aa ($\mathfrak{SP}_1\text{–}\mathfrak{SP}_2$ — 4D Minkowski Clifford Algebra $(-, +, +, +)$, Mass-Shell Square Law, & Lorentz Bivector Factorization from the Two-Bit Real DeWitt Tetractys):**
Given two commuting real DeWitt Split Tetractys copies $(S_1, \Phi_1, J_1 = S_1 \Phi_1)$ and
$(S_2, \Phi_2, J_2 = S_2 \Phi_2)$ in any ring $B$, the four endogenous Tetractys operators
$$\gamma^0 = \mathtt{tetractysGamma0}\; S_1\; \Phi_1, \quad \gamma^1 = \mathtt{tetractysGamma1}\; S_1, \quad \gamma^2 = \mathtt{tetractysGamma2}\; \Phi_1\; S_2, \quad \gamma^3 = \mathtt{tetractysGamma3}\; \Phi_1\; \Phi_2$$
generate the 4D Minkowski Clifford algebra $\mathcal{C}\ell(3, 1)$ with metric signature $(-, +, +, +)$:
1. **Metric squares:** $(\gamma^0)^2 = -1$ and $(\gamma^1)^2 = (\gamma^2)^2 = (\gamma^3)^2 = +1$,
2. **All 6 distinct pairs strictly anticommute:** $\{\gamma^\mu, \gamma^\nu\} = 0$ for $0 \le \mu < \nu \le 3$,
3. **Endogenous 4D Minkowski Mass-Shell Square Law:**
   $$\mathtt{tetractysSlash}\; S_1\; \Phi_1\; S_2\; \Phi_2\; p_0\; p_1\; p_2\; p_3 * \mathtt{tetractysSlash}\; S_1\; \Phi_1\; S_2\; \Phi_2\; p_0\; p_1\; p_2\; p_3 = (-p_0^2 + p_1^2 + p_2^2 + p_3^2) \bullet (1 : B),$$
4. **Explicit Tetractys Factorization of the 6 Lorentz Bivectors:**
   $$K_{01} = -\Phi_1, \quad K_{02} = S_1 S_2, \quad K_{03} = S_1 \Phi_2, \quad J_{12} = J_1 S_2, \quad J_{23} = J_2, \quad J_{31} = -J_1 \Phi_2.$$
-/
theorem dewitt_tetractys_generates_4d_minkowski_clifford_algebra
    (S1 Φ1 S2 Φ2 : B) (p0 p1 p2 p3 : ℤ)
    (hS1 : S1 * S1 = 1) (hΦ1 : Φ1 * Φ1 = 1) (hAnti1 : S1 * Φ1 + Φ1 * S1 = 0)
    (hS2 : S2 * S2 = 1) (hΦ2 : Φ2 * Φ2 = 1) (hAnti2 : S2 * Φ2 + Φ2 * S2 = 0)
    (hCommS1S2 : S1 * S2 = S2 * S1) (hCommS1Φ2 : S1 * Φ2 = Φ2 * S1)
    (hCommΦ1S2 : Φ1 * S2 = S2 * Φ1) (hCommΦ1Φ2 : Φ1 * Φ2 = Φ2 * Φ1) :
    ((tetractysGamma0 S1 Φ1 * tetractysGamma0 S1 Φ1 = -1 ∧
      tetractysGamma1 S1 * tetractysGamma1 S1 = 1 ∧
      tetractysGamma2 Φ1 S2 * tetractysGamma2 Φ1 S2 = 1 ∧
      tetractysGamma3 Φ1 Φ2 * tetractysGamma3 Φ1 Φ2 = 1) ∧
     (tetractysGamma0 S1 Φ1 * tetractysGamma1 S1 +
        tetractysGamma1 S1 * tetractysGamma0 S1 Φ1 = 0 ∧
      tetractysGamma0 S1 Φ1 * tetractysGamma2 Φ1 S2 +
        tetractysGamma2 Φ1 S2 * tetractysGamma0 S1 Φ1 = 0 ∧
      tetractysGamma0 S1 Φ1 * tetractysGamma3 Φ1 Φ2 +
        tetractysGamma3 Φ1 Φ2 * tetractysGamma0 S1 Φ1 = 0 ∧
      tetractysGamma1 S1 * tetractysGamma2 Φ1 S2 +
        tetractysGamma2 Φ1 S2 * tetractysGamma1 S1 = 0 ∧
      tetractysGamma1 S1 * tetractysGamma3 Φ1 Φ2 +
        tetractysGamma3 Φ1 Φ2 * tetractysGamma1 S1 = 0 ∧
      tetractysGamma2 Φ1 S2 * tetractysGamma3 Φ1 Φ2 +
        tetractysGamma3 Φ1 Φ2 * tetractysGamma2 Φ1 S2 = 0)) ∧
    tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 =
      (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (1 : B) ∧
    (tetractysBoost01 S1 Φ1 = -Φ1 ∧
     tetractysBoost02 S1 Φ1 S2 = S1 * S2 ∧
     tetractysBoost03 S1 Φ1 Φ2 = S1 * Φ2 ∧
     tetractysRot12 S1 Φ1 S2 = tetractysJ S1 Φ1 * S2 ∧
     tetractysRot23 Φ1 S2 Φ2 = tetractysJ S2 Φ2 ∧
     tetractysRot31 S1 Φ1 Φ2 = -(tetractysJ S1 Φ1 * Φ2)) := by
  have hΦ1S1 : Φ1 * S1 = -(S1 * Φ1) := eq_neg_of_add_eq_zero_right hAnti1
  have hG0 : tetractysGamma0 S1 Φ1 * tetractysGamma0 S1 Φ1 = -1 := by
    unfold tetractysGamma0 tetractysJ
    calc
      (S1 * Φ1) * (S1 * Φ1) = S1 * (Φ1 * S1) * Φ1 := by noncomm_ring
      _ = S1 * (-(S1 * Φ1)) * Φ1 := by rw [hΦ1S1]
      _ = -((S1 * S1) * (Φ1 * Φ1)) := by noncomm_ring
      _ = -(1 * 1) := by rw [hS1, hΦ1]
      _ = -1 := by noncomm_ring
  have hG1 : tetractysGamma1 S1 * tetractysGamma1 S1 = 1 := hS1
  have hG2 : tetractysGamma2 Φ1 S2 * tetractysGamma2 Φ1 S2 = 1 := by
    unfold tetractysGamma2
    calc
      (Φ1 * S2) * (Φ1 * S2) = Φ1 * (S2 * Φ1) * S2 := by noncomm_ring
      _ = Φ1 * (Φ1 * S2) * S2 := by rw [← hCommΦ1S2]
      _ = (Φ1 * Φ1) * (S2 * S2) := by noncomm_ring
      _ = 1 * 1 := by rw [hΦ1, hS2]
      _ = 1 := by noncomm_ring
  have hG3 : tetractysGamma3 Φ1 Φ2 * tetractysGamma3 Φ1 Φ2 = 1 := by
    unfold tetractysGamma3
    calc
      (Φ1 * Φ2) * (Φ1 * Φ2) = Φ1 * (Φ2 * Φ1) * Φ2 := by noncomm_ring
      _ = Φ1 * (Φ1 * Φ2) * Φ2 := by rw [← hCommΦ1Φ2]
      _ = (Φ1 * Φ1) * (Φ2 * Φ2) := by noncomm_ring
      _ = 1 * 1 := by rw [hΦ1, hΦ2]
      _ = 1 := by noncomm_ring
  have h01 :
      tetractysGamma0 S1 Φ1 * tetractysGamma1 S1 +
        tetractysGamma1 S1 * tetractysGamma0 S1 Φ1 = 0 := by
    unfold tetractysGamma0 tetractysGamma1 tetractysJ
    calc
      (S1 * Φ1) * S1 + S1 * (S1 * Φ1) = S1 * (Φ1 * S1 + S1 * Φ1) := by noncomm_ring
      _ = S1 * (-(S1 * Φ1) + S1 * Φ1) := by rw [hΦ1S1]
      _ = 0 := by noncomm_ring
  have hΦJ : Φ1 * tetractysJ S1 Φ1 + tetractysJ S1 Φ1 * Φ1 = 0 := by
    unfold tetractysJ
    calc
      Φ1 * (S1 * Φ1) + (S1 * Φ1) * Φ1 = (Φ1 * S1 + S1 * Φ1) * Φ1 := by noncomm_ring
      _ = (-(S1 * Φ1) + S1 * Φ1) * Φ1 := by rw [hΦ1S1]
      _ = 0 := by noncomm_ring
  have hJS2 : S2 * tetractysJ S1 Φ1 = tetractysJ S1 Φ1 * S2 := by
    unfold tetractysJ
    calc
      S2 * (S1 * Φ1) = (S2 * S1) * Φ1 := by noncomm_ring
      _ = (S1 * S2) * Φ1 := by rw [← hCommS1S2]
      _ = S1 * (S2 * Φ1) := by noncomm_ring
      _ = S1 * (Φ1 * S2) := by rw [← hCommΦ1S2]
      _ = (S1 * Φ1) * S2 := by noncomm_ring
  have h02 :
      tetractysGamma0 S1 Φ1 * tetractysGamma2 Φ1 S2 +
        tetractysGamma2 Φ1 S2 * tetractysGamma0 S1 Φ1 = 0 := by
    unfold tetractysGamma0 tetractysGamma2
    calc
      tetractysJ S1 Φ1 * (Φ1 * S2) + (Φ1 * S2) * tetractysJ S1 Φ1 =
        tetractysJ S1 Φ1 * Φ1 * S2 + Φ1 * (S2 * tetractysJ S1 Φ1) := by noncomm_ring
      _ = tetractysJ S1 Φ1 * Φ1 * S2 + Φ1 * (tetractysJ S1 Φ1 * S2) := by rw [hJS2]
      _ = (Φ1 * tetractysJ S1 Φ1 + tetractysJ S1 Φ1 * Φ1) * S2 := by noncomm_ring
      _ = 0 * S2 := by rw [hΦJ]
      _ = 0 := by noncomm_ring
  have hJΦ2 : Φ2 * tetractysJ S1 Φ1 = tetractysJ S1 Φ1 * Φ2 := by
    unfold tetractysJ
    calc
      Φ2 * (S1 * Φ1) = (Φ2 * S1) * Φ1 := by noncomm_ring
      _ = (S1 * Φ2) * Φ1 := by rw [← hCommS1Φ2]
      _ = S1 * (Φ2 * Φ1) := by noncomm_ring
      _ = S1 * (Φ1 * Φ2) := by rw [← hCommΦ1Φ2]
      _ = (S1 * Φ1) * Φ2 := by noncomm_ring
  have h03 :
      tetractysGamma0 S1 Φ1 * tetractysGamma3 Φ1 Φ2 +
        tetractysGamma3 Φ1 Φ2 * tetractysGamma0 S1 Φ1 = 0 := by
    unfold tetractysGamma0 tetractysGamma3
    calc
      tetractysJ S1 Φ1 * (Φ1 * Φ2) + (Φ1 * Φ2) * tetractysJ S1 Φ1 =
        tetractysJ S1 Φ1 * Φ1 * Φ2 + Φ1 * (Φ2 * tetractysJ S1 Φ1) := by noncomm_ring
      _ = tetractysJ S1 Φ1 * Φ1 * Φ2 + Φ1 * (tetractysJ S1 Φ1 * Φ2) := by rw [hJΦ2]
      _ = (Φ1 * tetractysJ S1 Φ1 + tetractysJ S1 Φ1 * Φ1) * Φ2 := by noncomm_ring
      _ = 0 * Φ2 := by rw [hΦJ]
      _ = 0 := by noncomm_ring
  have h12 :
      tetractysGamma1 S1 * tetractysGamma2 Φ1 S2 +
        tetractysGamma2 Φ1 S2 * tetractysGamma1 S1 = 0 := by
    unfold tetractysGamma1 tetractysGamma2
    calc
      S1 * (Φ1 * S2) + (Φ1 * S2) * S1 =
        S1 * Φ1 * S2 + Φ1 * (S2 * S1) := by noncomm_ring
      _ = S1 * Φ1 * S2 + Φ1 * (S1 * S2) := by rw [← hCommS1S2]
      _ = (S1 * Φ1 + Φ1 * S1) * S2 := by noncomm_ring
      _ = 0 * S2 := by rw [hAnti1]
      _ = 0 := by noncomm_ring
  have h13 :
      tetractysGamma1 S1 * tetractysGamma3 Φ1 Φ2 +
        tetractysGamma3 Φ1 Φ2 * tetractysGamma1 S1 = 0 := by
    unfold tetractysGamma1 tetractysGamma3
    calc
      S1 * (Φ1 * Φ2) + (Φ1 * Φ2) * S1 =
        S1 * Φ1 * Φ2 + Φ1 * (Φ2 * S1) := by noncomm_ring
      _ = S1 * Φ1 * Φ2 + Φ1 * (S1 * Φ2) := by rw [← hCommS1Φ2]
      _ = (S1 * Φ1 + Φ1 * S1) * Φ2 := by noncomm_ring
      _ = 0 * Φ2 := by rw [hAnti1]
      _ = 0 := by noncomm_ring
  have h23 :
      tetractysGamma2 Φ1 S2 * tetractysGamma3 Φ1 Φ2 +
        tetractysGamma3 Φ1 Φ2 * tetractysGamma2 Φ1 S2 = 0 := by
    unfold tetractysGamma2 tetractysGamma3
    calc
      (Φ1 * S2) * (Φ1 * Φ2) + (Φ1 * Φ2) * (Φ1 * S2) =
        Φ1 * (S2 * Φ1) * Φ2 + Φ1 * (Φ2 * Φ1) * S2 := by noncomm_ring
      _ = Φ1 * (Φ1 * S2) * Φ2 + Φ1 * (Φ1 * Φ2) * S2 := by rw [← hCommΦ1S2, ← hCommΦ1Φ2]
      _ = (Φ1 * Φ1) * (S2 * Φ2 + Φ2 * S2) := by noncomm_ring
      _ = 1 * 0 := by rw [hΦ1, hAnti2]
      _ = 0 := by noncomm_ring
  have hShell :
      tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 =
        (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (1 : B) := by
    calc
      tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 =
        (p0 * p0) • (tetractysGamma0 S1 Φ1 * tetractysGamma0 S1 Φ1) +
        (p1 * p1) • (tetractysGamma1 S1 * tetractysGamma1 S1) +
        (p2 * p2) • (tetractysGamma2 Φ1 S2 * tetractysGamma2 Φ1 S2) +
        (p3 * p3) • (tetractysGamma3 Φ1 Φ2 * tetractysGamma3 Φ1 Φ2) +
        (p0 * p1) • (tetractysGamma0 S1 Φ1 * tetractysGamma1 S1 +
          tetractysGamma1 S1 * tetractysGamma0 S1 Φ1) +
        (p0 * p2) • (tetractysGamma0 S1 Φ1 * tetractysGamma2 Φ1 S2 +
          tetractysGamma2 Φ1 S2 * tetractysGamma0 S1 Φ1) +
        (p0 * p3) • (tetractysGamma0 S1 Φ1 * tetractysGamma3 Φ1 Φ2 +
          tetractysGamma3 Φ1 Φ2 * tetractysGamma0 S1 Φ1) +
        (p1 * p2) • (tetractysGamma1 S1 * tetractysGamma2 Φ1 S2 +
          tetractysGamma2 Φ1 S2 * tetractysGamma1 S1) +
        (p1 * p3) • (tetractysGamma1 S1 * tetractysGamma3 Φ1 Φ2 +
          tetractysGamma3 Φ1 Φ2 * tetractysGamma1 S1) +
        (p2 * p3) • (tetractysGamma2 Φ1 S2 * tetractysGamma3 Φ1 Φ2 +
          tetractysGamma3 Φ1 Φ2 * tetractysGamma2 Φ1 S2) := by
          unfold tetractysSlash
          noncomm_ring
          simp only [smul_add, smul_smul, mul_comm p1 p0, mul_comm p2 p0, mul_comm p3 p0,
            mul_comm p2 p1, mul_comm p3 p1, mul_comm p3 p2]
          abel
      _ = (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (1 : B) := by
          rw [hG0, hG1, hG2, hG3, h01, h02, h03, h12, h13, h23]
          simp only [sq, add_smul, neg_smul, smul_neg, smul_zero, add_zero]
  have hB01Fact : tetractysBoost01 S1 Φ1 = -Φ1 := by
    unfold tetractysBoost01 tetractysGamma0 tetractysGamma1 tetractysJ
    calc
      (S1 * Φ1) * S1 = S1 * (Φ1 * S1) := by noncomm_ring
      _ = S1 * (-(S1 * Φ1)) := by rw [hΦ1S1]
      _ = -((S1 * S1) * Φ1) := by noncomm_ring
      _ = -(1 * Φ1) := by rw [hS1]
      _ = -Φ1 := by noncomm_ring
  have hB02Fact : tetractysBoost02 S1 Φ1 S2 = S1 * S2 := by
    unfold tetractysBoost02 tetractysGamma0 tetractysGamma2 tetractysJ
    calc
      (S1 * Φ1) * (Φ1 * S2) = S1 * (Φ1 * Φ1) * S2 := by noncomm_ring
      _ = S1 * 1 * S2 := by rw [hΦ1]
      _ = S1 * S2 := by noncomm_ring
  have hB03Fact : tetractysBoost03 S1 Φ1 Φ2 = S1 * Φ2 := by
    unfold tetractysBoost03 tetractysGamma0 tetractysGamma3 tetractysJ
    calc
      (S1 * Φ1) * (Φ1 * Φ2) = S1 * (Φ1 * Φ1) * Φ2 := by noncomm_ring
      _ = S1 * 1 * Φ2 := by rw [hΦ1]
      _ = S1 * Φ2 := by noncomm_ring
  have hR12Fact : tetractysRot12 S1 Φ1 S2 = tetractysJ S1 Φ1 * S2 := by
    unfold tetractysRot12 tetractysGamma1 tetractysGamma2 tetractysJ
    noncomm_ring
  have hR23Fact : tetractysRot23 Φ1 S2 Φ2 = tetractysJ S2 Φ2 := by
    unfold tetractysRot23 tetractysGamma2 tetractysGamma3 tetractysJ
    calc
      (Φ1 * S2) * (Φ1 * Φ2) = Φ1 * (S2 * Φ1) * Φ2 := by noncomm_ring
      _ = Φ1 * (Φ1 * S2) * Φ2 := by rw [← hCommΦ1S2]
      _ = (Φ1 * Φ1) * (S2 * Φ2) := by noncomm_ring
      _ = 1 * (S2 * Φ2) := by rw [hΦ1]
      _ = S2 * Φ2 := by noncomm_ring
  have hR31Fact : tetractysRot31 S1 Φ1 Φ2 = -(tetractysJ S1 Φ1 * Φ2) := by
    unfold tetractysRot31 tetractysGamma3 tetractysGamma1 tetractysJ
    calc
      (Φ1 * Φ2) * S1 = Φ1 * (Φ2 * S1) := by noncomm_ring
      _ = Φ1 * (S1 * Φ2) := by rw [← hCommS1Φ2]
      _ = (Φ1 * S1) * Φ2 := by noncomm_ring
      _ = (-(S1 * Φ1)) * Φ2 := by rw [hΦ1S1]
      _ = -((S1 * Φ1) * Φ2) := by noncomm_ring
  exact ⟨⟨⟨hG0, hG1, hG2, hG3⟩, ⟨h01, h02, h03, h12, h13, h23⟩⟩,
    hShell,
    ⟨hB01Fact, hB02Fact, hB03Fact, hR12Fact, hR23Fact, hR31Fact⟩⟩

/-- Universal Clifford bivector commutator lemma `[X * Y, a • X + b • Y + c • Z + d • W] =
(2 * b) • (X * Y²) - (2 * a) • (X² * Y)` for pairwise anticommuting generators `(X, Y, Z, W)`
in any ring `B`. -/
lemma clifford_bivector_linear_comm (X Y Z W : B) (a b c d : ℤ)
    (hYX : Y * X = -(X * Y))
    (hZX : Z * X = -(X * Z)) (hYZ : Y * Z = -(Z * Y))
    (hWX : W * X = -(X * W)) (hYW : Y * W = -(W * Y)) :
    (X * Y) * (a • X + b • Y + c • Z + d • W) -
      (a • X + b • Y + c • Z + d • W) * (X * Y) =
      (2 * b) • (X * (Y * Y)) - (2 * a) • ((X * X) * Y) := by
  have hX : (X * Y) * X - X * (X * Y) = -((2 : ℤ) • ((X * X) * Y)) := by
    calc
      (X * Y) * X - X * (X * Y) = X * (Y * X) - (X * X) * Y := by noncomm_ring
      _ = X * (-(X * Y)) - (X * X) * Y := by rw [hYX]
      _ = -((2 : ℤ) • ((X * X) * Y)) := by noncomm_ring
  have hY : (X * Y) * Y - Y * (X * Y) = (2 : ℤ) • (X * (Y * Y)) := by
    calc
      (X * Y) * Y - Y * (X * Y) = X * (Y * Y) - (Y * X) * Y := by noncomm_ring
      _ = X * (Y * Y) - (-(X * Y)) * Y := by rw [hYX]
      _ = (2 : ℤ) • (X * (Y * Y)) := by noncomm_ring
  have hZ : (X * Y) * Z - Z * (X * Y) = 0 := by
    calc
      (X * Y) * Z - Z * (X * Y) = X * (Y * Z) - (Z * X) * Y := by noncomm_ring
      _ = X * (-(Z * Y)) - (-(X * Z)) * Y := by rw [hYZ, hZX]
      _ = 0 := by noncomm_ring
  have hW : (X * Y) * W - W * (X * Y) = 0 := by
    calc
      (X * Y) * W - W * (X * Y) = X * (Y * W) - (W * X) * Y := by noncomm_ring
      _ = X * (-(W * Y)) - (-(X * W)) * Y := by rw [hYW, hWX]
      _ = 0 := by noncomm_ring
  calc
    (X * Y) * (a • X + b • Y + c • Z + d • W) -
      (a • X + b • Y + c • Z + d • W) * (X * Y) =
      a • ((X * Y) * X - X * (X * Y)) + b • ((X * Y) * Y - Y * (X * Y)) +
      c • ((X * Y) * Z - Z * (X * Y)) + d • ((X * Y) * W - W * (X * Y)) := by
        noncomm_ring
        simp only [smul_add, smul_smul, neg_smul, smul_neg, neg_mul, one_mul, mul_one]
        abel
    _ = a • (-((2 : ℤ) • ((X * X) * Y))) + b • ((2 : ℤ) • (X * (Y * Y))) +
        c • (0 : B) + d • (0 : B) := by rw [hX, hY, hZ, hW]
    _ = (2 * b) • (X * (Y * Y)) - (2 * a) • ((X * X) * Y) := by
        simp only [smul_neg, smul_smul, smul_zero, add_zero, mul_comm a 2, mul_comm b 2]
        abel

/--
Diagonal Peirce stabilizer generator $L_P(M) = P M P + (1 - P) M (1 - P)$ representing the
Lorentz subalgebra $\mathfrak{so}(3, 1)$ acting on the primal/dual Peirce split $(P, 1 - P)$.
-/
def poincareLorentz (P M : B) : B :=
  P * M * P + (1 - P) * M * (1 - P)

/--
**Theorem 4bb ($\mathfrak{SP}_3\text{–}\mathfrak{SP}_4$ — 10D Poincaré Algebra $\mathfrak{iso}(3, 1) = \mathfrak{so}(3, 1) \ltimes \mathbb{R}^{3,1}$ via Peirce Contraction):**
For any idempotent $P^2 = P$ in a ring $B$:
1. **10D Poincaré dimension budget:** $6 + 4 = 10$ ($6$ Lorentz bivectors $\gamma^{\mu\nu}$ + $4$ nilpotent Peirce translations),
2. **Abelian spacetime translations in the primal Peirce nilpotent cone $N_+(P, p) = P p (1 - P)$:**
   $$N_+(P, p)\,N_+(P, q) = 0, \qquad [N_+(P, p), N_+(P, q)] = 0, \qquad (1 + N_+(P, p))(1 + N_+(P, q)) = 1 + N_+(P, p + q),$$
3. **Lorentz-translation semidirect commutator & universal Peirce corner preservation:**
   $$[L_P(M), N_+(P, p)] = P M N_+(P, p) - N_+(P, p) M (1 - P),$$
   $$N_+(P, [L_P(M), N_+(P, p)]) = [L_P(M), N_+(P, p)],$$
   and whenever $M$ commutes with the conformal infinity projector ($P M = M P$),
   $$[L_P(M), N_+(P, p)] = N_+(P, [M, p]),$$
4. **Super-Poincaré graded Jacobi identity:** $[Q, \{Q, Q\}] = Q(Q^2 + Q^2) - (Q^2 + Q^2)Q = 0$.
-/
theorem poincare_translations_commute_and_lorentz_covariance
    (P M p q Q : B) (hP : P * P = P) :
    6 + 4 = 10 ∧
    (N_plus P p * N_plus P q = 0 ∧
     N_plus P p * N_plus P q - N_plus P q * N_plus P p = 0 ∧
     (1 + N_plus P p) * (1 + N_plus P q) = 1 + N_plus P (p + q)) ∧
    (poincareLorentz P M * N_plus P p - N_plus P p * poincareLorentz P M =
       P * M * N_plus P p - N_plus P p * M * (1 - P) ∧
     N_plus P (poincareLorentz P M * N_plus P p - N_plus P p * poincareLorentz P M) =
       poincareLorentz P M * N_plus P p - N_plus P p * poincareLorentz P M ∧
     (P * M = M * P →
       poincareLorentz P M * N_plus P p - N_plus P p * poincareLorentz P M =
         N_plus P (M * p - p * M))) ∧
    Q * (Q * Q + Q * Q) - (Q * Q + Q * Q) * Q = 0 := by
  have hPQ : N_plus P p * N_plus P q = 0 := by
    unfold N_plus
    calc
      (P * p * (1 - P)) * (P * q * (1 - P)) =
        P * p * (P - P * P) * q * (1 - P) := by noncomm_ring
      _ = P * p * (P - P) * q * (1 - P) := by rw [hP]
      _ = 0 := by noncomm_ring
  have hQP : N_plus P q * N_plus P p = 0 := by
    unfold N_plus
    calc
      (P * q * (1 - P)) * (P * p * (1 - P)) =
        P * q * (P - P * P) * p * (1 - P) := by noncomm_ring
      _ = P * q * (P - P) * p * (1 - P) := by rw [hP]
      _ = 0 := by noncomm_ring
  have hComm : N_plus P p * N_plus P q - N_plus P q * N_plus P p = 0 := by
    rw [hPQ, hQP, sub_zero]
  have hGroup : (1 + N_plus P p) * (1 + N_plus P q) = 1 + N_plus P (p + q) := by
    calc
      (1 + N_plus P p) * (1 + N_plus P q) =
        1 + N_plus P p + N_plus P q + N_plus P p * N_plus P q := by noncomm_ring
      _ = 1 + N_plus P p + N_plus P q + 0 := by rw [hPQ]
      _ = 1 + N_plus P (p + q) := by
        unfold N_plus
        noncomm_ring
  have hLeft : poincareLorentz P M * N_plus P p = P * M * N_plus P p := by
    unfold poincareLorentz N_plus
    calc
      (P * M * P + (1 - P) * M * (1 - P)) * (P * p * (1 - P)) =
        P * M * (P * P) * p * (1 - P) +
        (1 - P) * M * (P - P * P) * p * (1 - P) := by noncomm_ring
      _ = P * M * P * p * (1 - P) +
        (1 - P) * M * (P - P) * p * (1 - P) := by rw [hP]
      _ = P * M * (P * p * (1 - P)) := by noncomm_ring
  have hRight : N_plus P p * poincareLorentz P M = N_plus P p * M * (1 - P) := by
    unfold poincareLorentz N_plus
    calc
      (P * p * (1 - P)) * (P * M * P + (1 - P) * M * (1 - P)) =
        P * p * (P - P * P) * M * P +
        P * p * (1 - P - P + P * P) * M * (1 - P) := by noncomm_ring
      _ = P * p * (P - P) * M * P +
        P * p * (1 - P - P + P) * M * (1 - P) := by rw [hP]
      _ = (P * p * (1 - P)) * M * (1 - P) := by noncomm_ring
  have hLor :
      poincareLorentz P M * N_plus P p - N_plus P p * poincareLorentz P M =
        P * M * N_plus P p - N_plus P p * M * (1 - P) := by
    rw [hLeft, hRight]
  have hLorCorner :
      N_plus P (poincareLorentz P M * N_plus P p - N_plus P p * poincareLorentz P M) =
        poincareLorentz P M * N_plus P p - N_plus P p * poincareLorentz P M := by
    rw [hLor]
    unfold N_plus
    calc
      P * (P * M * (P * p * (1 - P)) - (P * p * (1 - P)) * M * (1 - P)) * (1 - P) =
        (P * P) * M * (P * p * (1 - P - P + P * P)) -
        (P * P) * p * (1 - P) * M * (1 - P - P + P * P) := by noncomm_ring
      _ = P * M * (P * p * (1 - P - P + P)) -
        P * p * (1 - P) * M * (1 - P - P + P) := by rw [hP]
      _ = P * M * (P * p * (1 - P)) - (P * p * (1 - P)) * M * (1 - P) := by noncomm_ring
  have hLorStab :
      P * M = M * P →
        poincareLorentz P M * N_plus P p - N_plus P p * poincareLorentz P M =
          N_plus P (M * p - p * M) := by
    intro hMP
    rw [hLor]
    unfold N_plus
    calc
      P * M * (P * p * (1 - P)) - (P * p * (1 - P)) * M * (1 - P) =
        P * (M * P) * p * (1 - P) - P * p * (M - P * M) * (1 - P) := by noncomm_ring
      _ = P * (P * M) * p * (1 - P) - P * p * (M - M * P) * (1 - P) := by rw [hMP]
      _ = (P * P) * M * p * (1 - P) - P * p * M * (1 - P - P + P * P) := by noncomm_ring
      _ = P * M * p * (1 - P) - P * p * M * (1 - P - P + P) := by rw [hP]
      _ = P * (M * p - p * M) * (1 - P) := by noncomm_ring
  exact ⟨by decide, ⟨hPQ, hComm, hGroup⟩, ⟨hLor, hLorCorner, hLorStab⟩, by noncomm_ring⟩

/--
**Theorem 4cc ($\mathfrak{SP}_3\text{–}\mathfrak{SP}_4$ — Endogenous 4-Dimensional Tetractys Translation Module in the Peirce Corner & Corner-Preserving 6-Generator Lorentz Action):**
Constructed purely from two commuting DeWitt Split Tetractys copies $(S_1, \Phi_1, J_1)$ and
$(S_2, \Phi_2, J_2)$ in any ring $B$ (with zero coordinate Dirac matrices):
1. **Four-Dimensional Translation Module in the Peirce Corner (`tetractysCornerTranslation4`):**
   For any idempotent $P^2 = P$:
   - Corner invariance: $N_+(P, T(p)) = T(p)$,
   - 4-basis decomposition: $T(p_0, p_1, p_2, p_3) = p_0 \bullet N_+(P, \gamma^0) + p_1 \bullet N_+(P, \gamma^1) + p_2 \bullet N_+(P, \gamma^2) + p_3 \bullet N_+(P, \gamma^3)$,
   - Module additivity: $T(p + q) = T(p) + T(q)$,
   - Abelian nilpotent multiplication: $T(p) \, T(q) = 0$.
2. **Corner-Preserving 6-Generator Lorentz Action (`Block2.lorentzDiag` on `Block2.cornerEmbed`):**
   All 6 endogenous Tetractys Lorentz bivectors $(K_{01}, K_{02}, K_{03}, J_{12}, J_{23}, J_{31})$
   preserve the 4-dimensional Peirce translation corner and transform $(p_0, p_1, p_2, p_3)$ by
   the exact 3 hyperbolic Lorentz boosts and 3 spatial rotations.
-/
theorem tetractys_corner_4d_translation_module_and_lorentz_action
    (P S1 Φ1 S2 Φ2 : B) (p0 p1 p2 p3 q0 q1 q2 q3 : ℤ)
    (hP : P * P = P)
    (hS1 : S1 * S1 = 1) (hΦ1 : Φ1 * Φ1 = 1) (hAnti1 : S1 * Φ1 + Φ1 * S1 = 0)
    (hS2 : S2 * S2 = 1) (hΦ2 : Φ2 * Φ2 = 1) (hAnti2 : S2 * Φ2 + Φ2 * S2 = 0)
    (hCommS1S2 : S1 * S2 = S2 * S1) (hCommS1Φ2 : S1 * Φ2 = Φ2 * S1)
    (hCommΦ1S2 : Φ1 * S2 = S2 * Φ1) (hCommΦ1Φ2 : Φ1 * Φ2 = Φ2 * Φ1) :
    (N_plus P (tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 p0 p1 p2 p3) =
       tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 p0 p1 p2 p3 ∧
     tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 p0 p1 p2 p3 =
       p0 • N_plus P (tetractysGamma0 S1 Φ1) +
       p1 • N_plus P (tetractysGamma1 S1) +
       p2 • N_plus P (tetractysGamma2 Φ1 S2) +
       p3 • N_plus P (tetractysGamma3 Φ1 Φ2) ∧
     tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 (p0 + q0) (p1 + q1) (p2 + q2) (p3 + q3) =
       tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 p0 p1 p2 p3 +
       tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 q0 q1 q2 q3 ∧
     tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 p0 p1 p2 p3 *
       tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 q0 q1 q2 q3 = 0) ∧
    (Block2.lorentzDiag (tetractysBoost01 S1 Φ1) *
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
         Block2.lorentzDiag (tetractysBoost01 S1 Φ1) =
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 (2 * p1) (2 * p0) 0 0) ∧
     Block2.lorentzDiag (tetractysBoost02 S1 Φ1 S2) *
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
         Block2.lorentzDiag (tetractysBoost02 S1 Φ1 S2) =
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 (2 * p2) 0 (2 * p0) 0) ∧
     Block2.lorentzDiag (tetractysBoost03 S1 Φ1 Φ2) *
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
         Block2.lorentzDiag (tetractysBoost03 S1 Φ1 Φ2) =
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 (2 * p3) 0 0 (2 * p0)) ∧
     Block2.lorentzDiag (tetractysRot12 S1 Φ1 S2) *
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
         Block2.lorentzDiag (tetractysRot12 S1 Φ1 S2) =
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 0 (2 * p2) (-2 * p1) 0) ∧
     Block2.lorentzDiag (tetractysRot23 Φ1 S2 Φ2) *
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
         Block2.lorentzDiag (tetractysRot23 Φ1 S2 Φ2) =
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 0 0 (2 * p3) (-2 * p2)) ∧
     Block2.lorentzDiag (tetractysRot31 S1 Φ1 Φ2) *
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
         Block2.lorentzDiag (tetractysRot31 S1 Φ1 Φ2) =
       Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 0 (-2 * p3) 0 (2 * p1))) := by
  have hCl :=
    dewitt_tetractys_generates_4d_minkowski_clifford_algebra
      S1 Φ1 S2 Φ2 p0 p1 p2 p3 hS1 hΦ1 hAnti1 hS2 hΦ2 hAnti2
      hCommS1S2 hCommS1Φ2 hCommΦ1S2 hCommΦ1Φ2
  have hG0 := hCl.1.1.1
  have hG1 := hCl.1.1.2.1
  have hG2 := hCl.1.1.2.2.1
  have hG3 := hCl.1.1.2.2.2
  have h10 : tetractysGamma1 S1 * tetractysGamma0 S1 Φ1 =
      -(tetractysGamma0 S1 Φ1 * tetractysGamma1 S1) :=
    eq_neg_of_add_eq_zero_right hCl.1.2.1
  have h01' : tetractysGamma0 S1 Φ1 * tetractysGamma1 S1 =
      -(tetractysGamma1 S1 * tetractysGamma0 S1 Φ1) :=
    eq_neg_of_add_eq_zero_left hCl.1.2.1
  have h20 : tetractysGamma2 Φ1 S2 * tetractysGamma0 S1 Φ1 =
      -(tetractysGamma0 S1 Φ1 * tetractysGamma2 Φ1 S2) :=
    eq_neg_of_add_eq_zero_right hCl.1.2.2.1
  have h02' : tetractysGamma0 S1 Φ1 * tetractysGamma2 Φ1 S2 =
      -(tetractysGamma2 Φ1 S2 * tetractysGamma0 S1 Φ1) :=
    eq_neg_of_add_eq_zero_left hCl.1.2.2.1
  have h30 : tetractysGamma3 Φ1 Φ2 * tetractysGamma0 S1 Φ1 =
      -(tetractysGamma0 S1 Φ1 * tetractysGamma3 Φ1 Φ2) :=
    eq_neg_of_add_eq_zero_right hCl.1.2.2.2.1
  have h03' : tetractysGamma0 S1 Φ1 * tetractysGamma3 Φ1 Φ2 =
      -(tetractysGamma3 Φ1 Φ2 * tetractysGamma0 S1 Φ1) :=
    eq_neg_of_add_eq_zero_left hCl.1.2.2.2.1
  have h21 : tetractysGamma2 Φ1 S2 * tetractysGamma1 S1 =
      -(tetractysGamma1 S1 * tetractysGamma2 Φ1 S2) :=
    eq_neg_of_add_eq_zero_right hCl.1.2.2.2.2.1
  have h12' : tetractysGamma1 S1 * tetractysGamma2 Φ1 S2 =
      -(tetractysGamma2 Φ1 S2 * tetractysGamma1 S1) :=
    eq_neg_of_add_eq_zero_left hCl.1.2.2.2.2.1
  have h31 : tetractysGamma3 Φ1 Φ2 * tetractysGamma1 S1 =
      -(tetractysGamma1 S1 * tetractysGamma3 Φ1 Φ2) :=
    eq_neg_of_add_eq_zero_right hCl.1.2.2.2.2.2.1
  have h13' : tetractysGamma1 S1 * tetractysGamma3 Φ1 Φ2 =
      -(tetractysGamma3 Φ1 Φ2 * tetractysGamma1 S1) :=
    eq_neg_of_add_eq_zero_left hCl.1.2.2.2.2.2.1
  have h32 : tetractysGamma3 Φ1 Φ2 * tetractysGamma2 Φ1 S2 =
      -(tetractysGamma2 Φ1 S2 * tetractysGamma3 Φ1 Φ2) :=
    eq_neg_of_add_eq_zero_right hCl.1.2.2.2.2.2.2
  have h23' : tetractysGamma2 Φ1 S2 * tetractysGamma3 Φ1 Φ2 =
      -(tetractysGamma3 Φ1 Φ2 * tetractysGamma2 Φ1 S2) :=
    eq_neg_of_add_eq_zero_left hCl.1.2.2.2.2.2.2
  have hCornerIdem :
      N_plus P (tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 p0 p1 p2 p3) =
        tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 p0 p1 p2 p3 := by
    unfold tetractysCornerTranslation4 N_plus
    calc
      P * (P * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * (1 - P)) * (1 - P) =
        (P * P) * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * (1 - P - P + P * P) := by noncomm_ring
      _ = P * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * (1 - P - P + P) := by rw [hP]
      _ = P * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * (1 - P) := by noncomm_ring
  have hCornerBasis :
      tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 p0 p1 p2 p3 =
        p0 • N_plus P (tetractysGamma0 S1 Φ1) +
        p1 • N_plus P (tetractysGamma1 S1) +
        p2 • N_plus P (tetractysGamma2 Φ1 S2) +
        p3 • N_plus P (tetractysGamma3 Φ1 Φ2) := by
    unfold tetractysCornerTranslation4 tetractysSlash N_plus
    noncomm_ring
    simp only [smul_add, smul_smul, neg_mul, one_mul, mul_neg, mul_one]
    abel
  have hCornerAdd :
      tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 (p0 + q0) (p1 + q1) (p2 + q2) (p3 + q3) =
        tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 p0 p1 p2 p3 +
        tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 q0 q1 q2 q3 := by
    unfold tetractysCornerTranslation4 tetractysSlash N_plus
    noncomm_ring
    simp only [add_smul, smul_add, smul_smul, neg_mul, one_mul]
    abel
  have hCornerNilp :
      tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 p0 p1 p2 p3 *
        tetractysCornerTranslation4 P S1 Φ1 S2 Φ2 q0 q1 q2 q3 = 0 :=
    (poincare_translations_commute_and_lorentz_covariance P P
      (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3)
      (tetractysSlash S1 Φ1 S2 Φ2 q0 q1 q2 q3) P hP).2.1.1
  have hB01 :
      tetractysBoost01 S1 Φ1 * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 -
        tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * tetractysBoost01 S1 Φ1 =
        tetractysSlash S1 Φ1 S2 Φ2 (2 * p1) (2 * p0) 0 0 := by
    unfold tetractysBoost01 tetractysSlash
    rw [clifford_bivector_linear_comm (tetractysGamma0 S1 Φ1) (tetractysGamma1 S1)
      (tetractysGamma2 Φ1 S2) (tetractysGamma3 Φ1 Φ2) p0 p1 p2 p3
      h10 h20 h12' h30 h13', hG0, hG1]
    noncomm_ring
    simp only [smul_smul, neg_smul, smul_neg, zero_smul, one_smul, neg_mul, one_mul]
    abel
  have hB02 :
      tetractysBoost02 S1 Φ1 S2 * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 -
        tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * tetractysBoost02 S1 Φ1 S2 =
        tetractysSlash S1 Φ1 S2 Φ2 (2 * p2) 0 (2 * p0) 0 := by
    have hPerm :
        tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 =
          p0 • tetractysGamma0 S1 Φ1 + p2 • tetractysGamma2 Φ1 S2 +
            p1 • tetractysGamma1 S1 + p3 • tetractysGamma3 Φ1 Φ2 := by
      unfold tetractysSlash; abel
    rw [hPerm]
    unfold tetractysBoost02
    rw [clifford_bivector_linear_comm (tetractysGamma0 S1 Φ1) (tetractysGamma2 Φ1 S2)
      (tetractysGamma1 S1) (tetractysGamma3 Φ1 Φ2) p0 p2 p1 p3
      h20 h10 h21 h30 h23', hG0, hG2]
    unfold tetractysSlash
    noncomm_ring
    simp only [smul_smul, neg_smul, smul_neg, zero_smul, one_smul, neg_mul, one_mul]
    abel
  have hB03 :
      tetractysBoost03 S1 Φ1 Φ2 * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 -
        tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * tetractysBoost03 S1 Φ1 Φ2 =
        tetractysSlash S1 Φ1 S2 Φ2 (2 * p3) 0 0 (2 * p0) := by
    have hPerm :
        tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 =
          p0 • tetractysGamma0 S1 Φ1 + p3 • tetractysGamma3 Φ1 Φ2 +
            p1 • tetractysGamma1 S1 + p2 • tetractysGamma2 Φ1 S2 := by
      unfold tetractysSlash; abel
    rw [hPerm]
    unfold tetractysBoost03
    rw [clifford_bivector_linear_comm (tetractysGamma0 S1 Φ1) (tetractysGamma3 Φ1 Φ2)
      (tetractysGamma1 S1) (tetractysGamma2 Φ1 S2) p0 p3 p1 p2
      h30 h10 h31 h20 h32, hG0, hG3]
    unfold tetractysSlash
    noncomm_ring
    simp only [smul_smul, neg_smul, smul_neg, zero_smul, one_smul, neg_mul, one_mul]
    abel
  have hR12 :
      tetractysRot12 S1 Φ1 S2 * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 -
        tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * tetractysRot12 S1 Φ1 S2 =
        tetractysSlash S1 Φ1 S2 Φ2 0 (2 * p2) (-2 * p1) 0 := by
    have hPerm :
        tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 =
          p1 • tetractysGamma1 S1 + p2 • tetractysGamma2 Φ1 S2 +
            p0 • tetractysGamma0 S1 Φ1 + p3 • tetractysGamma3 Φ1 Φ2 := by
      unfold tetractysSlash; abel
    rw [hPerm]
    unfold tetractysRot12
    rw [clifford_bivector_linear_comm (tetractysGamma1 S1) (tetractysGamma2 Φ1 S2)
      (tetractysGamma0 S1 Φ1) (tetractysGamma3 Φ1 Φ2) p1 p2 p0 p3
      h21 h01' h20 h31 h23', hG1, hG2]
    unfold tetractysSlash
    noncomm_ring
    simp only [smul_smul, neg_smul, zero_smul, neg_mul, one_mul]
    abel
  have hR23 :
      tetractysRot23 Φ1 S2 Φ2 * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 -
        tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * tetractysRot23 Φ1 S2 Φ2 =
        tetractysSlash S1 Φ1 S2 Φ2 0 0 (2 * p3) (-2 * p2) := by
    have hPerm :
        tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 =
          p2 • tetractysGamma2 Φ1 S2 + p3 • tetractysGamma3 Φ1 Φ2 +
            p0 • tetractysGamma0 S1 Φ1 + p1 • tetractysGamma1 S1 := by
      unfold tetractysSlash; abel
    rw [hPerm]
    unfold tetractysRot23
    rw [clifford_bivector_linear_comm (tetractysGamma2 Φ1 S2) (tetractysGamma3 Φ1 Φ2)
      (tetractysGamma0 S1 Φ1) (tetractysGamma1 S1) p2 p3 p0 p1
      h32 h02' h30 h12' h31, hG2, hG3]
    unfold tetractysSlash
    noncomm_ring
    simp only [smul_smul, neg_smul, zero_smul, neg_mul, one_mul]
    abel
  have hR31 :
      tetractysRot31 S1 Φ1 Φ2 * tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 -
        tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 * tetractysRot31 S1 Φ1 Φ2 =
        tetractysSlash S1 Φ1 S2 Φ2 0 (-2 * p3) 0 (2 * p1) := by
    have hPerm :
        tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3 =
          p3 • tetractysGamma3 Φ1 Φ2 + p1 • tetractysGamma1 S1 +
            p0 • tetractysGamma0 S1 Φ1 + p2 • tetractysGamma2 Φ1 S2 := by
      unfold tetractysSlash; abel
    rw [hPerm]
    unfold tetractysRot31
    rw [clifford_bivector_linear_comm (tetractysGamma3 Φ1 Φ2) (tetractysGamma1 S1)
      (tetractysGamma0 S1 Φ1) (tetractysGamma2 Φ1 S2) p3 p1 p0 p2
      h13' h03' h10 h23' h12', hG3, hG1]
    unfold tetractysSlash
    noncomm_ring
    simp only [smul_smul, neg_smul, zero_smul, neg_mul, one_mul]
    abel
  have hAct01 :
      Block2.lorentzDiag (tetractysBoost01 S1 Φ1) *
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
          Block2.lorentzDiag (tetractysBoost01 S1 Φ1) =
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 (2 * p1) (2 * p0) 0 0) := by
    rw [(Block2.peirce_corner_embed_and_diagonal_lorentz_action
          (tetractysBoost01 S1 Φ1) (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) 0).2.2.2.2, hB01]
  have hAct02 :
      Block2.lorentzDiag (tetractysBoost02 S1 Φ1 S2) *
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
          Block2.lorentzDiag (tetractysBoost02 S1 Φ1 S2) =
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 (2 * p2) 0 (2 * p0) 0) := by
    rw [(Block2.peirce_corner_embed_and_diagonal_lorentz_action
          (tetractysBoost02 S1 Φ1 S2) (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) 0).2.2.2.2, hB02]
  have hAct03 :
      Block2.lorentzDiag (tetractysBoost03 S1 Φ1 Φ2) *
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
          Block2.lorentzDiag (tetractysBoost03 S1 Φ1 Φ2) =
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 (2 * p3) 0 0 (2 * p0)) := by
    rw [(Block2.peirce_corner_embed_and_diagonal_lorentz_action
          (tetractysBoost03 S1 Φ1 Φ2) (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) 0).2.2.2.2, hB03]
  have hAct12 :
      Block2.lorentzDiag (tetractysRot12 S1 Φ1 S2) *
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
          Block2.lorentzDiag (tetractysRot12 S1 Φ1 S2) =
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 0 (2 * p2) (-2 * p1) 0) := by
    rw [(Block2.peirce_corner_embed_and_diagonal_lorentz_action
          (tetractysRot12 S1 Φ1 S2) (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) 0).2.2.2.2, hR12]
  have hAct23 :
      Block2.lorentzDiag (tetractysRot23 Φ1 S2 Φ2) *
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
          Block2.lorentzDiag (tetractysRot23 Φ1 S2 Φ2) =
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 0 0 (2 * p3) (-2 * p2)) := by
    rw [(Block2.peirce_corner_embed_and_diagonal_lorentz_action
          (tetractysRot23 Φ1 S2 Φ2) (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) 0).2.2.2.2, hR23]
  have hAct31 :
      Block2.lorentzDiag (tetractysRot31 S1 Φ1 Φ2) *
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) -
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) *
          Block2.lorentzDiag (tetractysRot31 S1 Φ1 Φ2) =
        Block2.cornerEmbed (tetractysSlash S1 Φ1 S2 Φ2 0 (-2 * p3) 0 (2 * p1)) := by
    rw [(Block2.peirce_corner_embed_and_diagonal_lorentz_action
          (tetractysRot31 S1 Φ1 Φ2) (tetractysSlash S1 Φ1 S2 Φ2 p0 p1 p2 p3) 0).2.2.2.2, hR31]
  exact ⟨⟨hCornerIdem, hCornerBasis, hCornerAdd, hCornerNilp⟩,
    ⟨hAct01, hAct02, hAct03, hAct12, hAct23, hAct31⟩⟩

end Z4ParafermionBraidAndUnipotentGate

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
   2-hop collar excursion, square-first healing, 8-fold Brown–Gauss matrix powers, IMS double-commutator
   identity, parameterized Pfaffian square law, BDI chiral stack index mod-8 reduction, 3D Kramers TRS
   mass-channel blocking, and `ℤ₄` parafermion binary-carry / Peirce-braid / unipotent-gate laws (`𝔎𝔏₉–𝔎𝔏₁₁`).
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
       (16 : B) • (1 : Block2 B) ∧
     P * P * A + A * (P * P) - (2 : ℤ) • (P * A * P) =
       InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
         (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P A) ∧
     (Mat4.majoranaParamA Q a_sq b_sq).det = (Q ^ 2 + a_sq * b_sq) ^ 2 ∧
     Mat4.pfaffianMat4 (Mat4.trivChainA : Mat4 K) = 1 ∧
     Mat4.pfaffianMat4 (Mat4.closedTopChainA : Mat4 K) = -1 ∧
     Mat4.bdiLeftZeroModeIndex (Mat4.kitaevChainA : Mat4 K) = 1 ∧
     Mat4.bdiLeftZeroModeIndex (Mat4.kitaevChainSublatticeSwapA : Mat4 K) = -1 ∧
     Mat4.bdiStackIndexMod8 (List.replicate 8 Mat4.kitaevChainA) = 0 ∧
     Mat4.diracMassRotor a_sq b_sq * Mat4.diracMass1 -
       Mat4.diracMass1 * Mat4.diracMassRotor a_sq b_sq =
       (2 * b_sq) • ((Mat4.diracMass2 : Mat4 K) * Mat4.diracMass1) ∧
     (Mat4.z4ShiftTau : Mat4 K) * Mat4.z4ShiftTau = Mat4.pauliX2 ∧
     z4BraidU2 A c = z4PeirceOdd2 A + c * A * z4PeirceEven2 A ∧
     (1 - A) * unipotentGate4 A = 1 - (A * A) * (A * A) ∧
     (Mat4.peirceP2 : Mat4 K) * Mat4.pauliX1 +
       (Mat4.I4 - Mat4.peirceP2) * Mat4.diracMass2 * Mat4.pauliX1 = Mat4.zetaRealMat4 ∧
     (Mat4.zetaRealMat4 : Mat4 K) * Mat4.zetaRealMat4 = Mat4.diracMass2 ∧
     Block2.shearPlus Q * Block2.shearMinus a_sq = Block2.gaussianTP2 Q a_sq ∧
     Block2.det2 (Block2.gaussianTP2 Q a_sq) = 1 ∧
     Block2.det2 (Block2.twistorMomentum2 Q a_sq) = 0 ∧
     poincareLorentz P A * N_plus P A0 - N_plus P A0 * poincareLorentz P A =
       P * A * N_plus P A0 - N_plus P A0 * A * (1 - P) ∧
     N_plus P (poincareLorentz P A * N_plus P A0 - N_plus P A0 * poincareLorentz P A) =
       poincareLorentz P A * N_plus P A0 - N_plus P A0 * poincareLorentz P A ∧
     Block2.lorentzDiag A * Block2.cornerEmbed A0 -
       Block2.cornerEmbed A0 * Block2.lorentzDiag A =
       Block2.cornerEmbed (A * A0 - A0 * A)) := by
  have hFib := convex_hamiltonian_fiber_ground_state_invariance H0 H1 P0 t h0 h1
  have hAnn := energy_gap_annulus_midpoint_centering Q a_sq b_sq
  have hGap := square_first_local_bulk_gap_collar_healing P A μ0 hP
  have hCones := n_plus_minus_eq_centralizer_cones P A
  have hInv := Block2.universal_invertibility_anticommuting_homotopy A A0 c s hc hs hcs
  have hUnrot := Block2.universal_unrotated_and_hadamard_invertibility_rotor A c s hc hs hcs
  have hUnit := Block2.unit_gap_rotor_preservation_and_pole_endpoints A c s hc hs hcs
  have hMaj := Mat4.open_kitaev_majorana_chain_square_first_healing (K := K)
  have hBrown := Block2.brown_gauss_matrix_power_identities (B := B)
  have hIms := ims_single_double_commutator_identity P A
  have hPf := Mat4.bdi_parameterized_majorana_pfaffian_and_phase_sign_flip Q a_sq b_sq
  have hDetParam : (Mat4.majoranaParamA Q a_sq b_sq).det = (Q ^ 2 + a_sq * b_sq) ^ 2 := by
    rw [hPf.2.2.1.2.2, hPf.2.2.1.2.1]
  have hBdi :=
    Mat4.bdi_chiral_zero_mode_index_and_mod8_fidkowski_kitaev_reduction
      (K := K) [] [] [] [] 0
  have hD3 := Mat4.d3_dirac_clifford_mass_circle_and_kramers_trs_z2_blocking a_sq b_sq
  have hZ4Tau := Mat4.z4_binary_carry_synthesis_and_tau_powers (K := K)
  have hZ4Braid := z4_peirce_braid_brown_gauss_and_nilpotent_unipotent_gate A c A
  have hZeta8 := Mat4.dewitt_tetractys_mat4_zeta8_and_sp4_invariance (K := K)
  have hTP2 :=
    Block2.positive_grassmannian_gaussian_tp2_and_homogeneous_projector
      Q a_sq 1 1 (by decide) (by decide)
  have hTwistor :=
    Block2.real_twistor_susy_null_and_massive_momentum_factorization Q a_sq a_sq b_sq 0 0 0 0
  have hPoinc := poincare_translations_commute_and_lorentz_covariance P A A0 A0 A hP
  have hCorner := Block2.peirce_corner_embed_and_diagonal_lorentz_action A A0 A0
  exact ⟨KitaevLocalGapStage.coverEdge_acyclic,
    ⟨hFib, hAnn⟩,
    ⟨hGap.1, hCones.1, hCones.2.1⟩,
    ⟨hInv.1, hUnrot.2.1, hUnrot.2.2.1.1, hInv.2.1, hUnrot.2.2.2.2,
     hUnit.1, hUnit.2.2.2.2.2.1, hInv.2.2⟩,
    ⟨hMaj.2.1, hMaj.2.2.2.1.2.2, hMaj.2.2.2.2.1, hMaj.2.2.2.2.2.2, hBrown.2.2.2,
     hIms, hDetParam, hPf.2.2.2.1.1, hPf.2.2.2.2.1.1,
     Mat4.bdiLeftZeroModeIndex_kitaevChainA,
     Mat4.bdiLeftZeroModeIndex_kitaevChainSublatticeSwapA,
     hBdi.2.2.1.2.2.2.1, hD3.2.2.1.2.1, hZ4Tau.2.2.1,
     hZ4Braid.1.1, hZ4Braid.2.2.2.2.1, hZeta8.1.2.2, hZeta8.2.1.1,
     hTP2.1, hTP2.2.1, hTwistor.1.1, hPoinc.2.2.1.1, hPoinc.2.2.1.2.1, hCorner.2.2.2.2⟩⟩

end KitaevLocalGapOmegaSpectrumPoset
