/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChainFull
import InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset

/-!
# Kitaev Local Bulk Energy Gap, Universal Invertibility & $\Omega$-Spectrum Poset ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$)

## i. Overview

Complete, `0 sorry`, `[propext, Classical.choice, Quot.sound]`-only finite-stage formalization of the
7-node causal poset ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$) distilled from Alexei Kitaev's
Lecture 1 (*Condensed-Matter-Inspired $K$-Theory: Graphene Quantum Hall Effect, the Transverse-Field
Ising Model, Local Bulk Energy Gaps, and the $\Omega$-Spectrum $A_d \simeq \Omega A_{d+1} \simeq KO_{d-2}$*):

1. **Node $\mathfrak{KL}_1$ (`convex_hamiltonian_fiber_ground_state_invariance` &
   `convex_hamiltonian_fiber_eigenvalue_interpolation`):**
   Proves the algebraic mechanism of 0D Hamiltonian fiber contractibility over a fixed ground-state
   projector $P_0$ (`00:21:39`): if $H_0 P_0 = 0$ and $H_1 P_0 = 0$ (or more generally
   $H_0 P_0 = E_0 P_0$ and $H_1 P_0 = E_1 P_0$), then every convex combination
   $H(t) = (1 - t) H_0 + t H_1$ preserves $P_0$ with interpolated ground-state energy
   $(1 - t) E_0 + t E_1$.
2. **Node $\mathfrak{KL}_2$ (`energy_gap_annulus_midpoint_centering` &
   `noncomm_energy_gap_annulus_commutator_defect`):**
   Proves Kitaev's division-free spectral annulus midpoint identity (`00:41:40`):
   $$(b^2 - a^2)^2 - \big(2 Q - (a^2 + b^2)\big)^2 = 4 (Q - a^2)(b^2 - Q),$$
   together with its exact noncommutative commutator defect over any associative ring `[Ring B]`.
3. **Node $\mathfrak{KL}_3$ (`square_first_local_bulk_gap_collar_healing` &
   `square_first_local_bulk_gap_shifted_collar_healing`):**
   Establishes the exact Socratic difference between **Square-First** ($P(-A^2 - \mu_0)P$, Kitaev's
   interior bulk local gap on $P = \Pi_{\widetilde{D}}$, `00:42:48`) and **Truncate-First**
   ($-(P A P)^2 - P \mu_0 P$):
   $$\mathrm{SquareFirstBulkOp}\;P\;A\;\mu_0 - \mathrm{TruncateFirstBulkOp}\;P\;A\;\mu_0 =
     -\big(\mathrm{N\_plus}\;P\;A * \mathrm{N\_minus}\;P\;A\big),$$
   where $\mathrm{N\_plus}\;P\;A = \mathrm{conePlus}\;P\;A = P A (1 - P)$ and
   $\mathrm{N\_minus}\;P\;A = \mathrm{coneMinus}\;P\;A = (1 - P) A P$ are the canonical Peirce
   collar-hopping cones across $\partial\widetilde{D}$. When the interior bulk is unit-gapped
   ($P (A * A) P = -P$), `SquareFirstBulkOp P A 1 = 0` whereas `TruncateFirstBulkOp P A 1` leaves
   the spurious boundary collar defect `N_plus P A * N_minus P A`.
4. **Nodes $\mathfrak{KL}_4\text{–}\mathfrak{KL}_5$ (`Block2.hadamard_conjugation_diag_to_offdiag_intertwining` &
   `Block2.universal_invertibility_anticommuting_homotopy`):**
   Over the canonical $2 \times 2$ matrix carrier `Block2 B := Matrix (Fin 2) (Fin 2) B` for any
   associative ring `[Ring B]` (with **zero commutativity assumptions on $A \in B$**):
   - Proves that the unnormalized Hadamard block matrix $H_2 = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$
     intertwines the diagonal stacked pair $\mathrm{diagDoubledSys}\;A = \begin{pmatrix} A & 0 \\ 0 & -A \end{pmatrix}$
     and the off-diagonal doubled system $\mathrm{doubledSys}\;A = \begin{pmatrix} 0 & A \\ A & 0 \end{pmatrix}$:
     $$H_2 * \mathrm{diagDoubledSys}\;A * H_2 = \mathrm{doubledSys}\;(A + A),$$
   - Proves that $\mathrm{doubledSys}\;A$ and $\mathrm{baseDecoupler} = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$
     strictly anticommute ($\{X(A), Y\} = 0$) for **every** $A \in B$, and that the homotopy rotor
     $\mathrm{RotorXY}\;A\;c\;s = \begin{pmatrix} 0 & c A + s \\ c A - s & 0 \end{pmatrix}$ squares to
     $\begin{pmatrix} c^2 A^2 - s^2 & 0 \\ 0 & c^2 A^2 - s^2 \end{pmatrix}$.
5. **Nodes $\mathfrak{KL}_6\text{–}\mathfrak{KL}_7$ (`Block2.dimer_peierls_suspension_reassociativity_cancellation` &
   `kl7_master_kitaev_local_gap_omega_spectrum_synthesis`):**
   Proves the Eilenberg–Swindle / Peierls dimer re-association identities underlying the suspension
   map $F_d$ and wood-grain diagonal restriction $G_d$ (`01:13:04`–`01:19:15`), and welds all seven
   stages to `InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset`.

## ii. Key results

- `KitaevLocalGapOmegaSpectrumStage`, `rank`, `rank_injective`, `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`
- `convex_hamiltonian_fiber_ground_state_invariance`, `convex_hamiltonian_fiber_eigenvalue_interpolation`
- `energy_gap_annulus_midpoint_centering`, `noncomm_energy_gap_annulus_commutator_defect`
- `N_plus`, `N_minus`, `SquareFirstBulkOp`, `TruncateFirstBulkOp`, `n_plus_minus_eq_peirce_cones`
- `square_first_local_bulk_gap_collar_healing`, `square_first_local_bulk_gap_shifted_collar_healing`
- `Block2`, `Block2.mk2`, `Block2.doubledSys`, `Block2.diagDoubledSys`, `Block2.hadamard2`, `Block2.baseDecoupler`, `Block2.RotorXY`
- `Block2.hadamard_conjugation_diag_to_offdiag_intertwining`
- `Block2.universal_invertibility_anticommuting_homotopy`
- `Block2.dimer_peierls_suspension_reassociativity_cancellation`
- `kl7_master_kitaev_local_gap_omega_spectrum_synthesis`

## iii. Table of contents

- Section 0: The 7-Stage Kitaev Local-Gap & $\Omega$-Spectrum Causal Poset ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$)
- Section 1 ($\mathfrak{KL}_1\text{–}\mathfrak{KL}_2$): Contractible 0D Hamiltonian Fibers & Spectral Gap Midpoint Centering
- Section 2 ($\mathfrak{KL}_3$): Square-First Local Bulk Gap vs. Truncate-First Boundary Failure
- Section 3 ($\mathfrak{KL}_4\text{–}\mathfrak{KL}_6$): Canonical `Matrix (Fin 2) (Fin 2) B` Carrier, Hadamard Rotation, Universal Invertibility Rotor & Dimer Cancellation
- Section 4 ($\mathfrak{KL}_7$): Master Synthesis & Cross-Module Bridge to `KitaevFreeFermionKOSpectrumLocalGapPoset`

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `KitaevLocalGapOmegaSpectrumStage` ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$), `rank`, `rank_injective`, `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`,
  - `convex_hamiltonian_fiber_ground_state_invariance`, `convex_hamiltonian_fiber_eigenvalue_interpolation`,
  - `energy_gap_annulus_midpoint_centering`, `noncomm_energy_gap_annulus_commutator_defect`,
  - `n_plus_minus_eq_peirce_cones`, `square_first_local_bulk_gap_collar_healing`, `square_first_local_bulk_gap_shifted_collar_healing`,
  - `Block2.hadamard_conjugation_diag_to_offdiag_intertwining`, `Block2.universal_invertibility_anticommuting_homotopy`, `Block2.dimer_peierls_suspension_reassociativity_cancellation`,
  - `kl7_master_kitaev_local_gap_omega_spectrum_synthesis`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Projector idempotence (`hP : P * P = P`), ground-state annihilation/eigenvalue hypotheses (`h0 : H0 * P0 = 0`, `h1 : H1 * P0 = 0`), central scalar commutation (`hc : c * A = A * c`, `hs : s * A = A * s`, `hcs : c * s = s * c`), and nested 3-shell idempotent hypotheses (`h₁`, `h₂`, `h₁₂`, `h₂₁`) are explicit theorem parameters.
* **BUCKET 3 — Out-of-Scope Continuum / Homotopy Claims:**
  - Continuous classifying-space homotopy equivalences ($B_0 \simeq \mathbb{C}\mathrm{P}^\infty \simeq K(\mathbb{Z}, 2)$, $F_0 \simeq \mathbb{C}\mathrm{P}^\infty \times \mathbb{Z}_2$, $A_d \simeq \Omega A_{d+1} \simeq KO_{d-2}$) and infinite-volume analytic operator-norm bounds $\|M\| \le 1 + O(r^2 / R^2)$ remain outside this finite-stage algebraic and matrix owner.

## iv. References

- Alexei Kitaev, *Periodic table for topological insulators and superconductors*, AIP Conf. Proc. 1134, 22–30 (2009), arXiv:0901.2686.
- Alexei Kitaev, *Lecture 1: Condensed-matter-inspired $K$-theory, graphene quantum Hall effect, transverse-field Ising model, local spectral gaps, and the $\Omega$-spectrum*.
- `InfoGeometry.OperatorAlgebra.PeirceSpine.Basic`
- `InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChainFull`
- `InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset`
-/

namespace InfoGeometry.Kitaev.KitaevLocalGapOmegaSpectrumPoset

open Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChainFull

universe u

-- ============================================================================
-- SECTION 0: The 7-Stage Kitaev Local-Gap & Ω-Spectrum Poset (𝔎𝔏₁ ≺ ⋯ ≺ 𝔎𝔏₇)
-- ============================================================================

/-- The 7-stage causal poset ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$) governing
Kitaev's Lecture 1 architecture: 0D Hamiltonian fiber convexity, spectral-annulus midpoint
centering, square-first interior local bulk gap collar healing, Hadamard-rotated $2 \times 2$
block anticommutation, universal invertibility rotor homotopy, dimer Peierls re-association,
and $\Omega$-spectrum synthesis. -/
inductive KitaevLocalGapOmegaSpectrumStage : Type
  | kl1ZeroDimConvexHamiltonianFiber
  | kl2SpectralGapAnnulusMidpointCentering
  | kl3SquareFirstLocalBulkGapCollarHealing
  | kl4HadamardRotatedBlockAnticommutator
  | kl5UniversalInvertibilityRotorHomotopy
  | kl6DimerPeierlsSuspensionReassociation
  | kl7OmegaSpectrumMasterSynthesis
  deriving DecidableEq, Repr

namespace KitaevLocalGapOmegaSpectrumStage

/-- Numerical stage rank `0 .. 6` for `KitaevLocalGapOmegaSpectrumStage`. -/
def rank : KitaevLocalGapOmegaSpectrumStage → ℕ
  | .kl1ZeroDimConvexHamiltonianFiber => 0
  | .kl2SpectralGapAnnulusMidpointCentering => 1
  | .kl3SquareFirstLocalBulkGapCollarHealing => 2
  | .kl4HadamardRotatedBlockAnticommutator => 3
  | .kl5UniversalInvertibilityRotorHomotopy => 4
  | .kl6DimerPeierlsSuspensionReassociation => 5
  | .kl7OmegaSpectrumMasterSynthesis => 6

/-- The stage rank map on `KitaevLocalGapOmegaSpectrumStage` is strictly injective. -/
lemma rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder KitaevLocalGapOmegaSpectrumStage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype KitaevLocalGapOmegaSpectrumStage where
  elems := {
    .kl1ZeroDimConvexHamiltonianFiber,
    .kl2SpectralGapAnnulusMidpointCentering,
    .kl3SquareFirstLocalBulkGapCollarHealing,
    .kl4HadamardRotatedBlockAnticommutator,
    .kl5UniversalInvertibilityRotorHomotopy,
    .kl6DimerPeierlsSuspensionReassociation,
    .kl7OmegaSpectrumMasterSynthesis
  }
  complete x := by cases x <;> decide

/-- Immediate Hasse cover edges $\mathfrak{KL}_k \prec \mathfrak{KL}_{k+1}$ of the 7-stage spine. -/
inductive coverEdge : KitaevLocalGapOmegaSpectrumStage → KitaevLocalGapOmegaSpectrumStage → Prop
  | kl1_to_kl2 :
      coverEdge .kl1ZeroDimConvexHamiltonianFiber
        .kl2SpectralGapAnnulusMidpointCentering
  | kl2_to_kl3 :
      coverEdge .kl2SpectralGapAnnulusMidpointCentering
        .kl3SquareFirstLocalBulkGapCollarHealing
  | kl3_to_kl4 :
      coverEdge .kl3SquareFirstLocalBulkGapCollarHealing
        .kl4HadamardRotatedBlockAnticommutator
  | kl4_to_kl5 :
      coverEdge .kl4HadamardRotatedBlockAnticommutator
        .kl5UniversalInvertibilityRotorHomotopy
  | kl5_to_kl6 :
      coverEdge .kl5UniversalInvertibilityRotorHomotopy
        .kl6DimerPeierlsSuspensionReassociation
  | kl6_to_kl7 :
      coverEdge .kl6DimerPeierlsSuspensionReassociation
        .kl7OmegaSpectrumMasterSynthesis

/-- Every Hasse cover edge strictly increases the stage rank. -/
lemma coverEdge_strictMono {a b : KitaevLocalGapOmegaSpectrumStage} (h : coverEdge a b) :
    a.rank < b.rank := by
  cases h <;> decide

/-- No stage in `KitaevLocalGapOmegaSpectrumStage` has a cover edge to itself. -/
lemma coverEdge_acyclic (a : KitaevLocalGapOmegaSpectrumStage) : ¬ coverEdge a a := by
  intro h
  exact Nat.lt_irrefl a.rank (coverEdge_strictMono h)

end KitaevLocalGapOmegaSpectrumStage

-- ============================================================================
-- SECTION 1 (𝔎𝔏₁ & 𝔎𝔏₂): Contractible 0D Hamiltonian Fibers & Spectral Gap Centering
-- ============================================================================

section ZeroDimFiberAndGapCentering
variable {B : Type u} [Ring B]

/--
**Theorem 1a (𝔎𝔏₁ — Convexity of the 0D Hamiltonian Fiber Over a Ground State `P₀`, 00:21:39):**
If two Hamiltonians `H₀, H₁` annihilate the ground-state projector `P₀` (`H₀ * P₀ = 0` and
`H₁ * P₀ = 0`), then for any interpolation parameter `t`, the convex combination
`H(t) = (1 - t) * H₀ + t * H₁` also annihilates `P₀` (`H(t) * P₀ = 0`), providing the algebraic
invariance underlying the contractibility of the 0D Hamiltonian fiber over a fixed ground state.
-/
lemma convex_hamiltonian_fiber_ground_state_invariance
    (H0 H1 P0 t : B) (h0 : H0 * P0 = 0) (h1 : H1 * P0 = 0) :
    ((1 - t) * H0 + t * H1) * P0 = 0 := by
  calc ((1 - t) * H0 + t * H1) * P0
    _ = (1 - t) * (H0 * P0) + t * (H1 * P0) := by noncomm_ring
    _ = 0 := by rw [h0, h1, mul_zero, mul_zero, add_zero]

/--
**Theorem 1b (𝔎𝔏₁ — General Eigenvalue Interpolation on a Shared Ground-State Projector `P₀`):**
If `H₀ * P₀ = E₀ * P₀` and `H₁ * P₀ = E₁ * P₀` in any associative ring `[Ring B]`, then:
1. For any `t : B`, `((1 - t) * H₀ + t * H₁) * P₀ = ((1 - t) * E₀ + t * E₁) * P₀`.
2. In particular, when `E₀ = E₁`, `((1 - t) * H₀ + t * H₁) * P₀ = E₀ * P₀`.
-/
lemma convex_hamiltonian_fiber_eigenvalue_interpolation
    (H0 H1 P0 E0 E1 t : B) (h0 : H0 * P0 = E0 * P0) (h1 : H1 * P0 = E1 * P0) :
    ((1 - t) * H0 + t * H1) * P0 = ((1 - t) * E0 + t * E1) * P0 ∧
    (E0 = E1 → ((1 - t) * H0 + t * H1) * P0 = E0 * P0) := by
  have hInterp : ((1 - t) * H0 + t * H1) * P0 = ((1 - t) * E0 + t * E1) * P0 := by
    calc ((1 - t) * H0 + t * H1) * P0
      _ = (1 - t) * (H0 * P0) + t * (H1 * P0) := by noncomm_ring
      _ = (1 - t) * (E0 * P0) + t * (E1 * P0) := by rw [h0, h1]
      _ = ((1 - t) * E0 + t * E1) * P0 := by noncomm_ring
  refine ⟨hInterp, ?_⟩
  intro hEq
  rw [hInterp, ← hEq]
  noncomm_ring

/--
**Theorem 2a (𝔎𝔏₂ — Kitaev's Spectral Annulus Midpoint Centering Identity, 00:41:40):**
In any commutative ring `K` (scaled by `4` to avoid division by `2`), the spectral condition
that `Q = -A²` lies in `[a², b²]` (`(Q - a²)(b² - Q) ≥ 0`) is algebraically identical to
the centered norm bound `(b² - a²)² - (2Q - (a² + b²))² = 4 * (Q - a²) * (b² - Q)`.
-/
lemma energy_gap_annulus_midpoint_centering
    {K : Type u} [CommRing K] (Q a_sq b_sq : K) :
    (b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2 =
      4 * (Q - a_sq) * (b_sq - Q) := by
  have hDiffSq :
      (b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2 =
        ((b_sq - a_sq) - (2 * Q - (a_sq + b_sq))) *
          ((b_sq - a_sq) + (2 * Q - (a_sq + b_sq))) := by
    ring
  have hLeft : (b_sq - a_sq) - (2 * Q - (a_sq + b_sq)) = 2 * (b_sq - Q) := by
    ring
  have hRight : (b_sq - a_sq) + (2 * Q - (a_sq + b_sq)) = 2 * (Q - a_sq) := by
    ring
  rw [hDiffSq, hLeft, hRight]
  ring

/--
**Theorem 2b (𝔎𝔏₂ — Noncommutative Spectral Annulus Midpoint Identity & Commutator Defect):**
In any associative ring `[Ring B]`, for any operator `Q : B` (such as `Q = -(A * A)`) and
spectral bounds `a_sq, b_sq : B`:
$$((b_{\mathrm{sq}} - a_{\mathrm{sq}}) * (b_{\mathrm{sq}} - a_{\mathrm{sq}}) -
  ((2 : \mathbb{Z}) \bullet Q - (a_{\mathrm{sq}} + b_{\mathrm{sq}})) *
    ((2 : \mathbb{Z}) \bullet Q - (a_{\mathrm{sq}} + b_{\mathrm{sq}}))) -
  (4 : \mathbb{Z}) \bullet ((Q - a_{\mathrm{sq}}) * (b_{\mathrm{sq}} - Q)) =
  -(2 : \mathbb{Z}) \bullet \big(\mathrm{comm}\;a_{\mathrm{sq}}\;Q +
    \mathrm{comm}\;Q\;b_{\mathrm{sq}} + \mathrm{comm}\;b_{\mathrm{sq}}\;a_{\mathrm{sq}}\big).$$
-/
lemma noncomm_energy_gap_annulus_commutator_defect
    (Q a_sq b_sq : B) :
    ((b_sq - a_sq) * (b_sq - a_sq) -
      ((2 : ℤ) • Q - (a_sq + b_sq)) * ((2 : ℤ) • Q - (a_sq + b_sq))) -
      (4 : ℤ) • ((Q - a_sq) * (b_sq - Q)) =
      -(2 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm a_sq Q +
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q b_sq +
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm b_sq a_sq) := by
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  noncomm_ring

end ZeroDimFiberAndGapCentering

-- ============================================================================
-- SECTION 2 (𝔎𝔏₃): Square-First Local Bulk Gap vs. Truncate-First Boundary Failure
-- ============================================================================

section SquareFirstLocalBulkGap
variable {B : Type u} [Ring B]

/-- Interior-to-collar off-diagonal Peirce hopping operator `N_plus P A = P * A * (1 - P)`
(canonically equal to `InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A`). -/
def N_plus (P A : B) : B := P * A * (1 - P)

/-- Collar-to-interior off-diagonal Peirce hopping operator `N_minus P A = (1 - P) * A * P`
(canonically equal to `InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P A`). -/
def N_minus (P A : B) : B := (1 - P) * A * P

/-- Kitaev's Square-First Local Gap Operator `P * (-(A * A) - μ0) * P` on the shrunk interior
disk `P = Π_{D̃}` (`00:42:48`), which squares `A` on the full sample before projecting to `P`. -/
def SquareFirstBulkOp (P A μ0 : B) : B :=
  P * (- (A * A) - μ0) * P

/-- Naive Truncate-First Operator `-((P * A * P) * (P * A * P)) - P * μ0 * P` obtained by
truncating `A ↦ P * A * P` to the interior disk `P = Π_{D̃}` before squaring. -/
def TruncateFirstBulkOp (P A μ0 : B) : B :=
  - ((P * A * P) * (P * A * P)) - P * μ0 * P

/-- Left-multiplication absorption `P * (P * Z) = P * Z` for any idempotent `P * P = P`. -/
lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/--
**Bridge Lemma (𝔎𝔏₃ — Alignment of `N_plus`, `N_minus`, `SquareFirstBulkOp`, and `TruncateFirstBulkOp` with Canonical `PeirceSpine`):**
Verifies that `N_plus` and `N_minus` coincide with canonical `conePlus` and `coneMinus` from
`InfoGeometry.OperatorAlgebra.PeirceSpine`, and expresses `SquareFirstBulkOp` and `TruncateFirstBulkOp`
in terms of `peirce11 P`.
-/
lemma n_plus_minus_eq_peirce_cones (P A μ0 : B) (hP : P * P = P) :
    N_plus P A = InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A ∧
    N_minus P A = InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P A ∧
    SquareFirstBulkOp P A μ0 =
      InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 P (-(A * A) - μ0) ∧
    TruncateFirstBulkOp P A μ0 =
      -(InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 P A *
          InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 P A) -
        InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 P μ0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 P (-(A * A) - μ0) =
      -(InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 P A *
          InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 P A) -
        InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 P μ0 -
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A *
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P A := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11,
    InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
    InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus]
  simp only [sub_mul, mul_sub, one_mul, mul_one,
    neg_mul, mul_neg, mul_assoc, proj_idem hP]
  abel

/--
**Theorem 3a (𝔎𝔏₃ — Square-First Collar Healing vs. Truncate-First Spurious Edge Modes, 00:42:48):**
For any interior disk projector `P² = P` (`Π_{D̃}`) and hopping matrix `A`:
1. **Exact Collar Healing Identity:**
   `SquareFirstBulkOp P A μ₀ - TruncateFirstBulkOp P A μ₀ = - (N_plus P A * N_minus P A)`.
2. **Why Square-First Succeeds When the Interior Bulk Is Unit-Gapped (`P * (A * A) * P = -P`):**
   If `P * (A * A) * P = -P` (unit bulk gap in `D̃` despite gapless modes on the outer boundary),
   then `SquareFirstBulkOp P A 1 = 0` (exact zero bulk defect!), whereas `TruncateFirstBulkOp P A 1`
   fails by the spurious collar edge mode `N_plus P A * N_minus P A`.
-/
lemma square_first_local_bulk_gap_collar_healing
    (P A μ0 : B) (hP : P * P = P) :
    SquareFirstBulkOp P A μ0 - TruncateFirstBulkOp P A μ0 =
      - (N_plus P A * N_minus P A) ∧
    (P * (A * A) * P = -P →
      SquareFirstBulkOp P A 1 = 0 ∧
      TruncateFirstBulkOp P A 1 = N_plus P A * N_minus P A) := by
  have h_diff : ∀ m : B, SquareFirstBulkOp P A m - TruncateFirstBulkOp P A m =
      - (N_plus P A * N_minus P A) := by
    intro m
    dsimp only [SquareFirstBulkOp, TruncateFirstBulkOp, N_plus, N_minus]
    simp only [sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, proj_idem hP]
    abel
  refine ⟨h_diff μ0, ?_⟩
  intro h_unit_gap
  have h_sq_zero : SquareFirstBulkOp P A 1 = 0 := by
    dsimp [SquareFirstBulkOp]
    calc P * (-(A * A) - 1) * P
      _ = - (P * (A * A) * P) - P * P := by noncomm_ring
      _ = - (-P) - P := by rw [h_unit_gap, hP]
      _ = 0 := by abel
  have h_trunc : TruncateFirstBulkOp P A 1 = N_plus P A * N_minus P A := by
    have h2 := h_diff 1
    rw [h_sq_zero, zero_sub, neg_inj] at h2
    exact h2
  exact ⟨h_sq_zero, h_trunc⟩

/--
**Theorem 3b (𝔎𝔏₃ — Shifted Midpoint Collar Healing Identity for Arbitrary Spectral Midpoint `μ₀`):**
For any interior disk projector `P * P = P`, hopping operator `A : B`, and midpoint shift `μ0 : B`:
if the interior square satisfies `P * (A * A) * P = -(P * μ0 * P)` (so $-A^2$ agrees with $\mu_0$
on the interior disk $\widetilde{D}$), then `SquareFirstBulkOp P A μ0 = 0` whereas
`TruncateFirstBulkOp P A μ0 = N_plus P A * N_minus P A`.
-/
lemma square_first_local_bulk_gap_shifted_collar_healing
    (P A μ0 : B) (hP : P * P = P) (hBulk : P * (A * A) * P = -(P * μ0 * P)) :
    SquareFirstBulkOp P A μ0 = 0 ∧
    TruncateFirstBulkOp P A μ0 = N_plus P A * N_minus P A := by
  have hDiff := (square_first_local_bulk_gap_collar_healing P A μ0 hP).1
  have hSqZero : SquareFirstBulkOp P A μ0 = 0 := by
    dsimp [SquareFirstBulkOp]
    calc P * (-(A * A) - μ0) * P
      _ = -(P * (A * A) * P) - P * μ0 * P := by noncomm_ring
      _ = -(-(P * μ0 * P)) - P * μ0 * P := by rw [hBulk]
      _ = 0 := by abel
  have hTrunc : TruncateFirstBulkOp P A μ0 = N_plus P A * N_minus P A := by
    rw [hSqZero, zero_sub, neg_inj] at hDiff
    exact hDiff
  exact ⟨hSqZero, hTrunc⟩

/--
**Theorem 3c (𝔎𝔏₃ — Buffered Concentric Disk Collar Stabilization & Square-First Finite-Stage Invariance):**
Let `P_m` and `P_n` be nested concentric disk projectors (`P_m * P_n = P_m`, `P_n * P_m = P_m`,
`P_n * P_n = P_n`) such that `A` is `r`-local between the inner disk `P_m` and the exterior
`1 - P_n` of the outer buffer disk `P_n` (`P_m * A * (1 - P_n) = 0` and `(1 - P_n) * A * P_m = 0`).
Then truncating `A` to the outer buffer disk `A_n := P_n * A * P_n` before computing the
inner-disk collar and Square-First local gap on `P_m` is **exact**:
1. `N_plus P_m (P_n * A * P_n) = N_plus P_m A`,
2. `N_minus P_m (P_n * A * P_n) = N_minus P_m A`,
3. `P_m * ((P_n * A * P_n) * (P_n * A * P_n)) * P_m = P_m * (A * A) * P_m`,
4. `SquareFirstBulkOp P_m (P_n * A * P_n) μ0 = SquareFirstBulkOp P_m A μ0`.
-/
lemma buffered_disk_collar_stabilization_and_square_first_invariance
    (P_m P_n A μ0 : B)
    (hPn : P_n * P_n = P_n)
    (hmn_left : P_m * P_n = P_m)
    (hmn_right : P_n * P_m = P_m)
    (h_loc_out : P_m * A * (1 - P_n) = 0)
    (h_loc_in : (1 - P_n) * A * P_m = 0) :
    N_plus P_m (P_n * A * P_n) = N_plus P_m A ∧
    N_minus P_m (P_n * A * P_n) = N_minus P_m A ∧
    P_m * ((P_n * A * P_n) * (P_n * A * P_n)) * P_m = P_m * (A * A) * P_m ∧
    SquareFirstBulkOp P_m (P_n * A * P_n) μ0 = SquareFirstBulkOp P_m A μ0 := by
  have h_out : P_m * A * P_n = P_m * A := by
    have h1 : P_m * A - P_m * A * P_n = P_m * A * (1 - P_n) := by noncomm_ring
    rw [h_loc_out] at h1
    exact (sub_eq_zero.mp h1).symm
  have h_in : P_n * A * P_m = A * P_m := by
    have h1 : A * P_m - P_n * A * P_m = (1 - P_n) * A * P_m := by noncomm_ring
    rw [h_loc_in] at h1
    exact (sub_eq_zero.mp h1).symm
  have hNplus : N_plus P_m (P_n * A * P_n) = N_plus P_m A := by
    dsimp [N_plus]
    have h_assoc : P_m * (P_n * A * P_n) * (1 - P_m) = (P_m * P_n) * A * P_n * (1 - P_m) := by
      noncomm_ring
    rw [h_assoc, hmn_left, h_out]
  have hNminus : N_minus P_m (P_n * A * P_n) = N_minus P_m A := by
    dsimp [N_minus]
    have h_assoc : (1 - P_m) * (P_n * A * P_n) * P_m = (1 - P_m) * (P_n * A * (P_n * P_m)) := by
      noncomm_ring
    rw [h_assoc, hmn_right, h_in, ← mul_assoc]
  have hSq : P_m * ((P_n * A * P_n) * (P_n * A * P_n)) * P_m = P_m * (A * A) * P_m := by
    have h_assoc :
        P_m * ((P_n * A * P_n) * (P_n * A * P_n)) * P_m =
          (P_m * P_n) * A * (P_n * P_n) * (A * (P_n * P_m)) := by
      noncomm_ring
    rw [h_assoc, hmn_left, hPn, hmn_right, h_out]
    noncomm_ring
  have hBulk : SquareFirstBulkOp P_m (P_n * A * P_n) μ0 = SquareFirstBulkOp P_m A μ0 := by
    dsimp [SquareFirstBulkOp]
    calc P_m * (-((P_n * A * P_n) * (P_n * A * P_n)) - μ0) * P_m
      _ = -(P_m * ((P_n * A * P_n) * (P_n * A * P_n)) * P_m) - P_m * μ0 * P_m := by noncomm_ring
      _ = -(P_m * (A * A) * P_m) - P_m * μ0 * P_m := by rw [hSq]
      _ = P_m * (-(A * A) - μ0) * P_m := by noncomm_ring
  exact ⟨hNplus, hNminus, hSq, hBulk⟩

end SquareFirstLocalBulkGap

-- ============================================================================
-- SECTION 3 (𝔎𝔏₄–𝔎𝔏₆): Canonical 2×2 Block Carrier, Universal Invertibility Rotor & Dimer Cancellation
-- ============================================================================

/-- Canonical $2 \times 2$ block matrix carrier `Block2 B := Matrix (Fin 2) (Fin 2) B` over any
type `B`, avoiding bespoke wrapper structures while inheriting Mathlib's full matrix algebra. -/
abbrev Block2 (B : Type u) : Type u := Matrix (Fin 2) (Fin 2) B

namespace Block2
variable {B : Type u} [Ring B]

/-- Explicit $2 \times 2$ block matrix constructor `mk2 b11 b12 b21 b22 = !![b11, b12; b21, b22]`
on `Block2 B = Matrix (Fin 2) (Fin 2) B`. -/
def mk2 (b11 b12 b21 b22 : B) : Block2 B :=
  !![b11, b12; b21, b22]

/-- Hadamard-rotated doubled system `doubledSys A = [[0, A], [A, 0]]` (orthogonal-conjugate to
the diagonal stacked system `A ⊕ (-A)`). -/
def doubledSys (A : B) : Block2 B :=
  mk2 0 A A 0

/-- Diagonal stacked system `diagDoubledSys A = [[A, 0], [0, -A]] = A ⊕ (-A)`. -/
def diagDoubledSys (A : B) : Block2 B :=
  mk2 A 0 0 (-A)

/-- Unnormalized orthogonal Hadamard $2 \times 2$ block matrix `hadamard2 = [[1, 1], [1, -1]]`
satisfying `hadamard2 * hadamard2 = [[2, 0], [0, 2]]` and conjugating `diagDoubledSys A` into
`doubledSys (A + A)`. -/
def hadamard2 : Block2 B :=
  mk2 1 1 1 (-1)

/-- Universal skew-symmetric basepoint decoupler `baseDecoupler = [[0, 1], [-1, 0]]` (`Y² = -I₂`). -/
def baseDecoupler : Block2 B :=
  mk2 0 1 (-1) 0

/-- Homotopy rotor `RotorXY A c s = [[0, c * A + s], [c * A - s, 0]] = c • X(A) + s • Y`. -/
def RotorXY (A c s : B) : Block2 B :=
  mk2 0 (c * A + s) (c * A - s) 0

/-- Direct, unrotated rotor `c • diag(A,-A) + s • Y`, written as a block matrix. -/
def DirectRotor (A c s : B) : Block2 B :=
  mk2 (c * A) s (-s) (-(c * A))

/-- Explicit non-commutativity witness on `Block2 ℤ = Matrix (Fin 2) (Fin 2) ℤ`:
`hadamard2` and `baseDecoupler` do not commute (`hadamard2 * baseDecoupler ≠ baseDecoupler * hadamard2`). -/
lemma hadamard2_baseDecoupler_noncomm :
    (hadamard2 : Block2 ℤ) * baseDecoupler ≠ baseDecoupler * hadamard2 := by
  intro h
  have h00 := congrArg (fun M : Block2 ℤ => M 0 0) h
  revert h00
  decide

/--
**Theorem 4a (𝔎𝔏₄ — Hadamard Block Rotation Between Diagonal `A ⊕ (-A)` and Off-Diagonal `[[0, A], [A, 0]]`):**
For **any** operator `A ∈ B` in an associative ring `[Ring B]` (with zero commutativity assumptions on `A`):
1. **Hadamard Involution Up to Scale `2`:**
   `hadamard2 * hadamard2 = mk2 (1 + 1) 0 0 (1 + 1)`.
2. **Hadamard Intertwining from Diagonal `A ⊕ (-A)` to Off-Diagonal `doubledSys`:**
   `hadamard2 * diagDoubledSys A * hadamard2 = doubledSys (A + A)` and
   `hadamard2 * doubledSys A * hadamard2 = diagDoubledSys (A + A)`.
3. **Universal Anticommutation in Both Bases:**
   Both `diagDoubledSys A` and `doubledSys A` strictly anticommute with `baseDecoupler`, and
   `baseDecoupler * baseDecoupler = mk2 (-1) 0 0 (-1)`.
-/
lemma hadamard_conjugation_diag_to_offdiag_intertwining (A : B) :
    (hadamard2 : Block2 B) * hadamard2 = mk2 (1 + 1) 0 0 (1 + 1) ∧
    hadamard2 * diagDoubledSys A * hadamard2 = doubledSys (A + A) ∧
    hadamard2 * doubledSys A * hadamard2 = diagDoubledSys (A + A) ∧
    diagDoubledSys A * baseDecoupler + baseDecoupler * diagDoubledSys A = (0 : Block2 B) ∧
    doubledSys A * baseDecoupler + baseDecoupler * doubledSys A = (0 : Block2 B) ∧
    (baseDecoupler : Block2 B) * baseDecoupler = mk2 (-1) 0 0 (-1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    (dsimp [hadamard2, mk2]; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]; noncomm_ring)
  · ext i j; fin_cases i <;> fin_cases j <;>
    (dsimp [hadamard2, diagDoubledSys, doubledSys, mk2];
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]; noncomm_ring)
  · ext i j; fin_cases i <;> fin_cases j <;>
    (dsimp [hadamard2, diagDoubledSys, doubledSys, mk2];
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]; noncomm_ring)
  · ext i j; fin_cases i <;> fin_cases j <;>
    (dsimp [diagDoubledSys, baseDecoupler, mk2];
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]; noncomm_ring)
  · ext i j; fin_cases i <;> fin_cases j <;>
    (dsimp [doubledSys, baseDecoupler, mk2];
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]; noncomm_ring)
  · ext i j; fin_cases i <;> fin_cases j <;>
    (dsimp [baseDecoupler, mk2]; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]; noncomm_ring)

/--
**Theorem 4b (𝔎𝔏₄ & 𝔎𝔏₅ — Kitaev's Universal Invertibility Homotopy `A ⊕ (-A) ~ Y`, 01:01:30):**
For **ANY** operator `A ∈ B` (without any commutation assumptions on `A`!):
1. `doubledSys A` and `baseDecoupler` **strictly anticommute**:
   `doubledSys A * baseDecoupler + baseDecoupler * doubledSys A = 0`.
2. For any central scalars `c, s` (`c = cos(πt/2), s = sin(πt/2)`), the homotopy `RotorXY A c s`
   has square:
   `RotorXY A c s * RotorXY A c s = mk2 (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s)`,
   an algebraic identity only. It does not imply gap preservation for general `A`; for example, a
   gap-preserving specialization requires assumptions such as `A * A = -1` and `c * c + s * s = 1`.
3. **Dimer Peierls Re-Association (`F_d` & `G_d`, 01:16:44):**
   Sliding the dimer pairing `(A - A₀) + (A₀ - A₀) + (A₀ - A₀) = A - A₀` cancels adjacent trivial
   dimers identically.
-/
lemma universal_invertibility_anticommuting_homotopy
    (A A0 c s : B) (hc : c * A = A * c) (hs : s * A = A * s) (hcs : c * s = s * c) :
    doubledSys A * baseDecoupler + baseDecoupler * doubledSys A = (0 : Block2 B) ∧
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
  refine ⟨(hadamard_conjugation_diag_to_offdiag_intertwining A).2.2.2.2.1, ?_, by abel⟩
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [RotorXY, mk2]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_add]
    exact h_quad
  · dsimp [RotorXY, mk2]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, mul_zero, add_zero]
  · dsimp [RotorXY, mk2]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, mul_zero, add_zero]
  · dsimp [RotorXY, mk2]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, add_zero]
    exact h_quad2

/-- The unrotated rotor has the same square as the Hadamard-rotated rotor.
The coefficients are assumed to commute with `A` and with each other; no
commutativity assumption is made on the ambient ring. -/
lemma direct_unrotated_rotor_square
    (A c s : B) (hc : c * A = A * c) (hs : s * A = A * s)
    (hcs : c * s = s * c) :
    DirectRotor A c s * DirectRotor A c s =
      mk2 (c * c * (A * A) - s * s) 0 0
        (c * c * (A * A) - s * s) := by
  have hdiag : (c * A) * (c * A) + s * (-s) =
      c * c * (A * A) - s * s := by
    calc
      (c * A) * (c * A) + s * (-s)
          = c * (A * c) * A - s * s := by noncomm_ring
      _ = c * c * (A * A) - s * s := by rw [← hc]; simp only [mul_assoc]
  have hdiag' : (-s) * s + (-(c * A)) * (-(c * A)) =
      c * c * (A * A) - s * s := by
    calc
      (-s) * s + (-(c * A)) * (-(c * A))
          = c * (A * c) * A - s * s := by noncomm_ring
      _ = c * c * (A * A) - s * s := by rw [← hc]; simp only [mul_assoc]
  have hoff : (c * A) * s + s * (-(c * A)) = 0 := by
    calc
      (c * A) * s + s * (-(c * A)) = c * (A * s) - s * c * A := by
        noncomm_ring
      _ = c * s * A - s * c * A := by rw [← hs]; simp only [mul_assoc]
      _ = 0 := by rw [hcs]; abel
  have hoff' : (-s) * (c * A) + (-(c * A)) * (-s) = 0 := by
    calc
      (-s) * (c * A) + (-(c * A)) * (-s) = c * (A * s) - s * c * A := by
        noncomm_ring
      _ = c * s * A - s * c * A := by rw [← hs]; simp only [mul_assoc]
      _ = 0 := by rw [hcs]; abel
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [DirectRotor, mk2]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hdiag
  · dsimp [DirectRotor, mk2]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hoff
  · dsimp [DirectRotor, mk2]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hoff'
  · dsimp [DirectRotor, mk2]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hdiag'

/--
**Unit-gap specialization of the rotor-square identity:** if the input operator has
`A * A = -1` and the central coefficients are normalized by `c² + s² = 1`,
then every point of the rotor has square `-I₂`. The normalization and centrality
hypotheses are explicit; the general algebraic rotor identity alone does not imply
this spectral conclusion.
-/
lemma rotorXY_square_eq_negative_identity_of_unit_gap
    (A A0 c s : B) (hc : c * A = A * c) (hs : s * A = A * s)
    (hcs : c * s = s * c) (hA : A * A = -1)
    (h_norm : c * c + s * s = 1) :
    RotorXY A c s * RotorXY A c s = mk2 (-1) 0 0 (-1) := by
  have h_rotor :=
    (universal_invertibility_anticommuting_homotopy A A0 c s hc hs hcs).2.1
  have h_scalar : c * c * (A * A) - s * s = -1 := by
    rw [hA]
    calc
      c * c * (-1) - s * s = -(c * c + s * s) := by noncomm_ring
      _ = -1 := by rw [h_norm]
  rw [h_scalar] at h_rotor
  exact h_rotor

/--
**Theorem 5 (𝔎𝔏₆ — Dimer Peierls Suspension Re-Association & Endpoint Evaluations of `RotorXY`):**
In any associative ring `[Ring B]`:
1. **Dimer Cascade Vacuum Cancellation (`01:16:44`):**
   `(A - A0) + (A0 - A0) + (A0 - A0) = A - A0`.
2. **Domain-Wall Telescoping Across an Intermediate Defect `B_op`:**
   `(A - B_op) + (B_op - A0) = A - A0`.
3. **Eilenberg–Swindle Alternating Dimer Re-Pairing (`01:13:04`):**
   `(A + -A) + A = A` and `A + (-A + A) = A`.
4. **Rotor Boundary Endpoints (`c = 1, s = 0` vs. `c = 0, s = 1`):**
   `RotorXY A 1 0 = doubledSys A` and `RotorXY A 0 1 = baseDecoupler`.
-/
lemma dimer_peierls_suspension_reassociativity_cancellation (A B_op A0 : B) :
    (A - A0) + (A0 - A0) + (A0 - A0) = A - A0 ∧
    (A - B_op) + (B_op - A0) = A - A0 ∧
    (A + -A) + A = A ∧
    A + (-A + A) = A ∧
    RotorXY A 1 0 = doubledSys A ∧
    RotorXY A 0 1 = baseDecoupler := by
  refine ⟨by abel, by abel, by abel, by abel, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
    (dsimp [RotorXY, doubledSys, mk2]; try noncomm_ring)
  · ext i j
    fin_cases i <;> fin_cases j <;>
    (dsimp [RotorXY, baseDecoupler, mk2]; try noncomm_ring)

end Block2

-- ============================================================================
-- SECTION 4 (𝔎𝔏₇): Master Synthesis & Cross-Module Bridge
-- ============================================================================

/--
**Theorem 6 (𝔎𝔏₇ — Master Kitaev Local Bulk Energy Gap, Universal Invertibility & $\Omega$-Spectrum Synthesis):**
Unifies all seven nodes ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$) of
`KitaevLocalGapOmegaSpectrumPoset` with the three-region Zorn–Kitaev interior disk projection of
`InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset`:
1. **7-Stage Poset Acyclicity:**
   `Function.Injective KitaevLocalGapOmegaSpectrumStage.rank` and
   `∀ s, ¬ KitaevLocalGapOmegaSpectrumStage.coverEdge s s`.
2. **0D Fiber Invariance & Spectral Annulus Midpoint Centering ($\mathfrak{KL}_1\text{–}\mathfrak{KL}_2$):**
   `((1 - t) * H0 + t * H1) * P0 = 0` (when `H0 * P0 = 0` and `H1 * P0 = 0`) and
   `(b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2 = 4 * (Q - a_sq) * (b_sq - Q)`.
3. **Square-First Local Bulk Gap Collar Healing & 3-Region Boundary Annihilation ($\mathfrak{KL}_3$):**
   `SquareFirstBulkOp P A μ0 - TruncateFirstBulkOp P A μ0 = -(N_plus P A * N_minus P A)` and
   `e1 P₁ * (chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂) * e1 P₁ = n12 P₁ P₂ A₁ * n21 P₁ P₂ C₁`.
4. **Hadamard Block Rotation, Universal Invertibility Rotor & Dimer Cancellation ($\mathfrak{KL}_4\text{–}\mathfrak{KL}_7$):**
   - `Block2.hadamard2 * Block2.diagDoubledSys A * Block2.hadamard2 = Block2.doubledSys (A + A)`,
   - `Block2.doubledSys A * Block2.baseDecoupler + Block2.baseDecoupler * Block2.doubledSys A = 0`,
   - `Block2.RotorXY A c s * Block2.RotorXY A c s = Block2.mk2 (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s)`,
   - `(A - A0) + (A0 - A0) + (A0 - A0) = A - A0`.
-/
lemma kl7_master_kitaev_local_gap_omega_spectrum_synthesis
    {B : Type u} [Ring B] {K : Type u} [CommRing K]
    (H0 H1 P0 t : B) (h0 : H0 * P0 = 0) (h1 : H1 * P0 = 0)
    (Q a_sq b_sq : K)
    (P A μ0 A0 c s : B) (hP : P * P = P)
    (hc : c * A = A * c) (hs : s * A = A * s) (hcs : c * s = s * c)
    (P₁ P₂ A₁ C₁ A₂ C₂ : B)
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    (Function.Injective KitaevLocalGapOmegaSpectrumStage.rank ∧
     ∀ st : KitaevLocalGapOmegaSpectrumStage, ¬ KitaevLocalGapOmegaSpectrumStage.coverEdge st st) ∧
    (((1 - t) * H0 + t * H1) * P0 = 0 ∧
     (b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2 = 4 * (Q - a_sq) * (b_sq - Q)) ∧
    (SquareFirstBulkOp P A μ0 - TruncateFirstBulkOp P A μ0 = - (N_plus P A * N_minus P A) ∧
     e1 P₁ * (chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂) * e1 P₁ =
       n12 P₁ P₂ A₁ * n21 P₁ P₂ C₁) ∧
    (Block2.hadamard2 * Block2.diagDoubledSys A * Block2.hadamard2 = Block2.doubledSys (A + A) ∧
     Block2.doubledSys A * Block2.baseDecoupler +
       Block2.baseDecoupler * Block2.doubledSys A = (0 : Block2 B) ∧
     Block2.RotorXY A c s * Block2.RotorXY A c s =
       Block2.mk2 (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s) ∧
     (A - A0) + (A0 - A0) + (A0 - A0) = A - A0) := by
  have hFib := convex_hamiltonian_fiber_ground_state_invariance H0 H1 P0 t h0 h1
  have hMid := energy_gap_annulus_midpoint_centering Q a_sq b_sq
  have hCollar := (square_first_local_bulk_gap_collar_healing P A μ0 hP).1
  have hDisk :=
    (InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset.ks4_interior_disk_projection_eliminates_boundary_modes
      (A₁ := A₁) (C₁ := C₁) (A₂ := A₂) (C₂ := C₂) h₁ h₂ h₁₂ h₂₁).2.2.2
  have hHad := (Block2.hadamard_conjugation_diag_to_offdiag_intertwining A).2.1
  have hRot := Block2.universal_invertibility_anticommuting_homotopy A A0 c s hc hs hcs
  exact ⟨⟨KitaevLocalGapOmegaSpectrumStage.rank_injective,
          KitaevLocalGapOmegaSpectrumStage.coverEdge_acyclic⟩,
    ⟨hFib, hMid⟩,
    ⟨hCollar, hDisk⟩,
    ⟨hHad, hRot.1, hRot.2.1, hRot.2.2⟩⟩

end InfoGeometry.Kitaev.KitaevLocalGapOmegaSpectrumPoset
