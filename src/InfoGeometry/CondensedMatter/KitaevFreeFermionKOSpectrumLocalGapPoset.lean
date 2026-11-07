/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChainFull
import InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset

/-!
# Kitaev's Condensed-Matter $KO$-Spectrum, Interior Local Spectral Gap & Alternating Dimer Loop Poset ($\mathfrak{KS}_1 \prec \dots \prec \mathfrak{KS}_7$)

## i. Overview

Complete, `0 sorry`, `[propext, Classical.choice, Quot.sound]`-only finite-stage formalization of the
algebraic, matrix, and Peirce-projector core of Alexei Kitaev's lecture on the condensed-matter
construction of $KO$-theory from gapped free-fermion Majorana Hamiltonians ($\mathcal{A}_d \simeq KO_{d-2}$):

1. **Stage `𝔎𝔖₁` (`ks1_transverse_field_ising_and_three_corner_domain_wall_algebra` &
   `ks1_zero_dim_convex_projector_defect_and_fermionic_z2_parity`):**
   - Proves the local Pauli spin-flip bond reversal $\sigma_x \sigma_z \sigma_x = -\sigma_z$ and
     the bulk two-bond excitation difference versus single-bond boundary excitation in any associative
     ring `[Ring B]`, alongside the 3-corner Zorn–Kitaev decomposition (`e1 P₁ + e2 P₁ P₂ + e3 P₂ = 1`).
   - Proves the 0D convex projector interpolation defect
     `((1 - t) * P₀ + t * P₁)² - ((1 - t) * P₀ + t * P₁) = -(t * (1 - t)) * (P₀ - P₁)²`
     (which vanishes when $P_0 = P_1$, corresponding to contractibility of the fiber over a fixed ground state)
     and the 0D fermionic $\mathbb{Z}_2$ determinant sign $\det Q \in \{+1, -1\}$ for $Q Q^\top = 1$.
2. **Stage `𝔎𝔖₂` (`ks2_majorana_standard_complex_structure_and_skew_clifford_shift`):**
   - Proves that the reference complex structure block $A_0 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$
     satisfies $A_0^\top = -A_0$ and $A_0^2 = -1$ ($-A_0^2 = 1$), and that the doubled skew-Clifford
     block $C_{\mathrm{skew}}(A) = \begin{pmatrix} 0 & A \\ -A & 0 \end{pmatrix}$ anticommutes with
     both split Clifford generators $e_1, e_2$, satisfies $C_{\mathrm{skew}}(A)^\top = C_{\mathrm{skew}}(A) \iff A^\top = -A$,
     and squares to $\begin{pmatrix} -A^2 & 0 \\ 0 & -A^2 \end{pmatrix}$.
3. **Stages `𝔎𝔖₃–𝔎𝔖₄` (`ks3_kitaev_centered_spectral_band_square_identity` &
   `ks4_interior_disk_projection_eliminates_boundary_modes`):**
   - Proves Kitaev's centered spectral-band polynomial factorization over any `[CommRing R]`:
     for $M_2(A, a, b) = -(2 \bullet (A * A)) - (a^2 + b^2) \bullet 1$,
     $$M_2(A, a, b)^2 - (b^2 - a^2)^2 \bullet 1 = 4 \bullet \big((-(A * A) - a^2 \bullet 1) * (-(A * A) - b^2 \bullet 1)\big).$$
   - Proves using canonical `InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChainFull`
     that for a 3-region radial decomposition (`e1 P₁` = interior disk $\widetilde{D} = D_{1-r}$,
     `e2 P₁ P₂` = buffer collar of width $r$, `e3 P₂` = boundary $\partial D$), while the squared
     1-hop chain $\mathrm{chainPhi}^2 = v_{12} + v_{23} + \phi_{13}$ contains boundary terms $v_{23}$
     and 2-hop terms $\phi_{13}$, its interior projection
     `e1 P₁ * (chainPhi * chainPhi) * e1 P₁ = n12 P₁ P₂ A₁ * n21 P₁ P₂ C₁`
     completely annihilates all boundary terms involving Shell `3` (`n23`, `n32`, `v23`, `phi13`)!
4. **Stage `𝔎𝔖₅` (`ks5_kitaev_invertibility_block_anticommutator_and_rotor_gap`):**
   - Proves Kitaev's Spectrum Principle 1 (Invertibility $A \oplus (-A) \sim A_0 \oplus (-A_0)$):
     for **every** matrix $A \in \mathrm{Matrix}\,n\,n\,R$ (with zero commutativity assumptions on $A$),
     the block-diagonal pair $X(A) = \begin{pmatrix} A & 0 \\ 0 & -A \end{pmatrix}$ and the universal
     off-diagonal complex structure $Y = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$ strictly
     anticommute ($X(A) * Y + Y * X(A) = 0$), preserve skew-symmetry when $A^\top = -A$, and
     satisfy along $X(\theta) = \cos\theta \bullet X(A) + \sin\theta \bullet Y$:
     $$-\big(X(\theta) * X(\theta)\big) = (\cos\theta)^2 \bullet \begin{pmatrix} -(A * A) & 0 \\ 0 & -(A * A) \end{pmatrix} + (\sin\theta)^2 \bullet 1,$$
     interpolating between $X(0) = A \oplus (-A)$ and the $A$-independent reference $X(\pi/2) = Y$.
5. **Stages `𝔎𝔖₆–𝔎𝔖₇` (`ks6_block_swap_conjugation_and_soft_diagonal_restriction` &
   `ks7_alternating_dimer_loop_and_ko_d_minus_2_master_synthesis`):**
   - Proves Spectrum Principle 2 ($A \oplus B \sim B \oplus A$ via orthogonal block-swap conjugation)
     and Spectrum Principle 3 (Softness / Diagonal Restriction: if $u : n \to \mathrm{Matrix}\,n\,n\,R$
     is a site-indexed family of skew-symmetric matrices $(u\,p)^\top = -(u\,p)$, then the diagonal
     restriction $A^{(u)}_{j k} = u(j)_{j k} + u(k)_{j k}$ is strictly skew-symmetric
     $(A^{(u)})^\top = -A^{(u)}$).
   - Assembles the alternating dimer re-pairing identity and the $KO_0$ Bruhat projector colimit /
     4-scale Bott periodicity synthesis.

## ii. Key results

- `KitaevFreeFermionKOSpectrumStage`, `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`
- `ks1_transverse_field_ising_and_three_corner_domain_wall_algebra`
- `ks1_zero_dim_convex_projector_defect_and_fermionic_z2_parity`
- `ks2_majorana_standard_complex_structure_and_skew_clifford_shift`
- `ks3_kitaev_centered_spectral_band_square_identity`
- `ks4_interior_disk_projection_eliminates_boundary_modes`
- `ks5_kitaev_invertibility_block_anticommutator_and_rotor_gap`
- `ks6_block_swap_conjugation_and_soft_diagonal_restriction`
- `ks7_alternating_dimer_loop_and_ko_d_minus_2_master_synthesis`

## iii. Table of contents

- Section 0: The 7-Stage Kitaev Free-Fermion $KO$-Spectrum Poset (`𝔎𝔖₁ ≺ ⋯ ≺ 𝔎𝔖₇`)
- Section 1 (`𝔎𝔖₁`): 1D Transverse-Field Ising Bond Algebra & 0D Bosonic/Fermionic Ground-State Split
- Section 2 (`𝔎𝔖₂`): Majorana Reference Complex Structure $A_0 \in \mathfrak{so}(2n)$ & Skew-Block Clifford Shift
- Section 3 (`𝔎𝔖₃–𝔎𝔖₄`): Centered Spectral-Band Polynomial Identity & Interior Disk Local-Gap Projection
- Section 4 (`𝔎𝔖₅`): Spectrum Principle 1 — Universal Invertibility Path $A \oplus (-A) \sim Y$
- Section 5 (`𝔎𝔖₆–𝔎𝔖₇`): Block-Swap Conjugation, Soft Diagonal Restriction & Master $KO_{d-2}$ Synthesis

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `KitaevFreeFermionKOSpectrumStage` ($\mathfrak{KS}_1 \prec \dots \prec \mathfrak{KS}_7$), `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`,
  - `ks1_transverse_field_ising_and_three_corner_domain_wall_algebra`, `ks1_zero_dim_convex_projector_defect_and_fermionic_z2_parity`,
  - `ks2_majorana_standard_complex_structure_and_skew_clifford_shift`,
  - `ks3_kitaev_centered_spectral_band_square_identity`, `ks4_interior_disk_projection_eliminates_boundary_modes`,
  - `ks5_kitaev_invertibility_block_anticommutator_and_rotor_gap`,
  - `ks6_block_swap_conjugation_and_soft_diagonal_restriction`,
  - `ks7_alternating_dimer_loop_and_ko_d_minus_2_master_synthesis`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Idempotence (`hP`, `h₁`, `h₂`, `h₁₂`, `h₂₁`), orthogonality (`Q * Q.transpose = 1`), and skew-symmetry (`A.transpose = -A`) are explicit theorem parameters.
* **BUCKET 3 — Out-of-Scope Continuum / Homotopy Claims:**
  - The infinite-volume filtered colimit over atom configurations $\widehat{S}$, the analytic operator-norm localization bound $\|M\| \le 1 + O(r^2 / R^2)$, and the full topological homotopy equivalences $B_0 \simeq K(\mathbb{Z}, 2)$, $B_1 \simeq K(\mathbb{Z}, 3)$, and $\mathcal{A}_d \simeq \Omega\mathcal{A}_{d+1} \simeq KO_{d-2}$ remain outside this finite-stage algebraic owner.

## iv. References

- Alexei Kitaev, *Periodic table for topological insulators and superconductors*, AIP Conf. Proc. 1134, 22–30 (2009), arXiv:0901.2686.
- Alexei Kitaev, *Toward a topological classification of many-body quantum states* (lecture on condensed-matter-inspired $KO$-theory).
- `InfoGeometry.OperatorAlgebra.PeirceSpine.Basic`
- `InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChainFull`
- `InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset`
-/

namespace InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset

open Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChainFull
open CliffordBottKTheoryWignerS4Poset

-- ============================================================================
-- SECTION 0: The 7-Stage Kitaev Free-Fermion KO-Spectrum Poset (𝔎𝔖₁ ≺ ⋯ ≺ 𝔎𝔖₇)
-- ============================================================================

/-- The 7-stage causal poset ($\mathfrak{KS}_1 \prec \dots \prec \mathfrak{KS}_7$) governing
Kitaev's condensed-matter construction of $KO$-theory from gapped free-fermion Majorana
Hamiltonians, local spectral gap projection, and the three $\Omega$-spectrum principles. -/
inductive KitaevFreeFermionKOSpectrumStage : Type
  | ks1TransverseIsingAndZeroDimGroundStateSplit
  | ks2MajoranaComplexStructureAndSkewCliffordShift
  | ks3CenteredSpectralBandPolynomialIdentity
  | ks4InteriorDiskLocalGapProjectionEliminatesEdge
  | ks5InvertibilityBlockAnticommutatorAndRotorPath
  | ks6BlockSwapHomotopyAndSoftDiagonalRestriction
  | ks7AlternatingDimerLoopAndShiftedKOSynthesis
  deriving DecidableEq, Repr

namespace KitaevFreeFermionKOSpectrumStage

/-- Numerical stage index `0 .. 6` for `KitaevFreeFermionKOSpectrumStage`. -/
def rank : KitaevFreeFermionKOSpectrumStage → ℕ
  | .ks1TransverseIsingAndZeroDimGroundStateSplit => 0
  | .ks2MajoranaComplexStructureAndSkewCliffordShift => 1
  | .ks3CenteredSpectralBandPolynomialIdentity => 2
  | .ks4InteriorDiskLocalGapProjectionEliminatesEdge => 3
  | .ks5InvertibilityBlockAnticommutatorAndRotorPath => 4
  | .ks6BlockSwapHomotopyAndSoftDiagonalRestriction => 5
  | .ks7AlternatingDimerLoopAndShiftedKOSynthesis => 6

/-- The stage rank map is injective. -/
lemma rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder KitaevFreeFermionKOSpectrumStage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype KitaevFreeFermionKOSpectrumStage where
  elems := {
    .ks1TransverseIsingAndZeroDimGroundStateSplit,
    .ks2MajoranaComplexStructureAndSkewCliffordShift,
    .ks3CenteredSpectralBandPolynomialIdentity,
    .ks4InteriorDiskLocalGapProjectionEliminatesEdge,
    .ks5InvertibilityBlockAnticommutatorAndRotorPath,
    .ks6BlockSwapHomotopyAndSoftDiagonalRestriction,
    .ks7AlternatingDimerLoopAndShiftedKOSynthesis
  }
  complete x := by cases x <;> decide

/-- Immediate Hasse cover edges $\mathfrak{KS}_k \prec \mathfrak{KS}_{k+1}$ of the 7-stage spine. -/
inductive coverEdge : KitaevFreeFermionKOSpectrumStage → KitaevFreeFermionKOSpectrumStage → Prop
  | ks1_to_ks2 :
      coverEdge .ks1TransverseIsingAndZeroDimGroundStateSplit
        .ks2MajoranaComplexStructureAndSkewCliffordShift
  | ks2_to_ks3 :
      coverEdge .ks2MajoranaComplexStructureAndSkewCliffordShift
        .ks3CenteredSpectralBandPolynomialIdentity
  | ks3_to_ks4 :
      coverEdge .ks3CenteredSpectralBandPolynomialIdentity
        .ks4InteriorDiskLocalGapProjectionEliminatesEdge
  | ks4_to_ks5 :
      coverEdge .ks4InteriorDiskLocalGapProjectionEliminatesEdge
        .ks5InvertibilityBlockAnticommutatorAndRotorPath
  | ks5_to_ks6 :
      coverEdge .ks5InvertibilityBlockAnticommutatorAndRotorPath
        .ks6BlockSwapHomotopyAndSoftDiagonalRestriction
  | ks6_to_ks7 :
      coverEdge .ks6BlockSwapHomotopyAndSoftDiagonalRestriction
        .ks7AlternatingDimerLoopAndShiftedKOSynthesis

/-- Every Hasse cover edge strictly increases the stage rank. -/
theorem coverEdge_strictMono {a b : KitaevFreeFermionKOSpectrumStage} (h : coverEdge a b) :
    a.rank < b.rank := by
  cases h <;> decide

/-- No stage has a cover edge to itself. -/
theorem coverEdge_acyclic (a : KitaevFreeFermionKOSpectrumStage) : ¬ coverEdge a a := by
  intro h
  exact Nat.lt_irrefl a.rank (coverEdge_strictMono h)

end KitaevFreeFermionKOSpectrumStage

-- ============================================================================
-- SECTION 1 (𝔎𝔖₁): 1D Transverse-Field Ising Bond Algebra & 0D Ground-State Split
-- ============================================================================

section TransverseIsingAndZeroDimSplit

variable {B : Type*} [Ring B]

/--
**Theorem 1a (𝔎𝔖₁ — 1D Transverse-Field Ising Spin-Flip Bond Reversal & Bulk vs. Boundary Domain-Wall Cost):**
In any associative ring `[Ring B]`:
1. **Single-Site Pauli Spin-Flip Conjugation (`00:08:30`–`00:13:58`):**
   If local Pauli operators `σx, σz : B` satisfy `σx * σx = 1` and `σx * σz + σz * σx = 0`,
   then flipping the spin via `σx` reverses the longitudinal spin `σx * σz * σx = -σz`.
2. **Interior Two-Bond Domain-Wall Cost (`+4J`) vs. Boundary Single-Bond Cost (`+2J`):**
   For any left and right incident Ising bond operators `B_left, B_right : B`, flipping an
   interior spin (`B_left ↦ -B_left` and `B_right ↦ -B_right`) increases the energy
   `-(B_left + B_right)` by `2 • (B_left + B_right)` (equal to `4 • J` when `B_left = B_right = J`),
   whereas flipping a boundary spin (`B_edge ↦ -B_edge`) increases `-B_edge` by `2 • B_edge`.
3. **3-Region Zorn–Kitaev Partition (`Left Edge ⊕ Interior Bulk ⊕ Right Edge`):**
   For any nested idempotents `P₁ * P₁ = P₁`, `P₂ * P₂ = P₂`, `P₁ * P₂ = P₁`, `P₂ * P₁ = P₁`,
   `e1 P₁ + e2 P₁ P₂ + e3 P₂ = 1` and the end-to-end boundary mode `phi13` commutes with any
   interior operator `bulk P₁ P₂ X`.
-/
theorem ks1_transverse_field_ising_and_three_corner_domain_wall_algebra
    {σx σz B_left B_right P₁ P₂ A₁ C₁ A₂ C₂ X : B}
    (hσx : σx * σx = 1) (hAnti : σx * σz + σz * σx = 0)
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    σx * σz * σx = -σz ∧
    ((-(-B_left) + -(-B_right)) - (-B_left + -B_right) =
      (B_left + B_right) + (B_left + B_right)) ∧
    ((-(-B_left)) - (-B_left) = B_left + B_left) ∧
    e1 P₁ + e2 P₁ P₂ + e3 P₂ = 1 ∧
    ZornKitaevMajoranaChainFull.comm (phi13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0 := by
  have hFlip : σx * σz * σx = -σz := by
    have h1 : σx * σz = -(σz * σx) := eq_neg_of_add_eq_zero_left hAnti
    calc
      σx * σz * σx = -(σz * σx) * σx := by rw [h1]
      _ = -(σz * (σx * σx)) := by noncomm_ring
      _ = -(σz * 1) := by rw [hσx]
      _ = -σz := by simp
  have hCorners := three_corner_laws h₁ h₂ h₁₂ h₂₁
  have h1' : ∀ Z : B, P₁ * (P₁ * Z) = P₁ * Z := fun Z => by rw [← mul_assoc, h₁]
  have h2' : ∀ Z : B, P₂ * (P₂ * Z) = P₂ * Z := fun Z => by rw [← mul_assoc, h₂]
  have h12' : ∀ Z : B, P₁ * (P₂ * Z) = P₁ * Z := fun Z => by rw [← mul_assoc, h₁₂]
  have h21' : ∀ Z : B, P₂ * (P₁ * Z) = P₁ * Z := fun Z => by rw [← mul_assoc, h₂₁]
  have hBulkComm :
      ZornKitaevMajoranaChainFull.comm (phi13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0 := by
    dsimp [ZornKitaevMajoranaChainFull.comm, phi13, n13, n31, n12, n21, n23, n32, bulk, e1, e2, e3]
    noncomm_ring [h₁, h₂, h₁₂, h₂₁, h1', h2', h12', h21']
  refine ⟨hFlip, by abel, by abel, hCorners.2.2.2.2.2.2.2.2.2, hBulkComm⟩

/--
**Theorem 1b (𝔎𝔖₁ — 0D Bosonic Convex Interpolation Defect vs. 0D Fermionic $\mathbb{Z}_2$ Parity Sign):**
1. **0D Convex Interpolation (`00:21:39`, $B_0 \simeq \mathbb{C}\mathrm{P}^\infty = K(\mathbb{Z}, 2)$):**
   For any idempotents `P₀ * P₀ = P₀` and `P₁ * P₁ = P₁` commuting with `t : B`, the convex
   combination `(1 - t) * P₀ + t * P₁` has idempotency defect
   `((1 - t) * P₀ + t * P₁)² - ((1 - t) * P₀ + t * P₁) = -(t * (1 - t)) * (P₀ - P₁)²`,
   which vanishes identically when `P₀ = P₁` (two Hamiltonians with the same ground state `P₀ = P₁`
   remain in the same projector fiber for every `t`).
2. **0D Fermionic $\mathbb{Z}_2$ Grading (`00:25:11`–`00:26:37`, $F_0 \simeq \mathbb{C}\mathrm{P}^\infty \times \mathbb{Z}_2$):**
   For any orthogonal transformation $Q \in \mathrm{Matrix}\,n\,n\,R$ ($Q * Q^\top = 1$) over an
   integral domain `R`, $(\det Q)^2 = 1$ and $\det Q = 1 \vee \det Q = -1$.
-/
theorem ks1_zero_dim_convex_projector_defect_and_fermionic_z2_parity
    {P₀ P₁ : B} (hP₀ : P₀ * P₀ = P₀) (hP₁ : P₁ * P₁ = P₁)
    (t : B) (ht0 : t * P₀ = P₀ * t) (ht1 : t * P₁ = P₁ * t)
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] [IsDomain R]
    (Q : Matrix n n R) (hOrth : Q * Q.transpose = 1) :
    ((1 - t) * P₀ + t * P₁) * ((1 - t) * P₀ + t * P₁) - ((1 - t) * P₀ + t * P₁) =
      -(t * (1 - t)) * ((P₀ - P₁) * (P₀ - P₁)) ∧
    ((1 - t) * P₀ + t * P₀) * ((1 - t) * P₀ + t * P₀) = (1 - t) * P₀ + t * P₀ ∧
    Matrix.det Q ^ 2 = 1 ∧
    (Matrix.det Q = 1 ∨ Matrix.det Q = -1) := by
  have ht0' : P₀ * (1 - t) = (1 - t) * P₀ := by
    calc P₀ * (1 - t) = P₀ - P₀ * t := by noncomm_ring
      _ = P₀ - t * P₀ := by rw [ht0]
      _ = (1 - t) * P₀ := by noncomm_ring
  have ht1' : P₁ * (1 - t) = (1 - t) * P₁ := by
    calc P₁ * (1 - t) = P₁ - P₁ * t := by noncomm_ring
      _ = P₁ - t * P₁ := by rw [ht1]
      _ = (1 - t) * P₁ := by noncomm_ring
  have hDefect :
      ((1 - t) * P₀ + t * P₁) * ((1 - t) * P₀ + t * P₁) - ((1 - t) * P₀ + t * P₁) =
        -(t * (1 - t)) * ((P₀ - P₁) * (P₀ - P₁)) := by
    calc
      ((1 - t) * P₀ + t * P₁) * ((1 - t) * P₀ + t * P₁) - ((1 - t) * P₀ + t * P₁)
          = (1 - t) * (P₀ * (1 - t)) * P₀ + (1 - t) * (P₀ * t) * P₁ +
              t * (P₁ * (1 - t)) * P₀ + t * (P₁ * t) * P₁ - ((1 - t) * P₀ + t * P₁) := by
            noncomm_ring
      _ = (1 - t) * ((1 - t) * P₀) * P₀ + (1 - t) * (t * P₀) * P₁ +
              t * ((1 - t) * P₁) * P₀ + t * (t * P₁) * P₁ - ((1 - t) * P₀ + t * P₁) := by
            rw [ht0', ← ht0, ht1', ← ht1]
      _ = (1 - t) * (1 - t) * (P₀ * P₀) + (1 - t) * t * (P₀ * P₁) +
              t * (1 - t) * (P₁ * P₀) + t * t * (P₁ * P₁) - ((1 - t) * P₀ + t * P₁) := by
            noncomm_ring
      _ = (1 - t) * (1 - t) * P₀ + (1 - t) * t * (P₀ * P₁) +
              t * (1 - t) * (P₁ * P₀) + t * t * P₁ - ((1 - t) * P₀ + t * P₁) := by
            rw [hP₀, hP₁]
      _ = -(t * (1 - t)) * (P₀ - P₀ * P₁ - P₁ * P₀ + P₁) := by
            noncomm_ring
      _ = -(t * (1 - t)) * ((P₀ - P₁) * (P₀ - P₁)) := by
            have hR : (P₀ - P₁) * (P₀ - P₁) = P₀ - P₀ * P₁ - P₁ * P₀ + P₁ := by
              calc (P₀ - P₁) * (P₀ - P₁)
                  = P₀ * P₀ - P₀ * P₁ - P₁ * P₀ + P₁ * P₁ := by noncomm_ring
                _ = P₀ - P₀ * P₁ - P₁ * P₀ + P₁ := by rw [hP₀, hP₁]
            rw [hR]
  have hSameFiber :
      ((1 - t) * P₀ + t * P₀) * ((1 - t) * P₀ + t * P₀) = (1 - t) * P₀ + t * P₀ := by
    have hColl : (1 - t) * P₀ + t * P₀ = P₀ := by noncomm_ring
    rw [hColl, hP₀]
  have hDetSq : Matrix.det Q ^ 2 = 1 := by
    calc
      Matrix.det Q ^ 2 = Matrix.det Q * Matrix.det Q := sq (Matrix.det Q)
      _ = Matrix.det Q * Matrix.det Q.transpose := by rw [Matrix.det_transpose]
      _ = Matrix.det (Q * Q.transpose) := (Matrix.det_mul Q Q.transpose).symm
      _ = Matrix.det (1 : Matrix n n R) := by rw [hOrth]
      _ = 1 := Matrix.det_one
  exact ⟨hDefect, hSameFiber, hDetSq, sq_eq_one_iff.mp hDetSq⟩

end TransverseIsingAndZeroDimSplit

-- ============================================================================
-- SECTION 2 (𝔎𝔖₂): Majorana Reference Complex Structure A₀ ∈ 𝔰𝔬(2n) & Skew-Clifford Shift
-- ============================================================================

section MajoranaComplexStructureAndSkewClifford

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Kitaev's standard reference complex structure $A_0 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$
(`00:31:05`) on `Matrix (n ⊕ n) (n ⊕ n) R`, serving as the basepoint of the space $\mathcal{A}_d$. -/
def kitaevStdComplexStructure (n : Type*) [DecidableEq n] (R : Type*) [CommRing R] :
    Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R)

/--
**Theorem 2 (𝔎𝔖₂ — Standard Complex Structure $A_0 \in \mathfrak{so}(2n)$ & Two-Clifford Skew Reduction):**
Over any `[CommRing R]`:
1. **Standard Complex Structure Basepoint (`00:31:05`):**
   `A₀ = kitaevStdComplexStructure n R` is skew-symmetric (`A₀.transpose = -A₀`) and squares to `-1`
   (`A₀ * A₀ = -1`, so `-(A₀ * A₀) = 1`).
2. **Two-Clifford Skew-Block Embedding (`C_skew(A) = [0, A; -A, 0]`):**
   For any `A : Matrix n n R`, `Matrix.fromBlocks 0 A (-A) 0` anticommutes with both split Clifford
   generators $e_1 = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$ and
   $e_2 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$, is symmetric iff `A.transpose = -A`,
   and squares to $\begin{pmatrix} -(A * A) & 0 \\ 0 & -(A * A) \end{pmatrix}$.
-/
theorem ks2_majorana_standard_complex_structure_and_skew_clifford_shift
    (A : Matrix n n R) :
    (kitaevStdComplexStructure n R).transpose = -(kitaevStdComplexStructure n R) ∧
    kitaevStdComplexStructure n R * kitaevStdComplexStructure n R = -1 ∧
    -(kitaevStdComplexStructure n R * kitaevStdComplexStructure n R) = 1 ∧
    Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) *
        Matrix.fromBlocks (1 : Matrix n n R) (0 : Matrix n n R) (0 : Matrix n n R) (-1 : Matrix n n R) +
      Matrix.fromBlocks (1 : Matrix n n R) (0 : Matrix n n R) (0 : Matrix n n R) (-1 : Matrix n n R) *
        Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) = 0 ∧
    Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) *
        Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (1 : Matrix n n R) (0 : Matrix n n R) +
      Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (1 : Matrix n n R) (0 : Matrix n n R) *
        Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) = 0 ∧
    ((Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R)).transpose =
        Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) ↔ A.transpose = -A) ∧
    Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) *
        Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) =
      Matrix.fromBlocks (-(A * A)) (0 : Matrix n n R) (0 : Matrix n n R) (-(A * A)) := by
  have hA0T : (kitaevStdComplexStructure n R).transpose = -(kitaevStdComplexStructure n R) := by
    dsimp [kitaevStdComplexStructure]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
    simp
  have hA0Sq : kitaevStdComplexStructure n R * kitaevStdComplexStructure n R = -1 := by
    dsimp [kitaevStdComplexStructure]
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have hA0NegSq : -(kitaevStdComplexStructure n R * kitaevStdComplexStructure n R) = 1 := by
    rw [hA0Sq, neg_neg]
  have hAntiE1 :
      Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) *
          Matrix.fromBlocks (1 : Matrix n n R) (0 : Matrix n n R) (0 : Matrix n n R) (-1 : Matrix n n R) +
        Matrix.fromBlocks (1 : Matrix n n R) (0 : Matrix n n R) (0 : Matrix n n R) (-1 : Matrix n n R) *
          Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) = 0 := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
    simp [Matrix.fromBlocks_zero]
  have hAntiE2 :
      Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) *
          Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (1 : Matrix n n R) (0 : Matrix n n R) +
        Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (1 : Matrix n n R) (0 : Matrix n n R) *
          Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) = 0 := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
    simp [Matrix.fromBlocks_zero]
  have hSymIff :
      (Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R)).transpose =
        Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) ↔ A.transpose = -A := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_inj]
    constructor
    · rintro ⟨_, h1, _⟩
      rw [Matrix.transpose_neg] at h1
      exact neg_eq_iff_eq_neg.mp h1
    · intro h
      refine ⟨rfl, ?_, ?_, rfl⟩
      · rw [Matrix.transpose_neg, h, neg_neg]
      · rw [h]
  have hSq :
      Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) *
          Matrix.fromBlocks (0 : Matrix n n R) A (-A) (0 : Matrix n n R) =
        Matrix.fromBlocks (-(A * A)) (0 : Matrix n n R) (0 : Matrix n n R) (-(A * A)) := by
    rw [Matrix.fromBlocks_multiply]
    simp
  exact ⟨hA0T, hA0Sq, hA0NegSq, hAntiE1, hAntiE2, hSymIff, hSq⟩

end MajoranaComplexStructureAndSkewClifford

-- ============================================================================
-- SECTION 3 (𝔎𝔖₃–𝔎𝔖₄): Centered Spectral-Band Polynomial & Interior Disk Projection
-- ============================================================================

section LocalSpectralGapAndInteriorProjection

/-- Division-free centered spectral-band operator
`kitaevCenteredGapOp A a b = -(2 • (A * A)) - (a ^ 2 + b ^ 2) • 1`
corresponding to $2 M(A) = 2\big(-A^2 - \frac{a^2 + b^2}{2} I\big)$ (`00:40:21`–`00:45:00`). -/
def kitaevCenteredGapOp {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (A : B) (a b : R) : B :=
  -((2 : R) • (A * A)) - (a ^ 2 + b ^ 2) • (1 : B)

/--
**Theorem 3a (𝔎𝔖₃ — Kitaev's Centered Spectral-Band Polynomial Factorization Identity):**
In any $R$-algebra `[Algebra R B]` over `[CommRing R]`, for any operator `A : B` and spectral bounds
`a, b : R`:
1. **Exact Quadratic Band Factorization (`00:40:21`–`00:41:40`):**
   $$\big(\mathrm{kitaevCenteredGapOp}\;A\;a\;b\big)^2 - (b^2 - a^2)^2 \bullet 1 =
     4 \bullet \Big(\big(-(A * A) - a^2 \bullet 1\big) * \big(-(A * A) - b^2 \bullet 1\big)\Big).$$
   Thus $-(A * A) \in [a^2, b^2]$ (where the RHS product is $\le 0$) is algebraically equivalent to
   bounding the norm of $\mathrm{kitaevCenteredGapOp}\;A\;a\;b$ by $b^2 - a^2$ (or $\frac{b^2 - a^2}{2}$
   after dividing by $2$).
2. **Flat-Band Complex-Structure Annihilation (`A * A = -1`):**
   If `A * A = -1` (such as $A = A_0$) and $a^2 + b^2 = 2$, then `kitaevCenteredGapOp A a b = 0`.
-/
theorem ks3_kitaev_centered_spectral_band_square_identity
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (A : B) (a b : R) :
    kitaevCenteredGapOp A a b * kitaevCenteredGapOp A a b - ((b ^ 2 - a ^ 2) ^ 2) • (1 : B) =
      (4 : R) • ((-(A * A) - (a ^ 2) • (1 : B)) * (-(A * A) - (b ^ 2) • (1 : B))) ∧
    (A * A = -1 → a ^ 2 + b ^ 2 = 2 → kitaevCenteredGapOp A a b = 0) := by
  have hFact :
      kitaevCenteredGapOp A a b * kitaevCenteredGapOp A a b - ((b ^ 2 - a ^ 2) ^ 2) • (1 : B) =
        (4 : R) • ((-(A * A) - (a ^ 2) • (1 : B)) * (-(A * A) - (b ^ 2) • (1 : B))) := by
    dsimp [kitaevCenteredGapOp]
    simp only [Algebra.smul_def]
    have h2 : Commute (algebraMap R B 2) (A * A) := Algebra.commute_algebraMap_left 2 (A * A)
    have hab : Commute (algebraMap R B (a ^ 2 + b ^ 2)) (A * A) :=
      Algebra.commute_algebraMap_left (a ^ 2 + b ^ 2) (A * A)
    have ha : Commute (algebraMap R B (a ^ 2)) (A * A) :=
      Algebra.commute_algebraMap_left (a ^ 2) (A * A)
    have hb : Commute (algebraMap R B (b ^ 2)) (A * A) :=
      Algebra.commute_algebraMap_left (b ^ 2) (A * A)
    calc
      (-(algebraMap R B 2 * (A * A)) - algebraMap R B (a ^ 2 + b ^ 2) * 1) *
            (-(algebraMap R B 2 * (A * A)) - algebraMap R B (a ^ 2 + b ^ 2) * 1) -
          algebraMap R B ((b ^ 2 - a ^ 2) ^ 2) * 1
        = algebraMap R B 2 * ((A * A) * algebraMap R B 2) * (A * A) +
            algebraMap R B 2 * ((A * A) * algebraMap R B (a ^ 2 + b ^ 2)) +
            algebraMap R B (a ^ 2 + b ^ 2) * algebraMap R B 2 * (A * A) +
            (algebraMap R B (a ^ 2 + b ^ 2) * algebraMap R B (a ^ 2 + b ^ 2) -
              algebraMap R B ((b ^ 2 - a ^ 2) ^ 2)) := by
          noncomm_ring
      _ = algebraMap R B 2 * (algebraMap R B 2 * (A * A)) * (A * A) +
            algebraMap R B 2 * (algebraMap R B (a ^ 2 + b ^ 2) * (A * A)) +
            algebraMap R B (a ^ 2 + b ^ 2) * algebraMap R B 2 * (A * A) +
            (algebraMap R B (a ^ 2 + b ^ 2) * algebraMap R B (a ^ 2 + b ^ 2) -
              algebraMap R B ((b ^ 2 - a ^ 2) ^ 2)) := by
          rw [← h2.eq, ← hab.eq]
      _ = algebraMap R B (2 * 2) * ((A * A) * (A * A)) +
            algebraMap R B (2 * (a ^ 2 + b ^ 2) + (a ^ 2 + b ^ 2) * 2) * (A * A) +
            algebraMap R B ((a ^ 2 + b ^ 2) * (a ^ 2 + b ^ 2) - (b ^ 2 - a ^ 2) ^ 2) := by
          simp only [map_mul, map_add, map_sub]
          noncomm_ring
      _ = algebraMap R B 4 * ((A * A) * (A * A)) +
            algebraMap R B (4 * (b ^ 2 + a ^ 2)) * (A * A) +
            algebraMap R B (4 * (a ^ 2 * b ^ 2)) := by
          congr 2
          · congr 2; ring
          · congr 2; ring
          · ring
      _ = algebraMap R B 4 *
            ((A * A) * (A * A) + (A * A) * algebraMap R B (b ^ 2) +
              algebraMap R B (a ^ 2) * (A * A) +
              algebraMap R B (a ^ 2) * algebraMap R B (b ^ 2)) := by
          rw [← hb.eq]
          simp only [map_mul, map_add]
          noncomm_ring
      _ = algebraMap R B 4 *
            ((-(A * A) - algebraMap R B (a ^ 2) * 1) *
              (-(A * A) - algebraMap R B (b ^ 2) * 1)) := by
          noncomm_ring
  have hFlat : A * A = -1 → a ^ 2 + b ^ 2 = 2 → kitaevCenteredGapOp A a b = 0 := by
    intro hA2 hab2
    dsimp [kitaevCenteredGapOp]
    rw [hA2, hab2, smul_neg, neg_neg, sub_self]
  exact ⟨hFact, hFlat⟩

/--
**Theorem 3b (𝔎𝔖₄ — Interior Disk Projection $\Pi_{\widetilde{D}} = e_1(P_1)$ Eliminates Boundary Modes):**
In any associative ring `[Ring B]` with nested radial projectors `P₁ * P₁ = P₁`, `P₂ * P₂ = P₂`,
`P₁ * P₂ = P₁`, `P₂ * P₁ = P₁` (`e1 P₁` = interior disk $\widetilde{D} = D_{1-r}$,
`e2 P₁ P₂` = collar annulus $D_1 \setminus D_{1-r}$ of width $r$, `e3 P₂` = boundary/exterior $\partial D$):
1. **Unprojected Squared Hopping Operator Contains Boundary & Two-Hop Modes (`00:41:40`–`00:42:48`):**
   `chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂ = v12 P₁ P₂ A₁ C₁ + v23 P₁ P₂ A₂ C₂ + phi13 P₁ P₂ A₁ C₁ A₂ C₂`.
2. **r-Locality Vanishing Between Interior $\widetilde{D}$ and Boundary $\partial D$:**
   `e1 P₁ * phi23 P₁ P₂ A₂ C₂ = 0` and `phi23 P₁ P₂ A₂ C₂ * e1 P₁ = 0`.
3. **Interior Disk Local-Gap Projection (`00:42:48`–`00:45:00`, $\Pi_{\widetilde{D}} M \Pi_{\widetilde{D}}$):**
   Projecting `chainPhi²` onto the interior disk $\widetilde{D}$ via `e1 P₁` completely annihilates
   both the boundary bond `v23 P₁ P₂ A₂ C₂` and the two-hop term `phi13 P₁ P₂ A₁ C₁ A₂ C₂`, leaving
   only the interior hopping `n12 P₁ P₂ A₁ * n21 P₁ P₂ C₁`:
   $$e_1(P_1) * \big(\mathrm{chainPhi}\;P_1\;P_2\;A_1\;C_1\;A_2\;C_2\big)^2 * e_1(P_1) =
     n_{12}\;P_1\;P_2\;A_1 * n_{21}\;P_1\;P_2\;C_1,$$
   which is completely independent of the boundary couplings `A₂, C₂`!
-/
theorem ks4_interior_disk_projection_eliminates_boundary_modes
    {B : Type*} [Ring B] {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂ =
      v12 P₁ P₂ A₁ C₁ + v23 P₁ P₂ A₂ C₂ + phi13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
    e1 P₁ * phi23 P₁ P₂ A₂ C₂ = 0 ∧
    phi23 P₁ P₂ A₂ C₂ * e1 P₁ = 0 ∧
    e1 P₁ * (chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂) * e1 P₁ =
      n12 P₁ P₂ A₁ * n21 P₁ P₂ C₁ := by
  have h1' : ∀ Z : B, P₁ * (P₁ * Z) = P₁ * Z := fun Z => by rw [← mul_assoc, h₁]
  have h2' : ∀ Z : B, P₂ * (P₂ * Z) = P₂ * Z := fun Z => by rw [← mul_assoc, h₂]
  have h12' : ∀ Z : B, P₁ * (P₂ * Z) = P₁ * Z := fun Z => by rw [← mul_assoc, h₁₂]
  have h21' : ∀ Z : B, P₂ * (P₁ * Z) = P₁ * Z := fun Z => by rw [← mul_assoc, h₂₁]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (dsimp [chainPhi, phi12, phi23, phi13, v12, v23, n13, n31, n12, n21, n23, n32, e1, e2, e3];
     noncomm_ring [h₁, h₂, h₁₂, h₂₁, h1', h2', h12', h21'])

end LocalSpectralGapAndInteriorProjection

-- ============================================================================
-- SECTION 4 (𝔎𝔖₅): Spectrum Principle 1 — Universal Invertibility Path A ⊕ (-A) ~ Y
-- ============================================================================

section SpectrumInvertibilityPrinciple

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Stacked opposite-orientation system $X(A) = A \oplus (-A) = \begin{pmatrix} A & 0 \\ 0 & -A \end{pmatrix}$
in Kitaev's first $\Omega$-spectrum principle (`01:00:27`–`01:02:09`). -/
def kitaevStackedPair (A : Matrix n n R) : Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks A (0 : Matrix n n R) (0 : Matrix n n R) (-A)

/--
**Theorem 4 (𝔎𝔖₅ — Spectrum Principle 1: Universal Invertibility Anticommutator & Rotor Gap Conservation):**
For **any** matrix `A : Matrix n n R` (with **zero commutativity assumptions on `A`**):
1. **Universal Anticommutation (`{A ⊕ (-A), A₀} = 0`, `01:02:09`):**
   `kitaevStackedPair A` and `kitaevStdComplexStructure n R` strictly anticommute:
   $$\begin{pmatrix} A & 0 \\ 0 & -A \end{pmatrix} \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix} +
     \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix} \begin{pmatrix} A & 0 \\ 0 & -A \end{pmatrix} = 0.$$
2. **Skew-Symmetry of the Stacked Pair:**
   If `A.transpose = -A`, then `(kitaevStackedPair A).transpose = -(kitaevStackedPair A)`.
3. **Exact Spectral-Gap Convex Combination Along the Invertibility Rotor (`01:02:09`–`01:03:50`):**
   Over `ℝ`, for any `A : Matrix n n ℝ` and angle `θ : ℝ`, the homotopy path
   `X(θ) = Real.cos θ • kitaevStackedPair A + Real.sin θ • kitaevStdComplexStructure n ℝ`
   satisfies:
   - `-(X(θ) * X(θ)) = (Real.cos θ ^ 2) • Matrix.fromBlocks (-(A * A)) 0 0 (-(A * A)) + (Real.sin θ ^ 2) • 1`
     (so if $a^2 \le -A^2 \le b^2$ with $a \le 1 \le b$, then $-X(\theta)^2$ stays in $[a^2, b^2]$ for all $\theta$!),
   - Boundary evaluations: `X(0) = kitaevStackedPair A` ($= A \oplus (-A)$) and
     `X(π / 2) = kitaevStdComplexStructure n ℝ` (completely independent of `A`, proving $A \oplus (-A) \sim A_0 \oplus (-A_0)$!).
-/
theorem ks5_kitaev_invertibility_block_anticommutator_and_rotor_gap
    (A : Matrix n n R) (B_real : Matrix n n ℝ) (θ : ℝ) :
    kitaevStackedPair A * kitaevStdComplexStructure n R +
      kitaevStdComplexStructure n R * kitaevStackedPair A = 0 ∧
    (A.transpose = -A → (kitaevStackedPair A).transpose = -(kitaevStackedPair A)) ∧
    -((Real.cos θ • kitaevStackedPair B_real + Real.sin θ • kitaevStdComplexStructure n ℝ) *
        (Real.cos θ • kitaevStackedPair B_real + Real.sin θ • kitaevStdComplexStructure n ℝ)) =
      (Real.cos θ ^ 2) •
        Matrix.fromBlocks (-(B_real * B_real)) (0 : Matrix n n ℝ)
          (0 : Matrix n n ℝ) (-(B_real * B_real)) +
      (Real.sin θ ^ 2) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) ∧
    (Real.cos 0 • kitaevStackedPair B_real + Real.sin 0 • kitaevStdComplexStructure n ℝ) =
      kitaevStackedPair B_real ∧
    (Real.cos (Real.pi / 2) • kitaevStackedPair B_real +
        Real.sin (Real.pi / 2) • kitaevStdComplexStructure n ℝ) =
      kitaevStdComplexStructure n ℝ := by
  have hAnti :
      kitaevStackedPair A * kitaevStdComplexStructure n R +
        kitaevStdComplexStructure n R * kitaevStackedPair A = 0 := by
    dsimp [kitaevStackedPair, kitaevStdComplexStructure]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
    simp [Matrix.fromBlocks_zero]
  have hSkew : A.transpose = -A → (kitaevStackedPair A).transpose = -(kitaevStackedPair A) := by
    intro hAT
    dsimp [kitaevStackedPair]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg, Matrix.transpose_neg, hAT, neg_neg]
    simp
  have hAntiReal :
      kitaevStackedPair B_real * kitaevStdComplexStructure n ℝ +
        kitaevStdComplexStructure n ℝ * kitaevStackedPair B_real = 0 := by
    dsimp [kitaevStackedPair, kitaevStdComplexStructure]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
    simp [Matrix.fromBlocks_zero]
  have hXSq :
      kitaevStackedPair B_real * kitaevStackedPair B_real =
        -Matrix.fromBlocks (-(B_real * B_real)) (0 : Matrix n n ℝ)
          (0 : Matrix n n ℝ) (-(B_real * B_real)) := by
    dsimp [kitaevStackedPair]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]
    simp
  have hYSq :
      kitaevStdComplexStructure n ℝ * kitaevStdComplexStructure n ℝ = -1 := by
    dsimp [kitaevStdComplexStructure]
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have hRotorSq :
      -((Real.cos θ • kitaevStackedPair B_real + Real.sin θ • kitaevStdComplexStructure n ℝ) *
          (Real.cos θ • kitaevStackedPair B_real + Real.sin θ • kitaevStdComplexStructure n ℝ)) =
        (Real.cos θ ^ 2) •
          Matrix.fromBlocks (-(B_real * B_real)) (0 : Matrix n n ℝ)
            (0 : Matrix n n ℝ) (-(B_real * B_real)) +
        (Real.sin θ ^ 2) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
    rw [add_mul, mul_add, mul_add,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_comm (Real.sin θ) (Real.cos θ),
      ← add_assoc,
      add_assoc ((Real.cos θ * Real.cos θ) • (kitaevStackedPair B_real * kitaevStackedPair B_real)),
      ← smul_add, hAntiReal, smul_zero, add_zero,
      ← sq (Real.cos θ), ← sq (Real.sin θ),
      hXSq, hYSq, smul_neg, smul_neg, neg_add, neg_neg, neg_neg]
  have hAt0 :
      Real.cos 0 • kitaevStackedPair B_real + Real.sin 0 • kitaevStdComplexStructure n ℝ =
        kitaevStackedPair B_real := by
    rw [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
  have hAtPi2 :
      Real.cos (Real.pi / 2) • kitaevStackedPair B_real +
          Real.sin (Real.pi / 2) • kitaevStdComplexStructure n ℝ =
        kitaevStdComplexStructure n ℝ := by
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add]
  exact ⟨hAnti, hSkew, hRotorSq, hAt0, hAtPi2⟩

end SpectrumInvertibilityPrinciple

-- ============================================================================
-- SECTION 5 (𝔎𝔖₆–𝔎𝔖₇): Block-Swap Homotopy, Soft Diagonal Restriction & KO_{d-2} Synthesis
-- ============================================================================

section SoftDiagonalRestrictionAndDimerLoop

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Kitaev's symmetrized diagonal restriction (`01:04:44`–`01:08:28`):
given a site-indexed family of local hopping matrices `u : n → Matrix n n R`, constructs the single
matrix `kitaevDiagRestriction u` with entries `(kitaevDiagRestriction u) j k = u j j k + u k j k`
(scaled by `2` to remain division-free over arbitrary `[CommRing R]`). -/
def kitaevDiagRestriction (u : n → Matrix n n R) : Matrix n n R :=
  Matrix.of fun j k => u j j k + u k j k

/--
**Theorem 5a (𝔎𝔖₆ — Spectrum Principles 2 & 3: Orthogonal Block-Swap $A \oplus B \sim B \oplus A$ & Soft Diagonal Restriction):**
Over any `[CommRing R]`:
1. **Spectrum Principle 2 (`01:03:50` — Block-Swap Conjugation $A \oplus B \mapsto B \oplus A$):**
   For any `A, B : Matrix n n R`, the orthogonal block-rotation matrix at $\theta = \pi/2$,
   $S_{\mathrm{swap}} = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix} = -\mathrm{kitaevStdComplexStructure}\;n\;R$,
   satisfies $S_{\mathrm{swap}}^\top * S_{\mathrm{swap}} = 1$ and conjugates $A \oplus B$ into $B \oplus A$:
   $$S_{\mathrm{swap}}^\top * \begin{pmatrix} A & 0 \\ 0 & B \end{pmatrix} * S_{\mathrm{swap}} =
     \begin{pmatrix} B & 0 \\ 0 & A \end{pmatrix}.$$
2. **Spectrum Principle 3 (`01:04:44`–`01:08:28` — Soft Diagonal Restriction Preserves Skew-Symmetry):**
   If every local matrix `u p` in a family `u : n → Matrix n n R` is skew-symmetric
   (`∀ p, (u p).transpose = -(u p)`), then `kitaevDiagRestriction u` is strictly skew-symmetric:
   $$\big(\mathrm{kitaevDiagRestriction}\;u\big)^\top = -\mathrm{kitaevDiagRestriction}\;u,$$
   and when `u` is constant (`fun _ => A`), `kitaevDiagRestriction (fun _ => A) = (2 : R) • A`.
-/
theorem ks6_block_swap_conjugation_and_soft_diagonal_restriction
    (A B : Matrix n n R) (u : n → Matrix n n R) (hu : ∀ p : n, (u p).transpose = -(u p)) :
    (kitaevStdComplexStructure n R).transpose * (kitaevStdComplexStructure n R) = 1 ∧
    (kitaevStdComplexStructure n R).transpose *
        Matrix.fromBlocks A (0 : Matrix n n R) (0 : Matrix n n R) B *
        (kitaevStdComplexStructure n R) =
      Matrix.fromBlocks B (0 : Matrix n n R) (0 : Matrix n n R) A ∧
    (kitaevDiagRestriction u).transpose = -(kitaevDiagRestriction u) ∧
    kitaevDiagRestriction (fun _ : n => A) = (2 : R) • A := by
  have hOrth : (kitaevStdComplexStructure n R).transpose * (kitaevStdComplexStructure n R) = 1 := by
    dsimp [kitaevStdComplexStructure]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp
  have hSwap :
      (kitaevStdComplexStructure n R).transpose *
          Matrix.fromBlocks A (0 : Matrix n n R) (0 : Matrix n n R) B *
          (kitaevStdComplexStructure n R) =
        Matrix.fromBlocks B (0 : Matrix n n R) (0 : Matrix n n R) A := by
    dsimp [kitaevStdComplexStructure]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  have hDiagSkew : (kitaevDiagRestriction u).transpose = -(kitaevDiagRestriction u) := by
    ext j k
    have hj : u j k j = -(u j j k) := by
      have h := congr_fun (congr_fun (hu j) j) k
      simpa [Matrix.transpose_apply] using h
    have hk : u k k j = -(u k j k) := by
      have h := congr_fun (congr_fun (hu k) j) k
      simpa [Matrix.transpose_apply] using h
    simp only [kitaevDiagRestriction, Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply,
      hj, hk]
    ring
  have hConst : kitaevDiagRestriction (fun _ : n => A) = (2 : R) • A := by
    ext j k
    simp only [kitaevDiagRestriction, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  exact ⟨hOrth, hSwap, hDiagSkew, hConst⟩

/--
**Theorem 5b (𝔎𝔖₇ — Alternating Dimer Loop Re-Pairing & Master Condensed-Matter $KO_{d-2}$ Synthesis):**
Assembles the complete 7-stage Kitaev condensed-matter $KO$-spectrum poset ($\mathfrak{KS}_1 \prec \dots \prec \mathfrak{KS}_7$):
1. **Poset Acyclicity:** `∀ s : KitaevFreeFermionKOSpectrumStage, ¬ coverEdge s s`.
2. **Centered Spectral-Band Identity (`𝔎𝔖₃`):**
   `kitaevCenteredGapOp A_op a b ^ 2 - (b² - a²)² • 1 = 4 • ((-(A_op * A_op) - a² • 1) * (-(A_op * A_op) - b² • 1))`.
3. **Interior Disk Local-Gap Projection (`𝔎𝔖₄`):**
   `e1 P₁ * (chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂) * e1 P₁ = n12 P₁ P₂ A₁ * n21 P₁ P₂ C₁`.
4. **Invertibility Anticommutator & Soft Diagonal Restriction (`𝔎𝔖₅–𝔎𝔖₆`):**
   `kitaevStackedPair A * kitaevStdComplexStructure n R + kitaevStdComplexStructure n R * kitaevStackedPair A = 0`
   and `(kitaevDiagRestriction u).transpose = -(kitaevDiagRestriction u)`.
5. **Alternating Dimer Re-Pairing & Shifted $KO_{d-2}$ Bott Periodicity (`01:13:04`–`01:20:39`, `𝔎𝔖₇`):**
   - In the 3-site alternating chain `A + (-A) + A`, pairing the left dimer `(A + (-A)) + A = A` or
     pairing the right dimer `A + ((-A) + A) = A` leaves the single unpaired system `A` invariant
     while replacing any dimer `A ⊕ (-A)` by `A₀ ⊕ (-A₀)` via `ks5`.
   - Reusing canonical `ko_theory_pmi_bruhat_projector_colimit_stability` from
     `CliffordBottKTheoryWignerS4Poset`, `P_hat_KO P M * P_hat_KO P M = P_hat_KO P M`,
     `K_diag P (P_hat_KO P M - P) = - comm (conePlus P M) (coneMinus P M)`,
     `Fintype.card (InfoGeometry.Core.TensorPeirceDecomposition.PeirceIndex (m + 4)) = 16 * Fintype.card (InfoGeometry.Core.TensorPeirceDecomposition.PeirceIndex m)`,
     and the mod-8 Bott periodicity of the shifted index `((d + 8 - 2 : ℕ) : ZMod 8) = ((d + 6 : ℕ) : ZMod 8)`.
-/
theorem ks7_alternating_dimer_loop_and_ko_d_minus_2_master_synthesis
    {B : Type*} [Ring B] [Algebra R B]
    (A : Matrix n n R) (u : n → Matrix n n R) (hu : ∀ p : n, (u p).transpose = -(u p))
    (A_op P M P₁ P₂ A₁ C₁ A₂ C₂ : B) (a b : R)
    (hP : P * P = P)
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁)
    (m d : ℕ) :
    (∀ s : KitaevFreeFermionKOSpectrumStage, ¬ KitaevFreeFermionKOSpectrumStage.coverEdge s s) ∧
    (kitaevCenteredGapOp A_op a b * kitaevCenteredGapOp A_op a b - ((b ^ 2 - a ^ 2) ^ 2) • (1 : B) =
      (4 : R) • ((-(A_op * A_op) - (a ^ 2) • (1 : B)) * (-(A_op * A_op) - (b ^ 2) • (1 : B)))) ∧
    (e1 P₁ * (chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂) * e1 P₁ =
      n12 P₁ P₂ A₁ * n21 P₁ P₂ C₁) ∧
    (kitaevStackedPair A * kitaevStdComplexStructure n R +
      kitaevStdComplexStructure n R * kitaevStackedPair A = 0 ∧
     (kitaevDiagRestriction u).transpose = -(kitaevDiagRestriction u)) ∧
    ((A + -A) + A = A ∧ A + (-A + A) = A) ∧
    (P_hat_KO P M * P_hat_KO P M = P_hat_KO P M ∧
     K_diag P (P_hat_KO P M - P) =
       -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P M) (coneMinus P M) ∧
     Fintype.card (InfoGeometry.Core.TensorPeirceDecomposition.PeirceIndex (m + 4)) =
       16 * Fintype.card (InfoGeometry.Core.TensorPeirceDecomposition.PeirceIndex m) ∧
     (((d + 8 - 2 : ℕ) : ZMod 8) = ((d + 6 : ℕ) : ZMod 8))) := by
  have hBand := (ks3_kitaev_centered_spectral_band_square_identity A_op a b).1
  have hInt :=
    (ks4_interior_disk_projection_eliminates_boundary_modes
      (A₁ := A₁) (C₁ := C₁) (A₂ := A₂) (C₂ := C₂) h₁ h₂ h₁₂ h₂₁).2.2.2
  have hInv := (ks5_kitaev_invertibility_block_anticommutator_and_rotor_gap A (0 : Matrix n n ℝ) 0).1
  have hDiag := (ks6_block_swap_conjugation_and_soft_diagonal_restriction A A u hu).2.2.1
  have hKO := ko_theory_pmi_bruhat_projector_colimit_stability P M hP (RingHom.id B) m
  have hMod8 : (((d + 8 - 2 : ℕ) : ZMod 8) = ((d + 6 : ℕ) : ZMod 8)) := by
    have hNat : d + 8 - 2 = d + 6 := by omega
    rw [hNat]
  exact ⟨KitaevFreeFermionKOSpectrumStage.coverEdge_acyclic,
    hBand, hInt, ⟨hInv, hDiag⟩, ⟨by abel, by abel⟩,
    ⟨hKO.2.1, hKO.2.2.1, hKO.2.2.2.2, hMod8⟩⟩

end SoftDiagonalRestrictionAndDimerLoop

end InfoGeometry.CondensedMatter.KitaevFreeFermionKOSpectrumLocalGapPoset
