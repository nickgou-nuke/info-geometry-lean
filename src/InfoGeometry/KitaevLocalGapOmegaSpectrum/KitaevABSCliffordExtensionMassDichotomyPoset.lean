/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Quantum.AZTenFoldFullPeriodicTable

/-!
# Kitaev ABS Clifford Extensions, Mass Rotation Dichotomy ($d = 1, 2, 3$), Class DIII Kramers TRS, and the $\mathcal{C}\ell(1,1) \otimes \mathcal{C}\ell(4,4) \cong \mathrm{Mat}_{32}$ Noncommutative Klein-Bottle Twist ($\mathfrak{KL}_{12} \prec \dots \prec \mathfrak{KL}_{18}$)

## i. Overview

This module formalizes Alexei Kitaev's Atiyah–Bott–Shapiro (ABS) Clifford extension mechanism
for real Majorana Hamiltonians $A = \sum_{a=1}^d \Gamma_a \partial_a + M$ ($\Gamma_a^\top = +\Gamma_a$,
$M^\top = -M$, $\{\Gamma_a, \Gamma_b\} = 2\delta_{ab}I$, $\{\Gamma_a, M\} = 0$, $M^2 = -I$) across
spatial dimensions $d = 1, 2, 3$ in Class D, $d = 3$ in Class DIII, and the real $\mathcal{C}\ell(1,1)$
Klein-bottle twist $\mathcal{A}_{\mathrm{Klein}} = \mathcal{C}\ell(1,1) \otimes \mathcal{C}\ell(4,4) \cong \mathrm{Mat}_{32}(K)$,
organized as a 7-stage poset `KitaevABSCliffordExtensionStage` ($\mathfrak{KL}_{12} \prec \dots \prec \mathfrak{KL}_{18}$):

1. **Stage $\mathfrak{KL}_{12}$ ($d = 1$, 1-Flavor Class D in $\mathrm{Mat}_2(K)$ — $\mathcal{C}\ell(1,0) \hookrightarrow \mathcal{C}\ell(1,1)$):**
   With kinetic generator $\Gamma_1 = \sigma_z$, every skew-symmetric matrix $X \in \mathrm{Mat}_2(\mathbb{R})$
   is a scalar multiple $X = X_{01} J$, automatically anticommuting with $\sigma_z$. The gapped mass
   condition $(m J)^2 = -m^2 I_2 = -I_2$ admits only the two isolated solutions $m = \pm 1$
   ($M_\pm = \pm J$), and their midpoint $M_+ + M_- = 0$ closes the bulk gap.
2. **Stage $\mathfrak{KL}_{13}$ ($d = 1$, 2-Flavor Class D in $\mathrm{Mat}_4(K)$ — $\mathcal{C}\ell(1,0) \hookrightarrow \mathcal{C}\ell(1,2)$ Rotor):**
   With doubled kinetic generator $\widetilde{\Gamma}_1 = \sigma_z \otimes I_2$ and standard doubled
   mass $M_{++} = J \otimes I_2$, the second skew-symmetric mass $M_{\mathrm{rot}} = \sigma_x \otimes J$
   anticommutes with both $\widetilde{\Gamma}_1$ and $M_{++}$. Consequently, the continuous mass rotor
   $M_{1D}(c, s) = c M_{\mathrm{rot}} + s M_{++}$ satisfies $M_{1D}(c, s)^2 = -(c^2 + s^2) I_4$,
   rotating $+M_{++}$ into $-M_{++}$ without closing the gap when $c^2 + s^2 = 1$ ($1 + 1 \equiv 0 \pmod 2$).
3. **Stage $\mathfrak{KL}_{14}$ ($d = 2$, Class D in $\mathrm{Mat}_2(K)$ & $\mathrm{Mat}_4(K)$ — $\mathcal{C}\ell(2,0) \hookrightarrow \mathcal{C}\ell(2,1)$ Locked Mass):**
   With kinetic generators $\Gamma_1 = \sigma_z$ and $\Gamma_2 = \sigma_x$, the unique skew-symmetric
   mass in $\mathrm{Mat}_2(\mathbb{R})$ is the locked product $J = \Gamma_1 \Gamma_2$ ($X = X_{01} J$
   whenever $\{\Gamma_1, X\} = \{\Gamma_2, X\} = 0$). For $N = 2$ flavors in $\mathrm{Mat}_4(K)$,
   $M_{2D}(s_1, s_2) = J \otimes \mathrm{diag}(s_1, s_2)$ has
   $-M_{2D}(s_1, s_2)^2 = \mathrm{diag}(s_1^2, s_2^2, s_1^2, s_2^2)$ and $\det(M_{2D}(s_1, s_2)) = (s_1 s_2)^2$.
4. **Stage $\mathfrak{KL}_{15}$ ($d = 3$, Class D in $\mathrm{Mat}_4(K)$ — $\mathcal{C}\ell(3,0) \hookrightarrow \mathcal{C}\ell(3,2)$ 2-Mass Plane & Triviality):**
   With kinetic generators $\Gamma_1 = \sigma_z \otimes I_2$, $\Gamma_2 = \sigma_x \otimes \sigma_z$,
   and $\Gamma_3 = \sigma_x \otimes \sigma_x$, both $M_1 = \sigma_x \otimes J$ and $M_2 = J \otimes I_2$
   are skew-symmetric, square to $-I_4$, anticommute with $\Gamma_1, \Gamma_2, \Gamma_3$, and anticommute
   with each other. Moreover, over $\mathbb{R}$, **every** matrix $X \in \mathrm{Mat}_4(\mathbb{R})$
   anticommuting with $\Gamma_1, \Gamma_2, \Gamma_3$ lies in the exact 2-plane $X = X_{03} M_1 + X_{02} M_2$.
5. **Stage $\mathfrak{KL}_{16}$ ($d = 3$, Class DIII Kramers TRS $T^2 = -I$ & Socratic Elenchus in $\mathrm{Mat}_4$ and $\mathrm{Mat}_8$):**
   - Resolves the Kronecker anticommutator elenchus in $\mathrm{Mat}_4(K)$: $J \otimes J$ is symmetric
     ($(J \otimes J)^\top = +(J \otimes J)$, $(J \otimes J)^2 = +I_4$), whereas $T_4 = M_2 = J \otimes I_2$
     is skew-symmetric ($T_4^\top = -T_4$, $T_4^2 = -I_4$) and anticommutes with $\Gamma_1, \Gamma_2, \Gamma_3$.
     Imposing $[a M_1 + b M_2, T_4] = 0$ over $\mathbb{R}$ forces $a = 0$, while $\{a M_1 + b M_2, T_4\} = 0$ forces $b = 0$.
   - Resolves the $8 \times 8$ elenchus in $\mathrm{Mat}_8(K)$: for $\widetilde{\Gamma}_a = I_2 \otimes \Gamma_a$,
     $J \otimes (J \otimes J)$ commutes with $\widetilde{\Gamma}_2$ and $\widetilde{\Gamma}_3$,
     whereas $T_8 = I_2 \otimes M_2$ anticommutes with all three $\widetilde{\Gamma}_1, \widetilde{\Gamma}_2, \widetilde{\Gamma}_3$.
6. **Stage $\mathfrak{KL}_{17}$ ($\mathcal{C}\ell(1,1) \cong \mathrm{Mat}_2(K)$ Klein-Bottle Twist, Projective $V_4 \cong \mathbb{Z}_2 \times \mathbb{Z}_2$ vs. $D_4$ Lift & Unorientable Holonomy):**
   With $\gamma_0 = \sigma_z$ ($\gamma_0^2 = +I_2$, $\det \gamma_0 = -1$) and $\gamma_1 = J$ ($\gamma_1^2 = -I_2$,
   $\det \gamma_1 = +1$, $\{\gamma_0, \gamma_1\} = 0$), the matrix generators form a central $D_4$ extension
   while their adjoint involutions $\mathrm{Ad}_{\gamma_0}(X) = \gamma_0 X \gamma_0$ and
   $\mathrm{Ad}_{\gamma_1}(X) = -\gamma_1 X \gamma_1$ generate the exact Klein four-group
   $V_4 \cong \mathbb{Z}_2 \times \mathbb{Z}_2$ ($\mathrm{Ad}_{\gamma_0}^2 = \mathrm{Ad}_{\gamma_1}^2 = \mathrm{id}$,
   $\mathrm{Ad}_{\gamma_0} \circ \mathrm{Ad}_{\gamma_1} = \mathrm{Ad}_{\gamma_1} \circ \mathrm{Ad}_{\gamma_0} = \mathrm{Ad}_{\gamma_0 \gamma_1}$).
7. **Stage $\mathfrak{KL}_{18}$ ($\mathcal{A}_{\mathrm{Klein}} = \mathcal{C}\ell(1,1) \otimes \mathcal{C}\ell(4,4) \cong \mathrm{Mat}_2(K) \otimes \mathrm{Mat}_{16}(K) \cong \mathrm{Mat}_{32}(K)$ & $\mathcal{D}_{\mathrm{Klein}}^2$):**
   For $\mathcal{D}_{\mathrm{Klein}}(D, M) = \gamma_0 \otimes D + \gamma_1 \otimes M \in \mathrm{Mat}_{32}(K)$,
   proves the universal square identity
   $$\mathcal{D}_{\mathrm{Klein}}(D, M)^2 = I_2 \otimes (D^2 - M^2) + (\gamma_0 \gamma_1) \otimes (D M - M D),$$
   showing that $[D, M] = 0$ eliminates the cross-term and $M^2 = -m^2 I_{16}$ opens the mass gap
   $\mathcal{D}_{\mathrm{Klein}}(D, M)^2 = I_2 \otimes (D^2 + m^2 I_{16})$.

## ii. Key results

- `KitaevABSCliffordExtensionStage` ($\mathfrak{KL}_{12} \prec \dots \prec \mathfrak{KL}_{18}$), `coverEdge_strictMono`, `coverEdge_acyclic`
- `Mat2.kl12_dim1_one_flavor_isolated_mass_dichotomy`
- `Mat4.kl13_dim1_two_flavor_mass_rotor_trivialization`
- `Mat2.kl14_dim2_locked_chiral_mass_uniqueness`, `Mat4.kl14_dim2_two_flavor_symmetric_signature_mass`
- `Mat4.kl15_dim3_classD_two_mass_plane_completeness_and_rotor`
- `Mat4.kl16_dim3_classDIII_kramers_trs_mass_channel_blocking`
- `Mat8.kl16_dim3_mat8_elenchus_and_kramers_trs_lift`
- `Mat2.kl17_cl11_klein_four_group_adjoint_and_unorientable_holonomy`
- `Mat32.kl18_klein_dirac_mat32_square_and_gap_shield`
- `kl18_master_abs_clifford_extension_and_klein_bottle_synthesis`

## iii. Table of contents

- Section 0: The 7-Stage ABS Clifford & Klein-Bottle Extension Poset ($\mathfrak{KL}_{12} \prec \dots \prec \mathfrak{KL}_{18}$)
- Section 1 ($\mathfrak{KL}_{12}$, $\mathfrak{KL}_{14}$, $\mathfrak{KL}_{17}$ in $\mathrm{Mat}_2$): $d = 1$ Mass, $d = 2$ Locked Mass & $\mathcal{C}\ell(1,1)$ Klein $V_4$ Twist
- Section 2 ($\mathfrak{KL}_{13}$, $\mathfrak{KL}_{14}$, $\mathfrak{KL}_{15}$ in $\mathrm{Mat}_4$): 2-Flavor $d=1$ Rotor, $d=2$ Signature & $d=3$ 2-Mass Plane
- Section 3 ($\mathfrak{KL}_{16}$ in $\mathrm{Mat}_4$ & $\mathrm{Mat}_8$): 3D Class DIII Kramers TRS ($T^2 = -I$) & Socratic Elenchus
- Section 4 ($\mathfrak{KL}_{18}$ in $\mathrm{Mat}_{32}$): $\mathcal{C}\ell(1,1) \otimes \mathcal{C}\ell(4,4) \cong \mathrm{Mat}_{32}(K)$ & $\mathcal{D}_{\mathrm{Klein}}^2$
- Section 5: Master Synthesis (`kl18_master_abs_clifford_extension_and_klein_bottle_synthesis`)

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `KitaevABSCliffordExtensionStage.rank_injective`, `KitaevABSCliffordExtensionStage.coverEdge_strictMono`, `KitaevABSCliffordExtensionStage.coverEdge_acyclic`,
  - `Mat2.kl12_dim1_one_flavor_isolated_mass_dichotomy`, `Mat2.kl14_dim2_locked_chiral_mass_uniqueness`,
  - `Mat2.kl17_cl11_klein_four_group_adjoint_and_unorientable_holonomy`,
  - `Mat4.kl13_dim1_two_flavor_mass_rotor_trivialization`, `Mat4.kl14_dim2_two_flavor_symmetric_signature_mass`,
  - `Mat4.kl15_dim3_classD_two_mass_plane_completeness_and_rotor`,
  - `Mat4.kl16_dim3_classDIII_kramers_trs_mass_channel_blocking`,
  - `Mat8.kl16_dim3_mat8_elenchus_and_kramers_trs_lift`,
  - `Mat32.kl18_klein_dirac_mat32_square_and_gap_shield`,
  - `kl18_master_abs_clifford_extension_and_klein_bottle_synthesis`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Division-free ring identities hold over any `[CommRing K]`; exact entry-level uniqueness without a factor of `2` is stated over `ℝ`.
* **BUCKET 3 — Out-of-Scope Continuum / Classifying-Space Claims:**
  - Infinite-dimensional Fredholm classifying-space homotopy equivalences $\pi_0(E_{d-2}) \cong KO_{2-d}(\mathrm{pt})$, continuum PDE zero-mode profiles, and infinite-dimensional $C^*$-algebraic noncommutative Klein-bottle bundles remain outside this finite-dimensional matrix Clifford owner.

## iv. References

- A. Y. Kitaev, *Periodic table for topological insulators and superconductors*, AIP Conf. Proc. 1134, 22–30 (2009).
- M. F. Atiyah, R. Bott, and A. Shapiro, *Clifford modules*, Topology 3, Suppl. 1, 3–38 (1964).
- `InfoGeometry.Quantum.AZTenFoldFullPeriodicTable`
-/

namespace InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset

open Matrix
open scoped Kronecker
open InfoGeometry.Quantum.AZTenFoldFullPeriodicTable
open InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge

universe u

-- ============================================================================
-- SECTION 0: The 7-Stage ABS Clifford & Klein-Bottle Poset (𝔎𝔏₁₂ ≺ ⋯ ≺ 𝔎𝔏₁₈)
-- ============================================================================

/-- The 7-stage causal poset ($\mathfrak{KL}_{12} \prec \dots \prec \mathfrak{KL}_{18}$) organizing
Kitaev's ABS Clifford extensions across $d = 1, 2, 3$ in Class D, $d = 3$ in Class DIII, and the
$\mathcal{C}\ell(1,1) \otimes \mathcal{C}\ell(4,4) \cong \mathrm{Mat}_{32}$ Klein-bottle twist. -/
inductive KitaevABSCliffordExtensionStage : Type
  | kl12Dim1OneFlavorIsolatedMassZ2
  | kl13Dim1TwoFlavorMassRotorTrivialization
  | kl14Dim2LockedChiralMassAndSymmetricSignature
  | kl15Dim3TwoMassPlaneAndHomotopyTriviality
  | kl16Dim3ClassDIIIKramersTRSMassSelectionZ2
  | kl17Cl11KleinFourGroupAdjointAndUnorientableHolonomy
  | kl18Cl11TensorCl44Mat32KleinDiracGapShield
  deriving DecidableEq, Repr

namespace KitaevABSCliffordExtensionStage

/-- Numeric rank `0..6` of each stage in `KitaevABSCliffordExtensionStage`. -/
def rank : KitaevABSCliffordExtensionStage → Nat
  | .kl12Dim1OneFlavorIsolatedMassZ2 => 0
  | .kl13Dim1TwoFlavorMassRotorTrivialization => 1
  | .kl14Dim2LockedChiralMassAndSymmetricSignature => 2
  | .kl15Dim3TwoMassPlaneAndHomotopyTriviality => 3
  | .kl16Dim3ClassDIIIKramersTRSMassSelectionZ2 => 4
  | .kl17Cl11KleinFourGroupAdjointAndUnorientableHolonomy => 5
  | .kl18Cl11TensorCl44Mat32KleinDiracGapShield => 6

/-- `rank` is injective on `KitaevABSCliffordExtensionStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

/-- Direct Hasse cover relation on `KitaevABSCliffordExtensionStage`. -/
def coverEdge : KitaevABSCliffordExtensionStage → KitaevABSCliffordExtensionStage → Prop
  | .kl12Dim1OneFlavorIsolatedMassZ2, .kl13Dim1TwoFlavorMassRotorTrivialization => True
  | .kl13Dim1TwoFlavorMassRotorTrivialization, .kl14Dim2LockedChiralMassAndSymmetricSignature => True
  | .kl14Dim2LockedChiralMassAndSymmetricSignature, .kl15Dim3TwoMassPlaneAndHomotopyTriviality => True
  | .kl15Dim3TwoMassPlaneAndHomotopyTriviality, .kl16Dim3ClassDIIIKramersTRSMassSelectionZ2 => True
  | .kl16Dim3ClassDIIIKramersTRSMassSelectionZ2, .kl17Cl11KleinFourGroupAdjointAndUnorientableHolonomy => True
  | .kl17Cl11KleinFourGroupAdjointAndUnorientableHolonomy, .kl18Cl11TensorCl44Mat32KleinDiracGapShield => True
  | _, _ => False

/-- Every Hasse cover edge strictly increases `rank`. -/
theorem coverEdge_strictMono {a b : KitaevABSCliffordExtensionStage}
    (h : coverEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> cases h <;> decide

/-- `coverEdge` is irreflexive on `KitaevABSCliffordExtensionStage`. -/
theorem coverEdge_acyclic (a : KitaevABSCliffordExtensionStage) : ¬ coverEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (coverEdge_strictMono h)

end KitaevABSCliffordExtensionStage

-- ============================================================================
-- SECTION 1 (𝔎𝔏₁₂, 𝔎𝔏₁₄, 𝔎𝔏₁₇ in Mat₂): d=1, d=2 & Cl(1,1) Klein V₄ Twist
-- ============================================================================

/-- Canonical $2 \times 2$ matrix carrier `Matrix (Fin 2) (Fin 2) K`. -/
abbrev Mat2 (K : Type u) : Type u := Matrix (Fin 2) (Fin 2) K

namespace Mat2
variable {K : Type u} [CommRing K]

/-- $2 \times 2$ identity matrix `I₂`. -/
def I2 : Mat2 K := (1 : Matrix (Fin 2) (Fin 2) K)

/-- Symmetric Pauli grading / orientation-reversing reflection matrix `γ₀ = σ_z = diag(1, -1)` in `Mat2 K`. -/
def sigmaZ : Mat2 K := !![1, 0; 0, -1]

/-- Symmetric Pauli flip / combined Klein twist matrix `γ₀γ₁ = σ_x = !![0, 1; 1, 0]` in `Mat2 K`. -/
def sigmaX : Mat2 K := !![0, 1; 1, 0]

/-- Skew-symmetric Majorana mass / symplectic glide generator `γ₁ = J = !![0, 1; -1, 0]` in `Mat2 K`. -/
def massJ : Mat2 K := !![0, 1; -1, 0]

/-- Closed anticommutator witness $\{\sigma_z, J\} = 0$ in `Mat2 K`. -/
lemma sigmaZ_anticomm_massJ :
    (sigmaZ : Mat2 K) * massJ + massJ * sigmaZ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaZ, massJ]

/-- Real specialization of $\{\sigma_z, J\} = 0$ in `Mat2 ℝ`. -/
lemma sigmaZ_anticomm_massJ_real :
    sigmaZ (K := ℝ) * massJ (K := ℝ) + massJ (K := ℝ) * sigmaZ (K := ℝ) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaZ, massJ]

/-- Entry-level extraction of a $2 \times 2$ anticommutator equation `A * X + X * A = 0`. -/
private lemma entry_anticomm2 {A X : Mat2 ℝ} (h : A * X + X * A = 0) (i j : Fin 2) :
    (A i 0 * X 0 j + A i 1 * X 1 j) + (X i 0 * A 0 j + X i 1 * A 1 j) = 0 := by
  have hij := congr_fun (congr_fun h i) j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_two, Matrix.zero_apply] at hij
  linarith

/-- **Theorem 1 ($\mathfrak{KL}_{12}$ — $d = 1$ Single-Flavor Class D Isolated Mass Dichotomy in $\mathrm{Mat}_2$):**
For the $d = 1$ single-flavor kinetic generator $\Gamma_1 = \sigma_z$:
1. $\sigma_z^\top = \sigma_z$, $\sigma_z^2 = I_2$, $J^\top = -J$, $J^2 = -I_2$, and $\{\sigma_z, J\} = 0$.
2. For any scalar $m \in K$, $(m \cdot J)^2 = -(m^2) \cdot I_2$, and the midpoint $(+J) + (-J) = 0$ vanishes.
3. Over $\mathbb{R}$, every skew-symmetric matrix $X \in \mathrm{Mat}_2(\mathbb{R})$ ($X^\top = -X$) is a scalar
   multiple $X = X_{01} \cdot J$, and $X^2 = -I_2$ holds if and only if $X = J \vee X = -J$. -/
theorem kl12_dim1_one_flavor_isolated_mass_dichotomy (m : K) (X : Mat2 ℝ) :
    ((sigmaZ : Mat2 K).transpose = sigmaZ ∧
      (sigmaZ : Mat2 K) * sigmaZ = I2 ∧
      (massJ : Mat2 K).transpose = -massJ ∧
      (massJ : Mat2 K) * massJ = -I2 ∧
      (sigmaZ : Mat2 K) * massJ + massJ * sigmaZ = 0) ∧
    ((m • (massJ : Mat2 K)) * (m • massJ) = (- (m ^ 2)) • I2 ∧
      (massJ : Mat2 K) + (-massJ) = 0) ∧
    (X.transpose = -X →
      X = (X 0 1) • (massJ : Mat2 ℝ) ∧
      (X * X = -(I2 : Mat2 ℝ) ↔ X = massJ ∨ X = -massJ)) := by
  have hGen : (sigmaZ : Mat2 K).transpose = sigmaZ ∧
      (sigmaZ : Mat2 K) * sigmaZ = I2 ∧
      (massJ : Mat2 K).transpose = -massJ ∧
      (massJ : Mat2 K) * massJ = -I2 ∧
      (sigmaZ : Mat2 K) * massJ + massJ * sigmaZ = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaZ, massJ, I2]
  have hScale : (m • (massJ : Mat2 K)) * (m • massJ) = (- (m ^ 2)) • I2 := by
    rw [smul_mul_smul_comm, hGen.2.2.2.1, smul_neg, ← neg_smul, sq]
  have hMid : (massJ : Mat2 K) + (-massJ) = 0 := add_neg_cancel massJ
  refine ⟨hGen, ⟨hScale, hMid⟩, fun hSkew => ?_⟩
  have h00 : X 0 0 = 0 := by
    have h := congr_fun (congr_fun hSkew 0) 0
    simp [Matrix.transpose_apply] at h
    linarith
  have h11 : X 1 1 = 0 := by
    have h := congr_fun (congr_fun hSkew 1) 1
    simp [Matrix.transpose_apply] at h
    linarith
  have h10 : X 1 0 = -X 0 1 := by
    have h := congr_fun (congr_fun hSkew 0) 1
    simp [Matrix.transpose_apply] at h
    linarith
  have hXeq : X = (X 0 1) • (massJ : Mat2 ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [massJ, h00, h11, h10]
  refine ⟨hXeq, ?_⟩
  constructor
  · intro hSq
    rw [hXeq] at hSq
    have h00_sq := congr_fun (congr_fun hSq 0) 0
    simp [massJ, I2, Matrix.mul_apply, Fin.sum_univ_two] at h00_sq
    have hsq1 : (X 0 1) ^ 2 = 1 := by nlinarith
    rcases sq_eq_one_iff.mp hsq1 with h1 | hm1
    · left
      rw [hXeq, h1, one_smul]
    · right
      rw [hXeq, hm1, neg_one_smul]
  · rintro (rfl | rfl)
    · ext i j; fin_cases i <;> fin_cases j <;> simp [massJ, I2]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [massJ, I2]

/-- **Theorem 2 ($\mathfrak{KL}_{14}$ in $\mathrm{Mat}_2$ — $d = 2$ Locked Chiral Mass $J = \Gamma_1 \Gamma_2$ & Uniqueness):**
For the $d = 2$ kinetic generators $\Gamma_1 = \sigma_z$ and $\Gamma_2 = \sigma_x$ in `Mat2 K`:
1. $\sigma_z \sigma_x + \sigma_x \sigma_z = 0$ and $\sigma_z \sigma_x = J$.
2. Both $\{\sigma_z, J\} = 0$ and $\{\sigma_x, J\} = 0$ hold.
3. **Uniqueness / Locking of the 2D Mass in $\mathrm{Mat}_2(\mathbb{R})$**:
   Every matrix $X \in \mathrm{Mat}_2(\mathbb{R})$ that anticommutes with both $\sigma_z$ and $\sigma_x$
   is necessarily $X = X_{01} \cdot J$ (automatically skew-symmetric, leaving zero second mass direction!). -/
theorem kl14_dim2_locked_chiral_mass_uniqueness (X : Mat2 ℝ) :
    ((sigmaZ : Mat2 K) * sigmaX + sigmaX * sigmaZ = 0 ∧
      (sigmaZ : Mat2 K) * sigmaX = massJ ∧
      (sigmaZ : Mat2 K) * massJ + massJ * sigmaZ = 0 ∧
      (sigmaX : Mat2 K) * massJ + massJ * sigmaX = 0) ∧
    ((sigmaZ : Mat2 ℝ) * X + X * sigmaZ = 0 →
      (sigmaX : Mat2 ℝ) * X + X * sigmaX = 0 →
      X = (X 0 1) • (massJ : Mat2 ℝ) ∧ X.transpose = -X) := by
  have hAlg : (sigmaZ : Mat2 K) * sigmaX + sigmaX * sigmaZ = 0 ∧
      (sigmaZ : Mat2 K) * sigmaX = massJ ∧
      (sigmaZ : Mat2 K) * massJ + massJ * sigmaZ = 0 ∧
      (sigmaX : Mat2 K) * massJ + massJ * sigmaX = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaZ, sigmaX, massJ]
  refine ⟨hAlg, fun hZ hX => ?_⟩
  have hz00 := entry_anticomm2 hZ 0 0
  have hz11 := entry_anticomm2 hZ 1 1
  have hx00 := entry_anticomm2 hX 0 0
  dsimp [sigmaZ, sigmaX] at hz00 hz11 hx00
  have h00 : X 0 0 = 0 := by linarith
  have h11 : X 1 1 = 0 := by linarith
  have h10 : X 1 0 = -X 0 1 := by linarith
  have hXeq : X = (X 0 1) • (massJ : Mat2 ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [massJ, h00, h11, h10]
  have hSkew : X.transpose = -X := by
    rw [hXeq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [massJ]
  exact ⟨hXeq, hSkew⟩

/-- First Klein four-group $V_4$ inner automorphism $\alpha_a(X) = \gamma_0 X \gamma_0^{-1} = \sigma_z X \sigma_z$. -/
def kleinAdjointA (X : Mat2 K) : Mat2 K :=
  (sigmaZ : Mat2 K) * X * sigmaZ

/-- Second Klein four-group $V_4$ inner automorphism $\alpha_b(X) = \gamma_1 X \gamma_1^{-1} = -J X J$. -/
def kleinAdjointB (X : Mat2 K) : Mat2 K :=
  -((massJ : Mat2 K) * X * massJ)

/-- Combined Klein four-group $V_4$ inner automorphism $\alpha_{ab}(X) = (\gamma_0 \gamma_1) X (\gamma_0 \gamma_1)^{-1} = \sigma_x X \sigma_x$. -/
def kleinAdjointAB (X : Mat2 K) : Mat2 K :=
  (sigmaX : Mat2 K) * X * sigmaX

/-- **Theorem 2b ($\mathfrak{KL}_{17}$ — $\mathcal{C}\ell(1,1) \cong \mathrm{Mat}_2(K)$ Klein-Bottle Twist, Projective $V_4 \cong \mathbb{Z}_2 \times \mathbb{Z}_2$ vs. $D_4$ Lift & Unorientable Holonomy):**
For the real split Clifford algebra $\mathcal{C}\ell(1,1) \cong \mathrm{Mat}_2(K)$ generated by
$\gamma_0 = \sigma_z$ ($\gamma_0^2 = +I_2$) and $\gamma_1 = J$ ($\gamma_1^2 = -I_2$) with combined twist
$\gamma_0 \gamma_1 = \sigma_x$:
1. **Clifford $D_4$ Relations**:
   $\gamma_0^2 = I_2$, $\gamma_1^2 = -I_2$, $\gamma_0 \gamma_1 = \sigma_x$, $\sigma_x^2 = I_2$, and $\gamma_0 \gamma_1 + \gamma_1 \gamma_0 = 0$.
2. **Exact Klein Four-Group $V_4 \cong \mathbb{Z}_2 \times \mathbb{Z}_2$ on Adjoint / Projective Action**:
   For every $X \in \mathrm{Mat}_2(K)$,
   - `kleinAdjointA (kleinAdjointA X) = X` ($\alpha_a^2 = \mathrm{id}$),
   - `kleinAdjointB (kleinAdjointB X) = X` ($\alpha_b^2 = \mathrm{id}$),
   - `kleinAdjointAB (kleinAdjointAB X) = X` ($\alpha_{ab}^2 = \mathrm{id}$),
   - `kleinAdjointA (kleinAdjointB X) = kleinAdjointAB X` and `kleinAdjointB (kleinAdjointA X) = kleinAdjointAB X`
     ($\alpha_a \circ \alpha_b = \alpha_b \circ \alpha_a = \alpha_{ab}$, commuting in $\mathrm{Aut}(\mathrm{Mat}_2(K))$!).
3. **Unorientable Berry / Stiefel–Whitney Holonomy & Non-Symmorphic Glide Reflection**:
   - Orientation reversal along the Klein cycle: $\det(\gamma_0) = -1$ and $\det(\gamma_0 \gamma_1) = -1$,
     whereas two traversals restore orientation: $\det(\gamma_0^2) = \det(I_2) = +1$,
   - Non-symmorphic glide square at zone boundary $k_x = \pi$ ($\gamma_1^2 = -I_2$) vs. zone center $k_x = 0$ ($\gamma_0^2 = +I_2$). -/
theorem kl17_cl11_klein_four_group_adjoint_and_unorientable_holonomy (X : Mat2 K) :
    ((sigmaZ : Mat2 K) * massJ = sigmaX ∧
      (sigmaX : Mat2 K) * sigmaX = I2 ∧
      (sigmaZ : Mat2 K) * massJ + massJ * sigmaZ = 0) ∧
    (kleinAdjointA (kleinAdjointA X) = X ∧
      kleinAdjointB (kleinAdjointB X) = X ∧
      kleinAdjointAB (kleinAdjointAB X) = X ∧
      kleinAdjointA (kleinAdjointB X) = kleinAdjointAB X ∧
      kleinAdjointB (kleinAdjointA X) = kleinAdjointAB X) ∧
    (Matrix.det (sigmaZ : Mat2 K) = -1 ∧
      Matrix.det (sigmaX : Mat2 K) = -1 ∧
      Matrix.det (massJ : Mat2 K) = 1 ∧
      Matrix.det ((sigmaZ : Mat2 K) * sigmaZ) = 1) := by
  have h12 := (kl12_dim1_one_flavor_isolated_mass_dichotomy (1 : K) 0).1
  have h14 := (kl14_dim2_locked_chiral_mass_uniqueness (K := K) 0).1
  have hSigXSq : (sigmaX : Mat2 K) * sigmaX = I2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaX, I2]
  have hAA : kleinAdjointA (kleinAdjointA X) = X := by
    dsimp [kleinAdjointA]
    have hZ2 : (sigmaZ : Mat2 K) * sigmaZ = 1 := h12.2.1
    calc
      (sigmaZ : Mat2 K) * (sigmaZ * X * sigmaZ) * sigmaZ
          = (sigmaZ * sigmaZ) * X * (sigmaZ * sigmaZ) := by noncomm_ring
      _ = 1 * X * 1 := by rw [hZ2]
      _ = X := by rw [Matrix.one_mul, Matrix.mul_one]
  have hBB : kleinAdjointB (kleinAdjointB X) = X := by
    dsimp [kleinAdjointB]
    have hJ2 : (massJ : Mat2 K) * massJ = -1 := h12.2.2.2.1
    calc
      -((massJ : Mat2 K) * -(massJ * X * massJ) * massJ)
          = (massJ * massJ) * X * (massJ * massJ) := by noncomm_ring
      _ = (-1) * X * (-1) := by rw [hJ2]
      _ = X := by noncomm_ring
  have hABAB : kleinAdjointAB (kleinAdjointAB X) = X := by
    dsimp [kleinAdjointAB]
    have hX2 : (sigmaX : Mat2 K) * sigmaX = 1 := hSigXSq
    calc
      (sigmaX : Mat2 K) * (sigmaX * X * sigmaX) * sigmaX
          = (sigmaX * sigmaX) * X * (sigmaX * sigmaX) := by noncomm_ring
      _ = 1 * X * 1 := by rw [hX2]
      _ = X := by rw [Matrix.one_mul, Matrix.mul_one]
  have hZj : (sigmaZ : Mat2 K) * massJ = sigmaX := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaZ, massJ, sigmaX]
  have hJz : (massJ : Mat2 K) * sigmaZ = -sigmaX := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [massJ, sigmaZ, sigmaX]
  have hAB : kleinAdjointA (kleinAdjointB X) = kleinAdjointAB X := by
    dsimp [kleinAdjointA, kleinAdjointB, kleinAdjointAB]
    calc
      (sigmaZ : Mat2 K) * -(massJ * X * massJ) * sigmaZ
          = -((sigmaZ * massJ) * X * (massJ * sigmaZ)) := by noncomm_ring
      _ = -(sigmaX * X * (-sigmaX)) := by rw [hZj, hJz]
      _ = sigmaX * X * sigmaX := by noncomm_ring
  have hBA : kleinAdjointB (kleinAdjointA X) = kleinAdjointAB X := by
    dsimp [kleinAdjointA, kleinAdjointB, kleinAdjointAB]
    calc
      -((massJ : Mat2 K) * (sigmaZ * X * sigmaZ) * massJ)
          = -((massJ * sigmaZ) * X * (sigmaZ * massJ)) := by noncomm_ring
      _ = -((-sigmaX) * X * sigmaX) := by rw [hJz, hZj]
      _ = sigmaX * X * sigmaX := by noncomm_ring
  have hDetZ : Matrix.det (sigmaZ : Mat2 K) = -1 := by
    rw [Matrix.det_fin_two]; simp [sigmaZ]
  have hDetX : Matrix.det (sigmaX : Mat2 K) = -1 := by
    rw [Matrix.det_fin_two]; simp [sigmaX]
  have hDetJ : Matrix.det (massJ : Mat2 K) = 1 := by
    rw [Matrix.det_fin_two]; simp [massJ]
  have hDetZ2 : Matrix.det ((sigmaZ : Mat2 K) * sigmaZ) = 1 := by
    rw [Matrix.det_mul, hDetZ]; ring
  exact ⟨⟨hZj, hSigXSq, h12.2.2.2.2⟩,
    ⟨hAA, hBB, hABAB, hAB, hBA⟩,
    ⟨hDetZ, hDetX, hDetJ, hDetZ2⟩⟩

end Mat2

-- ============================================================================
-- SECTION 2 (𝔎𝔏₁₃, 𝔎𝔏₁₄, 𝔎𝔏₁₅ in Mat₄): d=1 Rotor, d=2 Signature & d=3 Plane
-- ============================================================================

/-- Canonical $4 \times 4$ matrix carrier `Matrix (Fin 4) (Fin 4) K`. -/
abbrev Mat4 (K : Type u) : Type u := Matrix (Fin 4) (Fin 4) K

namespace Mat4
variable {K : Type u} [CommRing K]

/-- $4 \times 4$ identity matrix `I₄`. -/
def I4 : Mat4 K := (1 : Matrix (Fin 4) (Fin 4) K)

/-- Shared kinetic generator $\Gamma_1 = \sigma_z \otimes I_2 = \mathrm{diag}(1, 1, -1, -1)$ in `Mat4 K`. -/
def gamma1 : Mat4 K :=
  !![1, 0,  0,  0;
     0, 1,  0,  0;
     0, 0, -1,  0;
     0, 0,  0, -1]

/-- Second 3D kinetic generator $\Gamma_2 = \sigma_x \otimes \sigma_z$ in `Mat4 K`. -/
def gamma2 : Mat4 K :=
  !![0,  0, 1,  0;
     0,  0, 0, -1;
     1,  0, 0,  0;
     0, -1, 0,  0]

/-- Third 3D kinetic generator $\Gamma_3 = \sigma_x \otimes \sigma_x$ in `Mat4 K`. -/
def gamma3 : Mat4 K :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- First $4 \times 4$ skew-symmetric mass $M_1 = \sigma_x \otimes J$ (also $M_{\mathrm{rot}}$ in $d = 1$). -/
def massM1 : Mat4 K :=
  !![0,  0,  0, 1;
     0,  0, -1, 0;
     0,  1,  0, 0;
    -1,  0,  0, 0]

/-- Second $4 \times 4$ skew-symmetric mass $M_2 = J \otimes I_2$ (also $M_{++}$ in $d = 1$ and $T_4$ in Class DIII). -/
def massM2 : Mat4 K :=
  !![ 0,  0, 1, 0;
      0,  0, 0, 1;
     -1,  0, 0, 0;
      0, -1, 0, 0]

/-- Continuous 2-parameter mass rotor $M(c, s) = c \cdot M_1 + s \cdot M_2$ in `Mat4 K`. -/
def massRotor (c s : K) : Mat4 K :=
  c • (massM1 : Mat4 K) + s • (massM2 : Mat4 K)

/-- Entry-level extraction of a $4 \times 4$ anticommutator equation `A * X + X * A = 0`. -/
private lemma entry_anticomm4 {A X : Mat4 ℝ} (h : A * X + X * A = 0) (i j : Fin 4) :
    (A i 0 * X 0 j + A i 1 * X 1 j + A i 2 * X 2 j + A i 3 * X 3 j) +
    (X i 0 * A 0 j + X i 1 * A 1 j + X i 2 * A 2 j + X i 3 * A 3 j) = 0 := by
  have hij := congr_fun (congr_fun h i) j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_four, Fin.sum_univ_four, Matrix.zero_apply] at hij
  linarith

/-- Linear combination of two anticommuting matrices anticommutes with `G`. -/
private lemma anticomm_massRotor {G : Mat4 K} (c s : K)
    (h1 : G * massM1 + massM1 * G = 0) (h2 : G * massM2 + massM2 * G = 0) :
    G * massRotor c s + massRotor c s * G = 0 := by
  dsimp [massRotor]
  calc
    G * (c • (massM1 : Mat4 K) + s • massM2) + (c • massM1 + s • massM2) * G
        = c • (G * massM1 + massM1 * G) + s • (G * massM2 + massM2 * G) := by
          rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm,
              smul_mul_assoc, smul_mul_assoc, smul_add, smul_add]
          abel
    _ = 0 := by rw [h1, h2, smul_zero, smul_zero, add_zero]

/-- Skew-symmetry $M_1^\top = -M_1$ in `Mat4 K`. -/
private lemma massM1_transpose : (massM1 : Mat4 K).transpose = -massM1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [massM1]

/-- Skew-symmetry $M_2^\top = -M_2$ in `Mat4 K`. -/
private lemma massM2_transpose : (massM2 : Mat4 K).transpose = -massM2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [massM2]

/-- Square identity $M_1^2 = -I_4$ in `Mat4 K`. -/
private lemma massM1_sq : (massM1 : Mat4 K) * massM1 = -I4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [massM1, I4]

/-- Square identity $M_2^2 = -I_4$ in `Mat4 K`. -/
private lemma massM2_sq : (massM2 : Mat4 K) * massM2 = -I4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [massM2, I4]

/-- Anticommutation $\{\Gamma_1, M_1\} = 0$ in `Mat4 K`. -/
private lemma gamma1_anticomm_massM1 : (gamma1 : Mat4 K) * massM1 + massM1 * gamma1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma1, massM1]

/-- Anticommutation $\{\Gamma_1, M_2\} = 0$ in `Mat4 K`. -/
private lemma gamma1_anticomm_massM2 : (gamma1 : Mat4 K) * massM2 + massM2 * gamma1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma1, massM2]

/-- Mutual mass anticommutation $\{M_1, M_2\} = 0$ in `Mat4 K`. -/
private lemma massM1_anticomm_massM2 : (massM1 : Mat4 K) * massM2 + massM2 * massM1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [massM1, massM2]

/-- **Theorem 3 ($\mathfrak{KL}_{13}$ — $d = 1$ Two-Flavor Mass Rotor Trivialization $1 + 1 \equiv 0 \pmod 2$):**
In `Mat4 K` with doubled $d = 1$ kinetic generator $\widetilde{\Gamma}_1 = \mathrm{gamma1}$ ($\sigma_z \otimes I_2$),
standard doubled mass $M_{++} = \mathrm{massM2}$ ($J \otimes I_2$), and flavor-mixing mass
$M_{\mathrm{rot}} = \mathrm{massM1}$ ($\sigma_x \otimes J$):
1. $M_1^\top = -M_1$, $M_2^\top = -M_2$, $M_1^2 = -I_4$, and $M_2^2 = -I_4$.
2. Both $M_1$ and $M_2$ anticommute with $\Gamma_1$, and $\{M_1, M_2\} = 0$.
3. For any $c, s \in K$, `massRotor c s` satisfies `(massRotor c s)ᵀ = -massRotor c s`,
   `{gamma1, massRotor c s} = 0`, and `massRotor c s * massRotor c s = -(c² + s²) • I₄`
   (remaining unit-gapped whenever $c^2 + s^2 = 1$ and connecting $+M_2$ at $(0, 1)$ to $-M_2$ at $(0, -1)$). -/
theorem kl13_dim1_two_flavor_mass_rotor_trivialization (c s : K) :
    ((massM1 : Mat4 K).transpose = -massM1 ∧
      (massM2 : Mat4 K).transpose = -massM2 ∧
      (massM1 : Mat4 K) * massM1 = -I4 ∧
      (massM2 : Mat4 K) * massM2 = -I4) ∧
    ((gamma1 : Mat4 K) * massM1 + massM1 * gamma1 = 0 ∧
      (gamma1 : Mat4 K) * massM2 + massM2 * gamma1 = 0 ∧
      (massM1 : Mat4 K) * massM2 + massM2 * massM1 = 0) ∧
    ((massRotor c s).transpose = -massRotor c s ∧
      (gamma1 : Mat4 K) * massRotor c s + massRotor c s * gamma1 = 0 ∧
      massRotor c s * massRotor c s = (- (c ^ 2 + s ^ 2)) • (I4 : Mat4 K) ∧
      massRotor (0 : K) 1 = massM2 ∧
      massRotor (0 : K) (-1) = -massM2) := by
  have hM : (massM1 : Mat4 K).transpose = -massM1 ∧
      (massM2 : Mat4 K).transpose = -massM2 ∧
      (massM1 : Mat4 K) * massM1 = -I4 ∧
      (massM2 : Mat4 K) * massM2 = -I4 :=
    ⟨massM1_transpose, massM2_transpose, massM1_sq, massM2_sq⟩
  have hAnti : (gamma1 : Mat4 K) * massM1 + massM1 * gamma1 = 0 ∧
      (gamma1 : Mat4 K) * massM2 + massM2 * gamma1 = 0 ∧
      (massM1 : Mat4 K) * massM2 + massM2 * massM1 = 0 :=
    ⟨gamma1_anticomm_massM1, gamma1_anticomm_massM2, massM1_anticomm_massM2⟩
  have hRotSkew : (massRotor c s).transpose = -massRotor c s := by
    dsimp [massRotor]
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
        hM.1, hM.2.1, smul_neg, smul_neg, neg_add]
  have hRotAnti : (gamma1 : Mat4 K) * massRotor c s + massRotor c s * gamma1 = 0 :=
    anticomm_massRotor c s hAnti.1 hAnti.2.1
  have hRotSq : massRotor c s * massRotor c s = (- (c ^ 2 + s ^ 2)) • (I4 : Mat4 K) := by
    dsimp [massRotor]
    calc
      (c • (massM1 : Mat4 K) + s • massM2) * (c • massM1 + s • massM2)
          = (c * c) • (massM1 * massM1) +
            (c * s) • (massM1 * massM2 + massM2 * massM1) +
            (s * s) • (massM2 * massM2) := by
            rw [mul_add, add_mul, add_mul,
                smul_mul_smul_comm, smul_mul_smul_comm,
                smul_mul_smul_comm, smul_mul_smul_comm,
                mul_comm s c, smul_add]
            abel
      _ = (c * c) • (-(I4 : Mat4 K)) + (c * s) • 0 + (s * s) • (-I4) := by
            rw [hM.2.2.1, hAnti.2.2, hM.2.2.2]
      _ = (- (c ^ 2 + s ^ 2)) • (I4 : Mat4 K) := by
            rw [smul_zero, add_zero, smul_neg, smul_neg, ← neg_add, ← add_smul, ← neg_smul, sq, sq]
  have hEndPos : massRotor (0 : K) 1 = massM2 := by
    dsimp [massRotor]
    rw [zero_smul, zero_add, one_smul]
  have hEndNeg : massRotor (0 : K) (-1) = -massM2 := by
    dsimp [massRotor]
    rw [zero_smul, zero_add, neg_one_smul]
  exact ⟨hM, hAnti, ⟨hRotSkew, hRotAnti, hRotSq, hEndPos, hEndNeg⟩⟩

/-- Second $d = 2$ two-flavor kinetic generator $\widetilde{\Gamma}_2^{(2)} = \sigma_x \otimes I_2$ in `Mat4 K`. -/
def dim2Gamma2 : Mat4 K :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Two-flavor $d = 2$ chiral mass $M_{2D}(s_1, s_2) = J \otimes \mathrm{diag}(s_1, s_2)$ in `Mat4 K`. -/
def dim2SignatureMass (s1 s2 : K) : Mat4 K :=
  !![  0,   0, s1,  0;
       0,   0,  0, s2;
     -s1,   0,  0,  0;
       0, -s2,  0,  0]

/-- **Theorem 4 ($\mathfrak{KL}_{14}$ in $\mathrm{Mat}_4$ — $d = 2$ Two-Flavor Symmetric Signature Mass $J \otimes S$):**
For $N = 2$ stacked $d = 2$ layers with kinetic generators $\widetilde{\Gamma}_1 = \mathrm{gamma1}$ ($\sigma_z \otimes I_2$)
and $\widetilde{\Gamma}_2 = \mathrm{dim2Gamma2}$ ($\sigma_x \otimes I_2$) and diagonal symmetric matrix
$S = \mathrm{diag}(s_1, s_2)$:
1. `(dim2SignatureMass s1 s2)ᵀ = -dim2SignatureMass s1 s2`.
2. Both `{gamma1, dim2SignatureMass s1 s2} = 0` and `{dim2Gamma2, dim2SignatureMass s1 s2} = 0`.
3. `-(dim2SignatureMass s1 s2 * dim2SignatureMass s1 s2) = Matrix.diagonal ![s1 ^ 2, s2 ^ 2, s1 ^ 2, s2 ^ 2]`
   and `Matrix.det (dim2SignatureMass s1 s2) = (s1 * s2) ^ 2` (so reversing the sign of either eigenvalue $s_i$
   requires passing through $s_i = 0$ where $\det = 0$, closing the bulk gap). -/
theorem kl14_dim2_two_flavor_symmetric_signature_mass (s1 s2 : K) :
    (dim2SignatureMass s1 s2).transpose = -dim2SignatureMass s1 s2 ∧
    (gamma1 : Mat4 K) * dim2SignatureMass s1 s2 + dim2SignatureMass s1 s2 * gamma1 = 0 ∧
    (dim2Gamma2 : Mat4 K) * dim2SignatureMass s1 s2 + dim2SignatureMass s1 s2 * dim2Gamma2 = 0 ∧
    -(dim2SignatureMass s1 s2 * dim2SignatureMass s1 s2) =
      Matrix.diagonal ![s1 ^ 2, s2 ^ 2, s1 ^ 2, s2 ^ 2] ∧
    Matrix.det (dim2SignatureMass s1 s2) = (s1 * s2) ^ 2 := by
  have hSkew : (dim2SignatureMass s1 s2).transpose = -dim2SignatureMass s1 s2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [dim2SignatureMass]
  have hA1 : (gamma1 : Mat4 K) * dim2SignatureMass s1 s2 + dim2SignatureMass s1 s2 * gamma1 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [gamma1, dim2SignatureMass]
  have hA2 : (dim2Gamma2 : Mat4 K) * dim2SignatureMass s1 s2 + dim2SignatureMass s1 s2 * dim2Gamma2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [dim2Gamma2, dim2SignatureMass]
  have hSq : -(dim2SignatureMass s1 s2 * dim2SignatureMass s1 s2) =
      Matrix.diagonal ![s1 ^ 2, s2 ^ 2, s1 ^ 2, s2 ^ 2] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [dim2SignatureMass, sq]
  have hDet : Matrix.det (dim2SignatureMass s1 s2) = (s1 * s2) ^ 2 := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
    simp [dim2SignatureMass, Matrix.submatrix, Matrix.det_succ_row_zero,
      Fin.sum_univ_three, Fin.sum_univ_two, Fin.succAbove]
    ring
  exact ⟨hSkew, hA1, hA2, hSq, hDet⟩

/-- Symmetry $\Gamma_1^\top = \Gamma_1$ in `Mat4 K`. -/
private lemma gamma1_transpose : (gamma1 : Mat4 K).transpose = gamma1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma1]

/-- Symmetry $\Gamma_2^\top = \Gamma_2$ in `Mat4 K`. -/
private lemma gamma2_transpose : (gamma2 : Mat4 K).transpose = gamma2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma2]

/-- Symmetry $\Gamma_3^\top = \Gamma_3$ in `Mat4 K`. -/
private lemma gamma3_transpose : (gamma3 : Mat4 K).transpose = gamma3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma3]

/-- Square identity $\Gamma_1^2 = I_4$ in `Mat4 K`. -/
private lemma gamma1_sq : (gamma1 : Mat4 K) * gamma1 = I4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma1, I4]

/-- Square identity $\Gamma_2^2 = I_4$ in `Mat4 K`. -/
private lemma gamma2_sq : (gamma2 : Mat4 K) * gamma2 = I4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma2, I4]

/-- Square identity $\Gamma_3^2 = I_4$ in `Mat4 K`. -/
private lemma gamma3_sq : (gamma3 : Mat4 K) * gamma3 = I4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma3, I4]

/-- Anticommutation $\{\Gamma_1, \Gamma_2\} = 0$ in `Mat4 K`. -/
private lemma gamma1_anticomm_gamma2 : (gamma1 : Mat4 K) * gamma2 + gamma2 * gamma1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma1, gamma2]

/-- Anticommutation $\{\Gamma_1, \Gamma_3\} = 0$ in `Mat4 K`. -/
private lemma gamma1_anticomm_gamma3 : (gamma1 : Mat4 K) * gamma3 + gamma3 * gamma1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma1, gamma3]

/-- Anticommutation $\{\Gamma_2, \Gamma_3\} = 0$ in `Mat4 K`. -/
private lemma gamma2_anticomm_gamma3 : (gamma2 : Mat4 K) * gamma3 + gamma3 * gamma2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma2, gamma3]

/-- Anticommutation $\{\Gamma_2, M_1\} = 0$ in `Mat4 K`. -/
private lemma gamma2_anticomm_massM1 : (gamma2 : Mat4 K) * massM1 + massM1 * gamma2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma2, massM1]

/-- Anticommutation $\{\Gamma_3, M_1\} = 0$ in `Mat4 K`. -/
private lemma gamma3_anticomm_massM1 : (gamma3 : Mat4 K) * massM1 + massM1 * gamma3 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma3, massM1]

/-- Anticommutation $\{\Gamma_2, M_2\} = 0$ in `Mat4 K`. -/
private lemma gamma2_anticomm_massM2 : (gamma2 : Mat4 K) * massM2 + massM2 * gamma2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma2, massM2]

/-- Anticommutation $\{\Gamma_3, M_2\} = 0$ in `Mat4 K`. -/
private lemma gamma3_anticomm_massM2 : (gamma3 : Mat4 K) * massM2 + massM2 * gamma3 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma3, massM2]

/-- **Theorem 5 ($\mathfrak{KL}_{15}$ — $d = 3$ Class D Two-Mass Plane Completeness & Homotopy Rotor in $\mathrm{Mat}_4$):**
For the three $d = 3$ symmetric kinetic generators $\Gamma_1, \Gamma_2, \Gamma_3$ and the two
skew-symmetric masses $M_1 = \sigma_x \otimes J$ and $M_2 = J \otimes I_2$:
1. $\Gamma_a^\top = \Gamma_a$, $\Gamma_a^2 = I_4$, and $\{\Gamma_a, \Gamma_b\} = 0$ ($a \neq b$).
2. Both $M_1$ and $M_2$ anticommute with all three $\Gamma_1, \Gamma_2, \Gamma_3$, and $\{M_1, M_2\} = 0$.
3. For any $c, s \in K$, `massRotor c s` anticommutes with $\Gamma_1, \Gamma_2, \Gamma_3$ and satisfies
   `massRotor c s * massRotor c s = -(c² + s²) • I₄`.
4. **Exact 2-Plane Completeness in $\mathrm{Mat}_4(\mathbb{R})$**:
   Every matrix $X \in \mathrm{Mat}_4(\mathbb{R})$ that anticommutes with $\Gamma_1, \Gamma_2, \Gamma_3$
   is uniquely of the form `X = massRotor (X 0 3) (X 0 2)` (automatically skew-symmetric!). -/
theorem kl15_dim3_classD_two_mass_plane_completeness_and_rotor (c s : K) (X : Mat4 ℝ) :
    ((gamma1 : Mat4 K).transpose = gamma1 ∧
      (gamma2 : Mat4 K).transpose = gamma2 ∧
      (gamma3 : Mat4 K).transpose = gamma3 ∧
      (gamma1 : Mat4 K) * gamma1 = I4 ∧
      (gamma2 : Mat4 K) * gamma2 = I4 ∧
      (gamma3 : Mat4 K) * gamma3 = I4 ∧
      (gamma1 : Mat4 K) * gamma2 + gamma2 * gamma1 = 0 ∧
      (gamma1 : Mat4 K) * gamma3 + gamma3 * gamma1 = 0 ∧
      (gamma2 : Mat4 K) * gamma3 + gamma3 * gamma2 = 0) ∧
    ((gamma1 : Mat4 K) * massM1 + massM1 * gamma1 = 0 ∧
      (gamma2 : Mat4 K) * massM1 + massM1 * gamma2 = 0 ∧
      (gamma3 : Mat4 K) * massM1 + massM1 * gamma3 = 0 ∧
      (gamma1 : Mat4 K) * massM2 + massM2 * gamma1 = 0 ∧
      (gamma2 : Mat4 K) * massM2 + massM2 * gamma2 = 0 ∧
      (gamma3 : Mat4 K) * massM2 + massM2 * gamma3 = 0 ∧
      (massM1 : Mat4 K) * massM2 + massM2 * massM1 = 0) ∧
    ((gamma2 : Mat4 K) * massRotor c s + massRotor c s * gamma2 = 0 ∧
      (gamma3 : Mat4 K) * massRotor c s + massRotor c s * gamma3 = 0 ∧
      massRotor c s * massRotor c s = (- (c ^ 2 + s ^ 2)) • (I4 : Mat4 K)) ∧
    ((gamma1 : Mat4 ℝ) * X + X * gamma1 = 0 →
      (gamma2 : Mat4 ℝ) * X + X * gamma2 = 0 →
      (gamma3 : Mat4 ℝ) * X + X * gamma3 = 0 →
      X = massRotor (X 0 3) (X 0 2) ∧ X.transpose = -X) := by
  have hKin : (gamma1 : Mat4 K).transpose = gamma1 ∧
      (gamma2 : Mat4 K).transpose = gamma2 ∧
      (gamma3 : Mat4 K).transpose = gamma3 ∧
      (gamma1 : Mat4 K) * gamma1 = I4 ∧
      (gamma2 : Mat4 K) * gamma2 = I4 ∧
      (gamma3 : Mat4 K) * gamma3 = I4 ∧
      (gamma1 : Mat4 K) * gamma2 + gamma2 * gamma1 = 0 ∧
      (gamma1 : Mat4 K) * gamma3 + gamma3 * gamma1 = 0 ∧
      (gamma2 : Mat4 K) * gamma3 + gamma3 * gamma2 = 0 :=
    ⟨gamma1_transpose, gamma2_transpose, gamma3_transpose,
     gamma1_sq, gamma2_sq, gamma3_sq,
     gamma1_anticomm_gamma2, gamma1_anticomm_gamma3, gamma2_anticomm_gamma3⟩
  have hMass : (gamma1 : Mat4 K) * massM1 + massM1 * gamma1 = 0 ∧
      (gamma2 : Mat4 K) * massM1 + massM1 * gamma2 = 0 ∧
      (gamma3 : Mat4 K) * massM1 + massM1 * gamma3 = 0 ∧
      (gamma1 : Mat4 K) * massM2 + massM2 * gamma1 = 0 ∧
      (gamma2 : Mat4 K) * massM2 + massM2 * gamma2 = 0 ∧
      (gamma3 : Mat4 K) * massM2 + massM2 * gamma3 = 0 ∧
      (massM1 : Mat4 K) * massM2 + massM2 * massM1 = 0 :=
    ⟨gamma1_anticomm_massM1, gamma2_anticomm_massM1, gamma3_anticomm_massM1,
     gamma1_anticomm_massM2, gamma2_anticomm_massM2, gamma3_anticomm_massM2,
     massM1_anticomm_massM2⟩
  have hRot2 : (gamma2 : Mat4 K) * massRotor c s + massRotor c s * gamma2 = 0 :=
    anticomm_massRotor c s gamma2_anticomm_massM1 gamma2_anticomm_massM2
  have hRot3 : (gamma3 : Mat4 K) * massRotor c s + massRotor c s * gamma3 = 0 :=
    anticomm_massRotor c s gamma3_anticomm_massM1 gamma3_anticomm_massM2
  have hRotSq := (kl13_dim1_two_flavor_mass_rotor_trivialization c s).2.2.2.2.1
  refine ⟨hKin, hMass, ⟨hRot2, hRot3, hRotSq⟩, fun h1 h2 h3 => ?_⟩
  have h1_00 := entry_anticomm4 h1 0 0; simp [gamma1] at h1_00
  have h1_01 := entry_anticomm4 h1 0 1; simp [gamma1] at h1_01
  have h1_10 := entry_anticomm4 h1 1 0; simp [gamma1] at h1_10
  have h1_11 := entry_anticomm4 h1 1 1; simp [gamma1] at h1_11
  have h1_22 := entry_anticomm4 h1 2 2; simp [gamma1] at h1_22
  have h1_23 := entry_anticomm4 h1 2 3; simp [gamma1] at h1_23
  have h1_32 := entry_anticomm4 h1 3 2; simp [gamma1] at h1_32
  have h1_33 := entry_anticomm4 h1 3 3; simp [gamma1] at h1_33
  have h2_00 := entry_anticomm4 h2 0 0; simp [gamma2] at h2_00
  have h2_01 := entry_anticomm4 h2 0 1; simp [gamma2] at h2_01
  have h2_10 := entry_anticomm4 h2 1 0; simp [gamma2] at h2_10
  have h2_11 := entry_anticomm4 h2 1 1; simp [gamma2] at h2_11
  have h3_00 := entry_anticomm4 h3 0 0; simp [gamma3] at h3_00
  have h3_01 := entry_anticomm4 h3 0 1; simp [gamma3] at h3_01
  have h3_10 := entry_anticomm4 h3 1 0; simp [gamma3] at h3_10
  have h3_11 := entry_anticomm4 h3 1 1; simp [gamma3] at h3_11
  have hX : X = massRotor (X 0 3) (X 0 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [massRotor, massM1, massM2] <;>
      linarith
  have hSkew : X.transpose = -X := by
    rw [hX]
    exact (kl13_dim1_two_flavor_mass_rotor_trivialization (X 0 3) (X 0 2)).2.2.1
  exact ⟨hX, hSkew⟩

-- ============================================================================
-- SECTION 3 (𝔎𝔏₁₆ in Mat₄ & Mat₈): 3D Class DIII Kramers TRS & Socratic Elenchus
-- ============================================================================

/-- The tensor product $J \otimes J = \begin{pmatrix} 0 & J \\ -J & 0 \end{pmatrix}$ in `Mat4 K`,
which is **symmetric** ($(J \otimes J)^\top = +(J \otimes J)$) and squares to $+I_4$. -/
def symJJ4 : Mat4 K :=
  !![0,  0,  0, 1;
     0,  0, -1, 0;
     0, -1,  0, 0;
     1,  0,  0, 0]

/-- Algebraic expansion of the commutator `massRotor a b * massM2 - massM2 * massRotor a b`. -/
private lemma massRotor_comm_massM2 (a b : K) :
    massRotor a b * (massM2 : Mat4 K) - massM2 * massRotor a b =
      a • ((massM1 : Mat4 K) * massM2 - massM2 * massM1) := by
  dsimp [massRotor]
  rw [add_mul, mul_add, smul_mul_assoc, smul_mul_assoc,
      mul_smul_comm, mul_smul_comm, smul_sub]
  abel

/-- Algebraic expansion of the anticommutator `massRotor a b * massM2 + massM2 * massRotor a b`. -/
private lemma massRotor_anticomm_massM2 (a b : K) :
    massRotor a b * (massM2 : Mat4 K) + massM2 * massRotor a b =
      (- (2 * b)) • (I4 : Mat4 K) := by
  dsimp [massRotor]
  calc
    (a • (massM1 : Mat4 K) + b • massM2) * massM2 +
        massM2 * (a • massM1 + b • massM2)
        = a • (massM1 * massM2 + massM2 * massM1) +
          (b + b) • (massM2 * massM2) := by
          rw [add_mul, mul_add, smul_mul_assoc, smul_mul_assoc,
              mul_smul_comm, mul_smul_comm, smul_add, add_smul]
          abel
    _ = a • 0 + (b + b) • (-(I4 : Mat4 K)) := by rw [massM1_anticomm_massM2, massM2_sq]
    _ = (- (2 * b)) • (I4 : Mat4 K) := by
          rw [smul_zero, zero_add, smul_neg, ← neg_smul, two_mul]

/-- **Theorem 6a ($\mathfrak{KL}_{16}$ in $\mathrm{Mat}_4$ — Socratic Elenchus on $J \otimes J$ & Kramers TRS Mass Blocking):**
1. **Socratic Elenchus on $J \otimes J$**: `symJJ4ᵀ = +symJJ4`, `symJJ4 * symJJ4 = +I4`,
   `{gamma1, symJJ4} = 0`, `[gamma2, symJJ4] = 0`, and `[gamma3, symJJ4] = 0`.
2. **Kramers TRS in $\mathrm{Mat}_4$ (`T₄ = massM2 = J ⊗ I₂`)**:
   `massM2ᵀ = -massM2`, `massM2 * massM2 = -I4`, and `{gamma_a, massM2} = 0` for $a = 1, 2, 3$.
3. **Mass Channel Blocking on `massRotor a b = a • massM1 + b • massM2` over $\mathbb{R}$**:
   - Commuting with $T_4 = \mathrm{massM2}$ (`massRotor a b * massM2 - massM2 * massRotor a b = 0`)
     holds if and only if $a = 0$ (blocking $M_1$ and reducing $a^2 + b^2 = 1$ to $M = \pm M_2$).
   - Anticommuting with $T_4 = \mathrm{massM2}$ (`massRotor a b * massM2 + massM2 * massRotor a b = 0`)
     holds if and only if $b = 0$ (blocking $M_2$ and reducing $a^2 + b^2 = 1$ to $M = \pm M_1$). -/
theorem kl16_dim3_classDIII_kramers_trs_mass_channel_blocking (a b : ℝ) :
    ((symJJ4 : Mat4 K).transpose = symJJ4 ∧
      (symJJ4 : Mat4 K) * symJJ4 = I4 ∧
      (gamma1 : Mat4 K) * symJJ4 + symJJ4 * gamma1 = 0 ∧
      (gamma2 : Mat4 K) * symJJ4 - symJJ4 * gamma2 = 0 ∧
      (gamma3 : Mat4 K) * symJJ4 - symJJ4 * gamma3 = 0) ∧
    ((massM2 : Mat4 K).transpose = -massM2 ∧
      (massM2 : Mat4 K) * massM2 = -I4) ∧
    ((massRotor a b * (massM2 : Mat4 ℝ) - massM2 * massRotor a b = 0 ↔ a = 0) ∧
      (massRotor a b * (massM2 : Mat4 ℝ) + massM2 * massRotor a b = 0 ↔ b = 0)) := by
  have hJJ : (symJJ4 : Mat4 K).transpose = symJJ4 ∧
      (symJJ4 : Mat4 K) * symJJ4 = I4 ∧
      (gamma1 : Mat4 K) * symJJ4 + symJJ4 * gamma1 = 0 ∧
      (gamma2 : Mat4 K) * symJJ4 - symJJ4 * gamma2 = 0 ∧
      (gamma3 : Mat4 K) * symJJ4 - symJJ4 * gamma3 = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · ext i j; fin_cases i <;> fin_cases j <;> simp [symJJ4, gamma1, gamma2, gamma3, I4]
  have hT4 : (massM2 : Mat4 K).transpose = -massM2 ∧ (massM2 : Mat4 K) * massM2 = -I4 :=
    ⟨massM2_transpose, massM2_sq⟩
  have hComm : massRotor a b * (massM2 : Mat4 ℝ) - massM2 * massRotor a b = 0 ↔ a = 0 := by
    rw [massRotor_comm_massM2]
    constructor
    · intro h
      have h01 := congr_fun (congr_fun h 0) 1
      have hEntry : (((massM1 : Mat4 ℝ) * massM2 - massM2 * massM1 : Mat4 ℝ) 0 1) = -2 := by
        simp [massM1, massM2]
        norm_num
      rw [Matrix.smul_apply, hEntry, Matrix.zero_apply, smul_eq_mul] at h01
      linarith
    · rintro rfl
      exact zero_smul ℝ _
  have hAnti : massRotor a b * (massM2 : Mat4 ℝ) + massM2 * massRotor a b = 0 ↔ b = 0 := by
    rw [massRotor_anticomm_massM2]
    constructor
    · intro h
      have h00 := congr_fun (congr_fun h 0) 0
      simp [I4] at h00
      linarith
    · rintro rfl
      simp
  exact ⟨hJJ, hT4, ⟨hComm, hAnti⟩⟩

end Mat4

/-- Canonical $8 \times 8$ block-matrix carrier `Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) K`. -/
abbrev Mat8Split (K : Type u) : Type u := Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) K

namespace Mat8
variable {K : Type u} [CommRing K]

open scoped Kronecker

/-- $8 \times 8$ lifted kinetic generator $\widetilde{\Gamma}_1 = I_2 \otimes \Gamma_1$. -/
def tildeGamma1 : Mat8Split K := (Mat2.I2 : Mat2 K) ⊗ₖ (Mat4.gamma1 : Mat4 K)

/-- $8 \times 8$ lifted kinetic generator $\widetilde{\Gamma}_2 = I_2 \otimes \Gamma_2$. -/
def tildeGamma2 : Mat8Split K := (Mat2.I2 : Mat2 K) ⊗ₖ (Mat4.gamma2 : Mat4 K)

/-- $8 \times 8$ lifted kinetic generator $\widetilde{\Gamma}_3 = I_2 \otimes \Gamma_3$. -/
def tildeGamma3 : Mat8Split K := (Mat2.I2 : Mat2 K) ⊗ₖ (Mat4.gamma3 : Mat4 K)

/-- The raw text's candidate $T_{\mathrm{raw}} = J \otimes (J \otimes J)$ in `Mat8Split K`. -/
def rawCandidateJJJ8 : Mat8Split K := (Mat2.massJ : Mat2 K) ⊗ₖ (Mat4.symJJ4 : Mat4 K)

/-- Genuine $8 \times 8$ Kramers time-reversal operator $T_8 = I_2 \otimes M_2 = I_2 \otimes (J \otimes I_2)$. -/
def kramersTRS8 : Mat8Split K := (Mat2.I2 : Mat2 K) ⊗ₖ (Mat4.massM2 : Mat4 K)

/-- Genuine $8 \times 8$ TRS-compatible mass $M_8 = \sigma_z \otimes M_2$ (commuting with $T_8 = I_2 \otimes M_2$). -/
def trsCommutingMass8 : Mat8Split K := (Mat2.sigmaZ : Mat2 K) ⊗ₖ (Mat4.massM2 : Mat4 K)

/-- Blocked $8 \times 8$ mass partner $M_8' = I_2 \otimes M_1$ (anticommuting with $T_8$). -/
def trsBlockedMass8 : Mat8Split K := (Mat2.I2 : Mat2 K) ⊗ₖ (Mat4.massM1 : Mat4 K)

/-- Right linearity of `⊗ₖ` over addition in `Mat8Split K`. -/
private lemma kronecker_add_right (A : Mat2 K) (B C : Mat4 K) :
    (A ⊗ₖ B) + (A ⊗ₖ C) = A ⊗ₖ (B + C) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kroneckerMap_apply, mul_add]

/-- Right linearity of `⊗ₖ` over subtraction in `Mat8Split K`. -/
private lemma kronecker_sub_right (A : Mat2 K) (B C : Mat4 K) :
    (A ⊗ₖ B) - (A ⊗ₖ C) = A ⊗ₖ (B - C) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kroneckerMap_apply, mul_sub]

/-- Right annihilation `A ⊗ₖ 0 = 0` in `Mat8Split K`. -/
private lemma kronecker_zero_right (A : Mat2 K) :
    A ⊗ₖ (0 : Mat4 K) = 0 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kroneckerMap_apply]

/-- Right negation `A ⊗ₖ (-B) = -(A ⊗ₖ B)` in `Mat8Split K`. -/
private lemma kronecker_neg_right (A : Mat2 K) (B : Mat4 K) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kroneckerMap_apply]

/-- Kronecker transpose identity `(A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ` in `Mat8Split K`. -/
private lemma transpose_kronecker_local (A : Mat2 K) (B : Mat4 K) :
    (A ⊗ₖ B).transpose = A.transpose ⊗ₖ B.transpose := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kroneckerMap_apply]

/-- Tensor identity `(-I₂) ⊗ₖ I₄ = -1` in `Mat8Split K`. -/
private lemma neg_one_kronecker_one :
    (-(Mat2.I2 : Mat2 K)) ⊗ₖ (Mat4.I4 : Mat4 K) = -1 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Mat2.I2, Mat4.I4, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

/-- Tensor identity `I₂ ⊗ₖ (-I₄) = -1` in `Mat8Split K`. -/
private lemma one_kronecker_neg_one :
    (Mat2.I2 : Mat2 K) ⊗ₖ (-(Mat4.I4 : Mat4 K)) = -1 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Mat2.I2, Mat4.I4, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

/-- **Theorem 6b ($\mathfrak{KL}_{16}$ in $\mathrm{Mat}_8$ — Socratic Elenchus on $J \otimes J \otimes J$ & Kramers $T_8$ Lift):**
1. **Elenchus on $T_{\mathrm{raw}} = J \otimes (J \otimes J)$**:
   Although `rawCandidateJJJ8 * rawCandidateJJJ8 = -1` and `{tildeGamma1, rawCandidateJJJ8} = 0`,
   `rawCandidateJJJ8` **commutes** with `tildeGamma2` and `tildeGamma3`
   (`tildeGamma2 * rawCandidateJJJ8 - rawCandidateJJJ8 * tildeGamma2 = 0` and
   `tildeGamma3 * rawCandidateJJJ8 - rawCandidateJJJ8 * tildeGamma3 = 0`) because $J \otimes J$ flips two signs.
2. **Genuine Kramers TRS $T_8 = I_2 \otimes M_2$**:
   `kramersTRS8ᵀ = -kramersTRS8`, `kramersTRS8 * kramersTRS8 = -1`, and `kramersTRS8` anticommutes
   with all three $\widetilde{\Gamma}_1, \widetilde{\Gamma}_2, \widetilde{\Gamma}_3$.
3. **TRS Mass Selection in $\mathrm{Mat}_8$**:
   - `trsCommutingMass8` ($\sigma_z \otimes M_2$) satisfies `trsCommutingMass8 * trsCommutingMass8 = -1`,
     anticommutes with $\widetilde{\Gamma}_1, \widetilde{\Gamma}_2, \widetilde{\Gamma}_3$, and **commutes** with `kramersTRS8`
     (`trsCommutingMass8 * kramersTRS8 - kramersTRS8 * trsCommutingMass8 = 0`),
   - whereas `trsBlockedMass8` ($I_2 \otimes M_1$) **anticommutes** with `kramersTRS8`
     (`trsBlockedMass8 * kramersTRS8 + kramersTRS8 * trsBlockedMass8 = 0`). -/
theorem kl16_dim3_mat8_elenchus_and_kramers_trs_lift :
    ((rawCandidateJJJ8 : Mat8Split K) * rawCandidateJJJ8 = -1 ∧
      (tildeGamma1 : Mat8Split K) * rawCandidateJJJ8 + rawCandidateJJJ8 * tildeGamma1 = 0 ∧
      (tildeGamma2 : Mat8Split K) * rawCandidateJJJ8 - rawCandidateJJJ8 * tildeGamma2 = 0 ∧
      (tildeGamma3 : Mat8Split K) * rawCandidateJJJ8 - rawCandidateJJJ8 * tildeGamma3 = 0) ∧
    ((kramersTRS8 : Mat8Split K).transpose = -kramersTRS8 ∧
      (kramersTRS8 : Mat8Split K) * kramersTRS8 = -1 ∧
      (tildeGamma1 : Mat8Split K) * kramersTRS8 + kramersTRS8 * tildeGamma1 = 0 ∧
      (tildeGamma2 : Mat8Split K) * kramersTRS8 + kramersTRS8 * tildeGamma2 = 0 ∧
      (tildeGamma3 : Mat8Split K) * kramersTRS8 + kramersTRS8 * tildeGamma3 = 0) ∧
    ((trsCommutingMass8 : Mat8Split K) * trsCommutingMass8 = -1 ∧
      (tildeGamma1 : Mat8Split K) * trsCommutingMass8 + trsCommutingMass8 * tildeGamma1 = 0 ∧
      (tildeGamma2 : Mat8Split K) * trsCommutingMass8 + trsCommutingMass8 * tildeGamma2 = 0 ∧
      (tildeGamma3 : Mat8Split K) * trsCommutingMass8 + trsCommutingMass8 * tildeGamma3 = 0 ∧
      (trsCommutingMass8 : Mat8Split K) * kramersTRS8 - kramersTRS8 * trsCommutingMass8 = 0 ∧
      (trsBlockedMass8 : Mat8Split K) * kramersTRS8 + kramersTRS8 * trsBlockedMass8 = 0) := by
  have h2 := (Mat2.kl12_dim1_one_flavor_isolated_mass_dichotomy (1 : K) 0).1
  have h15 := Mat4.kl15_dim3_classD_two_mass_plane_completeness_and_rotor (0 : K) 0 0
  have h16 := Mat4.kl16_dim3_classDIII_kramers_trs_mass_channel_blocking (K := K) 0 0
  have hI2L : ∀ A : Mat2 K, (Mat2.I2 : Mat2 K) * A = A := fun A => Matrix.one_mul A
  have hI2R : ∀ A : Mat2 K, A * (Mat2.I2 : Mat2 K) = A := fun A => Matrix.mul_one A
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · dsimp [rawCandidateJJJ8]
    rw [← Matrix.mul_kronecker_mul, h2.2.2.2.1, h16.1.2.1, neg_one_kronecker_one]
  · dsimp [tildeGamma1, rawCandidateJJJ8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        hI2L, hI2R, kronecker_add_right, h16.1.2.2.1, kronecker_zero_right]
  · dsimp [tildeGamma2, rawCandidateJJJ8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        hI2L, hI2R, kronecker_sub_right, h16.1.2.2.2.1, kronecker_zero_right]
  · dsimp [tildeGamma3, rawCandidateJJJ8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        hI2L, hI2R, kronecker_sub_right, h16.1.2.2.2.2, kronecker_zero_right]
  · dsimp [kramersTRS8, Mat2.I2]
    rw [transpose_kronecker_local, Matrix.transpose_one, h16.2.1.1, kronecker_neg_right]
  · dsimp [kramersTRS8]
    rw [← Matrix.mul_kronecker_mul, hI2L, h16.2.1.2, one_kronecker_neg_one]
  · dsimp [tildeGamma1, kramersTRS8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        hI2L, kronecker_add_right, h15.2.1.2.2.2.1, kronecker_zero_right]
  · dsimp [tildeGamma2, kramersTRS8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        hI2L, kronecker_add_right, h15.2.1.2.2.2.2.1, kronecker_zero_right]
  · dsimp [tildeGamma3, kramersTRS8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        hI2L, kronecker_add_right, h15.2.1.2.2.2.2.2.1, kronecker_zero_right]
  · dsimp [trsCommutingMass8]
    rw [← Matrix.mul_kronecker_mul, h2.2.1, h16.2.1.2, one_kronecker_neg_one]
  · dsimp [tildeGamma1, trsCommutingMass8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        hI2L, hI2R, kronecker_add_right, h15.2.1.2.2.2.1, kronecker_zero_right]
  · dsimp [tildeGamma2, trsCommutingMass8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        hI2L, hI2R, kronecker_add_right, h15.2.1.2.2.2.2.1, kronecker_zero_right]
  · dsimp [tildeGamma3, trsCommutingMass8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        hI2L, hI2R, kronecker_add_right, h15.2.1.2.2.2.2.2.1, kronecker_zero_right]
  · dsimp [trsCommutingMass8, kramersTRS8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hI2L, hI2R, sub_self]
  · dsimp [trsBlockedMass8, kramersTRS8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        hI2L, kronecker_add_right, h15.2.1.2.2.2.2.2.2, kronecker_zero_right]

end Mat8

-- ============================================================================
-- SECTION 4 (𝔎𝔏₁₈ in Mat₃₂): Cl(1,1) ⊗ Cl(4,4) ≅ Mat₃₂(K) & D_Klein² Shield
-- ============================================================================

/-- Canonical $16 \times 16$ carrier for the 8D phase-space algebra $\mathcal{C}\ell(4,4) \cong \mathrm{Mat}_{16}(K)$. -/
abbrev Mat16 (K : Type u) : Type u := Matrix (Fin 16) (Fin 16) K

/-- Canonical $32 \times 32$ block-matrix carrier for the Klein-twisted algebra
$\mathcal{A}_{\mathrm{Klein}} = \mathcal{C}\ell(1,1) \otimes \mathcal{C}\ell(4,4) \cong \mathrm{Mat}_2(K) \otimes \mathrm{Mat}_{16}(K) \cong \mathrm{Mat}_{32}(K)$. -/
abbrev Mat32Split (K : Type u) : Type u := Matrix (Fin 2 × Fin 16) (Fin 2 × Fin 16) K

namespace Mat32
variable {K : Type u} [CommRing K]

open scoped Kronecker

/-- $16 \times 16$ identity matrix `I₁₆` in `Mat16 K`. -/
def I16 : Mat16 K := (1 : Matrix (Fin 16) (Fin 16) K)

/-- $16 \times 16$ grading involution $\Gamma_0^{(16)} = \mathrm{diag}(1, -1, \dots, -1)$ in `Mat16 K`. -/
def parity16 : Matrix (Fin 16) (Fin 16) K :=
  fun i j => if i = j then (if i = 0 then (1 : K) else -1) else 0

/-- $16 \times 16$ elementary transition $E_{0,1}^{(16)}$ in `Mat16 K`. -/
def flip01_16 : Matrix (Fin 16) (Fin 16) K :=
  fun i j => if i = 0 ∧ j = 1 then (1 : K) else 0

/-- Closed anticommutator witness $\{\Gamma_0^{(16)}, E_{0,1}^{(16)}\} = 0$ in `Mat16 K`. -/
lemma parity16_anticomm_flip01_16 :
    (parity16 : Matrix (Fin 16) (Fin 16) K) * flip01_16 + flip01_16 * parity16 = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.zero_apply]
  rw [Fintype.sum_eq_single i (fun k hk => by simp [parity16, Ne.symm hk])]
  rw [Fintype.sum_eq_single j (fun k hk => by simp [parity16, hk])]
  dsimp [parity16, flip01_16]
  simp only [↓reduceIte]
  by_cases h : i = 0 ∧ j = 1
  · rcases h with ⟨rfl, rfl⟩
    have h10 : (1 : Fin 16) ≠ 0 := by decide
    simp [h10]
  · simp [h]

/-- The Klein-twisted Dirac operator in $\mathcal{A}_{\mathrm{Klein}} \cong \mathrm{Mat}_{32}(K)$:
$$\mathcal{D}_{\mathrm{Klein}}(D_{8D}, M_{\mathrm{twist}}) \;=\; \gamma_0 \otimes D_{8D} \;+\; \gamma_1 \otimes M_{\mathrm{twist}},$$
where $\gamma_0 = \sigma_z$ ($\gamma_0^2 = +I_2$) and $\gamma_1 = J$ ($\gamma_1^2 = -I_2$). -/
def kleinDirac (D M : Mat16 K) : Mat32Split K :=
  ((Mat2.sigmaZ : Mat2 K) ⊗ₖ D) + ((Mat2.massJ : Mat2 K) ⊗ₖ M)

/-- Right linearity of `⊗ₖ` over addition in `Mat32Split K`. -/
private lemma kronecker_add_right16 (A : Mat2 K) (B C : Mat16 K) :
    (A ⊗ₖ B) + (A ⊗ₖ C) = A ⊗ₖ (B + C) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kroneckerMap_apply, mul_add]

/-- Right linearity of `⊗ₖ` over subtraction in `Mat32Split K`. -/
private lemma kronecker_sub_right16 (A : Mat2 K) (B C : Mat16 K) :
    (A ⊗ₖ B) - (A ⊗ₖ C) = A ⊗ₖ (B - C) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kroneckerMap_apply, mul_sub]

/-- Left negation `(-A) ⊗ₖ B = -(A ⊗ₖ B)` in `Mat32Split K`. -/
private lemma kronecker_neg_left16 (A : Mat2 K) (B : Mat16 K) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kroneckerMap_apply]

/-- Right annihilation `A ⊗ₖ 0 = 0` in `Mat32Split K`. -/
private lemma kronecker_zero_right16 (A : Mat2 K) :
    A ⊗ₖ (0 : Mat16 K) = 0 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kroneckerMap_apply]

/-- **Theorem 7 ($\mathfrak{KL}_{18}$ — $\mathcal{A}_{\mathrm{Klein}} = \mathcal{C}\ell(1,1) \otimes \mathcal{C}\ell(4,4) \cong \mathrm{Mat}_{32}(K)$ & Universal $\mathcal{D}_{\mathrm{Klein}}^2$ Gap Shield):**
1. **Real Split Dimension & Equivalence**:
   $2^1 = 2$, $2^4 = 16$, $2^1 \cdot 2^4 = 32 = 2^5$, and `Fintype.card (Fin 2 × Fin 16) = 32`.
2. **Universal Square Identity of $\mathcal{D}_{\mathrm{Klein}}(D, M) = \gamma_0 \otimes D + \gamma_1 \otimes M$**:
   Because $\gamma_0^2 = +I_2$, $\gamma_1^2 = -I_2$, $\gamma_0 \gamma_1 = \sigma_x$, and $\gamma_1 \gamma_0 = -\sigma_x$,
   for any $D, M \in \mathrm{Mat}_{16}(K)$:
   $$\mathcal{D}_{\mathrm{Klein}}(D, M)^2 \;=\; I_2 \otimes (D^2 - M^2) \;+\; \sigma_x \otimes (D M - M D).$$
3. **Commuting-Twist Mass Gap Shield ($[D, M] = 0$ & $M^2 = -m^2 I_{16}$)**:
   Whenever $D M = M D$, the off-diagonal Klein cross-term $\sigma_x \otimes (D M - M D)$ vanishes:
   $$\mathcal{D}_{\mathrm{Klein}}(D, M)^2 \;=\; I_2 \otimes (D^2 - M^2),$$
   and if $M$ is a skew-symmetric ABS mass satisfying $M^2 = -(m^2 \cdot I_{16})$, then
   $$\mathcal{D}_{\mathrm{Klein}}(D, M)^2 \;=\; I_2 \otimes (D^2 + m^2 \cdot I_{16}).$$ -/
theorem kl18_klein_dirac_mat32_square_and_gap_shield (D M : Mat16 K) (m : K) :
    (2 ^ 1 = 2 ∧ 2 ^ 4 = 16 ∧ 2 ^ 1 * 2 ^ 4 = 32 ∧ Fintype.card (Fin 2 × Fin 16) = 32) ∧
    (kleinDirac D M * kleinDirac D M =
      ((Mat2.I2 : Mat2 K) ⊗ₖ (D * D - M * M)) +
      ((Mat2.sigmaX : Mat2 K) ⊗ₖ (D * M - M * D))) ∧
    (D * M = M * D →
      kleinDirac D M * kleinDirac D M = (Mat2.I2 : Mat2 K) ⊗ₖ (D * D - M * M)) ∧
    (D * M = M * D → M * M = -((m ^ 2) • (I16 : Mat16 K)) →
      kleinDirac D M * kleinDirac D M =
        (Mat2.I2 : Mat2 K) ⊗ₖ (D * D + (m ^ 2) • (I16 : Mat16 K))) := by
  have hDim : 2 ^ 1 = 2 ∧ 2 ^ 4 = 16 ∧ 2 ^ 1 * 2 ^ 4 = 32 ∧ Fintype.card (Fin 2 × Fin 16) = 32 := by
    refine ⟨by norm_num, by norm_num, by norm_num, by decide⟩
  have h12 := (Mat2.kl12_dim1_one_flavor_isolated_mass_dichotomy (1 : K) 0).1
  have hZj : (Mat2.sigmaZ : Mat2 K) * Mat2.massJ = Mat2.sigmaX :=
    (Mat2.kl17_cl11_klein_four_group_adjoint_and_unorientable_holonomy (0 : Mat2 K)).1.1
  have hJz : (Mat2.massJ : Mat2 K) * Mat2.sigmaZ = -Mat2.sigmaX := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Mat2.massJ, Mat2.sigmaZ, Mat2.sigmaX]
  have hSq : kleinDirac D M * kleinDirac D M =
      ((Mat2.I2 : Mat2 K) ⊗ₖ (D * D - M * M)) +
      ((Mat2.sigmaX : Mat2 K) ⊗ₖ (D * M - M * D)) := by
    dsimp [kleinDirac]
    rw [mul_add, add_mul, add_mul,
        ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        h12.2.1, h12.2.2.2.1, hZj, hJz,
        kronecker_neg_left16, kronecker_neg_left16,
        ← kronecker_sub_right16, ← kronecker_sub_right16]
    abel
  have hComm : D * M = M * D →
      kleinDirac D M * kleinDirac D M = (Mat2.I2 : Mat2 K) ⊗ₖ (D * D - M * M) := by
    intro hDM
    rw [hSq, hDM, sub_self, kronecker_zero_right16, add_zero]
  have hGap : D * M = M * D → M * M = -((m ^ 2) • (I16 : Mat16 K)) →
      kleinDirac D M * kleinDirac D M =
        (Mat2.I2 : Mat2 K) ⊗ₖ (D * D + (m ^ 2) • (I16 : Mat16 K)) := by
    intro hDM hM2
    rw [hComm hDM, hM2, sub_neg_eq_add]
  exact ⟨hDim, hSq, hComm, hGap⟩

end Mat32

-- ============================================================================
-- SECTION 5: Master 7-Stage ABS Clifford & Klein-Bottle Synthesis (𝔎𝔏₁₂ ≺ ⋯ ≺ 𝔎𝔏₁₈)
-- ============================================================================

/-- **Master Theorem ($\mathfrak{KL}_{12} \prec \dots \prec \mathfrak{KL}_{18}$ — `kl18_master_abs_clifford_extension_and_klein_bottle_synthesis`):**
Unifies all seven stages of the Kitaev ABS Clifford extension, mass-rotation dichotomy, Class DIII
Kramers TRS elenchus, and the $\mathcal{C}\ell(1,1) \otimes \mathcal{C}\ell(4,4) \cong \mathrm{Mat}_{32}(K)$
noncommutative Klein-bottle twist:
1. Strict monotonicity & acyclicity of `KitaevABSCliffordExtensionStage` ($\mathfrak{KL}_{12} \prec \dots \prec \mathfrak{KL}_{18}$)
   alongside the AZ periodic table entries `azFullTable .D 1 = .Z2`, `azFullTable .D 2 = .Z`,
   `azFullTable .D 3 = .Zero`, `azFullTable .DIII 3 = .Z`, and `azFullTable .AIII 3 = .Z`,
2. $d = 1$ single-flavor isolated mass solutions $X^2 = -I_2 \iff X = \pm J$ ($\mathfrak{KL}_{12}$) vs.
   two-flavor continuous rotor $M(c, s)^2 = -(c^2 + s^2) I_4$ ($\mathfrak{KL}_{13}$),
3. $d = 2$ locked chiral mass uniqueness $X = X_{01} J$ in $\mathrm{Mat}_2(\mathbb{R})$ and
   2-flavor symmetric signature determinant $\det(J \otimes \mathrm{diag}(s_1, s_2)) = (s_1 s_2)^2$ ($\mathfrak{KL}_{14}$),
4. $d = 3$ Class D 2-mass plane completeness $X = \mathrm{massRotor}(X_{03}, X_{02})$ in $\mathrm{Mat}_4(\mathbb{R})$ ($\mathfrak{KL}_{15}$),
5. $d = 3$ Class DIII Kramers TRS mass blocking in $\mathrm{Mat}_4(\mathbb{R})$ and $8 \times 8$ elenchus resolution in $\mathrm{Mat}_8(K)$ ($\mathfrak{KL}_{16}$),
6. $\mathcal{C}\ell(1,1) \cong \mathrm{Mat}_2(K)$ projective Klein four-group $V_4 \cong \mathbb{Z}_2 \times \mathbb{Z}_2$
   ($\alpha_a \circ \alpha_b = \alpha_b \circ \alpha_a = \alpha_{ab}$) and unorientable holonomy $\det(\gamma_0) = -1$ ($\mathfrak{KL}_{17}$),
7. $\mathcal{A}_{\mathrm{Klein}} \cong \mathrm{Mat}_{32}(K)$ universal square law
   $\mathcal{D}_{\mathrm{Klein}}(D, M)^2 = I_2 \otimes (D^2 - M^2) + \sigma_x \otimes (D M - M D)$ ($\mathfrak{KL}_{18}$). -/
theorem kl18_master_abs_clifford_extension_and_klein_bottle_synthesis
    {K : Type u} [CommRing K] (c s s1 s2 : K) (X2 : Mat2 ℝ) (Y2 : Mat2 K)
    (X4 : Mat4 ℝ) (a b : ℝ) (D16 M16 : Mat16 K) :
    (Function.Injective KitaevABSCliffordExtensionStage.rank ∧
      (∀ st : KitaevABSCliffordExtensionStage, ¬ KitaevABSCliffordExtensionStage.coverEdge st st) ∧
      azFullTable AZClass.D 1 = TopologicalGroup.Z2 ∧
      azFullTable AZClass.D 2 = TopologicalGroup.Z ∧
      azFullTable AZClass.D 3 = TopologicalGroup.Zero ∧
      azFullTable AZClass.DIII 3 = TopologicalGroup.Z ∧
      azFullTable AZClass.AIII 3 = TopologicalGroup.Z) ∧
    (Mat4.massRotor c s * Mat4.massRotor c s = (- (c ^ 2 + s ^ 2)) • (Mat4.I4 : Mat4 K) ∧
      Matrix.det (Mat4.dim2SignatureMass s1 s2) = (s1 * s2) ^ 2) ∧
    ((Mat2.sigmaZ : Mat2 ℝ) * X2 + X2 * Mat2.sigmaZ = 0 →
      (Mat2.sigmaX : Mat2 ℝ) * X2 + X2 * Mat2.sigmaX = 0 →
      X2 = (X2 0 1) • (Mat2.massJ : Mat2 ℝ)) ∧
    ((Mat4.gamma1 : Mat4 ℝ) * X4 + X4 * Mat4.gamma1 = 0 →
      (Mat4.gamma2 : Mat4 ℝ) * X4 + X4 * Mat4.gamma2 = 0 →
      (Mat4.gamma3 : Mat4 ℝ) * X4 + X4 * Mat4.gamma3 = 0 →
      X4 = Mat4.massRotor (X4 0 3) (X4 0 2)) ∧
    ((Mat4.massRotor a b * (Mat4.massM2 : Mat4 ℝ) - Mat4.massM2 * Mat4.massRotor a b = 0 ↔ a = 0) ∧
      (Mat4.massRotor a b * (Mat4.massM2 : Mat4 ℝ) + Mat4.massM2 * Mat4.massRotor a b = 0 ↔ b = 0) ∧
      (Mat8.tildeGamma2 : Mat8Split K) * Mat8.rawCandidateJJJ8 -
        Mat8.rawCandidateJJJ8 * Mat8.tildeGamma2 = 0 ∧
      (Mat8.tildeGamma2 : Mat8Split K) * Mat8.kramersTRS8 +
        Mat8.kramersTRS8 * Mat8.tildeGamma2 = 0) ∧
    (Mat2.kleinAdjointA (Mat2.kleinAdjointB Y2) = Mat2.kleinAdjointAB Y2 ∧
      Mat2.kleinAdjointB (Mat2.kleinAdjointA Y2) = Mat2.kleinAdjointAB Y2 ∧
      Matrix.det (Mat2.sigmaZ : Mat2 K) = -1 ∧
      Mat32.kleinDirac D16 M16 * Mat32.kleinDirac D16 M16 =
        ((Mat2.I2 : Mat2 K) ⊗ₖ (D16 * D16 - M16 * M16)) +
        ((Mat2.sigmaX : Mat2 K) ⊗ₖ (D16 * M16 - M16 * D16))) := by
  have h13 := Mat4.kl13_dim1_two_flavor_mass_rotor_trivialization c s
  have h14_2 := Mat2.kl14_dim2_locked_chiral_mass_uniqueness (K := K) X2
  have h14_4 := Mat4.kl14_dim2_two_flavor_symmetric_signature_mass s1 s2
  have h15 := Mat4.kl15_dim3_classD_two_mass_plane_completeness_and_rotor c s X4
  have h16_4 := Mat4.kl16_dim3_classDIII_kramers_trs_mass_channel_blocking (K := K) a b
  have h16_8 := Mat8.kl16_dim3_mat8_elenchus_and_kramers_trs_lift (K := K)
  have h17 := Mat2.kl17_cl11_klein_four_group_adjoint_and_unorientable_holonomy Y2
  have h18 := Mat32.kl18_klein_dirac_mat32_square_and_gap_shield D16 M16 (0 : K)
  exact ⟨⟨KitaevABSCliffordExtensionStage.rank_injective,
          KitaevABSCliffordExtensionStage.coverEdge_acyclic,
          rfl, rfl, rfl, rfl, rfl⟩,
    ⟨h13.2.2.2.2.1, h14_4.2.2.2.2⟩,
    fun hZ hX => (h14_2.2 hZ hX).1,
    fun h1 h2 h3 => (h15.2.2.2 h1 h2 h3).1,
    ⟨h16_4.2.2.1, h16_4.2.2.2, h16_8.1.2.2.1, h16_8.2.1.2.2.2.1⟩,
    ⟨h17.2.1.2.2.2.1, h17.2.1.2.2.2.2, h17.2.2.1, h18.2.1⟩⟩

end InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset
