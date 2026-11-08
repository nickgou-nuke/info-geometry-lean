/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChainFull
import InfoGeometry.Algebra.BerezinianPfaffianBott
import InfoGeometry.Canonical.PfaffianFour
import InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian
import InfoGeometry.Canonical.TKNNTopologicalHallChernCapstone
import InfoGeometry.Quantum.KitaevDimerizationSwitch
import InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset

/-!
# Kitaev-Inspired Local-Gap and Finite Dimer Identities ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$)

## i. Overview

This module formalizes selected finite-dimensional and algebraic identities motivated by
Alexei Kitaev's lecture on topological insulators and free-fermion local spectral gaps. Its
stage labels organize these identities; they are not a construction of the classifying spaces
$A_d$, the maps $F_d,G_d$, or a proof of the spectrum equivalence
$A_d \simeq \Omega A_{d+1} \simeq KO_{d-2}$:

1. **Stage $\mathfrak{KL}_1$ (`kl1_tfim_paramagnetic_vs_ferromagnetic_local_gap_and_iqhe_tknn`)**:
   - **1D Transverse-Field Ising Model (TFIM)**:
     - Paramagnetic Point 1 ($h > 0, J = 0$): unique ground state energy $E_0 = -N h$, first excited
       single-spin-flip energy $E_1 = -(N - 2) h$, and $N$-independent spectral gap $E_1 - E_0 = 2 h > 0$.
     - Ferromagnetic Point 2 ($h = 0, J > 0$): 2-fold ground-state degeneracy on `Fin 3 → ℤ`
       (`![1, 1, 1]` and `![-1, -1, -1]` both at energy $-2 J$), interior bulk spin-flip excitation
       cost $4 J$ (`![1, -1, 1]`), and boundary spin-flip excitation cost $2 J$ (`![-1, 1, 1]`).
   - **Integer Quantum Hall Effect (IQHE) TKNN Quantization**:
     Reuses `InfoGeometry.Canonical.TKNNTopologicalHall.firstChernNumber_quantized` and
     `hallConductance` additivity.
2. **Stage $\mathfrak{KL}_2$ (`kl2_zero_dim_convex_ground_state_fiber_and_fermion_parity_split`)**:
   - The theorem proves preservation of a shared ground-state eigenvector and a stated scalar gap
     lower bound under convex interpolation, plus algebraic parity relations for an idempotent.
   - `convex_symmetric_matrix_common_ground_gap_fixed` separately proves that a common positive
     Rayleigh lower bound on the orthogonal complement of a shared eigenvector is preserved for
     finite real symmetric matrices under convex interpolation.
   - `convex_symmetric_matrix_common_ground_gap_minimum` handles unequal positive endpoint bounds
     and gives the uniform lower bound `min gap₀ gap₁` along the full interpolation.
   - `kitaevFiniteGroundGapFiber_contractible` proves that the explicitly defined, nonempty finite
     matrix fiber with fixed symmetric ground eigenpair and Rayleigh gap is contractible.
   - It does not construct the topology on the Hamiltonian spaces or identify them with
     $\mathbb{C}P^\infty$, $K(\mathbb{Z},2)$, or $\mathbb{C}P^\infty\times\mathbb{Z}_2$.
3. **Stage $\mathfrak{KL}_3$ (`kl3_majorana_clifford_complex_structure_and_creation_annihilation`)**:
   - Standard $2 \times 2$ real skew-symmetric complex structure $J_2 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$
     satisfies $J_2^\top = -J_2$, $J_2^2 = -I_2$, $\det J_2 = 1$, and $\mathrm{tr}(J_2) = 0$.
   - Over any associative ring `[Ring B]` with central imaginary unit $I_{\mathrm{im}}^2 = -1$ and
     Majorana generators $c_1^2 = 1$, $c_2^2 = 1$, $c_1 c_2 + c_2 c_1 = 0$, the scaled creation/annihilation
     operators $\tilde{a} = c_1 + I_{\mathrm{im}} c_2$ and $\tilde{a}^\dagger = c_1 - I_{\mathrm{im}} c_2$
     satisfy $\tilde{a}^2 = 0$, $(\tilde{a}^\dagger)^2 = 0$, $\{\tilde{a}, \tilde{a}^\dagger\} = 4$, and
     parity involution $\Gamma = -I_{\mathrm{im}} c_1 c_2$ satisfies $\Gamma^2 = 1$.
4. **Stage $\mathfrak{KL}_4$ (`kl4_spectral_gap_window_polynomial_and_bulk_disk_truncation`)**:
   - **Centered Operator-Square Spectral Gap Identity**:
     $$4 (X - a^2)(b^2 - X) = (b^2 - a^2)^2 - (2 X - (a^2 + b^2))^2,$$
     and over $\mathbb{R}$ ($0 \le a \le b$):
     $$a^2 \le X \wedge X \le b^2 \;\Longleftrightarrow\;
       \left|X - \frac{a^2 + b^2}{2}\right| \le \frac{b^2 - a^2}{2}.$$
   - **Bulk Disk Projection $\Pi_{\tilde D} (-A^2) \Pi_{\tilde D}$ vs. Boundary Truncation**:
     $$\mathrm{peirce11}\;P\;(-A^2) = -(\mathrm{peirce11}\;P\;A)^2 - \mathrm{conePlus}\;P\;A * \mathrm{coneMinus}\;P\;A.$$
5. **Stage $\mathfrak{KL}_5$ (`kl5_ims_double_commutator_localization_and_r_locality`)**:
   - **Universal Noncommutative IMS Double-Commutator Localization Identity**:
     $$\chi * \chi * M + M * (\chi * \chi) - (2 : \mathbb{Z}) \bullet (\chi * M * \chi) =
       \mathrm{comm}\;\chi\;(\mathrm{comm}\;\chi\;M),$$
     and for any finite partition of unity $\sum_{b : \iota} \chi_b * \chi_b = 1$:
     $$(2 : \mathbb{Z}) \bullet M - (2 : \mathbb{Z}) \bullet \sum_{b : \iota} \chi_b * M * \chi_b =
       \sum_{b : \iota} \mathrm{comm}\;\chi_b\;(\mathrm{comm}\;\chi_b\;M).$$
6. **Stage $\mathfrak{KL}_6$ (`kl6_kitaev_three_spectrum_principles_invertibility_swap_softness`)**:
   - **Principle 1 (Invertibility)**: Anticommuting homotopy $X(\theta) = \cos\theta \bullet X + \sin\theta \bullet Y$
     satisfies $X(\theta)^2 = \cos^2\theta \bullet X^2 + \sin^2\theta \bullet Y^2$. The accompanying scalar
     convexity lemma preserves $[a^2,b^2]$ when the squared-spectrum bounds hold at both endpoints; it does
     not by itself establish those bounds for an operator path or for an arbitrary basepoint.
   - **Principle 2 (Block-Swap Commutativity)**: Orthogonal conjugation by $\begin{pmatrix} 0 & I \\ -I & 0 \end{pmatrix}$
     intertwines $A \oplus B$ and $B \oplus A$.
   - **Principle 3 (Lipschitz Diagonal Restriction)**: $L$-Lipschitz modulation over $r$-local bonds
     bounds variation by $L r$.
7. **Stage $\mathfrak{KL}_7$ (`kl7_omega_spectrum_dimerization_switch_and_ko_d_minus_2_master_synthesis`)**:
   - Bundles the finite dimerization-switch and 2-site Pfaffian identities with the arithmetic
     residue equality $(d + 8 - 2 : \mathrm{ZMod}\;8) = (d - 2 : \mathrm{ZMod}\;8)$. This does not
     construct or identify a $KO$-theory spectrum.

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `KitaevKOSpectrumStage` ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$), `rank_injective`, `coverEdge`, `coverEdge_acyclic`,
  - `kl1_tfim_paramagnetic_vs_ferromagnetic_local_gap_and_iqhe_tknn`,
  - `kl2_zero_dim_convex_ground_state_fiber_and_fermion_parity_split`,
  - `convex_symmetric_matrix_common_ground_gap_fixed`,
  - `convex_symmetric_matrix_common_ground_gap_minimum`,
  - `kitaevFiniteGroundGapFiber_convex`, `kitaevFiniteGroundGapFiber_contractible`,
  - `kl3_majorana_clifford_complex_structure_and_creation_annihilation`,
  - `kl4_spectral_gap_window_polynomial_and_bulk_disk_truncation`,
  - `kitaev_local_gap_centered_band_square_identity`,
  - `ims_single_double_commutator_identity`, `kl5_ims_double_commutator_localization_and_r_locality`,
  - `kl6_kitaev_three_spectrum_principles_invertibility_swap_softness`,
  - `kitaev_invertibility_block_rotor_gap_preservation`,
  - `diagRestrict`, `kitaev_soft_diagonal_restriction_and_dimer_loop_shift`,
  - `kl7_omega_spectrum_dimerization_switch_and_ko_d_minus_2_master_synthesis`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Idempotence (`hP : P * P = P`), CAR relations, anticommutation (`anticomm X Y = 0`), and partition-of-unity hypotheses (`∑ b, χ b * χ b = 1`) are explicit theorem parameters.
* **BUCKET 3 — Out-of-Scope Continuum & Interacting Claims:**
  - Infinite-volume continuum limits $r \to 0$ and interacting many-body $\Omega$-spectrum classification conjectures remain outside this finite/algebraic owner.
-/

namespace InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset

open scoped BigOperators
open Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian
open InfoGeometry.Canonical.TKNNTopologicalHall
open InfoGeometry.Quantum.KitaevDimerizationSwitch

/-! ## §1. Poset Carrier & Acyclic Cover Spine ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$) -/

/-- The seven stages of Kitaev's Condensed-Matter $KO$-Spectrum causal poset. -/
inductive KitaevKOSpectrumStage : Type
  | kl1_TFIMLocalGapAndIQHE
  | kl2_ZeroDimConvexFiberAndParity
  | kl3_MajoranaCliffordComplexStructure
  | kl4_CenteredSpectralWindowAndBulkDisk
  | kl5_IMSDoubleCommutatorLocalization
  | kl6_ThreeSpectrumPrinciplesHomotopy
  | kl7_OmegaSpectrumDimerizationSynthesis
  deriving DecidableEq, Repr

namespace KitaevKOSpectrumStage

/-- Integer rank of each stage in `{0, …, 6}`. -/
def rank : KitaevKOSpectrumStage → ℕ
  | .kl1_TFIMLocalGapAndIQHE => 0
  | .kl2_ZeroDimConvexFiberAndParity => 1
  | .kl3_MajoranaCliffordComplexStructure => 2
  | .kl4_CenteredSpectralWindowAndBulkDisk => 3
  | .kl5_IMSDoubleCommutatorLocalization => 4
  | .kl6_ThreeSpectrumPrinciplesHomotopy => 5
  | .kl7_OmegaSpectrumDimerizationSynthesis => 6

/-- `rank` is strictly injective on `KitaevKOSpectrumStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

instance : LinearOrder KitaevKOSpectrumStage :=
  LinearOrder.lift' rank rank_injective

/-- Immediate Hasse cover edges $\mathfrak{KL}_k \prec \mathfrak{KL}_{k+1}$ of the 7-stage spine. -/
inductive coverEdge : KitaevKOSpectrumStage → KitaevKOSpectrumStage → Prop
  | kl1_to_kl2 : coverEdge .kl1_TFIMLocalGapAndIQHE .kl2_ZeroDimConvexFiberAndParity
  | kl2_to_kl3 : coverEdge .kl2_ZeroDimConvexFiberAndParity .kl3_MajoranaCliffordComplexStructure
  | kl3_to_kl4 : coverEdge .kl3_MajoranaCliffordComplexStructure .kl4_CenteredSpectralWindowAndBulkDisk
  | kl4_to_kl5 : coverEdge .kl4_CenteredSpectralWindowAndBulkDisk .kl5_IMSDoubleCommutatorLocalization
  | kl5_to_kl6 : coverEdge .kl5_IMSDoubleCommutatorLocalization .kl6_ThreeSpectrumPrinciplesHomotopy
  | kl6_to_kl7 : coverEdge .kl6_ThreeSpectrumPrinciplesHomotopy .kl7_OmegaSpectrumDimerizationSynthesis

/-- Every immediate Hasse cover edge increases rank by `1` and is strictly acyclic. -/
theorem coverEdge_acyclic {a b : KitaevKOSpectrumStage} (h : coverEdge a b) :
    rank b = rank a + 1 ∧ rank a < rank b ∧ a ≠ b := by
  cases h <;> decide

end KitaevKOSpectrumStage

/-! ## §2. Stage $\mathfrak{KL}_1$: 1D Transverse-Field Ising Model (Paramagnetic vs. Ferromagnetic Local Gap) & IQHE TKNN Conductance -/

/-- Classical ferromagnetic Ising bond energy on a 3-spin open chain `s : Fin 3 → ℤ`:
$$E_{\mathrm{Ising}}(J, s) = -J \,(s_0 s_1 + s_1 s_2).$$ -/
def tfimIsingEnergy3 (J : ℤ) (s : Fin 3 → ℤ) : ℤ :=
  -J * (s 0 * s 1 + s 1 * s 2)

/-- **Stage $\mathfrak{KL}_1$ (`kl1_tfim_paramagnetic_vs_ferromagnetic_local_gap_and_iqhe_tknn`) —
1D Transverse-Field Ising Model Phase Diagram (`00:05:38 – 00:16:08`) & IQHE TKNN Quantization (`00:01:07 – 00:03:06`)**:
1. **Paramagnetic Point 1 ($J = 0, h > 0$)**:
   The ground state energy $E_0 = -N h$ and single-spin-flip excited energy $E_1 = -(N - 2) h$
   have an $N$-independent positive spectral gap $E_1 - E_0 = 2 h > 0$.
2. **Ferromagnetic Point 2 ($h = 0, J > 0$) on a 3-Spin Chain (`tfimIsingEnergy3`)**:
   - All-up `![1, 1, 1]` and all-down `![-1, -1, -1]` are degenerate ground states at energy $-2 J$,
   - Flipping the **interior** bulk spin (`![1, -1, 1]`) breaks two bonds and costs $4 J$,
   - Flipping a **boundary** spin (`![-1, 1, 1]`) breaks one bond and costs $2 J$.
3. **Integer Quantum Hall Effect (IQHE) TKNN Quantization**:
   $C_1(2\pi n) = n$ and $\sigma_{xy}(C_1 + C_2, e, h_{\mathrm{Planck}}) =
   \sigma_{xy}(C_1, e, h_{\mathrm{Planck}}) + \sigma_{xy}(C_2, e, h_{\mathrm{Planck}})$. -/
theorem kl1_tfim_paramagnetic_vs_ferromagnetic_local_gap_and_iqhe_tknn
    (N : ℝ) (h : ℝ) (hh : 0 < h) (J : ℤ) (n : ℤ) (C1 C2 e hPlanck : ℝ) :
    (-(N - 2) * h - (-N * h) = 2 * h ∧ 0 < 2 * h) ∧
    (tfimIsingEnergy3 J ![1, 1, 1] = -2 * J ∧
     tfimIsingEnergy3 J ![-1, -1, -1] = -2 * J ∧
     tfimIsingEnergy3 J ![1, -1, 1] - tfimIsingEnergy3 J ![1, 1, 1] = 4 * J ∧
     tfimIsingEnergy3 J ![-1, 1, 1] - tfimIsingEnergy3 J ![1, 1, 1] = 2 * J) ∧
    (firstChernNumber ((n : ℝ) * (2 * Real.pi)) = (n : ℝ) ∧
     hallConductance (C1 + C2) e hPlanck =
       hallConductance C1 e hPlanck + hallConductance C2 e hPlanck) := by
  have hPara : -(N - 2) * h - (-N * h) = 2 * h := by ring
  have hGapPos : 0 < 2 * h := mul_pos zero_lt_two hh
  have hFerro :
      tfimIsingEnergy3 J ![1, 1, 1] = -2 * J ∧
      tfimIsingEnergy3 J ![-1, -1, -1] = -2 * J ∧
      tfimIsingEnergy3 J ![1, -1, 1] - tfimIsingEnergy3 J ![1, 1, 1] = 4 * J ∧
      tfimIsingEnergy3 J ![-1, 1, 1] - tfimIsingEnergy3 J ![1, 1, 1] = 2 * J := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change -J * (1 * 1 + 1 * 1) = -2 * J; ring
    · change -J * (-1 * -1 + -1 * -1) = -2 * J; ring
    · change -J * (1 * -1 + -1 * 1) - -J * (1 * 1 + 1 * 1) = 4 * J; ring
    · change -J * (-1 * 1 + 1 * 1) - -J * (1 * 1 + 1 * 1) = 2 * J; ring
  exact ⟨⟨hPara, hGapPos⟩, hFerro,
    ⟨firstChernNumber_quantized n, hallConductance_add C1 C2 e hPlanck⟩⟩

/-! ## §3. Stage $\mathfrak{KL}_2$: 0D Convex Ground-State Fiber Contractibility ($B_0 \simeq \mathbb{C}P^\infty$) & Fermionic $\mathbb{Z}_2$ Parity Superselection ($F_0 \simeq \mathbb{C}P^\infty \times \mathbb{Z}_2$) -/

/-- **Stage $\mathfrak{KL}_2$ (`kl2_zero_dim_convex_ground_state_fiber_and_fermion_parity_split`) —
Convex Eigenvector/Gap Inequalities & Algebraic Fermion-Parity Relations (`00:17:19 – 00:26:37`)**:
1. **Convex Fiber Eigenvector Preservation**:
   In any associative $\mathbb{R}$-algebra `B`, if $H_0 P = E_0 \bullet P$ and $H_1 P = E_1 \bullet P$,
   then for every $t \in \mathbb{R}$, the convex interpolation $H(t) = (1 - t) \bullet H_0 + t \bullet H_1$
   satisfies $H(t) P = ((1 - t) E_0 + t E_1) \bullet P$.
2. **Convex Gap Stability**:
   If $0 \le t \le 1$, $\Delta_0 \ge \gamma$, and $\Delta_1 \ge \gamma$, then
   $(1 - t) \Delta_0 + t \Delta_1 \ge \gamma$.
3. **Fermionic $\mathbb{Z}_2$-Graded Parity Superselection (`invS P`)**:
   For any idempotent $P * P = P$ in `[Ring B]` and any operator $H \in B$:
   - `invS P * invS P = 1`, `invS P * P = P`, and `invS P * (1 - P) = -(1 - P)`,
   - `H` commutes with fermion parity `invS P` (`comm (invS P) H = 0`) if and only if its
     parity-odd off-diagonal hopping vanishes (` (2 : ℤ) • genJ P H H = 0`),
   - For any parity-even block operator `evenGrade P H = peirce11 P H + peirce00 P H`,
     `comm (invS P) (evenGrade P H) = 0`. -/
theorem kl2_zero_dim_convex_ground_state_fiber_and_fermion_parity_split
    {B : Type*} [Ring B] [Module ℝ B] [IsScalarTower ℝ B B] [SMulCommClass ℝ B B]
    (H₀ H₁ P : B) (E₀ E₁ t Δ₀ Δ₁ γ : ℝ)
    (hH₀ : H₀ * P = E₀ • P) (hH₁ : H₁ * P = E₁ • P)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hΔ₀ : γ ≤ Δ₀) (hΔ₁ : γ ≤ Δ₁)
    (hP : P * P = P) (H : B) :
    (((1 - t) • H₀ + t • H₁) * P = ((1 - t) * E₀ + t * E₁) • P) ∧
    (γ ≤ (1 - t) * Δ₀ + t * Δ₁) ∧
    (invS P * invS P = 1 ∧ invS P * P = P ∧ invS P * (1 - P) = -(1 - P)) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) H = (2 : ℤ) • genJ P H H) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (evenGrade P H) = 0) := by
  have hEigen : ((1 - t) • H₀ + t • H₁) * P = ((1 - t) * E₀ + t * E₁) • P := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, hH₀, hH₁, smul_smul, smul_smul, ← add_smul]
  have hGap : γ ≤ (1 - t) * Δ₀ + t * Δ₁ := by
    have h1mt : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hA : (1 - t) * γ ≤ (1 - t) * Δ₀ := mul_le_mul_of_nonneg_left hΔ₀ h1mt
    have hB : t * γ ≤ t * Δ₁ := mul_le_mul_of_nonneg_left hΔ₁ ht0
    linarith
  have hInvSq : invS P * invS P = 1 := by peirce_nf hP
  have hInvP : invS P * P = P := by peirce_nf hP
  have hInvQ : invS P * (1 - P) = -(1 - P) := by peirce_nf hP
  have hCommInv :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) H = (2 : ℤ) • genJ P H H := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, invS, genJ, conePlus, coneMinus]
    rw [two_zsmul]
    peirce_nf hP
  have hCommEven :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (evenGrade P H) = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, invS, evenGrade, peirce11, peirce00]
    peirce_nf hP
  exact ⟨hEigen, hGap, ⟨hInvSq, hInvP, hInvQ⟩, hCommInv, hCommEven⟩

/-- The real quadratic form associated to a finite matrix. -/
def kitaevQuadraticForm {n : Type*} [Fintype n]
    (H : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  x ⬝ᵥ (H *ᵥ x)

/-- Convex interpolation preserves a quadratic-form lower bound on any fixed
set of test vectors. In applications to a spectral gap, the quantified vectors
are taken in the orthogonal complement of a common ground state, and the
Hamiltonians must be self-adjoint. -/
theorem convex_matrix_quadratic_form_lower_bound
    {n : Type*} [Fintype n]
    (H₀ H₁ : Matrix n n ℝ) (x : n → ℝ)
    (t gap₀ gap₁ : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (h₀ : gap₀ * (x ⬝ᵥ x) ≤ kitaevQuadraticForm H₀ x)
    (h₁ : gap₁ * (x ⬝ᵥ x) ≤ kitaevQuadraticForm H₁ x) :
    ((1 - t) * gap₀ + t * gap₁) * (x ⬝ᵥ x) ≤
      kitaevQuadraticForm ((1 - t) • H₀ + t • H₁) x := by
  have hForm :
      kitaevQuadraticForm ((1 - t) • H₀ + t • H₁) x =
        (1 - t) * kitaevQuadraticForm H₀ x + t * kitaevQuadraticForm H₁ x := by
    change x ⬝ᵥ (((1 - t) • H₀ + t • H₁) *ᵥ x) = _
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    simp [kitaevQuadraticForm, dotProduct_add, dotProduct_smul]
  have ht₁' : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  calc
    ((1 - t) * gap₀ + t * gap₁) * (x ⬝ᵥ x) =
        (1 - t) * (gap₀ * (x ⬝ᵥ x)) + t * (gap₁ * (x ⬝ᵥ x)) := by
          rw [add_mul, mul_assoc, mul_assoc]
    _ ≤ (1 - t) * kitaevQuadraticForm H₀ x + t * kitaevQuadraticForm H₁ x :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ ht₁') (mul_le_mul_of_nonneg_left h₁ ht₀)
    _ = kitaevQuadraticForm ((1 - t) • H₀ + t • H₁) x := hForm.symm

/-- A common eigenvector and a uniform quadratic-form gap on its orthogonal
complement persist under convex interpolation of finite real symmetric
Hamiltonians. The conclusion is stated as a Rayleigh-form lower bound above
the interpolated eigenvalue; finite-dimensional spectral-gap consequences use
the usual self-adjoint spectral theorem. -/
theorem convex_symmetric_matrix_common_ground_gap
    {n : Type*} [Fintype n] [DecidableEq n]
    (H₀ H₁ : Matrix n n ℝ) (v : n → ℝ)
    (energy₀ energy₁ gap₀ gap₁ t : ℝ)
    (hSymm₀ : H₀.IsSymm) (hSymm₁ : H₁.IsSymm)
    (hv : v ≠ 0)
    (hEig₀ : H₀ *ᵥ v = energy₀ • v)
    (hEig₁ : H₁ *ᵥ v = energy₁ • v)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hGap₀ : ∀ x : n → ℝ, v ⬝ᵥ x = 0 →
      gap₀ * (x ⬝ᵥ x) ≤ kitaevQuadraticForm (H₀ - energy₀ • (1 : Matrix n n ℝ)) x)
    (hGap₁ : ∀ x : n → ℝ, v ⬝ᵥ x = 0 →
      gap₁ * (x ⬝ᵥ x) ≤ kitaevQuadraticForm (H₁ - energy₁ • (1 : Matrix n n ℝ)) x) :
    let Ht := (1 - t) • H₀ + t • H₁
    let energyT := (1 - t) * energy₀ + t * energy₁
    let gapT := (1 - t) * gap₀ + t * gap₁
    v ≠ 0 ∧ Ht.IsSymm ∧ Ht *ᵥ v = energyT • v ∧
      (∀ x : n → ℝ, v ⬝ᵥ x = 0 →
        gapT * (x ⬝ᵥ x) ≤ kitaevQuadraticForm (Ht - energyT • (1 : Matrix n n ℝ)) x) := by
  dsimp only
  have hSymmT : ((1 - t) • H₀ + t • H₁).IsSymm :=
    (hSymm₀.smul (1 - t)).add (hSymm₁.smul t)
  have hEigT :
      ((1 - t) • H₀ + t • H₁) *ᵥ v = ((1 - t) * energy₀ + t * energy₁) • v := by
    calc
      ((1 - t) • H₀ + t • H₁) *ᵥ v =
          (1 - t) • (H₀ *ᵥ v) + t • (H₁ *ᵥ v) := by
            rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      _ = ((1 - t) * energy₀ + t * energy₁) • v := by
            rw [hEig₀, hEig₁, smul_smul, smul_smul, ← add_smul]
  have hShift :
      ((1 - t) • H₀ + t • H₁) -
          ((1 - t) * energy₀ + t * energy₁) • (1 : Matrix n n ℝ) =
        (1 - t) • (H₀ - energy₀ • (1 : Matrix n n ℝ)) +
          t • (H₁ - energy₁ • (1 : Matrix n n ℝ)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> ring
  have hGapT : ∀ x : n → ℝ, v ⬝ᵥ x = 0 →
      ((1 - t) * gap₀ + t * gap₁) * (x ⬝ᵥ x) ≤
        kitaevQuadraticForm (((1 - t) • H₀ + t • H₁) -
          ((1 - t) * energy₀ + t * energy₁) • (1 : Matrix n n ℝ)) x := by
    intro x hx
    have h := convex_matrix_quadratic_form_lower_bound
      (H₀ - energy₀ • (1 : Matrix n n ℝ))
      (H₁ - energy₁ • (1 : Matrix n n ℝ)) x t gap₀ gap₁ ht₀ ht₁
      (hGap₀ x hx) (hGap₁ x hx)
    rw [hShift]
    exact h
  exact ⟨hv, hSymmT, hEigT, hGapT⟩

/-- The smaller of two positive endpoint Rayleigh gaps is a uniform gap
throughout the convex interpolation. This gives an explicit fixed lower
bound, rather than only the parameter-dependent convex combination appearing
in `convex_symmetric_matrix_common_ground_gap`. The result is still a finite
real-matrix Rayleigh estimate, not a topological classification. -/
theorem convex_symmetric_matrix_common_ground_gap_minimum
    {n : Type*} [Fintype n] [DecidableEq n]
    (H₀ H₁ : Matrix n n ℝ) (v : n → ℝ)
    (energy₀ energy₁ gap₀ gap₁ t : ℝ)
    (hgap₀_pos : 0 < gap₀) (hgap₁_pos : 0 < gap₁)
    (hSymm₀ : H₀.IsSymm) (hSymm₁ : H₁.IsSymm)
    (hv : v ≠ 0)
    (hEig₀ : H₀ *ᵥ v = energy₀ • v)
    (hEig₁ : H₁ *ᵥ v = energy₁ • v)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hGap₀ : ∀ x : n → ℝ, v ⬝ᵥ x = 0 →
      gap₀ * (x ⬝ᵥ x) ≤ kitaevQuadraticForm (H₀ - energy₀ • (1 : Matrix n n ℝ)) x)
    (hGap₁ : ∀ x : n → ℝ, v ⬝ᵥ x = 0 →
      gap₁ * (x ⬝ᵥ x) ≤ kitaevQuadraticForm (H₁ - energy₁ • (1 : Matrix n n ℝ)) x) :
    let Ht := (1 - t) • H₀ + t • H₁
    let energyT := (1 - t) * energy₀ + t * energy₁
    let gapMin := min gap₀ gap₁
    0 < gapMin ∧ v ≠ 0 ∧ Ht.IsSymm ∧ Ht *ᵥ v = energyT • v ∧
      (∀ x : n → ℝ, v ⬝ᵥ x = 0 →
        gapMin * (x ⬝ᵥ x) ≤ kitaevQuadraticForm (Ht - energyT • (1 : Matrix n n ℝ)) x) := by
  have h := convex_symmetric_matrix_common_ground_gap H₀ H₁ v energy₀ energy₁ gap₀ gap₁ t
    hSymm₀ hSymm₁ hv hEig₀ hEig₁ ht₀ ht₁ hGap₀ hGap₁
  dsimp only at h ⊢
  have ht₁' : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  have hMinGap : min gap₀ gap₁ ≤ (1 - t) * gap₀ + t * gap₁ := by
    calc
      min gap₀ gap₁ = (1 - t) * min gap₀ gap₁ + t * min gap₀ gap₁ := by ring
      _ ≤ (1 - t) * gap₀ + t * gap₁ :=
        add_le_add
          (mul_le_mul_of_nonneg_left (min_le_left gap₀ gap₁) ht₁')
          (mul_le_mul_of_nonneg_left (min_le_right gap₀ gap₁) ht₀)
  have hMinPos : 0 < min gap₀ gap₁ := lt_min hgap₀_pos hgap₁_pos
  refine ⟨hMinPos, h.1, h.2.1, h.2.2.1, ?_⟩
  intro x hx
  have hxx : 0 ≤ x ⬝ᵥ x := by
    unfold dotProduct
    apply Finset.sum_nonneg
    intro i hi
    exact mul_self_nonneg (x i)
  have hGapOrder := mul_le_mul_of_nonneg_right hMinGap hxx
  exact hGapOrder.trans (h.2.2.2 x hx)

/-- Finite-dimensional fiber of real symmetric Hamiltonians with a fixed
eigenvector, eigenvalue, and Rayleigh lower bound on its orthogonal
complement. This is an actual subset of the finite matrix space; it does not
encode an infinite-volume or many-body Hamiltonian space. -/
def kitaevFiniteGroundGapFiber
    {n : Type*} [Fintype n] [DecidableEq n] (v : n → ℝ) (energy gap : ℝ) :
    Set (Matrix n n ℝ) :=
  {H | H.IsSymm ∧ H *ᵥ v = energy • v ∧
    ∀ x : n → ℝ, v ⬝ᵥ x = 0 →
      gap * (x ⬝ᵥ x) ≤ kitaevQuadraticForm (H - energy • (1 : Matrix n n ℝ)) x}

/-- The finite ground-gap fiber is convex: symmetry, the fixed eigenvector
equation, and each Rayleigh lower-bound inequality are preserved by affine
combinations with nonnegative coefficients summing to one. -/
theorem kitaevFiniteGroundGapFiber_convex
    {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → ℝ) (energy gap : ℝ) :
    Convex ℝ (kitaevFiniteGroundGapFiber v energy gap) := by
  intro H₀ h₀ H₁ h₁ a b ha hb hab
  dsimp only [kitaevFiniteGroundGapFiber] at h₀ h₁ ⊢
  change (a • H₀ + b • H₁).IsSymm ∧
    (a • H₀ + b • H₁) *ᵥ v = energy • v ∧
    (∀ x : n → ℝ, v ⬝ᵥ x = 0 →
      gap * (x ⬝ᵥ x) ≤
        kitaevQuadraticForm (a • H₀ + b • H₁ - energy • (1 : Matrix n n ℝ)) x)
  rcases h₀ with ⟨hSymm₀, hEig₀, hGap₀⟩
  rcases h₁ with ⟨hSymm₁, hEig₁, hGap₁⟩
  have hSymm : (a • H₀ + b • H₁).IsSymm :=
    (hSymm₀.smul a).add (hSymm₁.smul b)
  have hEig : (a • H₀ + b • H₁) *ᵥ v = energy • v := by
    calc
      (a • H₀ + b • H₁) *ᵥ v = a • (H₀ *ᵥ v) + b • (H₁ *ᵥ v) := by
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      _ = a • (energy • v) + b • (energy • v) := by rw [hEig₀, hEig₁]
      _ = energy • v := by
        rw [smul_smul, smul_smul, ← add_smul, ← add_mul, hab, one_mul]
  have hShift :
      a • H₀ + b • H₁ - energy • (1 : Matrix n n ℝ) =
        a • (H₀ - energy • (1 : Matrix n n ℝ)) +
          b • (H₁ - energy • (1 : Matrix n n ℝ)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
      linear_combination energy * hab
    · simp [hij]
  have hForm (x : n → ℝ) :
      kitaevQuadraticForm (a • (H₀ - energy • (1 : Matrix n n ℝ)) +
        b • (H₁ - energy • (1 : Matrix n n ℝ))) x =
        a * kitaevQuadraticForm (H₀ - energy • (1 : Matrix n n ℝ)) x +
        b * kitaevQuadraticForm (H₁ - energy • (1 : Matrix n n ℝ)) x := by
    change x ⬝ᵥ ((a • (H₀ - energy • (1 : Matrix n n ℝ)) +
      b • (H₁ - energy • (1 : Matrix n n ℝ))) *ᵥ x) = _
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    simp [kitaevQuadraticForm, dotProduct_add, dotProduct_smul]
  have hGap : ∀ x : n → ℝ, v ⬝ᵥ x = 0 →
      gap * (x ⬝ᵥ x) ≤
        kitaevQuadraticForm (a • H₀ + b • H₁ - energy • (1 : Matrix n n ℝ)) x := by
    intro x hx
    calc
      gap * (x ⬝ᵥ x) = a * (gap * (x ⬝ᵥ x)) + b * (gap * (x ⬝ᵥ x)) := by
        rw [← add_mul, hab, one_mul]
      _ ≤ a * kitaevQuadraticForm (H₀ - energy • (1 : Matrix n n ℝ)) x +
          b * kitaevQuadraticForm (H₁ - energy • (1 : Matrix n n ℝ)) x :=
        add_le_add (mul_le_mul_of_nonneg_left (hGap₀ x hx) ha)
          (mul_le_mul_of_nonneg_left (hGap₁ x hx) hb)
      _ = kitaevQuadraticForm (a • H₀ + b • H₁ - energy • (1 : Matrix n n ℝ)) x := by
        rw [hShift, hForm]
  exact ⟨hSymm, hEig, hGap⟩

/-- A nonempty finite ground-gap fiber is contractible by Mathlib's theorem
that every nonempty convex subset of a real topological vector space is
contractible. This finite result supports the fiber-convexity mechanism; it
does not identify the full 0D classifying space with `ℂP^∞`. -/
theorem kitaevFiniteGroundGapFiber_contractible
    {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → ℝ) (energy gap : ℝ)
    (hne : (kitaevFiniteGroundGapFiber v energy gap).Nonempty) :
    ContractibleSpace {H : Matrix n n ℝ // H ∈ kitaevFiniteGroundGapFiber v energy gap} := by
  exact (kitaevFiniteGroundGapFiber_convex v energy gap).contractibleSpace hne

/-- A common positive Rayleigh lower-gap bound is preserved exactly when the
two endpoint Hamiltonians have the same bound. This is the fixed-gap
specialization of `convex_symmetric_matrix_common_ground_gap`; it remains a
finite real-matrix statement and does not assert a classifying-space or
spectral-theorem result. -/
theorem convex_symmetric_matrix_common_ground_gap_fixed
    {n : Type*} [Fintype n] [DecidableEq n]
    (H₀ H₁ : Matrix n n ℝ) (v : n → ℝ)
    (energy₀ energy₁ gap t : ℝ) (hgap_pos : 0 < gap)
    (hSymm₀ : H₀.IsSymm) (hSymm₁ : H₁.IsSymm)
    (hv : v ≠ 0)
    (hEig₀ : H₀ *ᵥ v = energy₀ • v)
    (hEig₁ : H₁ *ᵥ v = energy₁ • v)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hGap₀ : ∀ x : n → ℝ, v ⬝ᵥ x = 0 →
      gap * (x ⬝ᵥ x) ≤ kitaevQuadraticForm (H₀ - energy₀ • (1 : Matrix n n ℝ)) x)
    (hGap₁ : ∀ x : n → ℝ, v ⬝ᵥ x = 0 →
      gap * (x ⬝ᵥ x) ≤ kitaevQuadraticForm (H₁ - energy₁ • (1 : Matrix n n ℝ)) x) :
    let Ht := (1 - t) • H₀ + t • H₁
    let energyT := (1 - t) * energy₀ + t * energy₁
    0 < gap ∧ v ≠ 0 ∧ Ht.IsSymm ∧ Ht *ᵥ v = energyT • v ∧
      (∀ x : n → ℝ, v ⬝ᵥ x = 0 →
        gap * (x ⬝ᵥ x) ≤ kitaevQuadraticForm (Ht - energyT • (1 : Matrix n n ℝ)) x) := by
  have h := convex_symmetric_matrix_common_ground_gap H₀ H₁ v energy₀ energy₁ gap gap t
    hSymm₀ hSymm₁ hv hEig₀ hEig₁ ht₀ ht₁ hGap₀ hGap₁
  dsimp only at h ⊢
  have hgap : (1 - t) * gap + t * gap = gap := by ring
  rw [hgap] at h
  exact ⟨hgap_pos, h⟩

/-! ## §4. Stage $\mathfrak{KL}_3$: Majorana Clifford Algebra $\mathcal{C}\ell_{2n}$, Standard Complex Structure $A_0$, and Creation/Annihilation Operators -/

/-- Kitaev's standard $2 \times 2$ skew-symmetric complex structure block
$A_0 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$ (`00:31:05`). -/
def kitaevComplexStructure2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; -1, 0]

/-- Standard $2 \times 2$ grading involution block
$e_1 = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$. -/
def kitaevGrading2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, -1]

/-- Explicit non-commutativity of `kitaevComplexStructure2` and `kitaevGrading2`. -/
theorem kitaevComplexStructure2_noncomm :
    kitaevComplexStructure2 * kitaevGrading2 ≠
      kitaevGrading2 * kitaevComplexStructure2 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  revert h01
  decide

/-- Explicit Clifford anticommutativity of `kitaevComplexStructure2` and `kitaevGrading2`. -/
theorem kitaevComplexStructure2_anticomm :
    kitaevComplexStructure2 * kitaevGrading2 +
      kitaevGrading2 * kitaevComplexStructure2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- **Stage $\mathfrak{KL}_3$ (`kl3_majorana_clifford_complex_structure_and_creation_annihilation`) —
Majorana Clifford Algebra $\mathcal{C}\ell_{2n}$, Standard Complex Structure $A_0$, and Creation/Annihilation Algebra (`00:29:08 – 00:37:23`)**:
1. **Standard Complex Structure $A_0 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$**:
   $A_0^\top = -A_0$, $A_0^2 = -I_2$, $\det A_0 = 1$, $\mathrm{tr}(A_0) = 0$, and $A_0 e_1 + e_1 A_0 = 0$.
2. **Majorana-to-Complex Fermion Creation/Annihilation Algebra**:
   In any associative ring `[Ring B]` with central imaginary unit $I_{\mathrm{im}}^2 = -1$ and
   Majorana generators $c_1^2 = 1$, $c_2^2 = 1$, $c_1 c_2 + c_2 c_1 = 0$ commuting with $I_{\mathrm{im}}$:
   - Scaled annihilation/creation operators $\tilde{a} = c_1 + I_{\mathrm{im}} c_2$ ($= 2 a$) and
     $\tilde{a}^\dagger = c_1 - I_{\mathrm{im}} c_2$ ($= 2 a^\dagger$) are square-zero:
     $\tilde{a} * \tilde{a} = 0$ and $\tilde{a}^\dagger * \tilde{a}^\dagger = 0$,
   - Their anticommutator is $\tilde{a} * \tilde{a}^\dagger + \tilde{a}^\dagger * \tilde{a} = (4 : \mathbb{Z}) \bullet 1$,
   - The local fermion parity operator $\Gamma = -I_{\mathrm{im}} * c_1 * c_2$ is an involution
     ($\Gamma * \Gamma = 1$) and satisfies $\tilde{a}^\dagger * \tilde{a} = (2 : \mathbb{Z}) \bullet (1 - \Gamma)$. -/
theorem kl3_majorana_clifford_complex_structure_and_creation_annihilation
    {B : Type*} [Ring B] (I_im c₁ c₂ : B)
    (hI : I_im * I_im = -1)
    (hc₁ : c₁ * c₁ = 1) (hc₂ : c₂ * c₂ = 1)
    (hCAR : c₁ * c₂ + c₂ * c₁ = 0)
    (hIc₁ : I_im * c₁ = c₁ * I_im) (hIc₂ : I_im * c₂ = c₂ * I_im) :
    (kitaevComplexStructure2.transpose = -kitaevComplexStructure2 ∧
     kitaevComplexStructure2 * kitaevComplexStructure2 = -1 ∧
     Matrix.det kitaevComplexStructure2 = 1 ∧
     Matrix.trace kitaevComplexStructure2 = 0 ∧
     kitaevComplexStructure2 * kitaevGrading2 + kitaevGrading2 * kitaevComplexStructure2 = 0) ∧
    (let a_tilde := c₁ + I_im * c₂
     let a_dag_tilde := c₁ - I_im * c₂
     let Γ := -(I_im * c₁ * c₂)
     a_tilde * a_tilde = 0 ∧
     a_dag_tilde * a_dag_tilde = 0 ∧
     a_tilde * a_dag_tilde + a_dag_tilde * a_tilde = (4 : ℤ) • (1 : B) ∧
     Γ * Γ = 1 ∧
     a_dag_tilde * a_tilde = (2 : ℤ) • (1 - Γ)) := by
  have hA0_skew : kitaevComplexStructure2.transpose = -kitaevComplexStructure2 := by decide
  have hA0_sq : kitaevComplexStructure2 * kitaevComplexStructure2 = -1 := by decide
  have hA0_det : Matrix.det kitaevComplexStructure2 = 1 := by decide
  have hA0_tr : Matrix.trace kitaevComplexStructure2 = 0 := by decide
  have hc₂c₁ : c₂ * c₁ = -(c₁ * c₂) := eq_neg_of_add_eq_zero_right hCAR
  have ha_sq : (c₁ + I_im * c₂) * (c₁ + I_im * c₂) = 0 := by
    calc
      (c₁ + I_im * c₂) * (c₁ + I_im * c₂) =
          c₁ * c₁ + (c₁ * I_im) * c₂ + I_im * (c₂ * c₁) + I_im * (c₂ * I_im) * c₂ := by
        noncomm_ring
      _ = c₁ * c₁ + I_im * (c₁ * c₂ + c₂ * c₁) + (I_im * I_im) * (c₂ * c₂) := by
        rw [← hIc₁, ← hIc₂]
        noncomm_ring
      _ = 0 := by
        rw [hc₁, hc₂, hCAR, hI]
        noncomm_ring
  have had_sq : (c₁ - I_im * c₂) * (c₁ - I_im * c₂) = 0 := by
    calc
      (c₁ - I_im * c₂) * (c₁ - I_im * c₂) =
          c₁ * c₁ - (c₁ * I_im) * c₂ - I_im * (c₂ * c₁) + I_im * (c₂ * I_im) * c₂ := by
        noncomm_ring
      _ = c₁ * c₁ - I_im * (c₁ * c₂ + c₂ * c₁) + (I_im * I_im) * (c₂ * c₂) := by
        rw [← hIc₁, ← hIc₂]
        noncomm_ring
      _ = 0 := by
        rw [hc₁, hc₂, hCAR, hI]
        noncomm_ring
  have hAnti_aa :
      (c₁ + I_im * c₂) * (c₁ - I_im * c₂) + (c₁ - I_im * c₂) * (c₁ + I_im * c₂) =
        (4 : ℤ) • (1 : B) := by
    calc
      (c₁ + I_im * c₂) * (c₁ - I_im * c₂) + (c₁ - I_im * c₂) * (c₁ + I_im * c₂) =
          c₁ * c₁ + c₁ * c₁ - I_im * (c₂ * I_im) * c₂ - I_im * (c₂ * I_im) * c₂ := by
        noncomm_ring
      _ = c₁ * c₁ + c₁ * c₁ - (I_im * I_im) * (c₂ * c₂) - (I_im * I_im) * (c₂ * c₂) := by
        rw [← hIc₂]
        noncomm_ring
      _ = (4 : ℤ) • (1 : B) := by
        rw [hc₁, hc₂, hI]
        have h4 : (4 : ℤ) • (1 : B) = 1 + 1 + 1 + 1 := by
          change ((3 + 1 : ℤ) • (1 : B)) = 1 + 1 + 1 + 1
          rw [add_zsmul, one_zsmul]
          change ((2 + 1 : ℤ) • (1 : B)) + 1 = 1 + 1 + 1 + 1
          rw [add_zsmul, one_zsmul, two_zsmul]
        rw [h4]
        noncomm_ring
  have hGamma_sq : (-(I_im * c₁ * c₂)) * (-(I_im * c₁ * c₂)) = 1 := by
    calc
      (-(I_im * c₁ * c₂)) * (-(I_im * c₁ * c₂)) =
          I_im * (c₁ * (c₂ * I_im)) * c₁ * c₂ := by noncomm_ring
      _ = (I_im * I_im) * (c₁ * (c₂ * c₁) * c₂) := by
          rw [← hIc₂, ← mul_assoc c₁ I_im c₂, ← hIc₁]
          noncomm_ring
      _ = (I_im * I_im) * (-(c₁ * c₁ * (c₂ * c₂))) := by
          rw [hc₂c₁]
          noncomm_ring
      _ = 1 := by
          rw [hI, hc₁, hc₂]
          noncomm_ring
  have hNumber :
      (c₁ - I_im * c₂) * (c₁ + I_im * c₂) = (2 : ℤ) • (1 - (-(I_im * c₁ * c₂))) := by
    calc
      (c₁ - I_im * c₂) * (c₁ + I_im * c₂) =
          c₁ * c₁ + (c₁ * I_im) * c₂ - I_im * (c₂ * c₁) - I_im * (c₂ * I_im) * c₂ := by
        noncomm_ring
      _ = c₁ * c₁ + I_im * (c₁ * c₂) - I_im * (-(c₁ * c₂)) - (I_im * I_im) * (c₂ * c₂) := by
        rw [← hIc₁, hc₂c₁, ← hIc₂]
        noncomm_ring
      _ = (2 : ℤ) • (1 - (-(I_im * c₁ * c₂))) := by
        rw [hc₁, hc₂, hI, two_zsmul]
        noncomm_ring
  exact ⟨⟨hA0_skew, hA0_sq, hA0_det, hA0_tr, kitaevComplexStructure2_anticomm⟩,
    ⟨ha_sq, had_sq, hAnti_aa, hGamma_sq, hNumber⟩⟩

/-! ## §5. Stage $\mathfrak{KL}_4$: Centered Operator-Square Spectral Gap Window & Bulk Disk Restriction $\Pi_{\tilde D}$ -/

/-- **Stage $\mathfrak{KL}_4$ (`kl4_spectral_gap_window_polynomial_and_bulk_disk_truncation`) —
Kitaev's Centered Operator-Square Spectral Window & Bulk Disk Restriction $\Pi_{\tilde D}$ (`00:37:23 – 00:46:58`)**:
1. **Division-Free Centered Spectral Window Identity**:
   Over any commutative ring `R`, for any $X, a, b \in R$ (where $X = -A^2$):
   $$4 (X - a^2)(b^2 - X) = (b^2 - a^2)^2 - (2 X - (a^2 + b^2))^2.$$
2. **Real Spectral Gap Equivalence (`a² ≤ -A² ≤ b² ⟺ |-A² - (a² + b²)/2| ≤ (b² - a²)/2`)**:
   Over $\mathbb{R}$, for any $a, b, X \in \mathbb{R}$ with $a^2 \le b^2$:
   $$(a^2 \le X \wedge X \le b^2) \;\Longleftrightarrow\;
     \left|X - \frac{a^2 + b^2}{2}\right| \le \frac{b^2 - a^2}{2}.$$
3. **Bulk Disk Projection $\Pi_{\tilde D} (-A^2) \Pi_{\tilde D}$ vs. Boundary Truncation**:
   In any associative ring `[Ring B]` with bulk disk projector $P * P = P$ and hopping generator $A \in B$:
   $$\mathrm{peirce11}\;P\;(-(A * A)) =
     -(\mathrm{peirce11}\;P\;A * \mathrm{peirce11}\;P\;A) -
       \mathrm{conePlus}\;P\;A * \mathrm{coneMinus}\;P\;A.$$ -/
theorem kl4_spectral_gap_window_polynomial_and_bulk_disk_truncation
    {R : Type*} [CommRing R] (X_R a_R b_R : R)
    (X a b : ℝ)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A : B) :
    (4 * (X_R - a_R ^ 2) * (b_R ^ 2 - X_R) =
      (b_R ^ 2 - a_R ^ 2) ^ 2 - (2 * X_R - (a_R ^ 2 + b_R ^ 2)) ^ 2) ∧
    ((a ^ 2 ≤ X ∧ X ≤ b ^ 2) ↔
      |X - (a ^ 2 + b ^ 2) / 2| ≤ (b ^ 2 - a ^ 2) / 2) ∧
    (peirce11 P (-(A * A)) =
      -(peirce11 P A * peirce11 P A) - conePlus P A * coneMinus P A) := by
  have hPoly :
      4 * (X_R - a_R ^ 2) * (b_R ^ 2 - X_R) =
        (b_R ^ 2 - a_R ^ 2) ^ 2 - (2 * X_R - (a_R ^ 2 + b_R ^ 2)) ^ 2 := by
    ring
  have hWindow :
      (a ^ 2 ≤ X ∧ X ≤ b ^ 2) ↔
        |X - (a ^ 2 + b ^ 2) / 2| ≤ (b ^ 2 - a ^ 2) / 2 := by
    rw [abs_le]
    constructor
    · rintro ⟨ha, hb⟩
      constructor <;> linarith
    · rintro ⟨hL, hU⟩
      constructor <;> linarith
  have hBulk :
      peirce11 P (-(A * A)) =
        -(peirce11 P A * peirce11 P A) - conePlus P A * coneMinus P A := by
    dsimp [peirce11, conePlus, coneMinus]
    peirce_nf hP
  exact ⟨hPoly, hWindow, hBulk⟩

/-- **Stage $\mathfrak{KS}_3$ (`kitaev_local_gap_centered_band_square_identity`) —
Operator-Algebraic Centered Spectral-Band Square Factorization**:
In any associative ring `[Ring B]`, for any operator `A : B` and spectral gap bounds `a2, b2 : B`,
let $Q = -(A * A)$ and $M_2 = (2 : \mathbb{Z}) \bullet Q - (a_2 + b_2)$. Then:
1. **Exact Noncommutative Commutator Defect**:
   $$M_2 * M_2 - (b_2 - a_2) * (b_2 - a_2) - (4 : \mathbb{Z}) \bullet ((Q - a_2) * (Q - b_2)) =
     (2 : \mathbb{Z}) \bullet \big(\mathrm{comm}\;a_2\;Q + \mathrm{comm}\;Q\;b_2 + \mathrm{comm}\;b_2\;a_2\big).$$
2. **Central Spectral-Bounds Factorization**:
   Whenever $a_2$ and $b_2$ commute with $Q$ and with each other (`comm a2 Q = 0`, `comm Q b2 = 0`,
   `comm b2 a2 = 0`, e.g., scalar multiples $a^2 \cdot 1, b^2 \cdot 1$),
   $$M_2 * M_2 - (b_2 - a_2) * (b_2 - a_2) = (4 : \mathbb{Z}) \bullet ((Q - a_2) * (Q - b_2)).$$ -/
theorem kitaev_local_gap_centered_band_square_identity
    {B : Type*} [Ring B] (A a2 b2 : B) :
    let Q := -(A * A)
    let M₂ := (2 : ℤ) • Q - (a2 + b2)
    (M₂ * M₂ - (b2 - a2) * (b2 - a2) - (4 : ℤ) • ((Q - a2) * (Q - b2)) =
      (2 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm a2 Q +
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q b2 +
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm b2 a2)) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm a2 Q = 0 →
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q b2 = 0 →
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm b2 a2 = 0 →
      M₂ * M₂ - (b2 - a2) * (b2 - a2) = (4 : ℤ) • ((Q - a2) * (Q - b2))) := by
  intro Q M₂
  have hDiff :
      M₂ * M₂ - (b2 - a2) * (b2 - a2) - (4 : ℤ) • ((Q - a2) * (Q - b2)) =
        (2 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.comm a2 Q +
          InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q b2 +
          InfoGeometry.OperatorAlgebra.PeirceSpine.comm b2 a2) := by
    dsimp only [M₂, Q, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  have hCentral :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm a2 Q = 0 →
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q b2 = 0 →
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm b2 a2 = 0 →
      M₂ * M₂ - (b2 - a2) * (b2 - a2) = (4 : ℤ) • ((Q - a2) * (Q - b2)) := by
    intro h1 h2 h3
    apply sub_eq_zero.mp
    rw [hDiff, h1, h2, h3, add_zero, add_zero, smul_zero]
  exact ⟨hDiff, hCentral⟩

/-! ### C*-algebra norm form of the centered spectral window

The scalar interval equivalence above has an operator counterpart in a real
C*-algebra. This theorem uses the native C*-order and self-adjoint norm bound;
it does not assume that an arbitrary ring has a spectral order or norm. -/

/-- A self-adjoint element bounded in C*-order by scalar endpoints lies within
the centered interval in norm. -/
theorem selfAdjoint_norm_le_centered_interval
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [PartialOrder A] [StarOrderedRing A]
    (x : A) (lo hi : ℝ) (hx : IsSelfAdjoint x)
    (hlo : algebraMap ℝ A lo ≤ x) (hhi : x ≤ algebraMap ℝ A hi)
    (hlohi : lo ≤ hi) :
    ‖x - algebraMap ℝ A ((lo + hi) / 2)‖ ≤ (hi - lo) / 2 := by
  let center : ℝ := (lo + hi) / 2
  let radius : ℝ := (hi - lo) / 2
  have hradius : 0 ≤ radius := div_nonneg (sub_nonneg.mpr hlohi) zero_le_two
  have hleft : -radius = lo - center := by dsimp [radius, center]; ring
  have hright : radius = hi - center := by dsimp [radius, center]; ring
  have hlow : algebraMap ℝ A (-radius) ≤ x - algebraMap ℝ A center := by
    rw [hleft, map_sub]
    exact sub_le_sub_right hlo _
  have hhigh : x - algebraMap ℝ A center ≤ algebraMap ℝ A radius := by
    calc
      x - algebraMap ℝ A center ≤ algebraMap ℝ A hi - algebraMap ℝ A center :=
        sub_le_sub_right hhi _
      _ = algebraMap ℝ A radius := by rw [← map_sub, hright]
  have hcenter : IsSelfAdjoint (x - algebraMap ℝ A center) := by
    exact hx.sub (IsSelfAdjoint.algebraMap A (.all center))
  have hnorm := IsSelfAdjoint.norm_le_max_of_le_of_le hlow hhigh hcenter
  have hloNorm : ‖algebraMap ℝ A (-radius)‖ = radius := by
    rw [norm_algebraMap, Real.norm_eq_abs]
    rw [abs_of_nonpos (neg_nonpos.mpr hradius), norm_one]
    ring
  have hhiNorm : ‖algebraMap ℝ A radius‖ = radius := by
    rw [norm_algebraMap, Real.norm_eq_abs]
    rw [abs_of_nonneg hradius, norm_one]
    ring
  rw [hloNorm, hhiNorm, max_self] at hnorm
  simpa [center, radius] using hnorm

/-- Centered norm bound for a self-adjoint operator compressed to a projection.
The order bounds are relative to `p` (the unit of the compressed corner), and
`‖p‖ ≤ 1` controls the endpoint norms in the ambient C*-algebra. -/
theorem compressed_selfAdjoint_norm_le_centered_interval
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [PartialOrder A] [StarOrderedRing A]
    (p y : A) (lo hi : ℝ) (hpSelf : IsSelfAdjoint p) (hy : IsSelfAdjoint y)
    (hp : ‖p‖ ≤ 1)
    (hlo : -(algebraMap ℝ A ((hi - lo) / 2) * p) ≤
      y - algebraMap ℝ A ((lo + hi) / 2) * p)
    (hhi : y - algebraMap ℝ A ((lo + hi) / 2) * p ≤
      algebraMap ℝ A ((hi - lo) / 2) * p)
    (hlohi : lo ≤ hi) :
    ‖y - algebraMap ℝ A ((lo + hi) / 2) * p‖ ≤ (hi - lo) / 2 := by
  let radius : ℝ := (hi - lo) / 2
  let centered : A := y - algebraMap ℝ A ((lo + hi) / 2) * p
  have hradius : 0 ≤ radius := div_nonneg (sub_nonneg.mpr hlohi) zero_le_two
  have hcenterScalarP : IsSelfAdjoint (algebraMap ℝ A ((lo + hi) / 2) * p) := by
    show star (algebraMap ℝ A ((lo + hi) / 2) * p) =
      algebraMap ℝ A ((lo + hi) / 2) * p
    rw [star_mul, hpSelf.star_eq,
      (IsSelfAdjoint.algebraMap A (IsSelfAdjoint.all ((lo + hi) / 2))).star_eq]
    exact (Algebra.commutes ((lo + hi) / 2) p).symm
  have hcentered : IsSelfAdjoint centered := by
    dsimp [centered]
    exact hy.sub hcenterScalarP
  have hnorm := IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi hcentered
  have hEndpoint : ‖algebraMap ℝ A radius * p‖ ≤ radius := by
    calc
      ‖algebraMap ℝ A radius * p‖ ≤ ‖algebraMap ℝ A radius‖ * ‖p‖ := norm_mul_le _ _
      _ = radius * ‖p‖ := by
        rw [norm_algebraMap, Real.norm_eq_abs, abs_of_nonneg hradius, norm_one]
        ring
      _ ≤ radius * 1 := mul_le_mul_of_nonneg_left hp hradius
      _ = radius := mul_one _
  have hNegEndpoint : ‖-(algebraMap ℝ A radius * p)‖ ≤ radius := by
    simpa only [norm_neg] using hEndpoint
  have hmax : max ‖-(algebraMap ℝ A radius * p)‖ ‖algebraMap ℝ A radius * p‖ ≤ radius :=
    max_le hNegEndpoint hEndpoint
  exact hnorm.trans hmax

/-- Compressing a self-adjoint operator interval by a self-adjoint
idempotent preserves the interval in the corner. Combining that order
preservation with the centered estimate gives the square-first norm bound
for the compression. -/
theorem compression_norm_le_centered_interval
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [PartialOrder A] [StarOrderedRing A]
    (p x : A) (lo hi : ℝ) (hp : IsStarProjection p) (hx : IsSelfAdjoint x)
    (hlo : algebraMap ℝ A lo ≤ x) (hhi : x ≤ algebraMap ℝ A hi)
    (hlohi : lo ≤ hi) :
    ‖p * x * p - algebraMap ℝ A ((lo + hi) / 2) * p‖ ≤ (hi - lo) / 2 := by
  have hpSelf := hp.isSelfAdjoint
  have hpIdem := hp.isIdempotentElem.eq
  have hpNorm := IsStarProjection.norm_le p hp
  have hcompressionSelf : IsSelfAdjoint (p * x * p) := by
    show star ((p * x) * p) = (p * x) * p
    calc
      star ((p * x) * p) = p * (x * p) := by
        simp only [star_mul, hpSelf.star_eq, hx.star_eq]
      _ = (p * x) * p := (mul_assoc p x p).symm
  have hscalar (r : ℝ) :
      p * algebraMap ℝ A r * p = algebraMap ℝ A r * p := by
    calc
      p * algebraMap ℝ A r * p = (algebraMap ℝ A r * p) * p := by
        rw [(Algebra.commutes r p).symm]
      _ = algebraMap ℝ A r * (p * p) := by rw [mul_assoc]
      _ = algebraMap ℝ A r * p := by rw [hpIdem]
  have hloCompressed : algebraMap ℝ A lo * p ≤ p * x * p := by
    calc
      algebraMap ℝ A lo * p = p * algebraMap ℝ A lo * p := (hscalar lo).symm
      _ ≤ p * x * p := by
        simpa only [hpSelf.star_eq] using star_left_conjugate_le_conjugate hlo p
  have hhiCompressed : p * x * p ≤ algebraMap ℝ A hi * p := by
    calc
      p * x * p ≤ p * algebraMap ℝ A hi * p := by
        simpa only [hpSelf.star_eq] using star_left_conjugate_le_conjugate hhi p
      _ = algebraMap ℝ A hi * p := hscalar hi
  let center : ℝ := (lo + hi) / 2
  let radius : ℝ := (hi - lo) / 2
  have hleft : lo - center = -radius := by dsimp [center, radius]; ring
  have hright : hi - center = radius := by dsimp [center, radius]; ring
  have hleftScalar : algebraMap ℝ A lo * p - algebraMap ℝ A center * p =
      -(algebraMap ℝ A radius * p) := by
    rw [← sub_mul, ← map_sub, hleft, map_neg, neg_mul]
  have hrightScalar : algebraMap ℝ A hi * p - algebraMap ℝ A center * p =
      algebraMap ℝ A radius * p := by
    rw [← sub_mul, ← map_sub, hright]
  have hloShift : -(algebraMap ℝ A radius * p) ≤
      p * x * p - algebraMap ℝ A center * p := by
    calc
      -(algebraMap ℝ A radius * p) =
          algebraMap ℝ A lo * p - algebraMap ℝ A center * p := hleftScalar.symm
      _ ≤ p * x * p - algebraMap ℝ A center * p := sub_le_sub_right hloCompressed _
  have hhiShift : p * x * p - algebraMap ℝ A center * p ≤
      algebraMap ℝ A radius * p := by
    calc
      p * x * p - algebraMap ℝ A center * p ≤
          algebraMap ℝ A hi * p - algebraMap ℝ A center * p := sub_le_sub_right hhiCompressed _
      _ = algebraMap ℝ A radius * p := hrightScalar
  simpa [center, radius] using
    compressed_selfAdjoint_norm_le_centered_interval p (p * x * p) lo hi
      hpSelf hcompressionSelf hpNorm hloShift hhiShift hlohi

/-- Square-first specialization of the compressed interval estimate. For a
skew-adjoint operator `k`, the operator `-(k * k)` is self-adjoint. Full-space
order bounds on this square therefore imply the centered norm bound in any
self-adjoint-projection corner. This states the operator-theoretic local-gap
step; geometric locality and collar hypotheses are separate. -/
theorem kitaev_square_first_compressed_gap_bound
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [PartialOrder A] [StarOrderedRing A]
    (p k : A) (lo hi : ℝ) (hp : IsStarProjection p)
    (hk : star k = -k)
    (hlo : algebraMap ℝ A lo ≤ -(k * k))
    (hhi : -(k * k) ≤ algebraMap ℝ A hi)
    (hlohi : lo ≤ hi) :
    ‖p * (-(k * k)) * p - algebraMap ℝ A ((lo + hi) / 2) * p‖ ≤
      (hi - lo) / 2 := by
  have hx : IsSelfAdjoint (-(k * k)) := by
    show star (-(k * k)) = -(k * k)
    simp only [star_neg, star_mul, hk, neg_mul_neg]
  exact compression_norm_le_centered_interval p (-(k * k)) lo hi hp hx hlo hhi hlohi

/-! ## §6. Stage $\mathfrak{KL}_5$: Noncommutative IMS Double-Commutator Localization Identity & $O(r^2 / R^2)$ Local Norm Testing -/

/-- **Single-Weight Noncommutative IMS Double-Commutator Identity (`ims_single_double_commutator_identity`)**:
In any associative ring `[Ring B]`, for any localization weight $\chi \in B$ and operator $M \in B$:
$$\chi * \chi * M + M * (\chi * \chi) - (2 : \mathbb{Z}) \bullet (\chi * M * \chi) =
  \mathrm{comm}\;\chi\;(\mathrm{comm}\;\chi\;M).$$ -/
lemma ims_single_double_commutator_identity
    {B : Type*} [Ring B] (χ M : B) :
    χ * χ * M + M * (χ * χ) - (2 : ℤ) • (χ * M * χ) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm χ
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm χ M) := by
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  rw [two_zsmul]
  noncomm_ring

/-- **Stage $\mathfrak{KL}_5$ (`kl5_ims_double_commutator_localization_and_r_locality`) —
Kitaev's Local Norm Testing Lemma (`00:46:58`) via the Noncommutative IMS Double-Commutator Identity**:
1. **Single-Patch Double-Commutator Identity**:
   $$\chi * \chi * M + M * (\chi * \chi) - (2 : \mathbb{Z}) \bullet (\chi * M * \chi) =
     \mathrm{comm}\;\chi\;(\mathrm{comm}\;\chi\;M).$$
2. **Global Partition-of-Unity Localization Identity**:
   For any finite family of localization weights `χ : ι → B` (`[Fintype ι]`) satisfying the
   quadratic partition of unity $\sum_{b : \iota} \chi_b * \chi_b = 1$:
   $$(2 : \mathbb{Z}) \bullet M - (2 : \mathbb{Z}) \bullet \sum_{b : \iota} (\chi_b * M * \chi_b) =
     \sum_{b : \iota} \mathrm{comm}\;(\chi_b)\;(\mathrm{comm}\;(\chi_b)\;M).$$
3. **Quadratic $(r / R)^2$ Localization Error Law**:
   For any locality range $r \in \mathbb{R}$ and ball radius $R \neq 0$,
   $(c \cdot (r / R))^2 = c^2 \cdot (r^2 / R^2)$. -/
theorem kl5_ims_double_commutator_localization_and_r_locality
    {B : Type*} [Ring B] {ι : Type*} [Fintype ι]
    (χ : ι → B) (M : B) (hPart : (∑ b : ι, χ b * χ b) = 1)
    (c r R : ℝ) :
    (∀ b : ι,
      χ b * χ b * M + M * (χ b * χ b) - (2 : ℤ) • (χ b * M * χ b) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)) ∧
    ((2 : ℤ) • M - (2 : ℤ) • (∑ b : ι, χ b * M * χ b) =
      ∑ b : ι, InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)) ∧
    ((c * (r / R)) ^ 2 = c ^ 2 * (r ^ 2 / R ^ 2)) := by
  have hSingle :
      ∀ b : ι,
        χ b * χ b * M + M * (χ b * χ b) - (2 : ℤ) • (χ b * M * χ b) =
          InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
            (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M) :=
    fun b => ims_single_double_commutator_identity (χ b) M
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
      exact (hSingle b).symm
    rw [hPointwise, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hPart, one_mul, mul_one,
      ← two_zsmul M, ← Finset.smul_sum]
  exact ⟨hSingle, hSum, by ring⟩

/-- **Operator-norm consequence of the finite IMS identity.**
For a finite quadratic partition of unity in a normed real algebra, the norm of the
localization error is bounded by one half the sum of the norms of the double
commutators. This is a genuine operator-norm estimate; geometric locality enters
only when separate hypotheses bound each double commutator. -/
theorem ims_localization_error_norm_le_sum_double_commutators
    {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
    {ι : Type*} [Fintype ι]
    (χ : ι → B) (M : B) (hPart : (∑ b : ι, χ b * χ b) = 1) :
    ‖M - ∑ b : ι, χ b * M * χ b‖ ≤
      (1 / 2 : ℝ) *
        ∑ b : ι, ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)‖ := by
  let E : B := M - ∑ b : ι, χ b * M * χ b
  let D : ι → B := fun b =>
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)
  have hIMS := (kl5_ims_double_commutator_localization_and_r_locality χ M hPart 0 0 1).2.1
  have hScaled : (2 : ℝ) • E = ∑ b : ι, D b := by
    dsimp [E, D]
    rw [show (2 : ℝ) • (M - ∑ b : ι, χ b * M * χ b) =
      (M - ∑ b : ι, χ b * M * χ b) + (M - ∑ b : ι, χ b * M * χ b) by
        rw [two_smul]]
    have hIMS' := hIMS
    simp only [two_zsmul] at hIMS'
    calc
      (M - ∑ b : ι, χ b * M * χ b) + (M - ∑ b : ι, χ b * M * χ b) =
          M + M - (∑ b : ι, χ b * M * χ b + ∑ b : ι, χ b * M * χ b) := by abel
      _ = ∑ b : ι, InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M) := hIMS'
  have hTriangle := norm_sum_le Finset.univ D
  rw [← hScaled] at hTriangle
  have hScale : ‖(2 : ℝ) • E‖ = 2 * ‖E‖ := by
    rw [norm_smul, Real.norm_ofNat]
  rw [hScale] at hTriangle
  have hhalf : (1 / 2 : ℝ) * (2 * ‖E‖) = ‖E‖ := by ring
  rw [← hhalf]
  exact mul_le_mul_of_nonneg_left hTriangle (by norm_num)

/-- A pointwise bound on each IMS double commutator gives the corresponding
summed bulk localization estimate. The geometric estimate for `δ b` must be
proved from locality and cutoff regularity in a concrete operator model. -/
theorem ims_localization_error_norm_le_sum_of_local_bounds
    {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
    {ι : Type*} [Fintype ι]
    (χ : ι → B) (M : B) (hPart : (∑ b : ι, χ b * χ b) = 1)
    (δ : ι → ℝ)
    (hLocal : ∀ b : ι,
      ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)‖ ≤ δ b) :
    ‖M - ∑ b : ι, χ b * M * χ b‖ ≤
      (1 / 2 : ℝ) * ∑ b : ι, δ b := by
  apply (ims_localization_error_norm_le_sum_double_commutators χ M hPart).trans
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hLocal b)
  norm_num

/-- Finite-overlap refinement of IMS aggregation. If the double commutator
vanishes outside an active patch family and is bounded by `ε` on active
patches, the localization error depends on the active-patch count bound `K`,
not on the cardinality of the entire indexing type. Geometric cutoff families
must still prove both the vanishing condition and a uniform `K`. -/
theorem ims_localization_error_norm_le_active_patch_overlap
    {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
    {ι : Type*} [Fintype ι] (active : ι → Prop) [DecidablePred active]
    (χ : ι → B) (M : B) (hPart : (∑ b : ι, χ b * χ b) = 1)
    (ε K : ℝ) (hε : 0 ≤ ε)
    (hOverlap : (∑ b : ι, if active b then (1 : ℝ) else 0) ≤ K)
    (hLocal : ∀ b : ι,
      ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)‖ ≤
          if active b then ε else 0) :
    ‖M - ∑ b : ι, χ b * M * χ b‖ ≤ (1 / 2 : ℝ) * ε * K := by
  have h := ims_localization_error_norm_le_sum_of_local_bounds
    χ M hPart (fun b : ι => if active b then ε else 0) hLocal
  have hsum : (∑ b : ι, if active b then ε else 0) =
      ε * (∑ b : ι, if active b then (1 : ℝ) else 0) := by
    calc
      (∑ b : ι, if active b then ε else 0) =
          ∑ b : ι, ε * (if active b then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro b hb
            split_ifs <;> simp
      _ = ε * (∑ b : ι, if active b then (1 : ℝ) else 0) :=
        by rw [Finset.mul_sum]
  have hεOverlap := mul_le_mul_of_nonneg_left hOverlap hε
  calc
    ‖M - ∑ b : ι, χ b * M * χ b‖ ≤
        (1 / 2 : ℝ) * (∑ b : ι, if active b then ε else 0) := h
    _ = (1 / 2 : ℝ) *
        (ε * (∑ b : ι, if active b then (1 : ℝ) else 0)) := by rw [hsum]
    _ ≤ (1 / 2 : ℝ) * (ε * K) :=
      mul_le_mul_of_nonneg_left hεOverlap (by norm_num)
    _ = (1 / 2 : ℝ) * ε * K := by ring

/-- The IMS approximation converts bounds on the localized compressions into
a finite global operator-norm bound. The partition and its localization error
are explicit hypotheses; this lemma does not construct geometric cutoffs. -/
theorem ims_global_norm_le_localized_norm_sum
    {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
    {ι : Type*} [Fintype ι]
    (χ : ι → B) (M : B) (hPart : (∑ b : ι, χ b * χ b) = 1)
    (δ : ι → ℝ)
    (hLocal : ∀ b : ι,
      ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)‖ ≤ δ b)
    (hCompression : ∀ b : ι, ‖χ b * M * χ b‖ ≤ δ b) :
    ‖M‖ ≤ (3 / 2 : ℝ) * ∑ b : ι, δ b := by
  have hError := ims_localization_error_norm_le_sum_of_local_bounds
    χ M hPart δ hLocal
  have hSum : ‖∑ b : ι, χ b * M * χ b‖ ≤ ∑ b : ι, δ b := by
    calc
      ‖∑ b : ι, χ b * M * χ b‖ ≤ ∑ b : ι, ‖χ b * M * χ b‖ := norm_sum_le _ _
      _ ≤ ∑ b : ι, δ b := Finset.sum_le_sum fun b _ => hCompression b
  have hTriangle : ‖M‖ ≤ ‖M - ∑ b : ι, χ b * M * χ b‖ +
      ‖∑ b : ι, χ b * M * χ b‖ := by
    have h := norm_add_le (M - ∑ b : ι, χ b * M * χ b)
      (∑ b : ι, χ b * M * χ b)
    simpa using h
  calc
    ‖M‖ ≤ ‖M - ∑ b : ι, χ b * M * χ b‖ +
        ‖∑ b : ι, χ b * M * χ b‖ := hTriangle
    _ ≤ (1 / 2 : ℝ) * ∑ b : ι, δ b + ∑ b : ι, δ b :=
      add_le_add hError hSum
    _ = (3 / 2 : ℝ) * ∑ b : ι, δ b := by ring

/-- Active-patch form of the finite IMS local-to-global norm estimate. Both
the local compression and double-commutator terms are assumed zero off the
active family and at most `ε` on it; the result then depends on its overlap
bound `K`, rather than on the full finite cover size. -/
theorem ims_global_norm_le_active_patch_overlap
    {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
    {ι : Type*} [Fintype ι] (active : ι → Prop) [DecidablePred active]
    (χ : ι → B) (M : B) (hPart : (∑ b : ι, χ b * χ b) = 1)
    (ε K : ℝ) (hε : 0 ≤ ε)
    (hOverlap : (∑ b : ι, if active b then (1 : ℝ) else 0) ≤ K)
    (hLocal : ∀ b : ι,
      ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)‖ ≤
          if active b then ε else 0)
    (hCompression : ∀ b : ι,
      ‖χ b * M * χ b‖ ≤ if active b then ε else 0) :
    ‖M‖ ≤ (3 / 2 : ℝ) * ε * K := by
  have h := ims_global_norm_le_localized_norm_sum χ M hPart
    (fun b : ι => if active b then ε else 0) hLocal hCompression
  have hsum : (∑ b : ι, if active b then ε else 0) =
      ε * (∑ b : ι, if active b then (1 : ℝ) else 0) := by
    calc
      (∑ b : ι, if active b then ε else 0) =
          ∑ b : ι, ε * (if active b then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro b hb
            split_ifs <;> simp
      _ = ε * (∑ b : ι, if active b then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
  have hεOverlap := mul_le_mul_of_nonneg_left hOverlap hε
  calc
    ‖M‖ ≤ (3 / 2 : ℝ) *
        (∑ b : ι, if active b then ε else 0) := by simpa using h
    _ = (3 / 2 : ℝ) *
        (ε * (∑ b : ι, if active b then (1 : ℝ) else 0)) := by rw [hsum]
    _ ≤ (3 / 2 : ℝ) * (ε * K) :=
      mul_le_mul_of_nonneg_left hεOverlap (by norm_num)
    _ = (3 / 2 : ℝ) * ε * K := by ring

/-! ### Finite-propagation matrix commutator estimate

The next estimate supplies a concrete finite-matrix input to the abstract IMS
aggregation theorem. For a diagonal Lipschitz multiplier, the double commutator
multiplies each matrix entry by the square of the multiplier difference. A
finite-propagation hypothesis then controls that factor uniformly. -/

section DiagonalMultiplierLocality

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable local instance : NormedRing (Matrix n n ℝ) := Matrix.linftyOpNormedRing
noncomputable local instance : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.linftyOpNormedAlgebra

open scoped Matrix.Norms.Operator

/-- Entrywise form of a single commutator with a diagonal multiplier. -/
private lemma diagonal_comm_apply (u : n → ℝ) (M : Matrix n n ℝ) (i j : n) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M i j =
      (u i - u j) * M i j := by
  simp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.sub_apply]
  ring

/-- Entrywise form of the double commutator with a diagonal multiplier. -/
theorem diagonal_double_comm_apply (u : n → ℝ) (M : Matrix n n ℝ) (i j : n) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M) i j =
        (u i - u j) ^ 2 * M i j := by
  calc
    _ = (u i - u j) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M i j :=
          diagonal_comm_apply u _ i j
    _ = (u i - u j) * ((u i - u j) * M i j) := by
          rw [diagonal_comm_apply]
    _ = _ := by ring

/-- The finite-propagation diagonal-multiplier estimate in the matrix `L∞→L∞`
operator norm (the supremum of absolute row sums). If every nonzero bond sees
multiplier oscillation at most `δ`, the double commutator costs at most `δ²`
times the original operator norm. -/
theorem diagonal_double_comm_norm_le_of_bond_oscillation
    (u : n → ℝ) (M : Matrix n n ℝ) (δ : NNReal)
    (hOsc : ∀ i j : n, M i j ≠ 0 → ‖u i - u j‖₊ ≤ δ) :
    ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M)‖ ≤
      (δ : ℝ) ^ 2 * ‖M‖ := by
  have hNN :
      ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M)‖₊ ≤
        δ ^ 2 * ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i hi
    calc
      ∑ j : n, ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M) i j‖₊
          ≤ ∑ j : n, δ ^ 2 * ‖M i j‖₊ := by
            apply Finset.sum_le_sum
            intro j hj
            rw [diagonal_double_comm_apply]
            by_cases hM : M i j = 0
            · simp [hM]
            · calc
                ‖(u i - u j) ^ 2 * M i j‖₊ = ‖u i - u j‖₊ ^ 2 * ‖M i j‖₊ := by
                  simp [nnnorm_mul, nnnorm_pow]
                _ ≤ δ ^ 2 * ‖M i j‖₊ := by
                  gcongr
                  exact hOsc i j hM
      _ = δ ^ 2 * ∑ j : n, ‖M i j‖₊ := by rw [Finset.mul_sum]
      _ ≤ δ ^ 2 * Finset.univ.sup (fun i : n => ∑ j : n, ‖M i j‖₊) := by
          gcongr
          exact Finset.le_sup (f := fun i : n => ∑ j : n, ‖M i j‖₊) (Finset.mem_univ i)
  exact_mod_cast hNN

/-- Lipschitz variation over bonds of range at most `r` gives the quadratic
double-commutator estimate in the row-sum operator norm. This is the concrete
finite-propagation (O((Lr)^2)) estimate needed as input to IMS localization. -/
theorem diagonal_double_comm_norm_le_of_lipschitz_local
    (u : n → ℝ) (dist : n → n → ℝ) (M : Matrix n n ℝ) (L r : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hLip : ∀ i j : n, |u i - u j| ≤ L * dist i j)
    (hRange : ∀ i j : n, M i j ≠ 0 → dist i j ≤ r) :
    ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M)‖ ≤
      (L * r) ^ 2 * ‖M‖ := by
  have hLr : 0 ≤ L * r := mul_nonneg hL hr
  have hOsc : ∀ i j : n, M i j ≠ 0 →
      ‖u i - u j‖₊ ≤ (L * r).toNNReal := by
    intro i j hij
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
      Real.toNNReal_of_nonneg hLr]
    exact (hLip i j).trans (mul_le_mul_of_nonneg_left (hRange i j hij) hL)
  have hCore := diagonal_double_comm_norm_le_of_bond_oscillation u M
    ((L * r).toNNReal) hOsc
  simpa [Real.toNNReal_of_nonneg hLr] using hCore

/-- Finite Hilbert--Schmidt energy estimate for the same finite-propagation
double commutator. This is an entrywise square-sum bound, not the Hilbert
operator-norm estimate used in the local-gap criterion. -/
theorem diagonal_double_comm_hilbertSchmidt_energy_le_of_lipschitz_local
    (u : n → ℝ) (dist : n → n → ℝ) (M : Matrix n n ℝ) (L r : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hLip : ∀ i j : n, |u i - u j| ≤ L * dist i j)
    (hRange : ∀ i j : n, M i j ≠ 0 → dist i j ≤ r) :
    (∑ i : n, ∑ j : n,
      ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M) i j‖ ^ 2) ≤
      (L * r) ^ 4 * (∑ i : n, ∑ j : n, ‖M i j‖ ^ 2) := by
  have hLr : 0 ≤ L * r := mul_nonneg hL hr
  have hEntry (i j : n) :
      ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M) i j‖ ^ 2 ≤
      (L * r) ^ 4 * ‖M i j‖ ^ 2 := by
    rw [diagonal_double_comm_apply, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_pow]
    rw [← Real.norm_eq_abs (M i j)]
    by_cases hM : M i j = 0
    · simp [hM]
    · have hdiff : |u i - u j| ≤ L * r :=
        (hLip i j).trans (mul_le_mul_of_nonneg_left (hRange i j hM) hL)
      have hdiff4 : |u i - u j| ^ 4 ≤ (L * r) ^ 4 := by
        gcongr
      calc
        (|u i - u j| ^ 2 * ‖M i j‖) ^ 2 =
            |u i - u j| ^ 4 * ‖M i j‖ ^ 2 := by ring
        _ ≤ (L * r) ^ 4 * ‖M i j‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hdiff4 (sq_nonneg _)
  calc
    (∑ i : n, ∑ j : n,
      ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M) i j‖ ^ 2)
        ≤ ∑ i : n, ∑ j : n, (L * r) ^ 4 * ‖M i j‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact hEntry i j
    _ = (L * r) ^ 4 * (∑ i : n, ∑ j : n, ‖M i j‖ ^ 2) := by
          simp_rw [Finset.mul_sum]

/-- Finite IMS localization bound for diagonal Lipschitz cutoffs and a
finite-propagation matrix. Each patch contributes its explicit quadratic
`(L r)² ‖M‖` error; no spectral or continuum conclusion is implicit. -/
theorem ims_diagonal_localization_norm_le_lipschitz_bond_sum
    {ι : Type*} [Fintype ι]
    (u : ι → n → ℝ) (dist : n → n → ℝ) (M : Matrix n n ℝ) (L r : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hPart : (∑ b : ι, Matrix.diagonal (u b) * Matrix.diagonal (u b)) = 1)
    (hLip : ∀ b : ι, ∀ i j : n, |u b i - u b j| ≤ L * dist i j)
    (hRange : ∀ i j : n, M i j ≠ 0 → dist i j ≤ r) :
    ‖M - ∑ b : ι, Matrix.diagonal (u b) * M * Matrix.diagonal (u b)‖ ≤
      (1 / 2 : ℝ) * ∑ _b : ι, (L * r) ^ 2 * ‖M‖ := by
  apply ims_localization_error_norm_le_sum_of_local_bounds
    (χ := fun b : ι => Matrix.diagonal (u b)) M hPart
  intro b
  exact diagonal_double_comm_norm_le_of_lipschitz_local
    (u b) dist M L r hL hr (hLip b) hRange

/-- The preceding finite-propagation estimate with a uniform bound per patch
made explicit as a patch-count factor. The norm here is the matrix `L∞→L∞`
row-sum norm inherited from this section. -/
theorem ims_diagonal_localization_norm_le_card_mul_lipschitz_bond_bound
    {ι : Type*} [Fintype ι]
    (u : ι → n → ℝ) (dist : n → n → ℝ) (M : Matrix n n ℝ) (L r : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hPart : (∑ b : ι, Matrix.diagonal (u b) * Matrix.diagonal (u b)) = 1)
    (hLip : ∀ b : ι, ∀ i j : n, |u b i - u b j| ≤ L * dist i j)
    (hRange : ∀ i j : n, M i j ≠ 0 → dist i j ≤ r) :
    ‖M - ∑ b : ι, Matrix.diagonal (u b) * M * Matrix.diagonal (u b)‖ ≤
      (1 / 2 : ℝ) * (Fintype.card ι : ℝ) * (L * r) ^ 2 * ‖M‖ := by
  have h := ims_diagonal_localization_norm_le_lipschitz_bond_sum
    u dist M L r hL hr hPart hLip hRange
  have hsum : (∑ _b : ι, (L * r) ^ 2 * ‖M‖) =
      (Fintype.card ι : ℝ) * ((L * r) ^ 2 * ‖M‖) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsum] at h
  simpa only [mul_assoc] using h

end DiagonalMultiplierLocality

/-! ### Hilbert--Schmidt IMS specialization

The entrywise finite-propagation estimate also supplies explicit local bounds
for the abstract IMS identity when the matrix algebra is equipped with its
Frobenius (Hilbert--Schmidt) norm. This remains distinct from the induced
Euclidean operator norm used in the local-gap criterion. -/

section HilbertSchmidtIMS

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable local instance : NormedRing (Matrix n n ℝ) :=
  Matrix.frobeniusNormedRing

noncomputable local instance : NormedAlgebra ℝ (Matrix n n ℝ) :=
  Matrix.frobeniusNormedAlgebra

/-- The squared Frobenius energy written as an explicit finite entry sum. -/
def matrixEntryEnergy (M : Matrix n n ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, ‖M i j‖ ^ 2

/-- Finite IMS localization in the Frobenius norm for a finite-propagation
matrix and diagonal Lipschitz cutoffs. The explicit patch error is the
Hilbert--Schmidt bound obtained from the entrywise double-commutator estimate.
This is not an operator-norm local-gap theorem. -/
theorem ims_frobenius_localization_norm_le_lipschitz_energy
    {ι : Type*} [Fintype ι]
    (u : ι → n → ℝ) (dist : n → n → ℝ) (M : Matrix n n ℝ) (L r : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hPart : (∑ b : ι, Matrix.diagonal (u b) * Matrix.diagonal (u b)) = 1)
    (hLip : ∀ b : ι, ∀ i j : n, |u b i - u b j| ≤ L * dist i j)
    (hRange : ∀ i j : n, M i j ≠ 0 → dist i j ≤ r) :
    ‖M - ∑ b : ι, Matrix.diagonal (u b) * M * Matrix.diagonal (u b)‖ ≤
      (1 / 2 : ℝ) * ∑ _b : ι,
        Real.sqrt ((L * r) ^ 4 * matrixEntryEnergy M) := by
  apply ims_localization_error_norm_le_sum_of_local_bounds
    (χ := fun b : ι => Matrix.diagonal (u b)) M hPart
  intro b
  have hEnergy := diagonal_double_comm_hilbertSchmidt_energy_le_of_lipschitz_local
    (u b) dist M L r hL hr (hLip b) hRange
  have hNorm := Real.sqrt_le_sqrt hEnergy
  simpa [matrixEntryEnergy, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow] using hNorm

end HilbertSchmidtIMS

/-! ### Hilbert-space operator-norm specialization

The preceding concrete row-sum estimate is useful for finite propagation, while
Kitaev's local-gap definition uses the operator norm on a Hilbert space. The
abstract IMS aggregation identity specializes to Mathlib's Euclidean (`L²`)
matrix operator norm whenever local double-commutator bounds are supplied.
This specialization does not itself derive those bounds from geometric cutoffs.
-/

section HilbertOperatorIMS

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator

/-- Finite IMS localization estimate in the Euclidean/Hilbert operator norm.
The local double-commutator bounds are explicit hypotheses; geometric locality
must supply them in a concrete lattice model. -/
theorem ims_matrix_l2_localization_norm_le_sum_of_local_bounds
    {ι : Type*} [Fintype ι]
    (χ : ι → Matrix n n ℝ) (M : Matrix n n ℝ)
    (hPart : (∑ b : ι, χ b * χ b) = 1)
    (δ : ι → ℝ)
    (hLocal : ∀ b : ι,
      ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)‖ ≤ δ b) :
    ‖M - ∑ b : ι, χ b * M * χ b‖ ≤ (1 / 2 : ℝ) * ∑ b : ι, δ b := by
  apply (ims_localization_error_norm_le_sum_double_commutators χ M hPart).trans
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hLocal b)
  norm_num

/-- Uniform patchwise L² double-commutator control gives a global finite-cover
bound with the number of patches explicit. This is the finite local-to-global
aggregation step; it does not construct a cover or estimate the local terms. -/
theorem ims_matrix_l2_localization_norm_le_card_mul_uniform_bound
    {ι : Type*} [Fintype ι]
    (χ : ι → Matrix n n ℝ) (M : Matrix n n ℝ)
    (hPart : (∑ b : ι, χ b * χ b) = 1)
    (ε : ℝ)
    (hLocal : ∀ b : ι,
      ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)‖ ≤ ε) :
    ‖M - ∑ b : ι, χ b * M * χ b‖ ≤
      (1 / 2 : ℝ) * (Fintype.card ι : ℝ) * ε := by
  have h := ims_matrix_l2_localization_norm_le_sum_of_local_bounds
    χ M hPart (fun _ : ι => ε) (fun b => hLocal b)
  have hsum : (∑ _b : ι, ε) = (Fintype.card ι : ℝ) * ε := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hsum] at h
  simpa only [mul_assoc] using h

set_option maxHeartbeats 1000000 in
/-- The induced Euclidean operator norm of a real matrix is bounded by the
square root of its entrywise square-sum energy. This finite-dimensional bridge
lets Hilbert--Schmidt commutator estimates supply (dimension-dependent) L²
operator bounds. -/
theorem l2_opNorm_le_sqrt_matrix_entry_energy (A : Matrix n n ℝ) :
    ‖A‖ ≤ Real.sqrt (matrixEntryEnergy A) := by
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A
  have hE : 0 ≤ matrixEntryEnergy A := by
    unfold matrixEntryEnergy
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact sq_nonneg _
  have hBound (x : EuclideanSpace ℝ n) :
      ‖T x‖ ≤ Real.sqrt (matrixEntryEnergy A) * ‖x‖ := by
    have hSq : ‖T x‖ ^ 2 ≤ matrixEntryEnergy A * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      change (∑ i, ((A *ᵥ (WithLp.ofLp x)) i) ^ 2) ≤ _
      simp only [Matrix.mulVec, dotProduct]
      calc
        (∑ i, (∑ j, A i j * (WithLp.ofLp x) j) ^ 2) ≤
            ∑ i, (∑ j, (A i j) ^ 2) * (∑ j, ((WithLp.ofLp x) j) ^ 2) := by
          apply Finset.sum_le_sum
          intro i hi
          exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
            (fun j => A i j) (fun j => (WithLp.ofLp x) j)
        _ = matrixEntryEnergy A * ‖x‖ ^ 2 := by
          simp [matrixEntryEnergy, EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
    have hSq' : ‖T x‖ ^ 2 ≤ (Real.sqrt (matrixEntryEnergy A) * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hE]
      exact hSq
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hSq'
  rw [← Matrix.l2_opNorm_toEuclideanCLM A]
  exact T.opNorm_le_bound (Real.sqrt_nonneg _) hBound

/-- The entrywise square-sum energy is at most the number of columns times
the squared Euclidean operator norm. This is the explicit finite-dimensional
cost needed to convert the Hilbert--Schmidt estimate into an operator bound. -/
theorem matrix_entry_energy_le_card_mul_l2_opNorm_sq (A : Matrix n n ℝ) :
    matrixEntryEnergy A ≤ (Fintype.card n : ℝ) * ‖A‖ ^ 2 := by
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A
  have hTnorm : ‖T‖ = ‖A‖ := rfl
  have hcol (j : n) :
      (∑ i : n, ‖A i j‖ ^ 2) ≤ ‖A‖ ^ 2 := by
    have hvec : ‖T (EuclideanSpace.single j (1 : ℝ))‖ ≤ ‖A‖ := by
      calc
        ‖T (EuclideanSpace.single j (1 : ℝ))‖ ≤
            ‖T‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := T.le_opNorm _
        _ = ‖A‖ := by simp [hTnorm]
    have hvecsq : ‖T (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ ‖A‖ ^ 2 := by
      nlinarith [norm_nonneg (T (EuclideanSpace.single j (1 : ℝ))), norm_nonneg A]
    have hident :
        (∑ i : n, ‖A i j‖ ^ 2) = ‖T (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      change (∑ i : n, ‖A i j‖ ^ 2) =
        ∑ i : n, ((Matrix.mulVec A
          (WithLp.ofLp (EuclideanSpace.single j (1 : ℝ))) i) ^ 2)
      simp [Matrix.mulVec, dotProduct, EuclideanSpace.single]
    calc
      (∑ i : n, ‖A i j‖ ^ 2) =
          ‖T (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := hident
      _ ≤ ‖A‖ ^ 2 := hvecsq
  calc
    matrixEntryEnergy A = ∑ j : n, ∑ i : n, ‖A i j‖ ^ 2 := by
      unfold matrixEntryEnergy
      rw [Finset.sum_comm]
    _ ≤ ∑ _j : n, ‖A‖ ^ 2 := Finset.sum_le_sum fun j _ => hcol j
    _ = (Fintype.card n : ℝ) * ‖A‖ ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Finite-propagation diagonal cutoffs satisfy a concrete Hilbert L² operator
localization bound through the entry-energy estimate. The bound depends on
the Hilbert--Schmidt energy of `M`; this theorem does not identify that energy
with the operator norm uniformly in matrix dimension. -/
theorem diagonal_double_comm_l2_norm_le_sqrt_lipschitz_energy
    (u : n → ℝ) (dist : n → n → ℝ) (M : Matrix n n ℝ) (L r : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hLip : ∀ i j : n, |u i - u j| ≤ L * dist i j)
    (hRange : ∀ i j : n, M i j ≠ 0 → dist i j ≤ r) :
    ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M)‖ ≤
      Real.sqrt ((L * r) ^ 4 * matrixEntryEnergy M) := by
  let C := InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M)
  have hE := diagonal_double_comm_hilbertSchmidt_energy_le_of_lipschitz_local
    u dist M L r hL hr hLip hRange
  have h := l2_opNorm_le_sqrt_matrix_entry_energy C
  have h' := Real.sqrt_le_sqrt hE
  simpa [C, matrixEntryEnergy] using h.trans h'

/-- Finite-propagation diagonal cutoffs give a concrete Euclidean operator-norm
double-commutator estimate. The factor `Fintype.card n` records the finite
matrix dimension cost in converting entry energy to operator norm. -/
theorem diagonal_double_comm_l2_norm_le_card_mul_lipschitz_bound
    (u : n → ℝ) (dist : n → n → ℝ) (M : Matrix n n ℝ) (L r : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hLip : ∀ i j : n, |u i - u j| ≤ L * dist i j)
    (hRange : ∀ i j : n, M i j ≠ 0 → dist i j ≤ r) :
    ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M)‖ ≤
      Real.sqrt ((L * r) ^ 4 * (Fintype.card n : ℝ) * ‖M‖ ^ 2) := by
  let C := InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u)
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal u) M)
  have hLocalEnergy := diagonal_double_comm_hilbertSchmidt_energy_le_of_lipschitz_local
    u dist M L r hL hr hLip hRange
  have hMatrixEnergy := matrix_entry_energy_le_card_mul_l2_opNorm_sq M
  have hCoeff : 0 ≤ (L * r) ^ 4 := by positivity
  have hCombined : (L * r) ^ 4 * matrixEntryEnergy M ≤
      (L * r) ^ 4 * (Fintype.card n : ℝ) * ‖M‖ ^ 2 := by
    calc
      (L * r) ^ 4 * matrixEntryEnergy M ≤
          (L * r) ^ 4 * ((Fintype.card n : ℝ) * ‖M‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hMatrixEnergy hCoeff
      _ = (L * r) ^ 4 * (Fintype.card n : ℝ) * ‖M‖ ^ 2 := (mul_assoc _ _ _).symm
  have h := l2_opNorm_le_sqrt_matrix_entry_energy C
  have hEnergy := Real.sqrt_le_sqrt hLocalEnergy
  have hOperator := Real.sqrt_le_sqrt hCombined
  have hBound := h.trans hEnergy
  have hBound' := hBound.trans hOperator
  simpa [C] using hBound'

/-! ### An explicit three-site finite metric cutoff instance

This finite path example supplies the partition, Lipschitz, and propagation
hypotheses to the preceding operator-norm IMS estimate. It is an actual
three-site matrix instance, not a statement about arbitrary geometric covers
or a continuum limit. -/

section ThreeSiteCutoffInstance

/-- Path distance `|i - j|` on the three-site path `Fin 3`. -/
private def threeSitePathDist (i j : Fin 3) : ℝ :=
  |(i : ℝ) - (j : ℝ)|

/-- Two nonconstant cutoff weights on the three-vertex path. At each vertex
their squares sum to one; their values are the rational points
`(1,0)`, `(4/5,3/5)`, and `(3/5,4/5)` on the unit circle. -/
private noncomputable def threeSiteCutoff (b : Fin 2) (i : Fin 3) : ℝ :=
  if b.val = 0 then
    if i.val = 0 then 1 else if i.val = 1 then 4 / 5 else 3 / 5
  else
    if i.val = 0 then 0 else if i.val = 1 then 3 / 5 else 4 / 5

/-- Quadratic partition-of-unity identity `∑_b diag(χ_b)² = I₃` for `threeSiteCutoff`. -/
private theorem threeSiteCutoff_partition :
    (∑ b : Fin 2,
      Matrix.diagonal (threeSiteCutoff b) * Matrix.diagonal (threeSiteCutoff b)) =
        (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.mul_apply, threeSiteCutoff,
      Fin.sum_univ_succ] <;> norm_num

/-- Lipschitz bound `|χ_b(i) - χ_b(j)| ≤ (3/5) · threeSitePathDist i j` on `Fin 3`. -/
private theorem threeSiteCutoff_lipschitz :
    ∀ b : Fin 2, ∀ i j : Fin 3,
      |threeSiteCutoff b i - threeSiteCutoff b j| ≤
        (3 / 5 : ℝ) * threeSitePathDist i j := by
  intro b i j
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [threeSiteCutoff, threeSitePathDist]

/-- For any real `3 × 3` matrix supported on the diagonal and nearest-neighbor
bonds of the three-site path, these explicit cutoffs give the Hilbert operator
norm IMS error bound. The dimension factor `3` is retained inside the local
entry-energy-to-operator-norm conversion. -/
theorem threeSiteCutoff_ims_l2_bound (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hRange : ∀ i j : Fin 3, M i j ≠ 0 → threeSitePathDist i j ≤ 1) :
    ‖M - ∑ b : Fin 2,
        Matrix.diagonal (threeSiteCutoff b) * M * Matrix.diagonal (threeSiteCutoff b)‖ ≤
      Real.sqrt ((3 / 5 : ℝ) ^ 4 * 3 * ‖M‖ ^ 2) := by
  have hLocal : ∀ b : Fin 2,
      ‖InfoGeometry.OperatorAlgebra.PeirceSpine.comm (Matrix.diagonal (threeSiteCutoff b))
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm
          (Matrix.diagonal (threeSiteCutoff b)) M)‖ ≤
        Real.sqrt ((3 / 5 : ℝ) ^ 4 * 3 * ‖M‖ ^ 2) := by
    intro b
    have h := diagonal_double_comm_l2_norm_le_card_mul_lipschitz_bound
      (threeSiteCutoff b) threeSitePathDist M (3 / 5) 1 (by norm_num) (by norm_num)
      (threeSiteCutoff_lipschitz b) hRange
    simpa using h
  have hIMS := ims_matrix_l2_localization_norm_le_card_mul_uniform_bound
    (fun b : Fin 2 => Matrix.diagonal (threeSiteCutoff b)) M
    threeSiteCutoff_partition _ hLocal
  simpa using hIMS

end ThreeSiteCutoffInstance

end HilbertOperatorIMS

/-! ### Concrete two-site open Majorana chain

The following finite matrix instance distinguishes the physical outer zero
modes from the artificial cut through a bulk dimer. With the owner convention
`N₊ = P A (1-P)` and `N₋ = (1-P) A P`, the collar product is `N₊N₋ = -P`
for a skew bond of unit strength; the restoring term in the square-first
operator is `-N₊N₋ = +P`. -/

section TwoSiteOpenMajoranaChain

/-- Generic square-first decomposition for a matrix compression. Inserting
`P + (1 - P) = 1` between the two factors of `A` separates the path that stays
inside the projected subspace from the one-hop-out-and-return collar term. -/
theorem matrix_square_first_collar_decomposition
    {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Ring K]
    (P A : Matrix n n K) (hP : P * P = P) :
    P * (-(A * A)) * P =
      -((P * A * P) * (P * A * P)) -
        (P * A * (1 - P)) * ((1 - P) * A * P) := by
  have hPleft : ∀ Z : Matrix n n K, P * (P * Z) = P * Z := by
    intro Z
    rw [← mul_assoc, hP]
  noncomm_ring [hP, hPleft]

private def twoSiteOpenMajoranaA {K : Type*} [CommRing K] :
    Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 0;
    0, 0, 1, 0;
    0, -1, 0, 0;
    0, 0, 0, 0]

private def twoSiteCutProjector {K : Type*} [CommRing K] :
    Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]

private def twoSiteCollarProjector {K : Type*} [CommRing K] :
    Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1]

private def twoSiteIdentity {K : Type*} [CommRing K] :
    Matrix (Fin 4) (Fin 4) K := 1

private def twoSiteBoundaryResidual {K : Type*} [CommRing K] :
    Matrix (Fin 4) (Fin 4) K :=
  !![(-1 : K), 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, -1]

/-- Exact finite `4 × 4` open-chain calculation. The inter-site dimer couples
Majoranas `c₂,c₃`, while `c₁,c₄` are outer zero modes. Cutting to `c₂` alone
annihilates the truncated bond, but square-first compression of `-A²-I`
is zero because the collar return restores the missing unit term. These are
matrix identities over a commutative ring, not a thermodynamic-limit claim. -/
theorem twoSiteOpenMajorana_squareFirst_collar_healing
    {K : Type*} [CommRing K] :
    let A : Matrix (Fin 4) (Fin 4) K := twoSiteOpenMajoranaA
    let P : Matrix (Fin 4) (Fin 4) K := twoSiteCutProjector
    let Q : Matrix (Fin 4) (Fin 4) K := twoSiteCollarProjector
    let IdM : Matrix (Fin 4) (Fin 4) K := twoSiteIdentity
    let Residual : Matrix (Fin 4) (Fin 4) K := twoSiteBoundaryResidual
    A.transpose = -A ∧
    -(A * A) - IdM = Residual ∧
    P * A * P = 0 ∧
    (P * A * Q) * (Q * A * P) = -P ∧
    (P * (-(A * A)) * P = P ∧
      P * (-(A * A) - IdM) * P = 0) ∧
    P * Residual * P = 0 ∧
    -((P * A * P) * (P * A * P)) - P = -P := by
  intro A P Q IdM Residual
  have hCollarQ : (P * A * Q) * (Q * A * P) = -P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, P, Q, twoSiteOpenMajoranaA, twoSiteCutProjector,
        twoSiteCollarProjector, Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, twoSiteOpenMajoranaA, Matrix.transpose_apply,
        Matrix.neg_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, IdM, Residual, twoSiteOpenMajoranaA, twoSiteIdentity,
        twoSiteBoundaryResidual, Matrix.sub_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, P, twoSiteOpenMajoranaA, twoSiteCutProjector,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · exact hCollarQ
  · have hPid : P * P = P := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, twoSiteCutProjector, Matrix.mul_apply, Fin.sum_univ_succ]
    have hCut : P * A * P = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, P, twoSiteOpenMajoranaA, twoSiteCutProjector,
          Matrix.mul_apply, Fin.sum_univ_succ]
    have hQ : Q = 1 - P := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, Q, twoSiteCutProjector, twoSiteCollarProjector,
          Matrix.sub_apply]
    have hCollar : (P * A * (1 - P)) * ((1 - P) * A * P) = -P := by
      simpa only [hQ] using hCollarQ
    have hdecomp := matrix_square_first_collar_decomposition P A hPid
    rw [hCut, hCollar] at hdecomp
    have hSquare : P * (-(A * A)) * P = P := by simpa using hdecomp
    have hIdP : P * IdM * P = P := by
      simpa [IdM, twoSiteIdentity] using hPid
    refine ⟨hSquare, ?_⟩
    calc
      P * (-(A * A) - IdM) * P =
          P * (-(A * A)) * P - P * IdM * P := by noncomm_ring
      _ = P - P := by rw [hSquare, hIdP]
      _ = 0 := sub_self P
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [P, Residual, twoSiteCutProjector, twoSiteBoundaryResidual]
  · have hCut : P * A * P = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, P, twoSiteOpenMajoranaA, twoSiteCutProjector,
          Matrix.mul_apply, Fin.sum_univ_succ]
    rw [hCut]
    simp

/-- The two boundary Majorana coordinate vectors lie in the kernel of the
finite open-chain matrix. This is the explicit zero-mode statement behind
the two negative diagonal entries of `-A² - I` above. -/
theorem twoSiteOpenMajorana_boundary_zero_modes
    {K : Type*} [CommRing K] :
    (twoSiteOpenMajoranaA : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (fun i : Fin 4 => if i = 0 then (1 : K) else 0) = 0 ∧
    (twoSiteOpenMajoranaA : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (fun i : Fin 4 => if i = 3 then (1 : K) else 0) = 0 := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [twoSiteOpenMajoranaA, Matrix.mulVec, dotProduct]

/-- The open-chain matrix is singular over every commutative ring: its first
column vanishes because the first boundary Majorana is uncoupled. This uses
Mathlib's determinant criterion for a zero column. -/
theorem twoSiteOpenMajorana_det_zero
    {K : Type*} [CommRing K] :
    Matrix.det (twoSiteOpenMajoranaA : Matrix (Fin 4) (Fin 4) K) = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  fin_cases i <;> simp [twoSiteOpenMajoranaA]

/-- The canonical Pfaffian owner's sweet-spot matrix uses bond strength `2`;
it is exactly twice the unit-bond matrix used in the collar calculation. -/
theorem twoSiteOpenMajorana_matches_pfaffian_sweet_spot :
    InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
        0 1 1 =
      (2 : ℝ) •
        (twoSiteOpenMajoranaA : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4,
      twoSiteOpenMajoranaA, Matrix.smul_apply]

/-- The repository's Kitaev Majorana matrix is the standard skew `4 × 4`
matrix with upper-triangular coordinates
`(μ, 0, t - Δ, t + Δ, 0, μ)`. -/
theorem kitaevMajoranaMatrix4_eq_standard_skew4 (mu t delta : ℝ) :
    InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
        mu t delta =
      InfoGeometry.Canonical.Pfaffian.skew4 mu 0 (t - delta) (t + delta) 0 mu := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4,
      InfoGeometry.Canonical.Pfaffian.skew4]

/-- Transport of the standard four-dimensional Pfaffian determinant identity
to the repository's parameterized Kitaev Majorana matrix. -/
theorem kitaevMajoranaMatrix4_pfaffian_sq_eq_det (mu t delta : ℝ) :
    (InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.pfaffian4
      (InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
        mu t delta)) ^ 2 =
      (InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
        mu t delta).det := by
  rw [kitaevMajoranaMatrix4_eq_standard_skew4]
  calc
    _ = (InfoGeometry.Canonical.Pfaffian.pfaffian4
        mu 0 (t - delta) (t + delta) 0 mu) ^ 2 := by
          simp [InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.pfaffian4,
            InfoGeometry.Canonical.Pfaffian.skew4,
            InfoGeometry.Canonical.Pfaffian.pfaffian4]
    _ = (InfoGeometry.Canonical.Pfaffian.skew4
        mu 0 (t - delta) (t + delta) 0 mu).det :=
          InfoGeometry.Canonical.Pfaffian.pfaffian4_sq_eq_det
            mu 0 (t - delta) (t + delta) 0 mu

/-- The canonical sweet-spot matrix inherits the two uncoupled boundary
kernel vectors through the explicitly proved matrix scaling map. -/
theorem twoSitePfaffianSweetSpot_boundary_zero_modes :
    let A := InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
      (0 : ℝ) 1 1
    A *ᵥ (fun i : Fin 4 => if i = 0 then (1 : ℝ) else 0) = 0 ∧
    A *ᵥ (fun i : Fin 4 => if i = 3 then (1 : ℝ) else 0) = 0 := by
  intro A
  have h := twoSiteOpenMajorana_boundary_zero_modes (K := ℝ)
  dsimp only [A]
  rw [twoSiteOpenMajorana_matches_pfaffian_sweet_spot]
  constructor
  · rw [Matrix.smul_mulVec, h.1, smul_zero]
  · rw [Matrix.smul_mulVec, h.2, smul_zero]

/-- The same sweet-spot parameter has the zero Pfaffian certified by the
canonical Kitaev-chain owner. -/
theorem twoSiteOpenMajorana_sweet_spot_pfaffian_zero :
    InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.pfaffian4
        (InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
          0 1 1) = 0 :=
  InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.sweet_spot_pfaffian_zero 1

/-- At every sweet-spot coupling `μ = 0`, `t = Δ`, the canonical Majorana
matrix is singular. This follows from the transported Pfaffian-square identity
and the owner theorem for the sweet-spot Pfaffian. -/
theorem kitaevSweetSpot_determinant_zero (t : ℝ) :
    (InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
      0 t t).det = 0 := by
  rw [← kitaevMajoranaMatrix4_pfaffian_sq_eq_det]
  rw [InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.sweet_spot_pfaffian_zero]
  norm_num

/-- Closed determinant formula for the parameterized two-site Kitaev matrix,
obtained by composing its Pfaffian formula with `Pf(A)^2 = det(A)`. -/
theorem kitaevMajoranaMatrix4_det_formula (mu t delta : ℝ) :
    (InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
      mu t delta).det = (mu ^ 2 + (t ^ 2 - delta ^ 2)) ^ 2 := by
  rw [← kitaevMajoranaMatrix4_pfaffian_sq_eq_det,
    InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaev_pfaffian4_formula]

/-- The finite Majorana matrix is nonsingular exactly away from the Pfaffian
zero locus. This is an algebraic determinant criterion, not a spectral-gap
classification. -/
theorem kitaevMajoranaMatrix4_det_ne_zero_iff (mu t delta : ℝ) :
    (InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
      mu t delta).det ≠ 0 ↔ mu ^ 2 + (t ^ 2 - delta ^ 2) ≠ 0 := by
  rw [kitaevMajoranaMatrix4_det_formula]
  simp

/-- The matrix-algebra formulation of the same criterion: the finite Kitaev
matrix is invertible exactly away from the Pfaffian zero locus. -/
theorem kitaevMajoranaMatrix4_isUnit_iff_pfaffian_ne_zero (mu t delta : ℝ) :
    IsUnit (InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
      mu t delta) ↔ mu ^ 2 + (t ^ 2 - delta ^ 2) ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, kitaevMajoranaMatrix4_det_formula]
  simp [isUnit_iff_ne_zero]

/-- Exact finite-dimensional zero-mode criterion: a nonzero Majorana vector is
annihilated by the Kitaev matrix exactly on the Pfaffian-zero parameter locus.
The equivalence uses Mathlib's determinant/kernel theorem for square matrices. -/
theorem kitaevMajoranaMatrix4_has_nonzero_kernel_iff_pfaffian_zero (mu t delta : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧
      InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
        mu t delta *ᵥ v = 0) ↔
      mu ^ 2 + (t ^ 2 - delta ^ 2) = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff, kitaevMajoranaMatrix4_det_formula]
  simp

/-- For a real transpose-skew matrix, the quadratic form of `-A^2` is the
squared Euclidean norm of `A v`. This is a finite-dimensional identity; no
locality, spectral-gap bound, or infinite-volume conclusion is assumed. -/
theorem neg_square_quadratic_form_eq_norm_sq
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hA : A.transpose = -A) (v : ι → ℝ) :
    dotProduct v ((-(A * A)) *ᵥ v) = dotProduct (A *ᵥ v) (A *ᵥ v) := by
  have hA2 : (A * A) *ᵥ v = A *ᵥ (A *ᵥ v) :=
    (Matrix.mulVec_mulVec v A A).symm
  have h : dotProduct v (A *ᵥ (A *ᵥ v)) =
      - dotProduct (A *ᵥ v) (A *ᵥ v) := by
    calc
      dotProduct v (A *ᵥ (A *ᵥ v)) = dotProduct (A.vecMul v) (A *ᵥ v) :=
        Matrix.dotProduct_mulVec v A (A *ᵥ v)
      _ = dotProduct (A.transpose *ᵥ v) (A *ᵥ v) := by
        rw [← Matrix.mulVec_transpose]
      _ = dotProduct ((-A) *ᵥ v) (A *ᵥ v) := by rw [hA]
      _ = - dotProduct (A *ᵥ v) (A *ᵥ v) := by
        rw [Matrix.neg_mulVec, neg_dotProduct]
  calc
    dotProduct v ((-(A * A)) *ᵥ v) = - dotProduct v ((A * A) *ᵥ v) := by
      rw [Matrix.neg_mulVec, dotProduct_neg]
    _ = - dotProduct v (A *ᵥ (A *ᵥ v)) := by rw [hA2]
    _ = dotProduct (A *ᵥ v) (A *ᵥ v) := by rw [h, neg_neg]

/-- A real transpose-skew matrix has positive-semidefinite negative square.
This is the Mathlib Gram-matrix result `Aᵀ A ≥ 0`, transported through
`Aᵀ = -A`. -/
theorem neg_square_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.transpose = -A) : Matrix.PosSemidef (-(A * A)) := by
  have hgram : Matrix.PosSemidef (Aᴴ * (1 : Matrix ι ι ℝ) * A) :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same Matrix.PosSemidef.one A
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hA] using hgram

/-- Congruence by a real matrix preserves positive semidefiniteness. This is
Mathlib's matrix Gram/congruence theorem specialized from `Bᴴ * M * B` to
`Bᵀ * M * B`. -/
theorem posSemidef_transpose_compression
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M P : Matrix ι ι ℝ) (hM : Matrix.PosSemidef M)
    (hP : P.transpose = P) : Matrix.PosSemidef (P * M * P) := by
  have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hM P
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hP] using h

/-- The square-first compression of a real skew matrix remains positive
semidefinite whenever the compression matrix is a symmetric idempotent or,
more generally, any symmetric matrix. -/
theorem neg_square_compression_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℝ) (hA : A.transpose = -A)
    (hP : P.transpose = P) :
    Matrix.PosSemidef (P * (-(A * A)) * P) := by
  exact posSemidef_transpose_compression (-(A * A)) P
    (neg_square_posSemidef A hA) hP

/-- The quadratic energy of `-A^2` vanishes precisely on the kernel of a
real transpose-skew matrix. -/
theorem neg_square_quadratic_form_eq_zero_iff_kernel
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hA : A.transpose = -A) (v : ι → ℝ) :
    dotProduct v ((-(A * A)) *ᵥ v) = 0 ↔ A *ᵥ v = 0 := by
  rw [neg_square_quadratic_form_eq_norm_sq A hA v,
    dotProduct_self_eq_zero]

/-- The parameterized two-site Kitaev Majorana matrix inherits the generic
nonnegative `-A²` quadratic-form identity from its canonical skew-symmetry
theorem. -/
theorem kitaevMajoranaMatrix4_neg_square_energy_identity (mu t delta : ℝ)
    (v : Fin 4 → ℝ) :
    let A := InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
      mu t delta
    dotProduct v ((-(A * A)) *ᵥ v) = dotProduct (A *ᵥ v) (A *ᵥ v) := by
  dsimp
  exact neg_square_quadratic_form_eq_norm_sq _
    (InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4_skew_symmetric
      mu t delta) v

/-- The negative square of the parameterized Kitaev Majorana matrix is
positive semidefinite as a real `4 × 4` matrix. -/
theorem kitaevMajoranaMatrix4_neg_square_posSemidef (mu t delta : ℝ) :
    Matrix.PosSemidef
      (-(InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
        mu t delta *
        InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4
          mu t delta)) := by
  exact neg_square_posSemidef _
    (InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian.kitaevMajoranaMatrix4_skew_symmetric
      mu t delta)

/-- The finite two-site square-first interior compression is positive
semidefinite by Mathlib's congruence theorem. The separate exact identity
above sharpens this to equality with the rank-one cut projector. -/
theorem twoSiteOpenMajorana_squareFirst_compression_posSemidef :
    Matrix.PosSemidef
      (twoSiteCutProjector *
        (-(twoSiteOpenMajoranaA * twoSiteOpenMajoranaA)) *
        twoSiteCutProjector : Matrix (Fin 4) (Fin 4) ℝ) := by
  apply neg_square_compression_posSemidef
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twoSiteOpenMajoranaA, Matrix.transpose_apply, Matrix.neg_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twoSiteCutProjector, Matrix.transpose_apply]

end TwoSiteOpenMajoranaChain

/-! ## §7. Stage $\mathfrak{KL}_6$: Kitaev's Three Spectrum Principles (Invertibility, Block-Swap Commutativity, and Softness / Lipschitz Diagonal Restriction) -/

/-- **Stage $\mathfrak{KL}_6$ (`kl6_kitaev_three_spectrum_principles_invertibility_swap_softness`) —
Kitaev's Three Spectrum Principles (`01:00:27 – 01:11:51`)**:
1. **Principle 1 (Invertibility / Anticommuting Rotor Spectral-Window Preservation)**:
   - For any anticommuting $X, Y \in B$ (`anticomm X Y = 0`) in an associative $\mathbb{R}$-algebra `B`,
     $(\cos\theta \bullet X + \sin\theta \bullet Y)^2 = (\cos\theta)^2 \bullet X^2 + (\sin\theta)^2 \bullet Y^2$.
   - If $a^2 \le \lambda_X \le b^2$ and $a^2 \le \lambda_Y \le b^2$, then for every $\theta \in \mathbb{R}$,
     the interpolated square $\lambda(\theta) = (\cos\theta)^2 \lambda_X + (\sin\theta)^2 \lambda_Y$
     satisfies the **exact same spectral gap bounds** $a^2 \le \lambda(\theta) \le b^2$.
2. **Principle 2 (Block-Swap Commutativity $A \oplus B \sim B \oplus A$)**:
   Over any commutative ring `R`, the orthogonal block-swap matrix
   $S = \begin{pmatrix} 0 & I \\ -I & 0 \end{pmatrix}$ satisfies $S * S^\top = 1$, $S^\top * S = 1$, and
   $$S * \begin{pmatrix} A & 0 \\ 0 & D \end{pmatrix} * S^\top = \begin{pmatrix} D & 0 \\ 0 & A \end{pmatrix}.$$
3. **Principle 3 (Softness / Lipschitz Diagonal Restriction)**:
   If $|u_j - u_k| \le L \cdot d_{jk}$, $0 \le L$, and $d_{jk} \le r$, then $|u_j - u_k| \le L \cdot r$. -/
theorem kl6_kitaev_three_spectrum_principles_invertibility_swap_softness
    {B : Type*} [Ring B] [Module ℝ B] [IsScalarTower ℝ B B] [SMulCommClass ℝ B B]
    (X Y : B) (hAnti : InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm X Y = 0) (θ : ℝ)
    (a b lamX lamY : ℝ) (haX : a ^ 2 ≤ lamX) (hbX : lamX ≤ b ^ 2)
    (haY : a ^ 2 ≤ lamY) (hbY : lamY ≤ b ^ 2)
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (A D : Matrix n n R)
    (u_j u_k L d_jk r : ℝ) (hL : 0 ≤ L) (hLip : |u_j - u_k| ≤ L * d_jk) (hr : d_jk ≤ r) :
    ((Real.cos θ • X + Real.sin θ • Y) * (Real.cos θ • X + Real.sin θ • Y) =
      (Real.cos θ ^ 2) • (X * X) + (Real.sin θ ^ 2) • (Y * Y) ∧
     a ^ 2 ≤ Real.cos θ ^ 2 * lamX + Real.sin θ ^ 2 * lamY ∧
     Real.cos θ ^ 2 * lamX + Real.sin θ ^ 2 * lamY ≤ b ^ 2) ∧
    (let S := Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R)
     S * S.transpose = 1 ∧
     S.transpose * S = 1 ∧
     S * Matrix.fromBlocks A (0 : Matrix n n R) (0 : Matrix n n R) D * S.transpose =
       Matrix.fromBlocks D (0 : Matrix n n R) (0 : Matrix n n R) A) ∧
    (|u_j - u_k| ≤ L * r) := by
  have hRotSq :
      (Real.cos θ • X + Real.sin θ • Y) * (Real.cos θ • X + Real.sin θ • Y) =
        (Real.cos θ ^ 2) • (X * X) + (Real.sin θ ^ 2) • (Y * Y) := by
    have hAnti' : X * Y + Y * X = 0 := hAnti
    rw [add_mul, mul_add, mul_add,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_comm (Real.sin θ) (Real.cos θ),
      ← add_assoc, add_assoc ((Real.cos θ * Real.cos θ) • (X * X)),
      ← smul_add, hAnti', smul_zero, add_zero,
      ← sq (Real.cos θ), ← sq (Real.sin θ)]
  have hCosNonneg : 0 ≤ Real.cos θ ^ 2 := sq_nonneg (Real.cos θ)
  have hSinNonneg : 0 ≤ Real.sin θ ^ 2 := sq_nonneg (Real.sin θ)
  have hTrigSum : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hLow : a ^ 2 ≤ Real.cos θ ^ 2 * lamX + Real.sin θ ^ 2 * lamY := by
    have h1 : Real.cos θ ^ 2 * a ^ 2 ≤ Real.cos θ ^ 2 * lamX :=
      mul_le_mul_of_nonneg_left haX hCosNonneg
    have h2 : Real.sin θ ^ 2 * a ^ 2 ≤ Real.sin θ ^ 2 * lamY :=
      mul_le_mul_of_nonneg_left haY hSinNonneg
    calc
      a ^ 2 = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * a ^ 2 := by rw [hTrigSum, one_mul]
      _ = Real.cos θ ^ 2 * a ^ 2 + Real.sin θ ^ 2 * a ^ 2 := by ring
      _ ≤ Real.cos θ ^ 2 * lamX + Real.sin θ ^ 2 * lamY := add_le_add h1 h2
  have hHigh : Real.cos θ ^ 2 * lamX + Real.sin θ ^ 2 * lamY ≤ b ^ 2 := by
    have h1 : Real.cos θ ^ 2 * lamX ≤ Real.cos θ ^ 2 * b ^ 2 :=
      mul_le_mul_of_nonneg_left hbX hCosNonneg
    have h2 : Real.sin θ ^ 2 * lamY ≤ Real.sin θ ^ 2 * b ^ 2 :=
      mul_le_mul_of_nonneg_left hbY hSinNonneg
    calc
      Real.cos θ ^ 2 * lamX + Real.sin θ ^ 2 * lamY ≤
          Real.cos θ ^ 2 * b ^ 2 + Real.sin θ ^ 2 * b ^ 2 := add_le_add h1 h2
      _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * b ^ 2 := by ring
      _ = b ^ 2 := by rw [hTrigSum, one_mul]
  have hSwap :
      let S := Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R)
      S * S.transpose = 1 ∧
      S.transpose * S = 1 ∧
      S * Matrix.fromBlocks A (0 : Matrix n n R) (0 : Matrix n n R) D * S.transpose =
        Matrix.fromBlocks D (0 : Matrix n n R) (0 : Matrix n n R) A := by
    dsimp only
    rw [Matrix.fromBlocks_transpose]
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.fromBlocks_multiply]
      simp [Matrix.fromBlocks_one]
    · rw [Matrix.fromBlocks_multiply]
      simp [Matrix.fromBlocks_one]
    · rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp
  have hSoft : |u_j - u_k| ≤ L * r :=
    le_trans hLip (mul_le_mul_of_nonneg_left hr hL)
  exact ⟨⟨hRotSq, hLow, hHigh⟩, hSwap, hSoft⟩

/-- **Stage $\mathfrak{KS}_5$ (`kitaev_invertibility_block_rotor_gap_preservation`) —
Kitaev's Universal Block-Matrix Invertibility Homotopy $A \oplus (-A) \sim A_0 \oplus (-A_0)$**:
Over any commutative ring `[CommRing R]` and finite index type `n` (`[Fintype n] [DecidableEq n]`),
for **any** matrix `A : Matrix n n R` (with **zero commutativity assumptions on `A`**), let
$$X(A) = \begin{pmatrix} A & 0 \\ 0 & -A \end{pmatrix}, \qquad
  Y = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}.$$
Then:
1. $X(A)^\top = -X(A) \iff A^\top = -A$, $Y^\top = -Y$, and $Y * Y = -1$,
2. **Universal Anticommutation**: $X(A) * Y + Y * X(A) = 0$,
3. **Exact Rotor Square & Skew-Symmetry Preservation**:
   For any scalars $c, s \in R$ (such as $c = \cos\theta, s = \sin\theta$), the interpolated matrix
   $X(c, s) = \mathrm{Matrix.fromBlocks}\;(c \bullet A)\;(s \bullet 1)\;(-(s \bullet 1))\;(-(c \bullet A))$
   satisfies:
   - If $A^\top = -A$, then $X(c, s)^\top = -X(c, s)$,
   - $- (X(c, s) * X(c, s)) = \mathrm{Matrix.fromBlocks}\;((c^2) \bullet (-(A * A)) + (s^2) \bullet 1)\;0\;0\;((c^2) \bullet (-(A * A)) + (s^2) \bullet 1)$. -/
theorem kitaev_invertibility_block_rotor_gap_preservation
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (A : Matrix n n R) (c s : R) :
    let XA := Matrix.fromBlocks A (0 : Matrix n n R) (0 : Matrix n n R) (-A)
    let Y := Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R)
    let Xcs := Matrix.fromBlocks (c • A) (s • (1 : Matrix n n R))
      (-(s • (1 : Matrix n n R))) (-(c • A))
    ((XA.transpose = -XA ↔ A.transpose = -A) ∧
     Y.transpose = -Y ∧
     Y * Y = -1) ∧
    (XA * Y + Y * XA = 0) ∧
    ((A.transpose = -A → Xcs.transpose = -Xcs) ∧
     -(Xcs * Xcs) =
       Matrix.fromBlocks ((c ^ 2) • (-(A * A)) + (s ^ 2) • (1 : Matrix n n R))
         (0 : Matrix n n R) (0 : Matrix n n R)
         ((c ^ 2) • (-(A * A)) + (s ^ 2) • (1 : Matrix n n R))) := by
  dsimp only
  have hXAT :
      (Matrix.fromBlocks A (0 : Matrix n n R) (0 : Matrix n n R) (-A)).transpose =
        -Matrix.fromBlocks A (0 : Matrix n n R) (0 : Matrix n n R) (-A) ↔
      A.transpose = -A := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg, Matrix.fromBlocks_inj]
    constructor
    · rintro ⟨h, _, _, _⟩; exact h
    · intro h
      refine ⟨h, by simp, by simp, ?_⟩
      rw [Matrix.transpose_neg, h]
  have hYT :
      (Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R)).transpose =
        -Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R) := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
    simp
  have hYSq :
      Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R) *
        Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R) = -1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have hAnti :
      Matrix.fromBlocks A (0 : Matrix n n R) (0 : Matrix n n R) (-A) *
          Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R) +
        Matrix.fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R) *
          Matrix.fromBlocks A (0 : Matrix n n R) (0 : Matrix n n R) (-A) = 0 := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
    simp [Matrix.fromBlocks_zero]
  have hXcsT :
      A.transpose = -A →
        (Matrix.fromBlocks (c • A) (s • (1 : Matrix n n R))
          (-(s • (1 : Matrix n n R))) (-(c • A))).transpose =
        -Matrix.fromBlocks (c • A) (s • (1 : Matrix n n R))
          (-(s • (1 : Matrix n n R))) (-(c • A)) := by
    intro hA
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
    simp [hA]
  have hXcsSq :
      -(Matrix.fromBlocks (c • A) (s • (1 : Matrix n n R))
          (-(s • (1 : Matrix n n R))) (-(c • A)) *
        Matrix.fromBlocks (c • A) (s • (1 : Matrix n n R))
          (-(s • (1 : Matrix n n R))) (-(c • A))) =
      Matrix.fromBlocks ((c ^ 2) • (-(A * A)) + (s ^ 2) • (1 : Matrix n n R))
        (0 : Matrix n n R) (0 : Matrix n n R)
        ((c ^ 2) • (-(A * A)) + (s ^ 2) • (1 : Matrix n n R)) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]
    congr 1
    · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.mul_neg, Matrix.one_mul,
        ← sq c, ← sq s, smul_neg]
      abel
    · simp [smul_smul, mul_comm s c]
    · simp [smul_smul, mul_comm s c]
    · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.one_mul,
        ← sq c, ← sq s, smul_neg]
      abel
  exact ⟨⟨hXAT, hYT, hYSq⟩, hAnti, ⟨hXcsT, hXcsSq⟩⟩

/--
**Flat-band specialization of the block rotor formula.** If `A * A = -1`, the rotor
with coefficients `cos θ` and `sin θ` remains exactly unit-gapped:
`-(Xcs * Xcs) = 1`. This uses the real trigonometric identity
`cos² θ + sin² θ = 1`; the general rotor formula above does not imply this
conclusion without the flat-band hypothesis.
-/
theorem kitaev_flat_complex_structure_rotor_remains_unit_gapped
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (θ : ℝ) (hA : A * A = -1) :
    let Xcs := Matrix.fromBlocks (Real.cos θ • A) (Real.sin θ • (1 : Matrix n n ℝ))
      (-(Real.sin θ • (1 : Matrix n n ℝ))) (-(Real.cos θ • A));
    -(Xcs * Xcs) = (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  dsimp only
  have hRotor := (kitaev_invertibility_block_rotor_gap_preservation A
    (Real.cos θ) (Real.sin θ)).2.2.2
  rw [hA] at hRotor
  simp only [neg_neg] at hRotor
  have hEntry : Real.cos θ ^ 2 • (1 : Matrix n n ℝ) +
      Real.sin θ ^ 2 • (1 : Matrix n n ℝ) = 1 := by
    rw [← add_smul, Real.cos_sq_add_sin_sq, one_smul]
  rw [hEntry, Matrix.fromBlocks_one] at hRotor
  exact hRotor

/-- The finite-dimensional real path from the doubled system `A ⊕ (-A)` to the
constant decoupler. Its continuity is part of the homotopy data, rather than
an inference from the pointwise algebraic rotor identity. -/
noncomputable def kitaevBlockRotorPath
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (θ : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Real.cos θ • Matrix.fromBlocks A (0 : Matrix n n ℝ) (0 : Matrix n n ℝ) (-A) +
    Real.sin θ • Matrix.fromBlocks (0 : Matrix n n ℝ) (1 : Matrix n n ℝ)
      (-1 : Matrix n n ℝ) (0 : Matrix n n ℝ)

/-- The Kitaev block-rotor path is continuous in the finite matrix topology. -/
theorem kitaevBlockRotorPath_continuous
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    Continuous (kitaevBlockRotorPath A) := by
  unfold kitaevBlockRotorPath
  exact (Real.continuous_cos.smul continuous_const).add
    (Real.continuous_sin.smul continuous_const)

/-- The continuous path has the stated doubled-system and decoupler endpoints. -/
theorem kitaevBlockRotorPath_endpoints
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    kitaevBlockRotorPath A 0 =
        Matrix.fromBlocks A (0 : Matrix n n ℝ) (0 : Matrix n n ℝ) (-A) ∧
      kitaevBlockRotorPath A (Real.pi / 2) =
        Matrix.fromBlocks (0 : Matrix n n ℝ) (1 : Matrix n n ℝ)
          (-1 : Matrix n n ℝ) (0 : Matrix n n ℝ) := by
  constructor
  · simp [kitaevBlockRotorPath]
  · simp [kitaevBlockRotorPath]

/-- The continuous path is exactly the block rotor used in the square formula. -/
theorem kitaevBlockRotorPath_eq_blockRotor
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (θ : ℝ) :
    kitaevBlockRotorPath A θ =
      Matrix.fromBlocks (Real.cos θ • A) (Real.sin θ • (1 : Matrix n n ℝ))
        (-(Real.sin θ • (1 : Matrix n n ℝ))) (-(Real.cos θ • A)) := by
  simp [kitaevBlockRotorPath, Matrix.fromBlocks_smul, Matrix.fromBlocks_add,
    smul_neg]

/-- Carrier of finite real matrices that are skew-symmetric and exactly
unit-gapped in the sense `-M² = 1`. -/
abbrev FlatMajoranaMatrix (n : Type*) [Fintype n] [DecidableEq n] :=
  { M : Matrix (n ⊕ n) (n ⊕ n) ℝ // M.transpose = -M ∧ -(M * M) = 1 }

/-- The skew, exactly unit-gapped locus is orthogonal: `Mᵀ M = 1` follows
from `Mᵀ = -M` and `-(M M) = 1`. These are concrete orthogonal complex
structures on the finite real coordinate space. -/
theorem flatMajoranaMatrix_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n] (M : FlatMajoranaMatrix n) :
    M.val.transpose * M.val = 1 := by
  calc
    M.val.transpose * M.val = (-M.val) * M.val := by rw [M.property.1]
    _ = -(M.val * M.val) := by simp
    _ = 1 := M.property.2

/-- The Kitaev rotor as a continuous map into the flat skew-Majorana locus.
The hypotheses state that the starting matrix is a skew complex structure. -/
noncomputable def kitaevFlatMajoranaRotorPath
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hAT : A.transpose = -A) (hA2 : A * A = -1) :
    C(ℝ, FlatMajoranaMatrix n) :=
  ⟨fun θ => ⟨kitaevBlockRotorPath A θ, by
      rw [kitaevBlockRotorPath_eq_blockRotor]
      have hRotor := (kitaev_invertibility_block_rotor_gap_preservation A
        (Real.cos θ) (Real.sin θ)).2.2
      exact ⟨hRotor.1 hAT,
        kitaev_flat_complex_structure_rotor_remains_unit_gapped A θ hA2⟩⟩,
    by
      apply Continuous.subtype_mk
      exact kitaevBlockRotorPath_continuous A⟩

/-- The flat-locus path starts at the doubled pair and ends at the constant
decoupler; `Subtype.val` records the underlying concrete matrices. -/
theorem kitaevFlatMajoranaRotorPath_endpoints
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hAT : A.transpose = -A) (hA2 : A * A = -1) :
    (kitaevFlatMajoranaRotorPath A hAT hA2 0).val =
        Matrix.fromBlocks A (0 : Matrix n n ℝ) (0 : Matrix n n ℝ) (-A) ∧
      (kitaevFlatMajoranaRotorPath A hAT hA2 (Real.pi / 2)).val =
        Matrix.fromBlocks (0 : Matrix n n ℝ) (1 : Matrix n n ℝ)
          (-1 : Matrix n n ℝ) (0 : Matrix n n ℝ) := by
  have hEnd := kitaevBlockRotorPath_endpoints A
  have hZero : (kitaevFlatMajoranaRotorPath A hAT hA2 0).val = kitaevBlockRotorPath A 0 := rfl
  have hHalfPi :
      (kitaevFlatMajoranaRotorPath A hAT hA2 (Real.pi / 2)).val =
        kitaevBlockRotorPath A (Real.pi / 2) := rfl
  rw [hZero, hHalfPi]
  exact ⟨hEnd.1, hEnd.2⟩

/-- Every point along the flat rotor path is an orthogonal complex structure:
it is skew, its square is `-1`, and therefore its transpose times itself is
the identity. -/
theorem kitaevFlatMajoranaRotorPath_point_is_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hAT : A.transpose = -A) (hA2 : A * A = -1) (θ : ℝ) :
    (kitaevFlatMajoranaRotorPath A hAT hA2 θ).val.transpose *
        (kitaevFlatMajoranaRotorPath A hAT hA2 θ).val = 1 := by
  exact flatMajoranaMatrix_orthogonal _

/-- The doubled input `A ⊕ (-A)` as a point of the flat skew-Majorana locus.
The hypotheses are exactly skew-symmetry and the flat-band identity `A²=-1`. -/
noncomputable def kitaevDoubledFlatMajorana
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hAT : A.transpose = -A) (hA2 : A * A = -1) :
    FlatMajoranaMatrix n := by
  let X := Matrix.fromBlocks A (0 : Matrix n n ℝ) (0 : Matrix n n ℝ) (-A)
  have hRotor := (kitaev_invertibility_block_rotor_gap_preservation A 1 0).2.2
  refine ⟨X, ?_⟩
  constructor
  · simpa [X] using hRotor.1 hAT
  · simpa [X, hA2] using hRotor.2

/-- The constant block decoupler in the same flat skew-Majorana locus. -/
noncomputable def kitaevDecouplerFlatMajorana
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hAT : A.transpose = -A) :
    FlatMajoranaMatrix n := by
  let Y := Matrix.fromBlocks (0 : Matrix n n ℝ) (1 : Matrix n n ℝ)
    (-1 : Matrix n n ℝ) (0 : Matrix n n ℝ)
  have hRotor := (kitaev_invertibility_block_rotor_gap_preservation A 0 1).2.2
  refine ⟨Y, ?_⟩
  constructor
  · simpa [Y] using hRotor.1 hAT
  · simpa [Y] using hRotor.2

/-- Mathlib `Path` realizing the finite-dimensional Kitaev null-homotopy
inside the flat skew-Majorana locus. This is the path for a fixed flat matrix;
it is not the separate spectrum-level equivalence `A_d ≃ Ω A_{d+1}`. -/
noncomputable def kitaevFlatMajoranaNullPath
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hAT : A.transpose = -A) (hA2 : A * A = -1) :
    Path (kitaevDoubledFlatMajorana A hAT hA2)
      (kitaevDecouplerFlatMajorana A hAT) := by
  let γ : C(unitInterval, FlatMajoranaMatrix n) := ⟨
    fun t => kitaevFlatMajoranaRotorPath A hAT hA2 (Real.pi / 2 * t),
    (kitaevFlatMajoranaRotorPath A hAT hA2).continuous.comp
      (continuous_const.mul continuous_subtype_val)⟩
  refine ⟨γ, ?_, ?_⟩
  · apply Subtype.ext
    have hEnd := (kitaevFlatMajoranaRotorPath_endpoints A hAT hA2).1
    change (kitaevFlatMajoranaRotorPath A hAT hA2
      (Real.pi / 2 * (0 : unitInterval))).val = _
    simpa [kitaevDoubledFlatMajorana] using hEnd
  · apply Subtype.ext
    have hEnd := (kitaevFlatMajoranaRotorPath_endpoints A hAT hA2).2
    change (kitaevFlatMajoranaRotorPath A hAT hA2
      (Real.pi / 2 * (1 : unitInterval))).val = _
    simpa [kitaevDecouplerFlatMajorana] using hEnd

/-- Endpoint theorem for the native Mathlib path object. -/
theorem kitaevFlatMajoranaNullPath_endpoints
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hAT : A.transpose = -A) (hA2 : A * A = -1) :
    (kitaevFlatMajoranaNullPath A hAT hA2 : unitInterval → FlatMajoranaMatrix n) 0 =
        kitaevDoubledFlatMajorana A hAT hA2 ∧
      (kitaevFlatMajoranaNullPath A hAT hA2 : unitInterval → FlatMajoranaMatrix n) 1 =
        kitaevDecouplerFlatMajorana A hAT := by
  exact ⟨(kitaevFlatMajoranaNullPath A hAT hA2).source',
    (kitaevFlatMajoranaNullPath A hAT hA2).target'⟩

/-- The map sending a flat Majorana matrix to its doubled pair `A ⊕ (-A)`. -/
noncomputable def kitaevDoubledFlatMajoranaMap
    {n : Type*} [Fintype n] [DecidableEq n] :
    C(FlatMajoranaMatrix n, FlatMajoranaMatrix (n ⊕ n)) := by
  refine ⟨fun M => kitaevDoubledFlatMajorana M.val M.property.1 ?_, ?_⟩
  · have h := congrArg Neg.neg M.property.2
    simpa using h
  · apply Continuous.subtype_mk
    have hA : Continuous (fun M : FlatMajoranaMatrix n => M.val) :=
      continuous_subtype_val
    simpa [kitaevDoubledFlatMajorana] using
      Continuous.matrix_fromBlocks hA
        (continuous_const : Continuous (fun _ : FlatMajoranaMatrix n => (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ)))
        (continuous_const : Continuous (fun _ : FlatMajoranaMatrix n => (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ)))
        hA.neg

/-- The constant map with value the finite-dimensional block decoupler. -/
noncomputable def kitaevDecouplerFlatMajoranaMap
    {n : Type*} [Fintype n] [DecidableEq n] :
    C(FlatMajoranaMatrix n, FlatMajoranaMatrix (n ⊕ n)) :=
  ⟨fun _ => kitaevDecouplerFlatMajorana 0 (by simp), continuous_const⟩

/-- Jointly continuous finite-dimensional null-homotopy of the doubled-system
map over the full flat-locus domain. This is stronger than choosing a path
separately for each input matrix; it still does not assert the spectrum-level
equivalence `A_d ≃ Ω A_{d+1}`. -/
noncomputable def kitaevFlatMajoranaLocusNullHomotopy
    {n : Type*} [Fintype n] [DecidableEq n] :
    ContinuousMap.Homotopy (kitaevDoubledFlatMajoranaMap (n := n))
      (kitaevDecouplerFlatMajoranaMap (n := n)) := by
  let θ : unitInterval × FlatMajoranaMatrix n → ℝ :=
    fun z => Real.pi / 2 * z.1
  let hθ : Continuous θ :=
    continuous_const.mul (continuous_subtype_val.comp continuous_fst)
  let hcos : Continuous (fun z => Real.cos (θ z)) := Real.continuous_cos.comp hθ
  let hsin : Continuous (fun z => Real.sin (θ z)) := Real.continuous_sin.comp hθ
  let hA : Continuous (fun z : unitInterval × FlatMajoranaMatrix n => z.2.val) :=
    continuous_subtype_val.comp continuous_snd
  let hTop : Continuous (fun z : unitInterval × FlatMajoranaMatrix n =>
      Matrix.fromBlocks (z.2.val) (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ)
        (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ) (-z.2.val)) :=
    Continuous.matrix_fromBlocks hA continuous_const continuous_const hA.neg
  let hBase : Continuous (fun _ : unitInterval × FlatMajoranaMatrix n =>
      Matrix.fromBlocks (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ) (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)
        (-1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ)) := continuous_const
  let hRotor : Continuous (fun z : unitInterval × FlatMajoranaMatrix n =>
      Real.cos (θ z) • Matrix.fromBlocks (z.2.val) (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ)
        (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ) (-z.2.val) +
        Real.sin (θ z) • Matrix.fromBlocks (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ)
          (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) (-1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)
          (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ)) :=
    (hcos.smul hTop).add (hsin.smul hBase)
  refine ⟨⟨fun z =>
    let M := z.2
    let hA2 : M.val * M.val = -1 := by
      have h := congrArg Neg.neg M.property.2
      simpa using h
    ⟨kitaevBlockRotorPath M.val (θ z), by
      rw [kitaevBlockRotorPath_eq_blockRotor]
      have hRotor := (kitaev_invertibility_block_rotor_gap_preservation M.val
        (Real.cos (θ z)) (Real.sin (θ z))).2.2
      exact ⟨hRotor.1 M.property.1,
        kitaev_flat_complex_structure_rotor_remains_unit_gapped M.val (θ z) hA2⟩⟩,
    by
      apply Continuous.subtype_mk
      simpa only [kitaevBlockRotorPath] using hRotor⟩,
    ?_, ?_⟩
  · intro M
    apply Subtype.ext
    have hEnd := kitaevBlockRotorPath_endpoints M.val
    simpa [θ, kitaevDoubledFlatMajoranaMap, kitaevDoubledFlatMajorana,
      Real.cos_zero, Real.sin_zero, Matrix.fromBlocks_smul] using hEnd.1
  · intro M
    apply Subtype.ext
    have hEnd := kitaevBlockRotorPath_endpoints M.val
    simpa [θ, kitaevDecouplerFlatMajoranaMap, kitaevDecouplerFlatMajorana,
      Real.cos_pi_div_two, Real.sin_pi_div_two,
      Matrix.fromBlocks_smul] using hEnd.2

/-- Kitaev's symmetrized diagonal restriction (`01:04:44 – 01:08:28`):
Given a site-indexed family of matrices `u : n → Matrix n n R`,
`(diagRestrict u) j k = u j j k + u k j k`. -/
def diagRestrict {n : Type*} {R : Type*} [Add R] (u : n → Matrix n n R) : Matrix n n R :=
  Matrix.of (fun j k => u j j k + u k j k)

/-- **Stages $\mathfrak{KS}_6\text{–}\mathfrak{KS}_7$ (`kitaev_soft_diagonal_restriction_and_dimer_loop_shift`) —
Symmetrized Diagonal Restriction Skew-Symmetry, $r$-Locality Preservation & Alternating Dimer Re-Pairing**:
1. **Symmetrized Diagonal Restriction Preserves Skew-Symmetry**:
   If every site matrix $u(p)$ is skew-symmetric ($\forall p,\; (u\;p)^\top = -u\;p$), then
   $(\mathrm{diagRestrict}\;u)^\top = -\mathrm{diagRestrict}\;u$.
2. **Symmetrized Diagonal Restriction Preserves $r$-Locality**:
   If $u(j)_{j k} = 0$ and $u(k)_{j k} = 0$ for separated sites $(j, k)$, then
   $\mathrm{diagRestrict}\;u\;j\;k = 0$.
3. **Constant Family Recovery**:
   If $u(p) = A$ for all $p$, then $\mathrm{diagRestrict}\;(fun\;\_ \Rightarrow A) = (2 : \mathbb{Z}) \bullet A$.
4. **Three-Term Reassociation and Cancellation**:
   In any associative ring `[Ring B]`, for arbitrary `e₁ e₂ e₃ A_op : B`, the two parenthesizations
   of `e₁*A_op*e₁ - e₂*A_op*e₂ + e₃*A_op*e₃` are equal; subtracting the last two terms from
   that sum leaves `e₁*A_op*e₁`. No idempotence, orthogonality, block decomposition, or topology
   is assumed or constructed by this algebraic identity. -/
theorem kitaev_soft_diagonal_restriction_and_dimer_loop_shift
    {n : Type*} {R : Type*} [CommRing R]
    (u : n → Matrix n n R) (hSkew : ∀ p : n, (u p).transpose = -u p)
    (j₀ k₀ : n) (hLocJ : u j₀ j₀ k₀ = 0) (hLocK : u k₀ j₀ k₀ = 0)
    (A_mat : Matrix n n R)
    {B : Type*} [Ring B] (e₁ e₂ e₃ A_op : B) :
    (diagRestrict u).transpose = -diagRestrict u ∧
    diagRestrict u j₀ k₀ = 0 ∧
    diagRestrict (fun _ : n => A_mat) = (2 : ℤ) • A_mat ∧
    ((e₁ * A_op * e₁ - e₂ * A_op * e₂) + e₃ * A_op * e₃ =
      e₁ * A_op * e₁ + (-(e₂ * A_op * e₂) + e₃ * A_op * e₃) ∧
     (e₁ * A_op * e₁ + (-(e₂ * A_op * e₂) + e₃ * A_op * e₃)) -
       (-(e₂ * A_op * e₂) + e₃ * A_op * e₃) = e₁ * A_op * e₁) := by
  have hSkewRestrict : (diagRestrict u).transpose = -diagRestrict u := by
    ext j k
    have hkj_k := congrArg (fun M : Matrix n n R => M j k) (hSkew k)
    have hkj_j := congrArg (fun M : Matrix n n R => M j k) (hSkew j)
    dsimp [Matrix.transpose_apply, Matrix.neg_apply] at hkj_k hkj_j
    dsimp [diagRestrict, Matrix.transpose_apply, Matrix.neg_apply]
    rw [hkj_k, hkj_j]
    ring
  have hLoc : diagRestrict u j₀ k₀ = 0 := by
    dsimp [diagRestrict]
    rw [hLocJ, hLocK, add_zero]
  have hConst : diagRestrict (fun _ : n => A_mat) = (2 : ℤ) • A_mat := by
    ext j k
    dsimp [diagRestrict]
    rw [two_zsmul]
  exact ⟨hSkewRestrict, hLoc, hConst, ⟨by abel, by abel⟩⟩

/-! ## §8. Stage $\mathfrak{KL}_7$: Finite Dimerization Identities and Bott-Residue Arithmetic -/

/-- **Stage $\mathfrak{KL}_7$ (`kl7_omega_spectrum_dimerization_switch_and_ko_d_minus_2_master_synthesis`) —
Finite Algebraic Bundle of Selected Kitaev Identities ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$)**:
Assembles selected previously proved finite/algebraic statements into one theorem. Despite the
historic declaration name, this result does not construct the spaces $A_d$, the suspension and
loop maps $F_d,G_d$, or prove an $\Omega$-spectrum or $KO_{d-2}$ classification:
1. **Acyclic 7-Stage Causal Poset ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_7$)**:
   `KitaevKOSpectrumStage.rank_injective` and `coverEdge_acyclic`.
2. **1D TFIM Bulk vs. Boundary Excitation Gap (`4 J` vs. `2 J`) & Paramagnetic Gap (`2 h`)**:
   `tfimIsingEnergy3 J ![1, -1, 1] - tfimIsingEnergy3 J ![1, 1, 1] = 4 * J` and
   `tfimIsingEnergy3 J ![-1, 1, 1] - tfimIsingEnergy3 J ![1, 1, 1] = 2 * J`.
3. **Centered Operator-Square Spectral Window & Bulk Disk Restriction $\Pi_{\tilde D}$**:
   `4 * (X_R - a_R ^ 2) * (b_R ^ 2 - X_R) = (b_R ^ 2 - a_R ^ 2) ^ 2 - (2 * X_R - (a_R ^ 2 + b_R ^ 2)) ^ 2`
   and `peirce11 P (-(A * A)) = -(peirce11 P A * peirce11 P A) - conePlus P A * coneMinus P A`.
4. **Noncommutative IMS Double-Commutator Localization Identity**:
   `(2 : ℤ) • M - (2 : ℤ) • (∑ b : ι, χ b * M * χ b) = ∑ b : ι, comm (χ b) (comm (χ b) M)`.
5. **Finite Dimerization Operator Laws (`pauli_dimerization_switch_operator_laws`) & Pfaffian Identity (`kitaev_pfaffian4_formula`)**:
   - Inter-cell dimer leaves the boundary Majorana $\gamma_0$ conserved (`[H_inter, γ₀] = 0`),
     whereas intra-cell dimerization has nonzero boundary commutator (`[H_intra, γ₀] = -2 γ₁ ≠ 0`),
   - 2-site Majorana Pfaffian $\mathrm{Pf}(A_4(\mu, t, \Delta)) = \mu^2 + (t^2 - \Delta^2)$ vanishes
     at the sweet spot $\mu = 0, t = \Delta$,
   - Mod-8 Bott periodicity shift $(d + 8 - 2 : \mathrm{ZMod}\;8) = (d - 2 : \mathrm{ZMod}\;8)$. -/
theorem kl7_omega_spectrum_dimerization_switch_and_ko_d_minus_2_master_synthesis
    (J : ℤ)
    {R : Type*} [CommRing R] (X_R a_R b_R : R)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A M : B)
    {ι : Type*} [Fintype ι] (χ : ι → B) (hPart : (∑ b : ι, χ b * χ b) = 1)
    (mu t delta : ℝ) (d : ZMod 8) :
    Function.Injective KitaevKOSpectrumStage.rank ∧
    (tfimIsingEnergy3 J ![1, -1, 1] - tfimIsingEnergy3 J ![1, 1, 1] = 4 * J ∧
     tfimIsingEnergy3 J ![-1, 1, 1] - tfimIsingEnergy3 J ![1, 1, 1] = 2 * J) ∧
    (4 * (X_R - a_R ^ 2) * (b_R ^ 2 - X_R) =
      (b_R ^ 2 - a_R ^ 2) ^ 2 - (2 * X_R - (a_R ^ 2 + b_R ^ 2)) ^ 2 ∧
     peirce11 P (-(A * A)) =
      -(peirce11 P A * peirce11 P A) - conePlus P A * coneMinus P A) ∧
    ((2 : ℤ) • M - (2 : ℤ) • (∑ b : ι, χ b * M * χ b) =
      ∑ b : ι, InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (χ b) M)) ∧
    (InfoGeometry.Quantum.KitaevChain.commutator pauliInterCellHamiltonian
        (InfoGeometry.Quantum.KitaevChain.pauliMajorana 0) = 0 ∧
     InfoGeometry.Quantum.KitaevChain.commutator pauliIntraCellHamiltonian
        (InfoGeometry.Quantum.KitaevChain.pauliMajorana 0) ≠ 0 ∧
     pfaffian4 (kitaevMajoranaMatrix4 mu t delta) = mu ^ 2 + (t ^ 2 - delta ^ 2) ∧
     pfaffian4 (kitaevMajoranaMatrix4 0 t t) = 0 ∧
     (d + 8) - 2 = d - 2) := by
  have hKL1 := kl1_tfim_paramagnetic_vs_ferromagnetic_local_gap_and_iqhe_tknn
    1 1 zero_lt_one J 1 0 0 1 1
  have hKL4 := kl4_spectral_gap_window_polynomial_and_bulk_disk_truncation
    X_R a_R b_R 0 0 0 hP A
  have hKL5 := kl5_ims_double_commutator_localization_and_r_locality χ M hPart 1 1 1
  have hSwitch := pauli_dimerization_switch_operator_laws
  have hBott8 : (d + 8) - 2 = d - 2 := by
    have h8 : (8 : ZMod 8) = 0 := ZMod.natCast_self 8
    rw [h8, add_zero]
  exact ⟨KitaevKOSpectrumStage.rank_injective,
    ⟨hKL1.2.1.2.2.1, hKL1.2.1.2.2.2⟩,
    ⟨hKL4.1, hKL4.2.2⟩,
    hKL5.2.1,
    ⟨hSwitch.1, hSwitch.2.2,
     kitaev_pfaffian4_formula mu t delta,
     sweet_spot_pfaffian_zero t,
     hBott8⟩⟩

/-! ## §9. Three-Region Zorn–Kitaev Interior Disk Projection & Clifford–Bott $KO$-Colimit Weld -/

open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChainFull
open CliffordBottKTheoryWignerS4Poset

/-- **Theorem 9 (`kl8_zorn_kitaev_three_region_disk_and_clifford_bott_colimit_weld`) —
Three-Region Radial Disk Local-Gap Projection $\Pi_{\tilde D} M \Pi_{\tilde D}$ & Clifford–Bott $KO_0$ Colimit Weld**:
1. **Three-Region Radial Partition (`e1 P₁` = interior disk $\tilde{D} = D_{1-r}$, `e2 P₁ P₂` = collar annulus of width $r$, `e3 P₂` = boundary $\partial D$)**:
   For nested idempotents `P₁ * P₁ = P₁`, `P₂ * P₂ = P₂`, `P₁ * P₂ = P₁`, `P₂ * P₁ = P₁`:
   - `e1 P₁ + e2 P₁ P₂ + e3 P₂ = 1`,
   - Unprojected squared 1-hop chain `chainPhi² = v12 + v23 + phi13` carries boundary modes `v23` and two-hop leakage `phi13`,
   - Projecting `chainPhi²` onto the interior disk via `e1 P₁` completely annihilates all boundary couplings (`A₂, C₂`):
     $$e_1(P_1) * \big(\mathrm{chainPhi}\;P_1\;P_2\;A_1\;C_1\;A_2\;C_2\big)^2 * e_1(P_1) =
       n_{12}\;P_1\;P_2\;A_1 * n_{21}\;P_1\;P_2\;C_1.$$
2. **Clifford–Bott $KO_0$ Bruhat Projector Colimit Stability (`ko_theory_pmi_bruhat_projector_colimit_stability`)**:
   - `P_hat_KO P M * P_hat_KO P M = P_hat_KO P M`,
   - `K_diag P (P_hat_KO P M - P) = - comm (conePlus P M) (coneMinus P M)`,
   - `Fintype.card (InfoGeometry.Core.TensorPeirceDecomposition.PeirceIndex (m + 4)) = 16 * Fintype.card (InfoGeometry.Core.TensorPeirceDecomposition.PeirceIndex m)`. -/
theorem kl8_zorn_kitaev_three_region_disk_and_clifford_bott_colimit_weld
    {B : Type*} [Ring B] {P M P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (hP : P * P = P)
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁)
    (m : ℕ) :
    (e1 P₁ + e2 P₁ P₂ + e3 P₂ = 1 ∧
     chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂ =
       v12 P₁ P₂ A₁ C₁ + v23 P₁ P₂ A₂ C₂ + phi13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
     e1 P₁ * phi23 P₁ P₂ A₂ C₂ = 0 ∧
     phi23 P₁ P₂ A₂ C₂ * e1 P₁ = 0 ∧
     e1 P₁ * (chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂) * e1 P₁ =
       n12 P₁ P₂ A₁ * n21 P₁ P₂ C₁) ∧
    (P_hat_KO P M * P_hat_KO P M = P_hat_KO P M ∧
     K_diag P (P_hat_KO P M - P) =
       -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P M) (coneMinus P M) ∧
     Fintype.card (InfoGeometry.Core.TensorPeirceDecomposition.PeirceIndex (m + 4)) =
       16 * Fintype.card (InfoGeometry.Core.TensorPeirceDecomposition.PeirceIndex m)) := by
  have hCorners := three_corner_laws h₁ h₂ h₁₂ h₂₁
  have h1' : ∀ Z : B, P₁ * (P₁ * Z) = P₁ * Z := fun Z => by rw [← mul_assoc, h₁]
  have h2' : ∀ Z : B, P₂ * (P₂ * Z) = P₂ * Z := fun Z => by rw [← mul_assoc, h₂]
  have h12' : ∀ Z : B, P₁ * (P₂ * Z) = P₁ * Z := fun Z => by rw [← mul_assoc, h₁₂]
  have h21' : ∀ Z : B, P₂ * (P₁ * Z) = P₁ * Z := fun Z => by rw [← mul_assoc, h₂₁]
  have hDisk :
      chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂ =
        v12 P₁ P₂ A₁ C₁ + v23 P₁ P₂ A₂ C₂ + phi13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
      e1 P₁ * phi23 P₁ P₂ A₂ C₂ = 0 ∧
      phi23 P₁ P₂ A₂ C₂ * e1 P₁ = 0 ∧
      e1 P₁ * (chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂) * e1 P₁ =
        n12 P₁ P₂ A₁ * n21 P₁ P₂ C₁ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (dsimp [chainPhi, phi12, phi23, phi13, v12, v23, n13, n31, n12, n21, n23, n32, e1, e2, e3];
       noncomm_ring [h₁, h₂, h₁₂, h₂₁, h1', h2', h12', h21'])
  have hKO := ko_theory_pmi_bruhat_projector_colimit_stability P M hP (RingHom.id B) m
  exact ⟨⟨hCorners.2.2.2.2.2.2.2.2.2, hDisk.1, hDisk.2.1, hDisk.2.2.1, hDisk.2.2.2⟩,
    ⟨hKO.2.1, hKO.2.2.1, hKO.2.2.2.2⟩⟩

end InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset
