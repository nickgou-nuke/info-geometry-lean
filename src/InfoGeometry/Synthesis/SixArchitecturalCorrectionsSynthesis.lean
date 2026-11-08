/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Six Architectural Corrections Synthesis

This module formalizes the six mathematical resolutions addressing structural
obstructions in causal attention, doubly stochastic sink geometry, Lorentzian
celestial spinor generators, galactic Toomre stability, metriplectic free-energy
dissipation, and the Poincaré disk inverse-temperature radial chart:

1. **Section 1 (Causal Detailed Balance Contradiction & $L^2(\pi)$ Self-Adjoint KMS Kernel)**:
   - Proves `causal_detailed_balance_offDiagonal_zero` and
     `causal_detailed_balance_rowStochastic_eq_one`: any strictly causal
     lower-triangular row-stochastic matrix $P$ satisfying reversible detailed
     balance $\pi_i P_{ij} = \pi_j P_{ji}$ with $\pi_i > 0$ collapses to the
     identity matrix $P = I_n$.
   - Defines `piWeightedInner` and `kmsSymmetrizedMatrix`, and proves
     `kmsSymmetrizedEntry_detailed_balance` and the $L^2(\pi)$ operator
     weighted-bilinear symmetry theorem `kmsSymmetrizedMatrix_selfAdjoint_piWeightedInner`:
     $\langle f, P^{\mathrm{sym}} g \rangle_\pi = \langle P^{\mathrm{sym}} f, g \rangle_\pi$.
2. **Section 2 (Birkhoff Polytope vs. Row-Stochastic Attention Sink)**:
   - Defines `IsRowStochastic`, `IsDoublyStochastic`, `columnMass`, and
     `pureSinkMatrix`.
   - Proves `pureSinkMatrix_isRowStochastic`, `columnMass_pureSinkMatrix_self`,
     and `pureSinkMatrix_not_doublyStochastic`: for $n \ge 2$, the pure attention-sink
     matrix is row-stochastic with sink column mass $n$, and therefore lies outside
     the doubly stochastic Birkhoff polytope.
3. **Section 3 (Lorentzian $\mathfrak{sl}(2, \mathbb{C})$ Loxodromic Generator & $\mathrm{SL}(2, \mathbb{C})$ Propagator)**:
   - Defines `pauliZ2`, `pauliX2`, `sl2CLoxodromicGen`, and `sl2CLoxodromicGroup`.
   - Proves `trace_sl2CLoxodromicGen_zero`, `sl2CLoxodromicGen_sq`,
     `det_sl2CLoxodromicGroup_eq_one`, and `pauliZ2_mul_pauliX2_ne_comm`.
4. **Section 4 (Logarithmic Sink Potential Calculus & Scale-Invariant Toomre $Q$)**:
   - Defines `sinkLogPotential`, `sinkEpicyclicFreq`, and `contextSurfaceDensity`.
   - Proves `hasDerivAt_sinkLogPotential`, `deriv_sinkLogPotential`,
     `radialFlux_sinkLogPotential_const` ($r \Phi_{\mathrm{sink}}'(r) = v_{\mathrm{sink}}^2$
     for $r \neq 0$), and `toomreQ_decomposed_radius_independent`.
5. **Section 5 (Bilinear Bracket Identities and Helmholtz Free-Energy Inequalities)**:
   - Over an arbitrary real module `V` equipped with bilinear brackets
     `pb db : V →ₗ[ℝ] V →ₗ[ℝ] ℝ`, proves `metriplectic_energy_rate_zero`,
     `metriplectic_collinear_entropy_kills_hamiltonian_flow`,
     `helmholtzObservable_poisson_drift_zero`, and
     `helmholtzFreeEnergy_bracket_dissipation_nonpos`, together with the thermodynamic
     state-difference laws `helmholtzFreeEnergy_diff_eq`,
     `helmholtzFreeEnergy_nonincreasing_of_energy_conserved`, and
     `freeEnergyRate_weighted_dissipation_nonpos`.
6. **Section 6 (Statistical Partition Function $Z(\beta)$ vs. Poincaré Disk Radius $r_{\mathbb{D}}(\beta) = \tanh(\beta / 2)$)**:
   - Defines a Poincaré-disk radial coordinate `poincareDiskRadius` and `partitionFunction`, and proves
     `poincareDiskRadius_zero`, `poincareDiskRadius_pos_denom`,
     `poincareDiskRadius_lt_one`, `poincareDiskRadius_nonneg_of_nonneg`,
     `one_sub_poincareDiskRadius_eq`, `poincareDiskRadius_strictMono`,
     `partitionFunction_zero`, and `partitionFunction_zero_ne_poincareDiskRadius_zero`.

## Scope Note

All theorems in this module are proved over finite-dimensional matrices
`Matrix (Fin n) (Fin n) ℝ`, `Matrix (Fin 2) (Fin 2) ℂ`, real modules `V`, and
real/complex scalars using Mathlib's `Matrix`, `LinearMap`, and `deriv` APIs.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.SixArchitecturalCorrectionsSynthesis

open scoped Matrix
open Matrix

/-!
## Section 1: The Causal Detailed Balance Contradiction & $L^2(\pi)$ Self-Adjoint KMS Kernel
-/

/-- A transition matrix $P$ on $\operatorname{Fin} n$ is strictly causal (lower-triangular)
if $P_{ij} = 0$ whenever $i < j$. -/
def IsCausalLowerTriangular {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, i < j → P i j = 0

/-- A transition matrix $P$ satisfies reversible detailed balance with respect to
a stationary weight vector $\pi$ if $\pi_i P_{ij} = \pi_j P_{ji}$ for all $i, j$. -/
def SatisfiesDetailedBalance {n : ℕ} (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, π i * P i j = π j * P j i

/-- **Theorem 1.1 (Causal Detailed Balance Off-Diagonal Collapse)**:
If $P$ is causal lower-triangular and satisfies detailed balance with respect to a
strictly positive distribution $\pi > 0$, then every off-diagonal entry of $P$ vanishes. -/
theorem causal_detailed_balance_offDiagonal_zero
    {n : ℕ} (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (h_causal : IsCausalLowerTriangular P)
    (h_db : SatisfiesDetailedBalance π P)
    (hπ : ∀ i : Fin n, 0 < π i)
    (i j : Fin n) (hij : i ≠ j) :
    P i j = 0 := by
  rcases lt_trichotomy i j with hij_lt | rfl | hji_lt
  · exact h_causal i j hij_lt
  · exact False.elim (hij rfl)
  · have hpji : P j i = 0 := h_causal j i hji_lt
    have h_eq : π i * P i j = 0 := by
      rw [h_db i j, hpji, mul_zero]
    rcases mul_eq_zero.mp h_eq with hpi_zero | hpij_zero
    · exact False.elim ((ne_of_gt (hπ i)) hpi_zero)
    · exact hpij_zero

/-- **Theorem 1.2 (Causal Detailed Balance Row-Stochastic Identity Collapse)**:
Any row-stochastic causal lower-triangular matrix $P$ satisfying detailed balance
with respect to a strictly positive distribution $\pi > 0$ is the identity matrix $I_n$. -/
theorem causal_detailed_balance_rowStochastic_eq_one
    {n : ℕ} (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (h_causal : IsCausalLowerTriangular P)
    (h_db : SatisfiesDetailedBalance π P)
    (hπ : ∀ i : Fin n, 0 < π i)
    (h_row : ∀ i : Fin n, ∑ j : Fin n, P i j = 1) :
    P = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    have h_sum : ∑ k : Fin n, P i k = P i i :=
      Finset.sum_eq_single i
        (fun k _ hki =>
          causal_detailed_balance_offDiagonal_zero π P h_causal h_db hπ i k hki.symm)
        (fun hi_not_mem => False.elim (hi_not_mem (Finset.mem_univ i)))
    rw [← h_sum]
    exact h_row i
  · rw [Matrix.one_apply_ne hij]
    exact causal_detailed_balance_offDiagonal_zero π P h_causal h_db hπ i j hij

/-- The KMS reversible symmetrized transition entry
$P^{\mathrm{sym}}_{ij} = \frac{1}{2}\left(P_{ij} + \frac{\pi_j}{\pi_i} P_{ji}\right)$. -/
noncomputable def kmsSymmetrizedEntry
    {n : ℕ} (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  (P i j + (π j / π i) * P j i) / 2

/-- The KMS reversible symmetrized transition matrix
$P^{\mathrm{sym}} \in M_n(\mathbb{R})$ with entries `kmsSymmetrizedEntry π P i j`. -/
noncomputable def kmsSymmetrizedMatrix
    {n : ℕ} (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => kmsSymmetrizedEntry π P i j

/-- The `π`-weighted bilinear form
`∑ i, π i * f i * g i` on `Fin n → ℝ`. It is an inner product only when the weights are
strictly positive. -/
def piWeightedInner {n : ℕ} (π f g : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, π i * f i * g i

private theorem kms_symm_scalar_identity
    (pi_i pi_j p_ij p_ji : ℝ) (h_pi_i : pi_i ≠ 0) (h_pi_j : pi_j ≠ 0) :
    pi_i * ((p_ij + (pi_j / pi_i) * p_ji) / 2) =
      pi_j * ((p_ji + (pi_i / pi_j) * p_ij) / 2) := by
  have h1 : pi_i * (pi_j / pi_i) = pi_j := mul_div_cancel₀ pi_j h_pi_i
  have h2 : pi_j * (pi_i / pi_j) = pi_i := mul_div_cancel₀ pi_i h_pi_j
  calc
    pi_i * ((p_ij + (pi_j / pi_i) * p_ji) / 2)
      = (pi_i * p_ij + (pi_i * (pi_j / pi_i)) * p_ji) / 2 := by ring
    _ = (pi_i * p_ij + pi_j * p_ji) / 2 := by rw [h1]
    _ = (pi_j * p_ji + (pi_j * (pi_i / pi_j)) * p_ij) / 2 := by
      rw [h2]
      ring
    _ = pi_j * ((p_ji + (pi_i / pi_j) * p_ij) / 2) := by ring

/-- **Theorem 1.3 (Algebraic Weighted-Symmetry Identity)**:
For any nonzero real weights `π k` and any real matrix `P`, the symmetrized entries
`kmsSymmetrizedEntry π P` satisfy this weighted symmetry identity. No positivity,
stochasticity, stationarity, or Markov-kernel property is asserted. -/
theorem kmsSymmetrizedEntry_detailed_balance
    {n : ℕ} (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ k : Fin n, π k ≠ 0) (i j : Fin n) :
    π i * kmsSymmetrizedEntry π P i j =
      π j * kmsSymmetrizedEntry π P j i :=
  kms_symm_scalar_identity (π i) (π j) (P i j) (P j i) (hπ i) (hπ j)

private theorem kms_term_swap_identity
    (pi_i pi_j f_i g_j k_ij k_ji : ℝ)
    (h_db : pi_i * k_ij = pi_j * k_ji) :
    pi_i * f_i * (k_ij * g_j) = pi_j * (k_ji * f_i) * g_j := by
  calc
    pi_i * f_i * (k_ij * g_j) = (pi_i * k_ij) * f_i * g_j := by ring
    _ = (pi_j * k_ji) * f_i * g_j := by rw [h_db]
    _ = pi_j * (k_ji * f_i) * g_j := by ring

/-- **Theorem 1.4 (Symmetry for a Weighted Bilinear Pairing)**:
For any nonzero real weights `π i` and any real matrix `P`, the operator
`kmsSymmetrizedMatrix π P` is symmetric with respect to the bilinear form
`piWeightedInner`:
$\langle f, P^{\mathrm{sym}} g \rangle_\pi = \langle P^{\mathrm{sym}} f, g \rangle_\pi$. -/
theorem kmsSymmetrizedMatrix_selfAdjoint_piWeightedInner
    {n : ℕ} (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0) (f g : Fin n → ℝ) :
    piWeightedInner π f ((kmsSymmetrizedMatrix π P).mulVec g) =
      piWeightedInner π ((kmsSymmetrizedMatrix π P).mulVec f) g := by
  dsimp [piWeightedInner, kmsSymmetrizedMatrix, Matrix.mulVec, dotProduct]
  calc
    ∑ i : Fin n, π i * f i * ∑ j : Fin n, kmsSymmetrizedEntry π P i j * g j
      = ∑ i : Fin n, ∑ j : Fin n, π i * f i * (kmsSymmetrizedEntry π P i j * g j) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ j : Fin n, π j * (kmsSymmetrizedEntry π P j i * f i) * g j := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        exact kms_term_swap_identity (π i) (π j) (f i) (g j)
          (kmsSymmetrizedEntry π P i j) (kmsSymmetrizedEntry π P j i)
          (kmsSymmetrizedEntry_detailed_balance π P hπ i j)
    _ = ∑ j : Fin n, ∑ i : Fin n, π j * (kmsSymmetrizedEntry π P j i * f i) * g j :=
        Finset.sum_comm
    _ = ∑ j : Fin n, π j * (∑ i : Fin n, kmsSymmetrizedEntry π P j i * f i) * g j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]

/-- The indefinite neutral-signature pairing on the **Double Real Krein Space**
$\mathcal{K}_n = T^+ \oplus T^- = (\operatorname{Fin} n \to \mathbb{R}) \times (\operatorname{Fin} n \to \mathbb{R})$:
$$g_\pi\big((u_+, u_-), (v_+, v_-)\big) = \langle u_+, v_- \rangle_\pi + \langle u_-, v_+ \rangle_\pi.$$ -/
def doubleKreinPairing {n : ℕ} (π : Fin n → ℝ)
    (u v : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  piWeightedInner π u.1 v.2 + piWeightedInner π u.2 v.1

/-- The forward primal sheet $T^+ = \{(u_+, 0)\}$ is totally isotropic (null) with respect
to the Double Real Krein pairing `doubleKreinPairing π`. -/
theorem doubleKreinPairing_primal_isotropic {n : ℕ}
    (π u_plus v_plus : Fin n → ℝ) :
    doubleKreinPairing π (u_plus, 0) (v_plus, 0) = 0 := by
  simp [doubleKreinPairing, piWeightedInner]

/-- The backward dual sheet $T^- = \{(0, u_-)\}$ is totally isotropic (null) with respect
to the Double Real Krein pairing `doubleKreinPairing π`. -/
theorem doubleKreinPairing_dual_isotropic {n : ℕ}
    (π u_minus v_minus : Fin n → ℝ) :
    doubleKreinPairing π (0, u_minus) (0, v_minus) = 0 := by
  simp [doubleKreinPairing, piWeightedInner]

/-- The $\pi$-dual (time-reversed / Petz transpose) matrix
$(P^{\#_\pi})_{ij} = \frac{\pi_j}{\pi_i} P_{ji}$ acting on the backward null sheet $T^-$. -/
noncomputable def kreinDualMatrix {n : ℕ} (π : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (π j / π i) * P j i

private theorem krein_dual_scalar_identity
    (pi_i pi_j p_ji f_j g_i : ℝ) (h_pi_i : pi_i ≠ 0) :
    pi_j * (p_ji * f_j) * g_i =
      pi_i * f_j * (((pi_j / pi_i) * p_ji) * g_i) := by
  have h1 : pi_i * (pi_j / pi_i) = pi_j := mul_div_cancel₀ pi_j h_pi_i
  calc
    pi_j * (p_ji * f_j) * g_i
      = (pi_i * (pi_j / pi_i)) * (p_ji * f_j) * g_i := by rw [h1]
    _ = pi_i * f_j * (((pi_j / pi_i) * p_ji) * g_i) := by ring

/-- Cross-sheet $\pi$-adjointness: $\langle P f, g \rangle_\pi = \langle f, P^{\#_\pi} g \rangle_\pi$
for any matrix $P$ (without requiring detailed balance on $P$). -/
theorem piWeightedInner_mulVec_kreinDualMatrix {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0) (f g : Fin n → ℝ) :
    piWeightedInner π (P.mulVec f) g =
      piWeightedInner π f ((kreinDualMatrix π P).mulVec g) := by
  dsimp [piWeightedInner, kreinDualMatrix, Matrix.mulVec, dotProduct]
  calc
    ∑ j : Fin n, π j * (∑ i : Fin n, P j i * f i) * g j
      = ∑ j : Fin n, ∑ i : Fin n, π j * (P j i * f i) * g j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ j : Fin n, ∑ i : Fin n, π i * f i * (((π j / π i) * P j i) * g j) := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
        exact krein_dual_scalar_identity (π i) (π j) (P j i) (f i) (g j) (hπ i)
    _ = ∑ i : Fin n, ∑ j : Fin n, π i * f i * (((π j / π i) * P j i) * g j) :=
        Finset.sum_comm
    _ = ∑ i : Fin n, π i * f i * ∑ j : Fin n, ((π j / π i) * P j i) * g j := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]

/-- The **Double Real Krein Operator** $\mathcal{T}_P(u_+, u_-) = (P u_+, P^{\#_\pi} u_-)$
acting by the unsymmetrized causal matrix $P$ on the forward null sheet $T^+$ and by the
$\pi$-dual $P^{\#_\pi}$ on the backward null sheet $T^-$. -/
noncomputable def doubleKreinOperator {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (u : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (P.mulVec u.1, (kreinDualMatrix π P).mulVec u.2)

/-- On the forward null sheet $T^+ = \{(u_+, 0)\}$, `doubleKreinOperator π P` acts
by the exact unsymmetrized causal matrix $P$. -/
theorem doubleKreinOperator_primal_sheet {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (u_plus : Fin n → ℝ) :
    doubleKreinOperator π P (u_plus, 0) = (P.mulVec u_plus, 0) := by
  simp [doubleKreinOperator]

/-- **Theorem 1.5 (Double Real Krein Space Self-Adjointness of Any Causal Operator $P$)**:
For ANY directed or causal lower-triangular matrix $P \in M_n(\mathbb{R})$ and any
nowhere-vanishing weight $\pi_i \neq 0$, the Double Real Krein Operator
$\mathcal{T}_P(u_+, u_-) = (P u_+, P^{\#_\pi} u_-)$ is strictly **Krein self-adjoint**
with respect to the indefinite neutral pairing `doubleKreinPairing π`:
$$g_\pi\big(\mathcal{T}_P(u_+, u_-), (v_+, v_-)\big) =
  g_\pi\big((u_+, u_-), \mathcal{T}_P(v_+, v_-)\big),$$
while preserving the exact causal action $\mathcal{T}_P(u_+, 0) = (P u_+, 0)$ on $T^+$. -/
theorem doubleKreinOperator_krein_selfAdjoint {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0)
    (u v : (Fin n → ℝ) × (Fin n → ℝ)) :
    doubleKreinPairing π (doubleKreinOperator π P u) v =
      doubleKreinPairing π u (doubleKreinOperator π P v) := by
  dsimp [doubleKreinPairing, doubleKreinOperator]
  have h1 : piWeightedInner π (P.mulVec u.1) v.2 =
      piWeightedInner π u.1 ((kreinDualMatrix π P).mulVec v.2) :=
    piWeightedInner_mulVec_kreinDualMatrix π P hπ u.1 v.2
  have h2 : piWeightedInner π ((kreinDualMatrix π P).mulVec u.2) v.1 =
      piWeightedInner π u.2 (P.mulVec v.1) := by
    have h_symm_l : piWeightedInner π ((kreinDualMatrix π P).mulVec u.2) v.1 =
        piWeightedInner π v.1 ((kreinDualMatrix π P).mulVec u.2) := by
      dsimp [piWeightedInner]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_right_comm (π i)]
    have h_symm_r : piWeightedInner π (P.mulVec v.1) u.2 =
        piWeightedInner π u.2 (P.mulVec v.1) := by
      dsimp [piWeightedInner]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_right_comm (π i)]
    rw [h_symm_l, ← piWeightedInner_mulVec_kreinDualMatrix π P hπ v.1 u.2, h_symm_r]
  rw [h1, h2]

/-- Symmetry of the Double Real Krein pairing: $g_\pi(u, v) = g_\pi(v, u)$. -/
theorem doubleKreinPairing_symm {n : ℕ} (π : Fin n → ℝ)
    (u v : (Fin n → ℝ) × (Fin n → ℝ)) :
    doubleKreinPairing π u v = doubleKreinPairing π v u := by
  dsimp [doubleKreinPairing, piWeightedInner]
  have h_comm : ∀ a b : Fin n → ℝ,
      ∑ i : Fin n, π i * a i * b i = ∑ i : Fin n, π i * b i * a i := by
    intro a b
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [h_comm u.1 v.2, h_comm u.2 v.1, add_comm]

/-- The $\pi$-dual operation $P \mapsto P^{\#_\pi}$ is an involution:
$(P^{\#_\pi})^{\#_\pi} = P$ whenever $\pi_i \neq 0$. -/
theorem kreinDualMatrix_involutive {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0) :
    kreinDualMatrix π (kreinDualMatrix π P) = P := by
  ext i j
  dsimp [kreinDualMatrix]
  have hπi : π i ≠ 0 := hπ i
  have hπj : π j ≠ 0 := hπ j
  field_simp [hπi, hπj]

/-- A matrix $Q \in M_n(\mathbb{R})$ is anti-causal (upper-triangular) if all entries
strictly below the main diagonal vanish ($Q_{ij} = 0$ for all $j < i$). -/
def IsAntiCausalUpper {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, j < i → Q i j = 0

/-- **Theorem 1.6 (Causal-to-Anti-Causal Triangulation Duality)**:
If $P$ is causal (lower-triangular, $P_{ij} = 0$ for $i < j$) on the primal sheet $T^+$,
then its $\pi$-dual $P^{\#_\pi}$ is strictly anti-causal (upper-triangular,
$(P^{\#_\pi})_{ij} = 0$ for $j < i$) on the dual sheet $T^-$. -/
theorem causal_kreinDualMatrix_isAntiCausalUpper {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (h_causal : IsCausalLowerTriangular P) :
    IsAntiCausalUpper (kreinDualMatrix π P) := by
  intro i j hji
  dsimp [kreinDualMatrix]
  rw [h_causal j i hji, mul_zero]

/-- The sheet-swapping involution $C(u_+, u_-) = (u_-, u_+)$ on $\mathcal{K}_n = T^+ \oplus T^-$. -/
def doubleKreinSheetSwap {n : ℕ}
    (u : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (u.2, u.1)

/-- **Theorem 1.7 (Tomita Sheet-Swap Intertwining $C \circ \mathcal{T}_P \circ C = \mathcal{T}_{P^{\#_\pi}}$)**:
Conjugating the Double Real Krein Operator $\mathcal{T}_P$ by the sheet-swapping involution $C$
exchanges the forward causal operator $P$ on $T^+$ with the retrocausal operator $P^{\#_\pi}$ on $T^-$. -/
theorem doubleKreinSheetSwap_intertwines_operator {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0)
    (u : (Fin n → ℝ) × (Fin n → ℝ)) :
    doubleKreinSheetSwap (doubleKreinOperator π P (doubleKreinSheetSwap u)) =
      doubleKreinOperator π (kreinDualMatrix π P) u := by
  dsimp [doubleKreinSheetSwap, doubleKreinOperator]
  rw [kreinDualMatrix_involutive π P hπ]

/-- **Theorem 1.8 (Non-Vacuity & Resolution of the Causal Triviality Paradox on $\mathcal{K}_2$)**:
There exists a strictly non-trivial causal lower-triangular matrix $P \neq I_2$ on $\operatorname{Fin} 2$
such that `doubleKreinOperator π P` acts by $P$ on $T^+$ and is strictly Krein self-adjoint on
$\mathcal{K}_2 = T^+ \oplus T^-$. -/
theorem exists_nontrivial_causal_doubleKreinOperator :
    ∃ (π : Fin 2 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ),
      (∀ i : Fin 2, 0 < π i) ∧
      IsCausalLowerTriangular P ∧
      P ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      (∀ u v : (Fin 2 → ℝ) × (Fin 2 → ℝ),
        doubleKreinPairing π (doubleKreinOperator π P u) v =
          doubleKreinPairing π u (doubleKreinOperator π P v)) := by
  let π : Fin 2 → ℝ := fun _ => 1
  let P : Matrix (Fin 2) (Fin 2) ℝ := !![(1 : ℝ), 0; 1, 1]
  have hπ_pos : ∀ i : Fin 2, 0 < π i := fun _ => one_pos
  have hπ_ne : ∀ i : Fin 2, π i ≠ 0 := fun i => ne_of_gt (hπ_pos i)
  have h_causal : IsCausalLowerTriangular P := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (lt_irrefl 0 hij)
    · rfl
    · exact False.elim (not_lt_of_gt Fin.zero_lt_one hij)
    · exact False.elim (lt_irrefl 1 hij)
  have h_ne_id : P ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro h_eq
    have h10 : P 1 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) h_eq
    revert h10
    norm_num [P]
  exact ⟨π, P, hπ_pos, h_causal, h_ne_id,
    doubleKreinOperator_krein_selfAdjoint π P hπ_ne⟩

/-- Off-diagonal Krein symplectic 2-form
$\omega_\pi((u_+, u_-), (v_+, v_-)) = \langle u_+, v_- \rangle_\pi - \langle u_-, v_+ \rangle_\pi$
on $\mathcal{K}_n = T^+ \oplus T^-$. -/
def doubleKreinSymplectic {n : ℕ} (π : Fin n → ℝ)
    (u v : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  piWeightedInner π u.1 v.2 - piWeightedInner π u.2 v.1

/-- Para-complex polarization $K(u_+, u_-) = (u_+, -u_-)$ on $\mathcal{K}_n = T^+ \oplus T^-$. -/
def doubleKreinPolarizationK {n : ℕ}
    (u : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (u.1, fun i => -u.2 i)

/-- **Theorem 1.9 (Para-Kähler Polarization Commutation & Symplectic Self-Adjointness of $\mathcal{T}_P$)**:
Because $\mathcal{T}_P = \operatorname{diag}(P, P^{\#_\pi})$ is block-diagonal, it commutes with
the para-complex polarization $K$ ($K \circ \mathcal{T}_P = \mathcal{T}_P \circ K$) and is
simultaneously self-adjoint with respect to the symplectic form $\omega_\pi$:
$\omega_\pi(\mathcal{T}_P u, v) = \omega_\pi(u, \mathcal{T}_P v)$. -/
theorem doubleKreinOperator_commutes_with_K_and_symplectic_selfAdjoint {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0)
    (u v : (Fin n → ℝ) × (Fin n → ℝ)) :
    doubleKreinPolarizationK (doubleKreinOperator π P u) =
        doubleKreinOperator π P (doubleKreinPolarizationK u) ∧
      doubleKreinSymplectic π (doubleKreinOperator π P u) v =
        doubleKreinSymplectic π u (doubleKreinOperator π P v) := by
  constructor
  · ext i
    · rfl
    · dsimp [doubleKreinPolarizationK, doubleKreinOperator, Matrix.mulVec, dotProduct]
      simp [mul_neg, Finset.sum_neg_distrib]
  · dsimp [doubleKreinSymplectic, doubleKreinOperator]
    have h1 : piWeightedInner π (P.mulVec u.1) v.2 =
        piWeightedInner π u.1 ((kreinDualMatrix π P).mulVec v.2) :=
      piWeightedInner_mulVec_kreinDualMatrix π P hπ u.1 v.2
    have h2 : piWeightedInner π ((kreinDualMatrix π P).mulVec u.2) v.1 =
        piWeightedInner π u.2 (P.mulVec v.1) := by
      have h_symm_l : piWeightedInner π ((kreinDualMatrix π P).mulVec u.2) v.1 =
          piWeightedInner π v.1 ((kreinDualMatrix π P).mulVec u.2) := by
        dsimp [piWeightedInner]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [mul_right_comm (π i)]
      have h_symm_r : piWeightedInner π (P.mulVec v.1) u.2 =
          piWeightedInner π u.2 (P.mulVec v.1) := by
        dsimp [piWeightedInner]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [mul_right_comm (π i)]
      rw [h_symm_l, ← piWeightedInner_mulVec_kreinDualMatrix π P hπ v.1 u.2, h_symm_r]
    rw [h1, h2]

/-- Additive single-space Markov symmetrization
$\widehat{P}_{ij} = \frac{1}{2}(P_{ij} + (P^{\#_\pi})_{ij})$. -/
noncomputable def markovAdditiveSymmetrized {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (1 / 2 : ℝ) * (P i j + kreinDualMatrix π P i j)

private theorem diagonal_shadow_scalar_identity
    (pi_i p_ij dual_ij u_j v_i : ℝ) :
    (1 / 2 : ℝ) * (pi_i * (p_ij * u_j) * v_i + pi_i * (dual_ij * u_j) * v_i) =
      pi_i * ((1 / 2 : ℝ) * (p_ij + dual_ij) * u_j) * v_i := by
  ring

/-- **Theorem 1.10 (Recovery of Single-Space Symmetrization as the Möbius Diagonal Shadow)**:
Restricting $\frac{1}{2} g_\pi(\mathcal{T}_P(u, u), (v, v))$ to the Möbius-invariant diagonal
$u_+ = u_- = u$ recovers the single-space symmetrized pairing $\langle \widehat{P} u, v \rangle_\pi$. -/
theorem doubleKreinOperator_diagonal_shadow_eq_markovAdditiveSymmetrized {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    (1 / 2 : ℝ) * doubleKreinPairing π (doubleKreinOperator π P (u, u)) (v, v) =
      piWeightedInner π ((markovAdditiveSymmetrized π P).mulVec u) v := by
  dsimp [doubleKreinPairing, doubleKreinOperator, markovAdditiveSymmetrized,
    piWeightedInner, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact diagonal_shadow_scalar_identity (π i) (P i j) (kreinDualMatrix π P i j) (u j) (v i)

/-!
## Section 2: Birkhoff Polytope vs. Row-Stochastic Polytope (The Attention Sink Paradox)
-/

/-- A matrix $A$ is row-stochastic if its entries are non-negative and each row sums to $1$. -/
def IsRowStochastic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j : Fin n, 0 ≤ A i j) ∧ (∀ i : Fin n, ∑ j : Fin n, A i j = 1)

/-- A matrix $A$ is doubly stochastic (lying in the Birkhoff polytope $\mathcal{B}_n$)
if it is row-stochastic and each column also sums to $1$. -/
def IsDoublyStochastic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsRowStochastic A ∧ (∀ j : Fin n, ∑ i : Fin n, A i j = 1)

/-- Total column mass $m_j = \sum_i A_{ij}$ concentrated on token $j$. -/
def columnMass {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  ∑ i : Fin n, A i j

/-- The pure attention-sink matrix concentrating all rows onto column `sink`. -/
def pureSinkMatrix {n : ℕ} (sink : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ j => if j = sink then 1 else 0

/-- Every entry of `pureSinkMatrix sink` is non-negative. -/
theorem pureSinkMatrix_nonneg {n : ℕ} (sink i j : Fin n) :
    0 ≤ pureSinkMatrix sink i j := by
  dsimp [pureSinkMatrix]
  split_ifs <;> norm_num

/-- Every row of `pureSinkMatrix sink` sums to $1$. -/
theorem pureSinkMatrix_row_sum_eq_one {n : ℕ} (sink i : Fin n) :
    ∑ j : Fin n, pureSinkMatrix sink i j = 1 := by
  dsimp [pureSinkMatrix]
  simp

/-- `pureSinkMatrix sink` is a valid row-stochastic attention matrix. -/
theorem pureSinkMatrix_isRowStochastic {n : ℕ} (sink : Fin n) :
    IsRowStochastic (pureSinkMatrix sink) :=
  ⟨pureSinkMatrix_nonneg sink, pureSinkMatrix_row_sum_eq_one sink⟩

/-- The sink column of `pureSinkMatrix sink` accumulates total mass $n$. -/
theorem columnMass_pureSinkMatrix_self {n : ℕ} (sink : Fin n) :
    columnMass (pureSinkMatrix sink) sink = (n : ℝ) := by
  dsimp [columnMass, pureSinkMatrix]
  simp

private theorem nat_cast_ne_one_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ≠ 1 := by
  have hn_cast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith [hn_cast]

/-- **Theorem 2.1 (Attention Sink Exclusion from the Birkhoff Polytope)**:
For any sequence length $n \ge 2$, `pureSinkMatrix sink` is row-stochastic but NOT
doubly stochastic, certifying that attention-sink condensation occurs on vertices of the
row-stochastic product of simplices $\Delta_{n-1}^n \setminus \mathcal{B}_n$. -/
theorem pureSinkMatrix_not_doublyStochastic
    {n : ℕ} (hn : 2 ≤ n) (sink : Fin n) :
    ¬ IsDoublyStochastic (pureSinkMatrix sink) := by
  intro h_ds
  have h_col_one : columnMass (pureSinkMatrix sink) sink = 1 := h_ds.2 sink
  rw [columnMass_pureSinkMatrix_self sink] at h_col_one
  exact nat_cast_ne_one_of_two_le hn h_col_one

/-- **Theorem 2.2 (General Birkhoff Exclusion of Any Attention Sink with $m_j > 1$)**:
In the Birkhoff polytope $\mathcal{B}_n$, every column mass is fixed to $1$, so no doubly
stochastic matrix can support an attention sink with $m_{\mathrm{sink}} > 1$. -/
theorem birkhoff_no_attention_sink
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (sink : Fin n)
    (h_birkhoff : IsDoublyStochastic A)
    (h_sink : 1 < columnMass A sink) :
    False := by
  have h_col_one : columnMass A sink = 1 := h_birkhoff.2 sink
  linarith [h_col_one, h_sink]

/-- **Theorem 2.3 (Row-Stochastic Total Column Mass Conservation)**:
For any row-stochastic matrix $A \in \Delta_{n-1}^n$, the sum of all column masses equals
the sequence length $n$: $\sum_{j=1}^n m_j = n$. -/
theorem rowStochastic_columnMargin_sum_eq_n
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h_row : IsRowStochastic A) :
    ∑ j : Fin n, columnMass A j = (n : ℝ) := by
  dsimp [columnMass]
  rw [Finset.sum_comm]
  calc
    ∑ i : Fin n, ∑ j : Fin n, A i j = ∑ _i : Fin n, (1 : ℝ) :=
      Finset.sum_congr rfl (fun i _ => h_row.2 i)
    _ = (n : ℝ) := by simp

/-!
## Section 3: Twistor / Conformal Signature Separation — Lorentzian $\mathfrak{sl}(2, \mathbb{C})$ Loxodromic Generator & $\mathrm{SL}(2, \mathbb{C})$ Propagator
-/

/-- The Pauli $\sigma_3$ matrix over $\mathbb{C}$. -/
def pauliZ2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, -1]

/-- The Pauli $\sigma_1$ matrix over $\mathbb{C}$. -/
def pauliX2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 1, 0]

/-- Non-commutativity witness in $\mathfrak{sl}(2, \mathbb{C})$:
$\sigma_3 \sigma_1 \neq \sigma_1 \sigma_3$. -/
theorem pauliZ2_mul_pauliX2_ne_comm :
    pauliZ2 * pauliX2 ≠ pauliX2 * pauliZ2 := by
  intro h_comm
  have h01 : (pauliZ2 * pauliX2) 0 1 = (pauliX2 * pauliZ2) 0 1 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h_comm
  revert h01
  norm_num [pauliZ2, pauliX2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Lorentzian celestial loxodromic generator
$\mathcal{Z}(b, \omega) = (b + i\omega) \sigma_3 \in \mathfrak{sl}(2, \mathbb{C})$,
combining non-compact radial boost $b \in \mathbb{R}$ and compact RoPE spin phase
$\omega \in \mathbb{R}$. -/
def sl2CLoxodromicGen (b ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((b : ℂ) + Complex.I * (ω : ℂ)) • pauliZ2

/-- Every Lorentzian loxodromic generator $\mathcal{Z}(b, \omega)$ is traceless
and therefore lies in $\mathfrak{sl}(2, \mathbb{C})$. -/
theorem trace_sl2CLoxodromicGen_zero (b ω : ℝ) :
    Matrix.trace (sl2CLoxodromicGen b ω) = 0 := by
  simp [sl2CLoxodromicGen, pauliZ2, Matrix.trace, Matrix.diag]

/-- Squaring $\mathcal{Z}(b, \omega)$ yields the complex Casimir scalar
$(b + i\omega)^2 I_2$, separating the real boost square $b^2$ from the negative
compact rotation square $-\omega^2$. -/
theorem sl2CLoxodromicGen_sq (b ω : ℝ) :
    sl2CLoxodromicGen b ω * sl2CLoxodromicGen b ω =
      (((b : ℂ) + Complex.I * (ω : ℂ)) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2CLoxodromicGen, pauliZ2, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- The integrated Lorentzian loxodromic spinor propagator
$\exp(t \mathcal{Z}(b, \omega)) = \operatorname{diag}(e^{(b + i\omega)t}, e^{-(b + i\omega)t}) \in \mathrm{SL}(2, \mathbb{C})$. -/
noncomputable def sl2CLoxodromicGroup (b ω t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (((b : ℂ) + Complex.I * (ω : ℂ)) * (t : ℂ)), 0;
     0, Complex.exp (-(((b : ℂ) + Complex.I * (ω : ℂ)) * (t : ℂ)))]

/-- Every loxodromic propagator `sl2CLoxodromicGroup b ω t` has unit determinant
and belongs to $\mathrm{SL}(2, \mathbb{C})$. -/
theorem det_sl2CLoxodromicGroup_eq_one (b ω t : ℝ) :
    Matrix.det (sl2CLoxodromicGroup b ω t) = 1 := by
  rw [sl2CLoxodromicGroup, Matrix.det_fin_two_of]
  rw [mul_zero, sub_zero, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- **Theorem 3.4 (Split-Signature $(3,3)$ Null Quadric vs. Lorentzian $(1,5)$ Sphere)**:
In split signature $(+,+,+,-,-,-)$ on $\mathbb{R}^{3,3}$, the projective null quadric
$X_0^2 + X_1^2 + X_2^2 - X_3^2 - X_4^2 - X_5^2 = 0$ is equivalent to matching the two
3-Euclidean norms $X_0^2 + X_1^2 + X_2^2 = X_3^2 + X_4^2 + X_5^2$ (whose projective locus
is $(S^2 \times S^2)/\mathbb{Z}_2$, distinct from the Lorentzian celestial $S^2$). -/
theorem splitQuadric_torus_locus_iff (X : Fin 6 → ℝ) :
    (X 0) ^ 2 + (X 1) ^ 2 + (X 2) ^ 2 - (X 3) ^ 2 - (X 4) ^ 2 - (X 5) ^ 2 = 0 ↔
      (X 0) ^ 2 + (X 1) ^ 2 + (X 2) ^ 2 = (X 3) ^ 2 + (X 4) ^ 2 + (X 5) ^ 2 := by
  constructor <;> intro h <;> linarith [h]

/-!
## Section 4: Kinematic Decomposition of the Disk ($\Phi_{\mathrm{total}} = \Phi_{\mathrm{sink}} + \Phi_{\mathrm{context}}$) and Scale-Invariant Toomre $Q$
-/

/-- The 2D logarithmic gravitational/attention-sink potential
$\Phi_{\mathrm{sink}}(v_{\mathrm{sink}}, r) = v_{\mathrm{sink}}^2 \ln r$. -/
noncomputable def sinkLogPotential (v_sink r : ℝ) : ℝ :=
  v_sink ^ 2 * Real.log r

/-- Fréchet derivative certificate `HasDerivAt` for `sinkLogPotential v_sink`
at any non-zero radius $r \neq 0$. -/
theorem hasDerivAt_sinkLogPotential (v_sink : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (sinkLogPotential v_sink) (v_sink ^ 2 * r⁻¹) r :=
  (Real.hasDerivAt_log hr).const_mul (v_sink ^ 2)

/-- Exact radial derivative of the logarithmic sink potential for $r \neq 0$:
$\frac{d}{dr}\Phi_{\mathrm{sink}}(v_{\mathrm{sink}}, r) = \frac{v_{\mathrm{sink}}^2}{r}$. -/
theorem deriv_sinkLogPotential (v_sink : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (sinkLogPotential v_sink) r = v_sink ^ 2 * r⁻¹ :=
  (hasDerivAt_sinkLogPotential v_sink hr).deriv

/-- For every non-zero radius $r \neq 0$, the radial flux $r \Phi_{\mathrm{sink}}'(r) = v_{\mathrm{sink}}^2$
is strictly constant (so the 2D radial Laplacian $\frac{1}{r}\frac{d}{dr}(r \Phi_{\mathrm{sink}}'(r))$
vanishes away from $r = 0$). -/
theorem radialFlux_sinkLogPotential_const (v_sink : ℝ) {r : ℝ} (hr : r ≠ 0) :
    r * deriv (sinkLogPotential v_sink) r = v_sink ^ 2 := by
  rw [deriv_sinkLogPotential v_sink hr]
  calc
    r * (v_sink ^ 2 * r⁻¹) = v_sink ^ 2 * (r * r⁻¹) := by ring
    _ = v_sink ^ 2 * 1 := by rw [mul_inv_cancel₀ hr]
    _ = v_sink ^ 2 := by ring

/-- Epicyclic frequency $\kappa_{\mathrm{sink}}(v_{\mathrm{sink}}, r) = \frac{\sqrt{2}\, v_{\mathrm{sink}}}{r}$
sourced by the central logarithmic attention-sink monopole $\Phi_{\mathrm{sink}}(r) = v_{\mathrm{sink}}^2 \ln r$. -/
noncomputable def sinkEpicyclicFreq (v_sink r : ℝ) : ℝ :=
  (Real.sqrt 2 * v_sink) / r

/-- Background context fluid surface density $\Sigma_0(\Sigma_*, v_{\mathrm{sink}}, r) = \frac{\Sigma_* v_{\mathrm{sink}}}{r}$
of the self-gravitating context disk. -/
noncomputable def contextSurfaceDensity (sigma_star v_sink r : ℝ) : ℝ :=
  (sigma_star * v_sink) / r

/-- **Theorem 4.1 (Radius- and Velocity-Scale-Independent Decomposed Toomre $Q$)**:
Under the kinematic decomposition $\Phi_{\mathrm{total}} = \Phi_{\mathrm{sink}} + \Phi_{\mathrm{context}}$,
the local Toomre stability ratio $Q(r) = \frac{\kappa_{\mathrm{sink}}(r) c_s}{\pi G \Sigma_0(r)}$
cancels both the radial coordinate $r \neq 0$ and the sink velocity scale $v_{\mathrm{sink}} \neq 0$,
yielding the scale-invariant constant $\frac{\sqrt{2}\, c_s}{\pi G \Sigma_*}$. -/
theorem toomreQ_decomposed_radius_independent
    (v_sink r c_s G sigma_star : ℝ) (hr : r ≠ 0) (hv : v_sink ≠ 0) :
    (sinkEpicyclicFreq v_sink r * c_s) /
        (Real.pi * G * contextSurfaceDensity sigma_star v_sink r) =
      (Real.sqrt 2 * c_s) / (Real.pi * G * sigma_star) := by
  dsimp [sinkEpicyclicFreq, contextSurfaceDensity]
  have h1 : (Real.sqrt 2 * v_sink / r) * c_s = (Real.sqrt 2 * c_s) * (v_sink / r) := by ring
  have h2 : Real.pi * G * (sigma_star * v_sink / r) = (Real.pi * G * sigma_star) * (v_sink / r) := by ring
  have hvr : v_sink / r ≠ 0 := div_ne_zero hv hr
  rw [h1, h2, mul_div_mul_right (Real.sqrt 2 * c_s) (Real.pi * G * sigma_star) hvr]

/-!
## Section 5: Bilinear Metriplectic Brackets vs. Helmholtz Free Energy Dissipation
-/

/-- **Theorem 5.1a (Metriplectic Energy Conservation under Radical Degeneracy)**:
For bilinear Poisson and dissipative brackets `pb db : V →ₗ[ℝ] V →ₗ[ℝ] ℝ` on a real
module `V`, if `pb` is alternating (`pb x x = 0`) and `H` lies in the left radical of `db`
(`db H F = 0`), then the metriplectic energy evolution rate `pb H H + db H S` vanishes. -/
theorem metriplectic_energy_rate_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (pb db : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (H S : V)
    (h_pb_skew : ∀ x : V, pb x x = 0)
    (h_db_H : ∀ F : V, db H F = 0) :
    pb H H + db H S = 0 := by
  rw [h_pb_skew H, h_db_H S, add_zero]

private theorem scalar_zero_of_linear_comb_eq_zero
    {β x c y : ℝ} (hβ : β ≠ 0) (h_comb : β * x + c * y = 0) (hy : y = 0) :
    x = 0 := by
  rw [hy, mul_zero, add_zero] at h_comb
  rcases mul_eq_zero.mp h_comb with hβ_zero | hx_zero
  · exact False.elim (hβ hβ_zero)
  · exact hx_zero

/-- **Theorem 5.1b (Collinear KMS Entropy Casimir Kills Bilinear Hamiltonian Flow)**:
In any real observable module `V` with bilinear Poisson bracket `pb : V →ₗ[ℝ] V →ₗ[ℝ] ℝ`,
if the KMS entropy observable decomposes as $S = \beta H + c I_{\mathrm{cas}}$ with $\beta \neq 0$
and $I_{\mathrm{cas}}$ a central Casimir (`pb F I_cas = 0`), then requiring $S$ to be a
Poisson Casimir (`pb F S = 0`) forces `pb F H = 0` for every observable $F \in V$. -/
theorem metriplectic_collinear_entropy_kills_hamiltonian_flow
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (pb : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (H S I_cas : V) (β c : ℝ)
    (hβ : β ≠ 0)
    (hS_decomp : S = β • H + c • I_cas)
    (h_cas_S : ∀ F : V, pb F S = 0)
    (h_cas_I : ∀ F : V, pb F I_cas = 0)
    (F : V) :
    pb F H = 0 := by
  have h_expand : β * pb F H + c * pb F I_cas = 0 := by
    have h0 : pb F S = 0 := h_cas_S F
    rw [hS_decomp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h0
    exact h0
  exact scalar_zero_of_linear_comb_eq_zero hβ h_expand (h_cas_I F)

/-- The Helmholtz free energy observable $\mathcal{F} = H - \beta^{-1} S \in V$. -/
noncomputable def helmholtzObservable
    {V : Type*} [AddCommGroup V] [Module ℝ V] (H S : V) (β : ℝ) : V :=
  H - β⁻¹ • S

/-- Under KMS stationarity (`pb H H = 0` and `pb S H = 0`), the reversible Hamiltonian
Poisson drift `pb (helmholtzObservable H S β) H` vanishes by bilinearity of `pb`. -/
theorem helmholtzObservable_poisson_drift_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (pb : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (H S : V) (β : ℝ)
    (h_pb_HH : pb H H = 0)
    (h_pb_SH : pb S H = 0) :
    pb (helmholtzObservable H S β) H = 0 := by
  dsimp [helmholtzObservable]
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, h_pb_HH, h_pb_SH, mul_zero, sub_zero]

/-- **Theorem 5.2 (Bilinear Helmholtz Free Energy Monotonic Dissipation)**:
Along the GENERIC / Lindblad flow $\dot{x} = \{x, H\} - (x, \mathcal{F})$ generated by
`helmholtzObservable H S β`, the free-energy evolution rate
$\dot{\mathcal{F}} = \{\mathcal{F}, H\} - (\mathcal{F}, \mathcal{F})$ is non-positive for
every positive-semidefinite dissipative bracket `db`, without requiring $S$ to be a
Poisson Casimir on $V$. -/
theorem helmholtzFreeEnergy_bracket_dissipation_nonpos
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (pb db : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (H S : V) (β : ℝ)
    (h_pb_HH : pb H H = 0)
    (h_pb_SH : pb S H = 0)
    (h_db_psd : ∀ x : V, 0 ≤ db x x) :
    pb (helmholtzObservable H S β) H -
      db (helmholtzObservable H S β) (helmholtzObservable H S β) ≤ 0 := by
  rw [helmholtzObservable_poisson_drift_zero pb H S β h_pb_HH h_pb_SH, zero_sub]
  exact neg_nonpos.mpr (h_db_psd (helmholtzObservable H S β))

/-- The scalar Helmholtz free energy $\mathcal{F}(E, S, \beta) = E - \beta^{-1} S$. -/
noncomputable def helmholtzFreeEnergy (E S β : ℝ) : ℝ :=
  E - S / β

/-- Exact difference decomposition of the Helmholtz free energy across two states
at fixed inverse temperature $\beta$:
$\mathcal{F}(E_2, S_2, \beta) - \mathcal{F}(E_1, S_1, \beta) = (E_2 - E_1) - \beta^{-1}(S_2 - S_1)$. -/
theorem helmholtzFreeEnergy_diff_eq (E₁ E₂ S₁ S₂ β : ℝ) :
    helmholtzFreeEnergy E₂ S₂ β - helmholtzFreeEnergy E₁ S₁ β =
      (E₂ - E₁) - (S₂ - S₁) / β := by
  dsimp [helmholtzFreeEnergy]
  ring

/-- When internal energy is conserved ($E_2 = E_1$) and entropy is non-decreasing
($S_1 \le S_2$) at positive inverse temperature ($\beta > 0$), the Helmholtz free energy
is monotonically non-increasing:
$\mathcal{F}(E_2, S_2, \beta) \le \mathcal{F}(E_1, S_1, \beta)$. -/
theorem helmholtzFreeEnergy_nonincreasing_of_energy_conserved
    {E₁ E₂ S₁ S₂ β : ℝ} (hE : E₂ = E₁) (hS : S₁ ≤ S₂) (hβ : 0 < β) :
    helmholtzFreeEnergy E₂ S₂ β ≤ helmholtzFreeEnergy E₁ S₁ β := by
  have h_diff :
      helmholtzFreeEnergy E₂ S₂ β - helmholtzFreeEnergy E₁ S₁ β =
        -((S₂ - S₁) / β) := by
    rw [helmholtzFreeEnergy_diff_eq, hE, sub_self, zero_sub]
  have hS_sub : 0 ≤ S₂ - S₁ := sub_nonneg.mpr hS
  have h_quot : 0 ≤ (S₂ - S₁) / β := div_nonneg hS_sub (le_of_lt hβ)
  linarith [h_diff, h_quot]

/-- Finite-dimensional non-negative symmetric metriplectic dissipation pairing
$(\mathcal{F}, \mathcal{F})_M = \sum_{i=1}^n w_i (\nabla_i \mathcal{F})^2$. -/
def weightedQuadraticDissipation {n : ℕ} (w gradF : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, w i * (gradF i) ^ 2

/-- For any non-negative metric weight profile $w_i \ge 0$, the weighted quadratic
dissipation pairing $(\mathcal{F}, \mathcal{F})_M$ is non-negative. -/
theorem weightedQuadraticDissipation_nonneg
    {n : ℕ} (w gradF : Fin n → ℝ) (hw : ∀ i : Fin n, 0 ≤ w i) :
    0 ≤ weightedQuadraticDissipation w gradF :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg (gradF i)))

/-- The componentwise Helmholtz thermodynamic force
$d\mathcal{F}_i = dH_i - \beta^{-1} dS_i$ on a finite state space $\operatorname{Fin} n$. -/
noncomputable def helmholtzForce {n : ℕ} (β : ℝ) (dH dS : Fin n → ℝ) (i : Fin n) : ℝ :=
  dH i - β⁻¹ * dS i

/-- The finite-dimensional Helmholtz free-energy dissipation rate
$\dot{\mathcal{F}} = -\sum_{i=1}^n \gamma_i (dH_i - \beta^{-1} dS_i)^2$ along a diagonal
Lindblad / GENERIC friction profile $\gamma_i \ge 0$. -/
noncomputable def helmholtzDissipationRate
    {n : ℕ} (β : ℝ) (γ dH dS : Fin n → ℝ) : ℝ :=
  - ∑ i : Fin n, γ i * (helmholtzForce β dH dS i) ^ 2

/-- **Theorem 5.3 (Helmholtz Dissipation Rate Non-Positivity & KMS Equilibrium Vanishing)**:
For any non-negative friction profile $\gamma_i \ge 0$, `helmholtzDissipationRate β γ dH dS ≤ 0`,
and at the Gibbs/KMS equilibrium $dS_i = \beta\, dH_i$ ($\beta \neq 0$) the thermodynamic force
`helmholtzForce β dH dS` vanishes identically without killing the Hamiltonian gradient $dH_i$. -/
theorem helmholtzDissipationRate_nonpos
    {n : ℕ} (β : ℝ) (γ dH dS : Fin n → ℝ) (hγ : ∀ i : Fin n, 0 ≤ γ i) :
    helmholtzDissipationRate β γ dH dS ≤ 0 := by
  dsimp [helmholtzDissipationRate]
  rw [neg_nonpos]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hγ i) (sq_nonneg (helmholtzForce β dH dS i)))

/-- At the Gibbs/KMS equilibrium $dS_i = \beta\, dH_i$ ($\beta \neq 0$), the Helmholtz
thermodynamic force vanishes identically while allowing $dH_i \neq 0$. -/
theorem helmholtzForce_eq_zero_at_gibbs
    {n : ℕ} (β : ℝ) (hβ : β ≠ 0) (dH dS : Fin n → ℝ)
    (h_gibbs : ∀ i : Fin n, dS i = β * dH i) (i : Fin n) :
    helmholtzForce β dH dS i = 0 := by
  dsimp [helmholtzForce]
  rw [h_gibbs i, ← mul_assoc, inv_mul_cancel₀ hβ, one_mul, sub_self]

/-!
## Section 6: Statistical Partition Function $Z(\beta)$ and Poincaré-Disk Radial Coordinate
-/

/-- A radial coordinate on the Poincaré disk for nonnegative input `β`:
$r_{\mathbb{D}}(\beta) = \tanh(\beta / 2) = \frac{e^{\beta / 2} - e^{-\beta / 2}}{e^{\beta / 2} + e^{-\beta / 2}}$,
mapping nonnegative `β` into `[0, 1)`. The theorems below establish bounds and strict
monotonicity on this domain, but do not package an inverse or a diffeomorphism theorem. -/
noncomputable def poincareDiskRadius (β : ℝ) : ℝ :=
  (Real.exp (β / 2) - Real.exp (-(β / 2))) /
    (Real.exp (β / 2) + Real.exp (-(β / 2)))

/-- At the maximum-entropy origin $\beta = 0$, the Poincaré disk radius vanishes:
$r_{\mathbb{D}}(0) = 0$. -/
theorem poincareDiskRadius_zero :
    poincareDiskRadius 0 = 0 := by
  dsimp [poincareDiskRadius]
  norm_num

/-- The hyperbolic cosine denominator $e^{\beta / 2} + e^{-\beta / 2}$ is strictly positive
for every $\beta \in \mathbb{R}$. -/
theorem poincareDiskRadius_pos_denom (β : ℝ) :
    0 < Real.exp (β / 2) + Real.exp (-(β / 2)) := by
  positivity

/-- For every $\beta \in \mathbb{R}$, the Poincaré disk radius lies strictly inside the
unit boundary horizon: $r_{\mathbb{D}}(\beta) < 1$. -/
theorem poincareDiskRadius_lt_one (β : ℝ) :
    poincareDiskRadius β < 1 := by
  dsimp [poincareDiskRadius]
  rw [div_lt_iff₀ (poincareDiskRadius_pos_denom β)]
  have h_exp : 0 < Real.exp (-(β / 2)) := Real.exp_pos (-(β / 2))
  linarith [h_exp]

/-- For every non-negative inverse temperature $\beta \ge 0$, the Poincaré disk radius
is non-negative: $0 \le r_{\mathbb{D}}(\beta)$. -/
theorem poincareDiskRadius_nonneg_of_nonneg {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ poincareDiskRadius β := by
  dsimp [poincareDiskRadius]
  have h_le : -(β / 2) ≤ β / 2 := by linarith [hβ]
  have h_exp_le : Real.exp (-(β / 2)) ≤ Real.exp (β / 2) :=
    Real.exp_le_exp.mpr h_le
  have h_num : 0 ≤ Real.exp (β / 2) - Real.exp (-(β / 2)) :=
    sub_nonneg.mpr h_exp_le
  exact div_nonneg h_num (le_of_lt (poincareDiskRadius_pos_denom β))

/-- Explicit boundary-gap identity:
$1 - r_{\mathbb{D}}(\beta) = \frac{2 e^{-\beta / 2}}{e^{\beta / 2} + e^{-\beta / 2}}$. -/
theorem one_sub_poincareDiskRadius_eq (β : ℝ) :
    1 - poincareDiskRadius β =
      (2 * Real.exp (-(β / 2))) /
        (Real.exp (β / 2) + Real.exp (-(β / 2))) := by
  dsimp [poincareDiskRadius]
  have h_denom_ne : Real.exp (β / 2) + Real.exp (-(β / 2)) ≠ 0 :=
    ne_of_gt (poincareDiskRadius_pos_denom β)
  calc
    1 - (Real.exp (β / 2) - Real.exp (-(β / 2))) /
          (Real.exp (β / 2) + Real.exp (-(β / 2)))
      = (Real.exp (β / 2) + Real.exp (-(β / 2))) /
          (Real.exp (β / 2) + Real.exp (-(β / 2))) -
        (Real.exp (β / 2) - Real.exp (-(β / 2))) /
          (Real.exp (β / 2) + Real.exp (-(β / 2))) := by
          rw [div_self h_denom_ne]
    _ = ((Real.exp (β / 2) + Real.exp (-(β / 2))) -
          (Real.exp (β / 2) - Real.exp (-(β / 2)))) /
          (Real.exp (β / 2) + Real.exp (-(β / 2))) := by
          rw [← sub_div]
    _ = (2 * Real.exp (-(β / 2))) /
          (Real.exp (β / 2) + Real.exp (-(β / 2))) := by
          ring

/-- The Poincaré disk radial map $\beta \mapsto r_{\mathbb{D}}(\beta) = \tanh(\beta / 2)$
is strictly increasing on $\mathbb{R}$. -/
theorem poincareDiskRadius_strictMono :
    StrictMono poincareDiskRadius := by
  intro β₁ β₂ hβ
  dsimp [poincareDiskRadius]
  rw [div_lt_div_iff₀ (poincareDiskRadius_pos_denom β₁) (poincareDiskRadius_pos_denom β₂)]
  have h_exp_lt :
      Real.exp (β₁ / 2) * Real.exp (-(β₂ / 2)) <
        Real.exp (β₂ / 2) * Real.exp (-(β₁ / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_lt_exp.mpr (by linarith [hβ])
  linarith [h_exp_lt]

/-- The canonical statistical partition function
$Z(\beta) = \sum_{i \in \iota} e^{-\beta E_i}$ over a finite state space $\iota$. -/
noncomputable def partitionFunction
    {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i : ι, Real.exp (-β * E i)

/-- At parameter value ($\beta = 0$), the canonical partition function equals the
cardinality $|\iota|$ of the state space. -/
theorem partitionFunction_zero
    {ι : Type*} [Fintype ι] (E : ι → ℝ) :
    partitionFunction E 0 = (Fintype.card ι : ℝ) := by
  dsimp [partitionFunction]
  simp

private theorem card_cast_ne_zero_of_nonempty
    {ι : Type*} [Fintype ι] [Nonempty ι] :
    (Fintype.card ι : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- **Theorem 6.1 (Non-Equivalence of Partition Function $Z(\beta)$ and Poincaré Disk Radius $r_{\mathbb{D}}(\beta)$)**:
For any non-empty finite state space $\iota$, $Z(0) = |\iota| \ge 1 \neq 0 = r_{\mathbb{D}}(0)$,
certifying that the partition function $Z(\beta)$ and the bounded Poincaré disk radius
$r_{\mathbb{D}}(\beta) = \tanh(\beta / 2)$ are distinct functions of $\beta$. -/
theorem partitionFunction_zero_ne_poincareDiskRadius_zero
    {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) :
    partitionFunction E 0 ≠ poincareDiskRadius 0 := by
  rw [partitionFunction_zero E, poincareDiskRadius_zero]
  exact card_cast_ne_zero_of_nonempty

/-- **Theorem 6.2 (Opposite Monotonicity of Partition Function $Z(\beta)$ vs. Poincaré Disk Radius $r_{\mathbb{D}}(\beta)$)**:
For strictly positive energy levels $E_i > 0$ on a non-empty finite state space $\iota$,
whenever $\beta_1 < \beta_2$ we have $Z(\beta_2) < Z(\beta_1)$ (strictly decreasing) while
$r_{\mathbb{D}}(\beta_1) < r_{\mathbb{D}}(\beta_2)$ (strictly increasing). -/
theorem partitionFunction_strictAnti_vs_poincareDiskRadius_strictMono
    {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ)
    (hE : ∀ i : ι, 0 < E i) {β₁ β₂ : ℝ} (hβ : β₁ < β₂) :
    partitionFunction E β₂ < partitionFunction E β₁ ∧
      poincareDiskRadius β₁ < poincareDiskRadius β₂ := by
  refine ⟨?_, poincareDiskRadius_strictMono hβ⟩
  dsimp [partitionFunction]
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => ?_)
  exact Real.exp_lt_exp.mpr (by nlinarith [hE i, hβ])

end InfoGeometry.Synthesis.SixArchitecturalCorrectionsSynthesis
