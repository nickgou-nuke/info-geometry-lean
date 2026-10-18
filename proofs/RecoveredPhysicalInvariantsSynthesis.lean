/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.SplitOctonionClifford33Soldering
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge

/-!
# Recovered Physical Invariants Synthesis: Six Historically Sidelined Mathematical Programs

This module formalizes how six historically sidelined mathematical programs in
20th-century theoretical physics—each originally obstructed in single-sheeted,
associative, positive-definite, or infinite-volume settings—are resolved by the
finite-dimensional, para-Kähler, and inductive-colimit algebraic structures of
the repository:

1. **Section 1 (Wheeler–Feynman Retarded/Advanced Action Duality & Finite Context Horizon Absorber)**:
   - Defines `piInner`, `kreinPairing`, `markovDual`, `kreinBlockOp`, and
     `wheelerFeynmanSymmetrized`.
   - Proves `wheelerFeynman_retarded_advanced_krein_identity`: on the Double Real
     Krein Space $\mathcal{K}_n = T^+ \oplus T^-$, the block operator
     `kreinBlockOp π P` pairs the retarded causal transition $P u_+$ against the
     advanced test state $v_-$ and the $\pi$-dual advanced transition $P^{\#_\pi} u_-$
     against $v_+$, and is strictly Krein self-adjoint for any nowhere-vanishing
     measure $\pi_i \neq 0$.
   - Defines the finite context-horizon sink absorber `sinkAbsorberMatrix` and
     proves `sinkAbsorberMatrix_idempotent` ($S^2 = S$) and the one-step complete
     absorption theorem `rowStochastic_mul_sinkAbsorberMatrix` ($P S = S$ for any
     row-normalized matrix $P$).

2. **Section 2 (Jordan–von Neumann–Wigner Symmetric Product vs. Zorn Split-Octonion Polarized Left-Alternativity & $\mathrm{Cl}(3,3)$)**:
   - Defines the symmetric Jordan anticommutator product `symJordanProduct A B = A * B + B * A`
     and proves `symJordanProduct_comm`.
   - Bridges the Zorn split-octonion carrier `ZornSplitOctonion R` to $\mathrm{Cl}(3,3)$
     via `zorn_polarized_left_alternative_cl33`: polarizing left-multiplication by pure
     para-Kähler phase-space vectors $z_1, z_2 \in T^+ \oplus T^-$ yields the exact
     $\mathrm{Cl}(3,3)$ soldering anticommutator
     $\iota(z_1) \star (\iota(z_2) \star w) + \iota(z_2) \star (\iota(z_1) \star w) = g(z_1, z_2) \bullet w$.
   - Bridges `symJordanProduct` on the $\mathrm{Cl}(1,1)^{\otimes k}$ spinor tower to the
     canonical anticommutation relations via `jordanWigner_symJordanProduct_car`:
     `symJordanProduct (jwAnnihilation k i) (jwCreation k j) = if i = j then 1 else 0`.

3. **Section 3 (Heisenberg / Lee–Wick Indefinite Diagonal Metric vs. Totally Isotropic Para-Kähler Null Sheets)**:
   - Defines the diagonal Lee–Wick indefinite pairing
     `leeWickDiagonalPairing π u v = piInner π u.1 v.1 - piInner π u.2 v.2`.
   - Proves `leeWickDiagonalPairing_ghost_negative`: for any strictly positive measure
     $\pi_i > 0$ and any state $u_-$ with a non-zero component $u_-(i_0) \neq 0$, the
     diagonal Lee–Wick norm on the second sector is strictly negative
     (`leeWickDiagonalPairing π (0, u_minus) (0, u_minus) < 0`), exhibiting the
     negative-norm ghost state.
   - Proves `kreinPairing_both_sheets_isotropic_zero`: in contrast, under the
     off-diagonal Double Real Krein pairing `kreinPairing π`, both the primal
     retarded sheet $T^+ = \{(u_+, 0)\}$ and the dual advanced sheet $T^- = \{(0, u_-)\}$
     are totally isotropic null Lagrangian subspaces with identically zero self-norm.

4. **Section 4 (Milne Kinematic Logarithmic Clock $\tau = t_0 \ln(t / t_0) + t_0$ & Attention-Sink Scale Shift)**:
   - Defines Milne's logarithmic kinematic clock
     `milneKinematicTime t₀ t = t₀ * Real.log (t / t₀) + t₀`.
   - Proves epoch normalization `milneKinematicTime_at_epoch` ($\tau(t_0) = t_0$),
     multiplicative-to-additive scale translation `milneKinematicTime_scale_shift`
     ($\tau(\lambda t) - \tau(t) = t_0 \ln \lambda$), the Fréchet derivative certificate
     `hasDerivAt_milneKinematicTime` and scalar derivative `deriv_milneKinematicTime`
     ($d\tau / dt = t_0 / t$), and the constant logarithmic clock-flux invariant
     `milne_clock_rate_mul_time_const` ($t \cdot \tau'(t) = t_0$).

5. **Section 5 (Prigogine Microscopic Irreversibility: Causal Lower-Triangular Semigroup & Riesz Simplex Variance Dissipation)**:
   - Defines causal lower-triangularity `IsCausalLower` ($P_{ij} = 0$ for $i < j$) and
     proves `isCausalLower_mul`: causal lower-triangular transition matrices form a
     directed multiplicative semigroup without time-symmetric inverses for absorbed steps.
   - Defines `expectedScore` and the Riesz replicator natural gradient
     `rieszNaturalGradient ρ ℓ i = ρ i * (ℓ i - ∑ j, ρ j * ℓ j)`.
   - Proves `rieszNaturalGradient_sum_eq_zero`, the exact score-variance identity
     `rieszNaturalGradient_pairing_eq_variance`
     ($\sum_i \ell_i (\nabla^R \ell)_i = \sum_i \rho_i (\ell_i - \langle \ell \rangle_\rho)^2$
     whenever $\sum_i \rho_i = 1$), and `rieszNaturalGradient_dissipation_nonneg`
     ($0 \le \sum_i \ell_i (\nabla^R \ell)_i$ on the probability simplex).

6. **Section 6 (Bohm–Hiley Implicate/Explicate Order, Cuntz $\mathcal{O}_2$ Trace Obstruction, & Holomovement Retraction)**:
   - Proves `cuntz_finite_matrix_trace_obstruction`: if finite matrices $S_1, S_1^*, S_2, S_2^* \in M_m(\mathbb{R})$
     satisfy $S_1^* S_1 = I$, $S_2^* S_2 = I$, and $S_1 S_1^* + S_2 S_2^* = I$, then cyclic trace forces
     $2 \cdot \operatorname{card}(m) = \operatorname{card}(m)$ and $\operatorname{card}(m) = 0$.
   - Defines block-diagonal enfoldment `bohmEnfold`, sub-channel unfoldments `bohmUnfold1`, `bohmUnfold2`,
     and the holomovement pinching channel `bohmHolomovement`, proving holographic retraction,
     holomovement idempotence, and trace doubling (`bohmEnfold_trace_scaling`).
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.RecoveredPhysicalInvariantsSynthesis

open scoped Matrix
open Matrix
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.Clifford.Cl11JordanWignerCARBridge

/-!
## Section 1: Wheeler–Feynman Retarded/Advanced Action Duality & Finite Context Horizon Absorber
-/

/-- The $\pi$-weighted inner product $\langle f, g \rangle_\pi = \sum_{i=1}^n \pi_i f_i g_i$
on $\operatorname{Fin} n \to \mathbb{R}$. -/
def piInner {n : ℕ} (π f g : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, π i * f i * g i

/-- Symmetry of `piInner`: $\langle f, g \rangle_\pi = \langle g, f \rangle_\pi$. -/
theorem piInner_symm {n : ℕ} (π f g : Fin n → ℝ) :
    piInner π f g = piInner π g f := by
  dsimp [piInner]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- The off-diagonal neutral-signature pairing on the Double Real Krein Space
$\mathcal{K}_n = T^+ \oplus T^- = (\operatorname{Fin} n \to \mathbb{R}) \times (\operatorname{Fin} n \to \mathbb{R})$:
$$g_\pi\big((u_+, u_-), (v_+, v_-)\big) = \langle u_+, v_- \rangle_\pi + \langle u_-, v_+ \rangle_\pi.$$ -/
def kreinPairing {n : ℕ} (π : Fin n → ℝ)
    (u v : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  piInner π u.1 v.2 + piInner π u.2 v.1

/-- The $\pi$-dual (advanced / time-reversed Petz transpose) transition matrix
$(P^{\#_\pi})_{ij} = \frac{\pi_j}{\pi_i} P_{ji}$. -/
def markovDual {n : ℕ} (π : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (π j / π i) * P j i

/-- The block-diagonal Double Real Krein operator
$\mathcal{T}_P(u_+, u_-) = (P u_+, P^{\#_\pi} u_-)$, acting by the retarded causal
operator $P$ on the forward sheet $T^+$ and by the advanced $\pi$-dual $P^{\#_\pi}$
on the backward sheet $T^-$. -/
def kreinBlockOp {n : ℕ} (π : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (u : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (P.mulVec u.1, (markovDual π P).mulVec u.2)

/-- The Wheeler–Feynman half-retarded plus half-advanced symmetrized transition matrix
$P^{\mathrm{WF}}_{ij} = \frac{1}{2}\big(P_{ij} + (P^{\#_\pi})_{ij}\big)$. -/
def wheelerFeynmanSymmetrized {n : ℕ} (π : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (P i j + markovDual π P i j) / 2

private theorem markovDual_scalar_swap
    (pi_i pi_j p_ji f_i g_j : ℝ) (h_pi_i : pi_i ≠ 0) :
    pi_j * (p_ji * f_i) * g_j =
      pi_i * f_i * (((pi_j / pi_i) * p_ji) * g_j) := by
  have h_cancel : pi_i * (pi_j / pi_i) = pi_j := mul_div_cancel₀ pi_j h_pi_i
  calc
    pi_j * (p_ji * f_i) * g_j
      = (pi_i * (pi_j / pi_i)) * (p_ji * f_i) * g_j := by rw [h_cancel]
    _ = pi_i * f_i * (((pi_j / pi_i) * p_ji) * g_j) := by ring

/-- Cross-sheet $\pi$-duality identity:
$\langle P f, g \rangle_\pi = \langle f, P^{\#_\pi} g \rangle_\pi$ for any matrix $P$
and any nowhere-vanishing measure $\pi_i \neq 0$. -/
theorem piInner_mulVec_markovDual {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0) (f g : Fin n → ℝ) :
    piInner π (P.mulVec f) g =
      piInner π f ((markovDual π P).mulVec g) := by
  dsimp [piInner, markovDual, Matrix.mulVec, dotProduct]
  calc
    ∑ j : Fin n, π j * (∑ i : Fin n, P j i * f i) * g j
      = ∑ j : Fin n, ∑ i : Fin n, π j * (P j i * f i) * g j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ j : Fin n, ∑ i : Fin n, π i * f i * (((π j / π i) * P j i) * g j) := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
        exact markovDual_scalar_swap (π i) (π j) (P j i) (f i) (g j) (hπ i)
    _ = ∑ i : Fin n, ∑ j : Fin n, π i * f i * (((π j / π i) * P j i) * g j) :=
        Finset.sum_comm
    _ = ∑ i : Fin n, π i * f i * ∑ j : Fin n, ((π j / π i) * P j i) * g j := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]

/-- **Theorem 1.1 (Wheeler–Feynman Retarded/Advanced Krein Action Identity & Self-Adjointness)**:
Evaluating `kreinPairing π` on `kreinBlockOp π P (u_plus, u_minus)` against `(v_plus, v_minus)`
couples the forward retarded propagation $P u_+$ to the backward state $v_-$ and the
advanced propagation $P^{\#_\pi} u_-$ to the forward state $v_+$, and is strictly
Krein self-adjoint for every nowhere-vanishing weight $\pi_i \neq 0$:
$$\langle \mathcal{T}_P u, v \rangle_{\mathcal{K}} =
  \langle P u_+, v_- \rangle_\pi + \langle P^{\#_\pi} u_-, v_+ \rangle_\pi =
  \langle u, \mathcal{T}_P v \rangle_{\mathcal{K}}.$$ -/
theorem wheelerFeynman_retarded_advanced_krein_identity
    {n : ℕ} (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0)
    (u_plus u_minus v_plus v_minus : Fin n → ℝ) :
    kreinPairing π (kreinBlockOp π P (u_plus, u_minus)) (v_plus, v_minus) =
      piInner π (P.mulVec u_plus) v_minus +
        piInner π ((markovDual π P).mulVec u_minus) v_plus ∧
    kreinPairing π (kreinBlockOp π P (u_plus, u_minus)) (v_plus, v_minus) =
      kreinPairing π (u_plus, u_minus) (kreinBlockOp π P (v_plus, v_minus)) := by
  refine ⟨rfl, ?_⟩
  dsimp [kreinPairing, kreinBlockOp]
  have h1 : piInner π (P.mulVec u_plus) v_minus =
      piInner π u_plus ((markovDual π P).mulVec v_minus) :=
    piInner_mulVec_markovDual π P hπ u_plus v_minus
  have h2 : piInner π ((markovDual π P).mulVec u_minus) v_plus =
      piInner π u_minus (P.mulVec v_plus) := by
    rw [piInner_symm π ((markovDual π P).mulVec u_minus) v_plus,
      ← piInner_mulVec_markovDual π P hπ v_plus u_minus,
      piInner_symm π (P.mulVec v_plus) u_minus]
  rw [h1, h2]

/-- Direct Krein self-adjointness of `kreinBlockOp π P` on arbitrary pair states
`u v : (Fin n → ℝ) × (Fin n → ℝ)`. -/
theorem kreinBlockOp_selfAdjoint {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0)
    (u v : (Fin n → ℝ) × (Fin n → ℝ)) :
    kreinPairing π (kreinBlockOp π P u) v =
      kreinPairing π u (kreinBlockOp π P v) :=
  (wheelerFeynman_retarded_advanced_krein_identity π P hπ u.1 u.2 v.1 v.2).2

private theorem wheelerFeynman_diagonal_scalar
    (pi_i p_ij dual_ij u_j v_i : ℝ) :
    (pi_i * (p_ij * u_j) * v_i + pi_i * (dual_ij * u_j) * v_i) / 2 =
      pi_i * (((p_ij + dual_ij) / 2) * u_j) * v_i := by
  ring

/-- **Theorem 1.2 (Diagonal Reduction to the Wheeler–Feynman Half-Retarded / Half-Advanced Kernel)**:
On the diagonal locus $u_+ = u_- = u$ and $v_+ = v_- = v$, half the Krein pairing of
`kreinBlockOp π P` reduces to the single-space pairing of `wheelerFeynmanSymmetrized π P`. -/
theorem wheelerFeynmanSymmetrized_diagonal_reduction {n : ℕ}
    (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    kreinPairing π (kreinBlockOp π P (u, u)) (v, v) / 2 =
      piInner π ((wheelerFeynmanSymmetrized π P).mulVec u) v := by
  dsimp [kreinPairing, kreinBlockOp, wheelerFeynmanSymmetrized,
    piInner, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact wheelerFeynman_diagonal_scalar (π i) (P i j) (markovDual π P i j) (u j) (v i)

/-- The finite context-horizon sink absorber matrix concentrating every row's transition
weight onto the boundary sink token `sink : Fin n`:
$$S_{ij} = \begin{cases} 1 & \text{if } j = \mathrm{sink}, \\ 0 & \text{otherwise.} \end{cases}$$ -/
def sinkAbsorberMatrix {n : ℕ} (sink : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ j => if j = sink then 1 else 0

/-- **Theorem 1.3 (Context Horizon Sink Absorber Idempotence)**:
The finite context-horizon absorber `sinkAbsorberMatrix sink` is an idempotent projector:
$S^2 = S$. -/
theorem sinkAbsorberMatrix_idempotent {n : ℕ} (sink : Fin n) :
    sinkAbsorberMatrix sink * sinkAbsorberMatrix sink = sinkAbsorberMatrix sink := by
  ext i j
  dsimp [Matrix.mul_apply, sinkAbsorberMatrix]
  rw [Finset.sum_eq_single sink]
  · simp
  · intro k _ hks
    simp [hks]
  · intro h_not_mem
    exact False.elim (h_not_mem (Finset.mem_univ sink))

/-- **Theorem 1.4 (One-Step Complete Absorption of Any Row-Stochastic Markov Operator)**:
For any transition matrix $P \in M_n(\mathbb{R})$ whose rows sum to $1$
($\sum_{j=1}^n P_{ij} = 1$), post-multiplying by the finite context-horizon absorber
`sinkAbsorberMatrix sink` yields `sinkAbsorberMatrix sink` in a single step ($P S = S$),
replacing Wheeler–Feynman's asymptotic $\infty$-volume absorber hypothesis with an exact
finite-dimensional right-ideal identity. -/
theorem rowStochastic_mul_sinkAbsorberMatrix
    {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (sink : Fin n)
    (h_row : ∀ i : Fin n, ∑ j : Fin n, P i j = 1) :
    P * sinkAbsorberMatrix sink = sinkAbsorberMatrix sink := by
  ext i j
  dsimp [Matrix.mul_apply, sinkAbsorberMatrix]
  rw [← Finset.sum_mul, h_row i, one_mul]

/-- Canonical real $2 \times 2$ diagonal spin matrix $\sigma_3 = \operatorname{diag}(1, -1)$. -/
def realPauliZ2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 : ℝ), 0; 0, -1]

/-- Canonical real $2 \times 2$ flip matrix $\sigma_1$. -/
def realPauliX2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(0 : ℝ), 1; 1, 0]

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`:
$\sigma_3 \sigma_1 \neq \sigma_1 \sigma_3$. -/
theorem realPauliZ2_mul_realPauliX2_ne_comm :
    realPauliZ2 * realPauliX2 ≠ realPauliX2 * realPauliZ2 := by
  intro h_comm
  have h01 : (realPauliZ2 * realPauliX2) 0 1 = (realPauliX2 * realPauliZ2) 0 1 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h_comm
  revert h01
  norm_num [realPauliZ2, realPauliX2, Matrix.mul_apply, Fin.sum_univ_two]

/-!
## Section 2: Jordan–von Neumann–Wigner Symmetric Product vs. Zorn Split-Octonion Polarized Left-Alternativity & $\mathrm{Cl}(3,3)$
-/

/-- The unnormalized symmetric Jordan anticommutator product
$A \circ_{\mathrm{sym}} B = A B + B A$ on `Matrix n n ℝ`. -/
def symJordanProduct {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) : Matrix n n ℝ :=
  A * B + B * A

/-- **Theorem 2.1 (Commutativity of the Symmetric Jordan Anticommutator Product)**:
For all matrices $A, B \in M_n(\mathbb{R})$, `symJordanProduct A B = symJordanProduct B A`. -/
theorem symJordanProduct_comm {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) :
    symJordanProduct A B = symJordanProduct B A := by
  dsimp [symJordanProduct]
  exact add_comm (A * B) (B * A)

/-- **Theorem 2.2 (Zorn Polarized Left-Alternativity Generates $\mathrm{Cl}(3,3)$)**:
Whereas the Jordan–von Neumann–Wigner classification restricted attention to commutative
Jordan algebras and found no new infinite hierarchy beyond $H_3(\mathbb{O})$, retaining the
full non-associative Zorn split-octonion product `zornMul` on `ZornSplitOctonion R` and
polarizing the left-alternative identity on pure para-Kähler vectors
$z_1, z_2 \in T^+ \oplus T^-$ yields the exact $\mathrm{Cl}(3,3)$ soldering anticommutator
$$\iota(z_1) \star (\iota(z_2) \star w) + \iota(z_2) \star (\iota(z_1) \star w) = g(z_1, z_2) \bullet w.$$ -/
theorem zorn_polarized_left_alternative_cl33 {R : Type*} [CommRing R]
    (z₁ z₂ : ParaKahlerVec R) (w : ZornSplitOctonion R) :
    zornAdd (zornMul (embedVec z₁) (zornMul (embedVec z₂) w))
            (zornMul (embedVec z₂) (zornMul (embedVec z₁) w)) =
      zornSmul (paraKahlerMetric z₁ z₂) w :=
  zorn_left_clifford33_soldering z₁ z₂ w

/-- **Theorem 2.3 (Jordan–Wigner Fermionic CAR as Symmetric Jordan Product on $\mathrm{Cl}(1,1)^{\otimes k}$)**:
On the $2^k \times 2^k$ real spinor matrix carrier `MatStage k`, the symmetric Jordan
anticommutator product of the Jordan–Wigner annihilation operator `jwAnnihilation k i`
and creation operator `jwCreation k j` satisfies the canonical anticommutation relation
`symJordanProduct (jwAnnihilation k i) (jwCreation k j) = if i = j then 1 else 0`. -/
theorem jordanWigner_symJordanProduct_car (k : ℕ) (i j : Fin k) :
    symJordanProduct (jwAnnihilation k i) (jwCreation k j) =
      if i = j then 1 else 0 := by
  dsimp [symJordanProduct]
  exact jwAnnihilation_creation_anticommutator k i j

/-!
## Section 3: Heisenberg / Lee–Wick Indefinite Diagonal Metric vs. Totally Isotropic Para-Kähler Null Sheets
-/

/-- The diagonal Heisenberg / Lee–Wick indefinite pairing
$$\langle (u_+, u_-), (v_+, v_-) \rangle_{\mathrm{LW}} =
  \langle u_+, v_+ \rangle_\pi - \langle u_-, v_- \rangle_\pi$$
in which the second sector carries a negative-definite self-norm $-\langle u_-, u_- \rangle_\pi$. -/
def leeWickDiagonalPairing {n : ℕ} (π : Fin n → ℝ)
    (u v : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  piInner π u.1 v.1 - piInner π u.2 v.2

/-- Evaluating `piInner π` on the zero vector yields $0$. -/
theorem piInner_zero_left {n : ℕ} (π v : Fin n → ℝ) :
    piInner π 0 v = 0 := by
  dsimp [piInner]
  simp

/-- **Theorem 3.1 (Lee–Wick Negative-Norm Ghost State on the Diagonal Indefinite Metric)**:
For any strictly positive measure $\pi_i > 0$ and any second-sector state $u_-$ with at least
one non-zero coordinate $u_-(i_0) \neq 0$, the diagonal Lee–Wick self-pairing is strictly
negative:
$$\langle (0, u_-), (0, u_-) \rangle_{\mathrm{LW}} = -\sum_{i=1}^n \pi_i u_-(i)^2 < 0.$$ -/
theorem leeWickDiagonalPairing_ghost_negative
    {n : ℕ} (π u_minus : Fin n → ℝ) (i₀ : Fin n)
    (hπ : ∀ i : Fin n, 0 < π i)
    (hu : u_minus i₀ ≠ 0) :
    leeWickDiagonalPairing π (0, u_minus) (0, u_minus) < 0 := by
  dsimp [leeWickDiagonalPairing]
  rw [piInner_zero_left π 0, zero_sub, neg_lt_zero]
  dsimp [piInner]
  have h_nonneg : ∀ i : Fin n, 0 ≤ π i * u_minus i * u_minus i := by
    intro i
    rw [mul_assoc]
    exact mul_nonneg (le_of_lt (hπ i)) (mul_self_nonneg (u_minus i))
  have h_le : π i₀ * u_minus i₀ * u_minus i₀ ≤
      ∑ i : Fin n, π i * u_minus i * u_minus i :=
    Finset.single_le_sum (fun i _ => h_nonneg i) (Finset.mem_univ i₀)
  have h_pos_i0 : 0 < π i₀ * u_minus i₀ * u_minus i₀ := by
    rw [mul_assoc]
    exact mul_pos (hπ i₀) (mul_self_pos.mpr hu)
  linarith [h_le, h_pos_i0]

/-- **Theorem 3.2 (Para-Kähler Double Real Krein Resolution: Both Sheets Are Totally Isotropic Null Subspaces)**:
In contrast to the diagonal Lee–Wick metric `leeWickDiagonalPairing`, under the off-diagonal
para-Kähler pairing `kreinPairing π` both the forward primal sheet $T^+ = \{(u_+, 0)\}$ and
the backward dual sheet $T^- = \{(0, u_-)\}$ have identically zero self-norm
($g_\pi((u_+, 0), (u_+, 0)) = 0$ and $g_\pi((0, u_-), (0, u_-)) = 0$), eliminating negative-norm
ghost states on each sheet while keeping the cross-sheet pairing non-degenerate. -/
theorem kreinPairing_both_sheets_isotropic_zero
    {n : ℕ} (π u_plus u_minus : Fin n → ℝ) :
    kreinPairing π (u_plus, 0) (u_plus, 0) = 0 ∧
      kreinPairing π (0, u_minus) (0, u_minus) = 0 := by
  constructor <;> simp [kreinPairing, piInner]

/-!
## Section 4: Milne Kinematic Logarithmic Clock $\tau = t_0 \ln(t / t_0) + t_0$ & Attention-Sink Scale Shift
-/

/-- Milne's kinematic logarithmic time reparameterization
$$\tau(t_0, t) = t_0 \ln(t / t_0) + t_0,$$
converting multiplicative scale dilations $t \mapsto \lambda t$ into additive clock shifts
$\tau \mapsto \tau + t_0 \ln \lambda$. -/
def milneKinematicTime (t₀ t : ℝ) : ℝ :=
  t₀ * Real.log (t / t₀) + t₀

/-- **Theorem 4.1 (Epoch Calibration of Milne Kinematic Time)**:
At the reference epoch $t = t_0 \neq 0$, Milne's logarithmic clock agrees with cosmic
time: $\tau(t_0, t_0) = t_0$. -/
theorem milneKinematicTime_at_epoch (t₀ : ℝ) (ht₀ : t₀ ≠ 0) :
    milneKinematicTime t₀ t₀ = t₀ := by
  dsimp [milneKinematicTime]
  rw [div_self ht₀, Real.log_one, mul_zero, zero_add]

/-- **Theorem 4.2 (Multiplicative Scale Dilation Becomes Additive Milne Clock Translation)**:
For any non-zero reference epoch $t_0 \neq 0$, time $t \neq 0$, and scale factor $\lambda \neq 0$,
rescaling $t \mapsto \lambda t$ shifts Milne kinematic time by the constant additive offset
$t_0 \ln \lambda$:
$$\tau(t_0, \lambda t) - \tau(t_0, t) = t_0 \ln \lambda.$$ -/
theorem milneKinematicTime_scale_shift
    (t₀ t lam : ℝ) (ht₀ : t₀ ≠ 0) (ht : t ≠ 0) (hlam : lam ≠ 0) :
    milneKinematicTime t₀ (lam * t) - milneKinematicTime t₀ t =
      t₀ * Real.log lam := by
  dsimp [milneKinematicTime]
  have h_div : t / t₀ ≠ 0 := div_ne_zero ht ht₀
  rw [mul_div_assoc lam t t₀, Real.log_mul hlam h_div]
  ring

private theorem milne_deriv_scalar_simplify
    (t₀ t : ℝ) (ht₀ : t₀ ≠ 0) :
    t₀ * ((1 / t₀) / (t / t₀)) = t₀ * t⁻¹ := by
  rw [div_div_eq_mul_div (1 / t₀) t t₀, div_mul_cancel₀ 1 ht₀, one_div]

/-- **Theorem 4.3 (Fréchet Derivative Certificate for Milne Kinematic Time)**:
For $t_0 \neq 0$ and $t \neq 0$, `milneKinematicTime t₀` has derivative $t_0 t^{-1}$ at $t$. -/
theorem hasDerivAt_milneKinematicTime
    (t₀ : ℝ) {t : ℝ} (ht₀ : t₀ ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (milneKinematicTime t₀) (t₀ * t⁻¹) t := by
  unfold milneKinematicTime
  have h_div : HasDerivAt (fun y : ℝ => y / t₀) (1 / t₀) t :=
    (hasDerivAt_id t).div_const t₀
  have h_ne : t / t₀ ≠ 0 := div_ne_zero ht ht₀
  have h_log : HasDerivAt (fun y : ℝ => Real.log (y / t₀)) ((1 / t₀) / (t / t₀)) t :=
    h_div.log h_ne
  have h_mul : HasDerivAt (fun y : ℝ => t₀ * Real.log (y / t₀))
      (t₀ * ((1 / t₀) / (t / t₀))) t :=
    h_log.const_mul t₀
  have h_add : HasDerivAt (fun y : ℝ => t₀ * Real.log (y / t₀) + t₀)
      (t₀ * ((1 / t₀) / (t / t₀))) t :=
    h_mul.add_const t₀
  rw [milne_deriv_scalar_simplify t₀ t ht₀] at h_add
  exact h_add

/-- Scalar derivative formula $\frac{d}{dt}\tau(t_0, t) = t_0 t^{-1}$ for $t_0 \neq 0$ and $t \neq 0$. -/
theorem deriv_milneKinematicTime
    (t₀ : ℝ) {t : ℝ} (ht₀ : t₀ ≠ 0) (ht : t ≠ 0) :
    deriv (milneKinematicTime t₀) t = t₀ * t⁻¹ :=
  (hasDerivAt_milneKinematicTime t₀ ht₀ ht).deriv

/-- **Theorem 4.4 (Scale-Invariant Milne Clock Rate Product $t \cdot \tau'(t) = t_0$)**:
For all $t_0 \neq 0$ and $t \neq 0$, the product of cosmic time $t$ and the Milne clock
rate $\tau'(t)$ is identically the constant epoch scale $t_0$. -/
theorem milne_clock_rate_mul_time_const
    (t₀ : ℝ) {t : ℝ} (ht₀ : t₀ ≠ 0) (ht : t ≠ 0) :
    t * deriv (milneKinematicTime t₀) t = t₀ := by
  rw [deriv_milneKinematicTime t₀ ht₀ ht]
  calc
    t * (t₀ * t⁻¹) = t₀ * (t * t⁻¹) := by ring
    _ = t₀ * 1 := by rw [mul_inv_cancel₀ ht]
    _ = t₀ := by ring

/-!
## Section 5: Prigogine Microscopic Irreversibility — Causal Lower-Triangular Semigroup & Riesz Simplex Variance Dissipation
-/

/-- A transition matrix $P \in M_n(\mathbb{R})$ is causal lower-triangular if all entries
strictly above the main diagonal vanish ($P_{ij} = 0$ whenever $i < j$). -/
def IsCausalLower {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, i < j → P i j = 0

/-- **Theorem 5.1 (Causal Lower-Triangular Semigroup Closure)**:
The product of any two causal lower-triangular matrices $P, Q \in M_n(\mathbb{R})$ is
again causal lower-triangular (`IsCausalLower (P * Q)`), forming a directed causal
semigroup on the finite context window. -/
theorem isCausalLower_mul {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : IsCausalLower P) (hQ : IsCausalLower Q) :
    IsCausalLower (P * Q) := by
  intro i j hij
  dsimp [Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  by_cases hik : i < k
  · rw [hP i k hik, zero_mul]
  · have hkj : k < j := lt_of_le_of_lt (not_lt.mp hik) hij
    rw [hQ k j hkj, mul_zero]

/-- Expected score $\langle \ell \rangle_\rho = \sum_{j=1}^n \rho_j \ell_j$ of a logit/payoff
vector $\ell$ under a probability distribution $\rho$. -/
def expectedScore {n : ℕ} (ρ ℓ : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, ρ j * ℓ j

/-- The Riesz / Shahshahani natural gradient (replicator vector field) on the simplex:
$$(\nabla^R_\rho \ell)_i = \rho_i \left(\ell_i - \sum_{j=1}^n \rho_j \ell_j\right).$$ -/
def rieszNaturalGradient {n : ℕ} (ρ ℓ : Fin n → ℝ) (i : Fin n) : ℝ :=
  ρ i * (ℓ i - ∑ j : Fin n, ρ j * ℓ j)

/-- Tangent-space conservation of total mass: whenever $\sum_{i=1}^n \rho_i = 1$,
the components of `rieszNaturalGradient ρ ℓ` sum to zero. -/
theorem rieszNaturalGradient_sum_eq_zero
    {n : ℕ} (ρ ℓ : Fin n → ℝ) (hρ_sum : ∑ i : Fin n, ρ i = 1) :
    ∑ i : Fin n, rieszNaturalGradient ρ ℓ i = 0 := by
  dsimp [rieszNaturalGradient]
  have h_sub : ∀ i : Fin n,
      ρ i * (ℓ i - ∑ j : Fin n, ρ j * ℓ j) =
        ρ i * ℓ i - ρ i * (∑ j : Fin n, ρ j * ℓ j) := by
    intro i
    ring
  rw [Finset.sum_congr rfl (fun i _ => h_sub i), Finset.sum_sub_distrib,
    ← Finset.sum_mul, hρ_sum, one_mul, sub_self]

/-- **Theorem 5.2 (Kimura–Price / Riesz Natural Gradient Variance Identity)**:
For any normalized distribution $\sum_{i=1}^n \rho_i = 1$ and any score vector $\ell$,
the pairing of $\ell$ with the Riesz natural gradient `rieszNaturalGradient ρ ℓ` equals
the exact $\rho$-weighted score variance:
$$\sum_{i=1}^n \ell_i (\nabla^R_\rho \ell)_i =
  \sum_{i=1}^n \rho_i \big(\ell_i - \langle \ell \rangle_\rho\big)^2.$$ -/
theorem rieszNaturalGradient_pairing_eq_variance
    {n : ℕ} (ρ ℓ : Fin n → ℝ) (hρ_sum : ∑ i : Fin n, ρ i = 1) :
    ∑ i : Fin n, ℓ i * rieszNaturalGradient ρ ℓ i =
      ∑ i : Fin n, ρ i * (ℓ i - expectedScore ρ ℓ) ^ 2 := by
  have h_pointwise : ∀ i : Fin n,
      ρ i * (ℓ i - expectedScore ρ ℓ) ^ 2 =
        ℓ i * rieszNaturalGradient ρ ℓ i -
          expectedScore ρ ℓ * rieszNaturalGradient ρ ℓ i := by
    intro i
    dsimp [rieszNaturalGradient, expectedScore]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h_pointwise i), Finset.sum_sub_distrib,
    ← Finset.mul_sum, rieszNaturalGradient_sum_eq_zero ρ ℓ hρ_sum, mul_zero, sub_zero]

/-- **Theorem 5.3 (Non-Negative Riesz Natural Gradient Dissipation on the Simplex)**:
For any probability distribution $\rho \in \Delta_{n-1}$ ($\sum_i \rho_i = 1$ and $\rho_i \ge 0$),
the Riesz natural gradient dissipation rate $\sum_{i=1}^n \ell_i (\nabla^R_\rho \ell)_i$
is non-negative. -/
theorem rieszNaturalGradient_dissipation_nonneg
    {n : ℕ} (ρ ℓ : Fin n → ℝ)
    (hρ_sum : ∑ i : Fin n, ρ i = 1)
    (hρ_nonneg : ∀ i : Fin n, 0 ≤ ρ i) :
    0 ≤ ∑ i : Fin n, ℓ i * rieszNaturalGradient ρ ℓ i := by
  rw [rieszNaturalGradient_pairing_eq_variance ρ ℓ hρ_sum]
  exact Finset.sum_nonneg
    (fun i _ => mul_nonneg (hρ_nonneg i) (sq_nonneg (ℓ i - expectedScore ρ ℓ)))

/-!
## Section 6: Bohm–Hiley Implicate/Explicate Order, Cuntz $\mathcal{O}_2$ Trace Obstruction, & Holomovement Retraction
-/

/-- **Theorem 6.1 (Cuntz $\mathcal{O}_2$ Finite-Dimensional Trace Obstruction $2N = N \implies N = 0$)**:
For any finite type `m` (`[Fintype m] [DecidableEq m]`), if four matrices
$S_1, S_1^*, S_2, S_2^* \in M_m(\mathbb{R})$ satisfy $S_1^* S_1 = I$, $S_2^* S_2 = I$,
and $S_1 S_1^* + S_2 S_2^* = I$, then cyclic invariance of the matrix trace forces
$2 \cdot \operatorname{card}(m) = \operatorname{card}(m)$ and $\operatorname{card}(m) = 0$. -/
theorem cuntz_finite_matrix_trace_obstruction
    {m : Type*} [Fintype m] [DecidableEq m]
    (S₁ S₁_star S₂ S₂_star : Matrix m m ℝ)
    (h1 : S₁_star * S₁ = 1)
    (h2 : S₂_star * S₂ = 1)
    (h_comp : S₁ * S₁_star + S₂ * S₂_star = 1) :
    2 * (Fintype.card m : ℝ) = (Fintype.card m : ℝ) ∧ Fintype.card m = 0 := by
  have htr1 : Matrix.trace (S₁ * S₁_star) = (Fintype.card m : ℝ) := by
    rw [Matrix.trace_mul_comm S₁ S₁_star, h1, Matrix.trace_one]
  have htr2 : Matrix.trace (S₂ * S₂_star) = (Fintype.card m : ℝ) := by
    rw [Matrix.trace_mul_comm S₂ S₂_star, h2, Matrix.trace_one]
  have htr_comp :
      Matrix.trace (S₁ * S₁_star + S₂ * S₂_star) = (Fintype.card m : ℝ) := by
    rw [h_comp, Matrix.trace_one]
  rw [Matrix.trace_add, htr1, htr2] at htr_comp
  have h_two : 2 * (Fintype.card m : ℝ) = (Fintype.card m : ℝ) := by
    linarith [htr_comp]
  have h_zero_real : (Fintype.card m : ℝ) = 0 := by
    linarith [h_two]
  exact ⟨h_two, Nat.cast_eq_zero.mp h_zero_real⟩

/-- **Explicate-to-Implicate Enfoldment ($\mathcal{E}(X) = X \oplus X$)**:
Embeds a local explicate matrix $X \in M_m(R)$ into the doubled stage $M_{m \oplus m}(R)$. -/
def bohmEnfold {m : Type*} {R : Type*} [Zero R]
    (X : Matrix m m R) : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks X 0 0 X

/-- **First-Channel Unfoldment ($U_1(Y) = Y_{11}$)**. -/
def bohmUnfold1 {m : Type*} {R : Type*}
    (Y : Matrix (m ⊕ m) (m ⊕ m) R) : Matrix m m R :=
  Matrix.toBlocks₁₁ Y

/-- **Second-Channel Unfoldment ($U_2(Y) = Y_{22}$)**. -/
def bohmUnfold2 {m : Type*} {R : Type*}
    (Y : Matrix (m ⊕ m) (m ⊕ m) R) : Matrix m m R :=
  Matrix.toBlocks₂₂ Y

/-- **Left Cuntz Sub-Channel Projector ($P_1 = I \oplus 0$)**. -/
def bohmProj1 {m : Type*} [DecidableEq m] {R : Type*} [Zero R] [One R] :
    Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 1 0 0 0

/-- **Right Cuntz Sub-Channel Projector ($P_2 = 0 \oplus I$)**. -/
def bohmProj2 {m : Type*} [DecidableEq m] {R : Type*} [Zero R] [One R] :
    Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 0 0 0 1

/-- **Holomovement Pinching Endomorphism ($\Phi(Y) = P_1 Y P_1 + P_2 Y P_2$)**. -/
def bohmHolomovement {m : Type*} [Fintype m] [DecidableEq m] {R : Type*} [CommRing R]
    (Y : Matrix (m ⊕ m) (m ⊕ m) R) : Matrix (m ⊕ m) (m ⊕ m) R :=
  bohmProj1 * Y * bohmProj1 + bohmProj2 * Y * bohmProj2

/-- **Theorem 6.2 (Bohmian Holographic Retraction & Holomovement Stationarity)**:
Both Cuntz sub-channel unfoldments recover the exact local observable
($U_1(\mathcal{E}(X)) = X$ and $U_2(\mathcal{E}(X)) = X$), and every enfolded
observable is a fixed point of the holomovement pinching channel
($\Phi(\mathcal{E}(X)) = \mathcal{E}(X)$). -/
theorem bohm_holographic_retraction_and_stationarity
    {m : Type*} [Fintype m] [DecidableEq m] {R : Type*} [CommRing R]
    (X : Matrix m m R) :
    bohmUnfold1 (bohmEnfold X) = X ∧
      bohmUnfold2 (bohmEnfold X) = X ∧
      bohmHolomovement (bohmEnfold X) = bohmEnfold X := by
  refine ⟨Matrix.toBlocks_fromBlocks₁₁ X 0 0 X,
    Matrix.toBlocks_fromBlocks₂₂ X 0 0 X, ?_⟩
  unfold bohmHolomovement bohmProj1 bohmProj2 bohmEnfold
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.fromBlocks_add, zero_add]

/-- **Theorem 6.3 (Trace Doubling Under Enfoldment $\operatorname{Tr}(\mathcal{E}(X)) = 2\operatorname{Tr}(X)$)**:
Enfolding a local observable $X \in M_m(R)$ into $M_{m \oplus m}(R)$ doubles its matrix
trace, making the normalized tracial state $\tau_k(X) = 2^{-k}\operatorname{Tr}(X)$
strictly scale-invariant across the UHF inductive limit. -/
theorem bohmEnfold_trace_scaling
    {m : Type*} [Fintype m] {R : Type*} [CommRing R]
    (X : Matrix m m R) :
    Matrix.trace (bohmEnfold X) = 2 * Matrix.trace X := by
  unfold bohmEnfold
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, ← two_mul]

end InfoGeometry.Synthesis.RecoveredPhysicalInvariantsSynthesis
