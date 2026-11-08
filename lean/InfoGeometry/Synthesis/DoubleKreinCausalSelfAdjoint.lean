/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Double Real Krein Space Causal Self-Adjointness & Wheeler–Feynman Absorber Duality

This module formalizes the indefinite neutral-signature **Double Real Krein Space**
$\mathcal{K}_n = \mathbb{R}^n_+ \oplus \mathbb{R}^n_-$ and proves that any directed or
strictly causal lower-triangular transition matrix $P \in M_n(\mathbb{R})$ lifts to a
strictly Krein self-adjoint (and $\Omega_\pi$-symplectic self-adjoint) block-diagonal
operator $\mathbb{P}_P = P \oplus P^{*_\pi}$ without collapsing causal propagation on
the primal null sheet:

1. **Weighted $L^2(\pi)$ Inner Product & $\pi$-Adjoint (`l2PiInner`, `piAdjoint`)**:
   - Defines `l2PiInner`, `matVec`, and `piAdjoint`, and proves symmetry `l2PiInner_symm`,
     involution `piAdjoint_involutive`, causal-to-anti-causal triangular duality
     `piAdjoint_upperTriangular_of_causal`, and cross-sheet $L^2(\pi)$ adjointness
     `l2PiInner_matVec_piAdjoint`.
2. **Double Real Krein Space & Para-Kähler Polarization (`DoubleKreinSpace`)**:
   - Defines `DoubleKreinSpace`, `primalKreinSheet`, `dualKreinSheet`, the split-signature
     metric `kreinMetricPi`, the para-Kähler symplectic form `kreinSymplecticPi`, the
     polarization involution `kreinPolarizationK`, the Möbius sheet swap `kreinMobiusSwap`,
     and the lifted operator `doubleKreinOp`.
3. **Krein & Symplectic Self-Adjointness, Möbius Intertwining, and KMS Diagonal Shadow**:
   - Proves `doubleKreinOp_preserves_primal_and_dual_null_sheets`,
     `doubleKreinOp_krein_selfAdjoint`,
     `doubleKreinOp_commutes_with_K_and_symplectic_selfAdjoint`,
     `mobiusSwap_intertwines_causal_and_retrodictive`, and
     `doubleKreinOp_diagonal_shadow_eq_kmsSymmetrized`.
4. **Non-Vacuous $2 \times 2$ Causal Witness (`causalWitnessP`, `uniformPi2`)**:
   - Exhibits an explicit causal lower-triangular Markov matrix with non-zero strict
     lower-triangular entry and certifies its Krein self-adjointness on $\mathcal{K}_2$
     in `causalWitnessP_nonVacuous_krein_selfAdjoint`.
5. **Multi-Step Causal Semigroup & Wheeler–Feynman Sink Absorber**:
   - Proves that causal lower-triangular matrices form a multiplicative semigroup
     (`isCausalLowerTriangular_mul`), that `piAdjoint` reverses multi-step composition
     (`piAdjoint_mul`), and that the pure attention-sink absorber is idempotent
     (`pureSinkAbsorber_mul_self`).
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.DoubleKreinCausalSelfAdjoint

open scoped Matrix
open Matrix

/-!
## Section 1: Weighted $L^2(\pi)$ Inner Product & $\pi$-Adjoint Duality
-/

/-- The $\pi$-weighted $L^2(\pi)$ inner product
$\langle u, v \rangle_\pi = \sum_{i=1}^n \pi_i u_i v_i$ on $\operatorname{Fin} n \to \mathbb{R}$. -/
def l2PiInner {n : ℕ} (π u v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, π i * u i * v i

/-- Symmetry of the $\pi$-weighted inner product:
$\langle u, v \rangle_\pi = \langle v, u \rangle_\pi$. -/
theorem l2PiInner_symm {n : ℕ} (π u v : Fin n → ℝ) :
    l2PiInner π u v = l2PiInner π v u := by
  dsimp [l2PiInner]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- Matrix-vector action $(P u)_i = \sum_{j=1}^n P_{ij} u_j$ on $\operatorname{Fin} n \to \mathbb{R}$. -/
def matVec {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, P i j * u j

/-- The $\pi$-adjoint (time-reversed / Petz transpose) matrix
$(P^{*_\pi})_{ij} = \frac{\pi_j}{\pi_i} P_{ji}$. -/
noncomputable def piAdjoint {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (π j / π i) * P j i

/-- A matrix $P \in M_n(\mathbb{R})$ is strictly causal (lower-triangular) if all entries
strictly above the main diagonal vanish ($P_{ij} = 0$ whenever $i < j$). -/
def IsCausalLowerTriangular {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, i < j → P i j = 0

/-- A matrix $Q \in M_n(\mathbb{R})$ is retrodictive / anti-causal (upper-triangular) if
all entries strictly below the main diagonal vanish ($Q_{ij} = 0$ whenever $j < i$). -/
def IsAntiCausalUpperTriangular {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, j < i → Q i j = 0

private theorem piAdjoint_involutive_scalar
    (pi_i pi_j p_ij : ℝ) (hπi : pi_i ≠ 0) (hπj : pi_j ≠ 0) :
    (pi_j / pi_i) * ((pi_i / pi_j) * p_ij) = p_ij := by
  field_simp [hπi, hπj]

/-- **Theorem 1.1 ($\pi$-Adjoint Involution)**:
For any nowhere-vanishing weight distribution $\pi$ ($\pi_i \neq 0$), the $\pi$-adjoint
operation $P \mapsto P^{*_\pi}$ is an involution: $(P^{*_\pi})^{*_\pi} = P$. -/
theorem piAdjoint_involutive {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0) :
    piAdjoint (piAdjoint P π) π = P := by
  ext i j
  dsimp [piAdjoint]
  exact piAdjoint_involutive_scalar (π i) (π j) (P i j) (hπ i) (hπ j)

/-- **Theorem 1.2 (Causal-to-Retrodictive Triangular Duality)**:
If $P$ is causal lower-triangular ($P_{ij} = 0$ for $i < j$), then its $\pi$-adjoint
$P^{*_\pi}$ is upper-triangular ($(P^{*_\pi})_{ij} = 0$ for $j < i$). -/
theorem piAdjoint_upperTriangular_of_causal {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hP : IsCausalLowerTriangular P) :
    IsAntiCausalUpperTriangular (piAdjoint P π) := by
  intro i j hji
  dsimp [piAdjoint]
  rw [hP j i hji, mul_zero]

/-- Pointwise scalar identity underlying $L^2(\pi)$ adjointness of `piAdjoint`. -/
theorem krein_dual_scalar_identity
    (pi_i pi_j p_ji u_j v_i : ℝ) (h_pi_i : pi_i ≠ 0) :
    pi_j * (p_ji * u_j) * v_i =
      pi_i * u_j * (((pi_j / pi_i) * p_ji) * v_i) := by
  have h1 : pi_i * (pi_j / pi_i) = pi_j := mul_div_cancel₀ pi_j h_pi_i
  calc
    pi_j * (p_ji * u_j) * v_i
      = (pi_i * (pi_j / pi_i)) * (p_ji * u_j) * v_i := by rw [h1]
    _ = pi_i * u_j * (((pi_j / pi_i) * p_ji) * v_i) := by ring

/-- **Theorem 1.3 (Cross-Sheet $L^2(\pi)$ Adjoint Identity)**:
For any matrix $P \in M_n(\mathbb{R})$ and any nowhere-vanishing distribution $\pi$,
$\langle P u, v \rangle_\pi = \langle u, P^{*_\pi} v \rangle_\pi$. -/
theorem l2PiInner_matVec_piAdjoint {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0) (u v : Fin n → ℝ) :
    l2PiInner π (matVec P u) v = l2PiInner π u (matVec (piAdjoint P π) v) := by
  dsimp [l2PiInner, matVec, piAdjoint]
  calc
    ∑ j : Fin n, π j * (∑ i : Fin n, P j i * u i) * v j
      = ∑ j : Fin n, ∑ i : Fin n, π j * (P j i * u i) * v j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ j : Fin n, ∑ i : Fin n, π i * u i * (((π j / π i) * P j i) * v j) := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
        exact krein_dual_scalar_identity (π i) (π j) (P j i) (u i) (v j) (hπ i)
    _ = ∑ i : Fin n, ∑ j : Fin n, π i * u i * (((π j / π i) * P j i) * v j) :=
        Finset.sum_comm
    _ = ∑ i : Fin n, π i * u i * ∑ j : Fin n, ((π j / π i) * P j i) * v j := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]

/-!
## Section 2: Double Real Krein Space & Para-Kähler Polarization
-/

/-- The $2n$-dimensional **Double Real Krein Space**
$\mathcal{K}_n = \mathbb{R}^n_+ \oplus \mathbb{R}^n_- = (\operatorname{Fin} n \to \mathbb{R}) \times (\operatorname{Fin} n \to \mathbb{R})$. -/
abbrev DoubleKreinSpace (n : ℕ) : Type :=
  (Fin n → ℝ) × (Fin n → ℝ)

/-- Canonical embedding of the primal (causal predictive) null sheet
$\mathbb{R}^n_+ \hookrightarrow \mathcal{K}_n$, $u \mapsto (u, 0)$. -/
def primalKreinSheet {n : ℕ} (u : Fin n → ℝ) : DoubleKreinSpace n :=
  (u, 0)

/-- Canonical embedding of the dual (retrodictive) null sheet
$\mathbb{R}^n_- \hookrightarrow \mathcal{K}_n$, $v \mapsto (0, v)$. -/
def dualKreinSheet {n : ℕ} (v : Fin n → ℝ) : DoubleKreinSpace n :=
  (0, v)

/-- The split-signature $(n, n)$ Krein metric pairing on $\mathcal{K}_n$:
$\eta_\pi((u_+, u_-), (v_+, v_-)) = \langle u_+, v_- \rangle_\pi + \langle u_-, v_+ \rangle_\pi$. -/
def kreinMetricPi {n : ℕ} (π : Fin n → ℝ) (x y : DoubleKreinSpace n) : ℝ :=
  l2PiInner π x.1 y.2 + l2PiInner π x.2 y.1

/-- The para-Kähler symplectic form on $\mathcal{K}_n$:
$\Omega_\pi((u_+, u_-), (v_+, v_-)) = \langle u_+, v_- \rangle_\pi - \langle u_-, v_+ \rangle_\pi$. -/
def kreinSymplecticPi {n : ℕ} (π : Fin n → ℝ) (x y : DoubleKreinSpace n) : ℝ :=
  l2PiInner π x.1 y.2 - l2PiInner π x.2 y.1

/-- The para-complex polarization involution $K(u_+, u_-) = (u_+, -u_-)$ with $K^2 = I_{2n}$,
whose $+1$ and $-1$ eigenspaces are the primal and dual null sheets. -/
def kreinPolarizationK {n : ℕ} (x : DoubleKreinSpace n) : DoubleKreinSpace n :=
  (x.1, -x.2)

/-- The Möbius sheet-swap involution $J_{\mathrm{swap}}(u_+, u_-) = (u_-, u_+)$ exchanging
the primal causal sheet and the dual retrodictive sheet. -/
def kreinMobiusSwap {n : ℕ} (x : DoubleKreinSpace n) : DoubleKreinSpace n :=
  (x.2, x.1)

/-- The lifted **Double Real Krein Operator** $\mathbb{P}_P = P \oplus P^{*_\pi}$ acting by
$P$ on the primal sheet $\mathbb{R}^n_+$ and by $P^{*_\pi}$ on the dual sheet $\mathbb{R}^n_-$. -/
noncomputable def doubleKreinOp {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (x : DoubleKreinSpace n) : DoubleKreinSpace n :=
  (matVec P x.1, matVec (piAdjoint P π) x.2)

/-!
## Section 3: Null-Sheet Preservation, Krein & Symplectic Self-Adjointness, and KMS Shadow
-/

/-- Action of any matrix `P` on the zero vector is zero. -/
theorem matVec_zero {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) :
    matVec P 0 = 0 := by
  ext i
  dsimp [matVec]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  change P i j * 0 = 0
  exact mul_zero (P i j)

/-- Action of any matrix `P` commutes with vector negation. -/
theorem matVec_neg {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    matVec P (-u) = -matVec P u := by
  ext i
  dsimp [matVec]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact mul_neg (P i j) (u j)

/-- **Theorem 3.1 (Double Krein Operator Preserves Primal & Dual Null Lagrangian Sheets)**:
Both the primal sheet `primalKreinSheet` and the dual sheet `dualKreinSheet` are totally
$\eta_\pi$-isotropic (null), and `doubleKreinOp P π` preserves both sheets while acting by
the exact unmodified causal operator $P$ on the primal sheet. -/
theorem doubleKreinOp_preserves_primal_and_dual_null_sheets {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π u v : Fin n → ℝ) :
    kreinMetricPi π (primalKreinSheet u) (primalKreinSheet v) = 0 ∧
    kreinMetricPi π (dualKreinSheet u) (dualKreinSheet v) = 0 ∧
    doubleKreinOp P π (primalKreinSheet u) = primalKreinSheet (matVec P u) ∧
    doubleKreinOp P π (dualKreinSheet v) = dualKreinSheet (matVec (piAdjoint P π) v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [kreinMetricPi, primalKreinSheet, l2PiInner]
    have h1 : ∑ i : Fin n, π i * u i * 0 = 0 :=
      Finset.sum_eq_zero (fun i _ => mul_zero (π i * u i))
    have h2 : ∑ i : Fin n, π i * 0 * v i = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [mul_zero (π i), zero_mul (v i)])
    rw [h1, h2, add_zero]
  · dsimp [kreinMetricPi, dualKreinSheet, l2PiInner]
    have h1 : ∑ i : Fin n, π i * 0 * v i = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [mul_zero (π i), zero_mul (v i)])
    have h2 : ∑ i : Fin n, π i * u i * 0 = 0 :=
      Finset.sum_eq_zero (fun i _ => mul_zero (π i * u i))
    rw [h1, h2, add_zero]
  · dsimp [doubleKreinOp, primalKreinSheet]
    rw [matVec_zero (piAdjoint P π)]
  · dsimp [doubleKreinOp, dualKreinSheet]
    rw [matVec_zero P]

/-- **Theorem 3.2 (Exact Krein Self-Adjointness of Any Directed or Causal Operator $P$)**:
For any matrix $P \in M_n(\mathbb{R})$ (including strictly causal lower-triangular matrices)
and any nowhere-vanishing weight distribution $\pi$, the lifted operator
$\mathbb{P}_P = P \oplus P^{*_\pi}$ is strictly self-adjoint with respect to `kreinMetricPi`:
$$\eta_\pi(\mathbb{P}_P x, y) = \eta_\pi(x, \mathbb{P}_P y).$$ -/
theorem doubleKreinOp_krein_selfAdjoint {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0)
    (x y : DoubleKreinSpace n) :
    kreinMetricPi π (doubleKreinOp P π x) y =
      kreinMetricPi π x (doubleKreinOp P π y) := by
  dsimp [kreinMetricPi, doubleKreinOp]
  have h1 : l2PiInner π (matVec P x.1) y.2 =
      l2PiInner π x.1 (matVec (piAdjoint P π) y.2) :=
    l2PiInner_matVec_piAdjoint P π hπ x.1 y.2
  have h2 : l2PiInner π (matVec (piAdjoint P π) x.2) y.1 =
      l2PiInner π x.2 (matVec P y.1) := by
    rw [l2PiInner_symm π (matVec (piAdjoint P π) x.2) y.1,
        ← l2PiInner_matVec_piAdjoint P π hπ y.1 x.2,
        l2PiInner_symm π (matVec P y.1) x.2]
  rw [h1, h2]

/-- **Theorem 3.3 (Para-Kähler Polarization Commutation & Symplectic Self-Adjointness)**:
The lifted operator $\mathbb{P}_P = P \oplus P^{*_\pi}$ commutes with the para-complex
polarization $K(u_+, u_-) = (u_+, -u_-)$ and is simultaneously self-adjoint with respect
to the para-Kähler symplectic form `kreinSymplecticPi`:
$$\Omega_\pi(\mathbb{P}_P x, y) = \Omega_\pi(x, \mathbb{P}_P y).$$ -/
theorem doubleKreinOp_commutes_with_K_and_symplectic_selfAdjoint {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0)
    (x y : DoubleKreinSpace n) :
    doubleKreinOp P π (kreinPolarizationK x) =
      kreinPolarizationK (doubleKreinOp P π x) ∧
    kreinSymplecticPi π (doubleKreinOp P π x) y =
      kreinSymplecticPi π x (doubleKreinOp P π y) := by
  refine ⟨?_, ?_⟩
  · dsimp [doubleKreinOp, kreinPolarizationK]
    rw [matVec_neg (piAdjoint P π) x.2]
  · dsimp [kreinSymplecticPi, doubleKreinOp]
    have h1 : l2PiInner π (matVec P x.1) y.2 =
        l2PiInner π x.1 (matVec (piAdjoint P π) y.2) :=
      l2PiInner_matVec_piAdjoint P π hπ x.1 y.2
    have h2 : l2PiInner π (matVec (piAdjoint P π) x.2) y.1 =
        l2PiInner π x.2 (matVec P y.1) := by
      rw [l2PiInner_symm π (matVec (piAdjoint P π) x.2) y.1,
          ← l2PiInner_matVec_piAdjoint P π hπ y.1 x.2,
          l2PiInner_symm π (matVec P y.1) x.2]
    rw [h1, h2]

/-- **Theorem 3.4 (Möbius Sheet-Swap Intertwining $J_{\mathrm{swap}} \mathbb{P}_P J_{\mathrm{swap}} = \mathbb{P}_{P^{*_\pi}}$)**:
Conjugating the Double Krein Operator $\mathbb{P}_P$ by the Möbius sheet swap `kreinMobiusSwap`
exchanges the forward causal operator $P$ with its retrodictive $\pi$-adjoint $P^{*_\pi}$. -/
theorem mobiusSwap_intertwines_causal_and_retrodictive {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0)
    (x : DoubleKreinSpace n) :
    kreinMobiusSwap (doubleKreinOp P π (kreinMobiusSwap x)) =
      doubleKreinOp (piAdjoint P π) π x := by
  dsimp [kreinMobiusSwap, doubleKreinOp]
  rw [piAdjoint_involutive P π hπ]

/-- The KMS-symmetrized transition matrix
$P_{\mathrm{sym}} = \frac{1}{2}(P + P^{*_\pi})$. -/
noncomputable def kmsSymmetrized {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (P i j + piAdjoint P π i j) / 2

private theorem kms_half_sum_mul_scalar (p_ij q_ij u_j : ℝ) :
    (p_ij * u_j + q_ij * u_j) / 2 = ((p_ij + q_ij) / 2) * u_j := by
  ring

private theorem kms_diagonal_pairing_scalar (pi_i a_i b_i v_i : ℝ) :
    pi_i * a_i * v_i + pi_i * b_i * v_i =
      2 * (pi_i * ((a_i + b_i) / 2) * v_i) := by
  ring

/-- **Theorem 3.5 (Diagonal KMS Shadow of the Double Krein Operator)**:
The KMS-symmetrized operator $P_{\mathrm{sym}} = \frac{1}{2}(P + P^{*_\pi})$ is the
diagonal half-sum shadow of `doubleKreinOp P π` restricted to the diagonal subspace
$\{(u, u) \in \mathcal{K}_n\}$, and the Krein pairing on the diagonal equals twice the
$L^2(\pi)$ pairing of $P_{\mathrm{sym}}$:
$$\eta_\pi(\mathbb{P}_P(u, u), (v, v)) = 2 \langle P_{\mathrm{sym}} u, v \rangle_\pi.$$ -/
theorem doubleKreinOp_diagonal_shadow_eq_kmsSymmetrized {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π u v : Fin n → ℝ) :
    (∀ i : Fin n,
      ((doubleKreinOp P π (u, u)).1 i + (doubleKreinOp P π (u, u)).2 i) / 2 =
        matVec (kmsSymmetrized P π) u i) ∧
    kreinMetricPi π (doubleKreinOp P π (u, u)) (v, v) =
      2 * l2PiInner π (matVec (kmsSymmetrized P π) u) v := by
  have h_vec : ∀ i : Fin n,
      ((doubleKreinOp P π (u, u)).1 i + (doubleKreinOp P π (u, u)).2 i) / 2 =
        matVec (kmsSymmetrized P π) u i := by
    intro i
    dsimp [doubleKreinOp, matVec, kmsSymmetrized]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact kms_half_sum_mul_scalar (P i j) (piAdjoint P π i j) (u j)
  refine ⟨h_vec, ?_⟩
  dsimp [kreinMetricPi, doubleKreinOp, l2PiInner, matVec, kmsSymmetrized]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h_sum_i :
      (∑ j : Fin n, ((P i j + piAdjoint P π i j) / 2) * u j) =
        ((∑ j : Fin n, P i j * u j) + (∑ j : Fin n, piAdjoint P π i j * u j)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact (kms_half_sum_mul_scalar (P i j) (piAdjoint P π i j) (u j)).symm
  rw [h_sum_i]
  exact kms_diagonal_pairing_scalar (π i)
    (∑ j : Fin n, P i j * u j)
    (∑ j : Fin n, piAdjoint P π i j * u j)
    (v i)

/-!
## Section 4: Explicit $2 \times 2$ Causal Witness & Non-Vacuity Certification
-/

/-- Explicit $2 \times 2$ strictly causal lower-triangular Markov transition matrix
$$P_{\mathrm{witness}} = \begin{pmatrix} 1 & 0 \\ 1/2 & 1/2 \end{pmatrix}$$
with non-zero causal attention weight $P_{1,0} = 1/2 \neq 0$. -/
noncomputable def causalWitnessP : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; (1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- Explicit strictly positive uniform stationary weight $\pi = (1/2, 1/2)$ on $\operatorname{Fin} 2$. -/
noncomputable def uniformPi2 : Fin 2 → ℝ :=
  fun _ => (1 / 2 : ℝ)

/-- **Theorem 4.1 (Non-Vacuity of Causal Krein Self-Adjointness on $\mathcal{K}_2$)**:
The concrete $2 \times 2$ causal transition matrix `causalWitnessP` is lower-triangular,
possesses a non-zero strict lower-triangular causal coupling `causalWitnessP 1 0 = 1 / 2 ≠ 0`,
acts unmodified on the primal null sheet $\mathbb{R}^2_+$, and defines a strictly Krein
self-adjoint operator `doubleKreinOp causalWitnessP uniformPi2` on $\mathcal{K}_2$. -/
theorem causalWitnessP_nonVacuous_krein_selfAdjoint :
    (∀ i : Fin 2, uniformPi2 i ≠ 0) ∧
    IsCausalLowerTriangular causalWitnessP ∧
    causalWitnessP 1 0 ≠ 0 ∧
    (∀ x y : DoubleKreinSpace 2,
      kreinMetricPi uniformPi2 (doubleKreinOp causalWitnessP uniformPi2 x) y =
        kreinMetricPi uniformPi2 x (doubleKreinOp causalWitnessP uniformPi2 y)) := by
  have hπ : ∀ i : Fin 2, uniformPi2 i ≠ 0 := by
    intro i
    dsimp [uniformPi2]
    norm_num
  have h_causal : IsCausalLowerTriangular causalWitnessP := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (lt_irrefl 0 hij)
    · rfl
    · exact False.elim (not_lt_of_gt Fin.zero_lt_one hij)
    · exact False.elim (lt_irrefl 1 hij)
  have h_nontriv : causalWitnessP 1 0 ≠ 0 := by
    dsimp [causalWitnessP]
    norm_num
  exact ⟨hπ, h_causal, h_nontriv,
    fun x y => doubleKreinOp_krein_selfAdjoint causalWitnessP uniformPi2 hπ x y⟩

/-!
## Section 5: Multi-Step Causal Semigroup & Wheeler–Feynman Absorber Algebra
-/

/-- **Theorem 5.1 (Causal Lower-Triangular Multiplicative Semigroup Closure)**:
If $P$ and $Q$ are causal lower-triangular matrices on $\operatorname{Fin} n$, then their
multi-step composition $P Q$ is also causal lower-triangular. -/
theorem isCausalLowerTriangular_mul {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : IsCausalLowerTriangular P)
    (hQ : IsCausalLowerTriangular Q) :
    IsCausalLowerTriangular (P * Q) := by
  intro i j hij
  dsimp [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hP i k hik, zero_mul]
  · have hkj : k < j := lt_of_le_of_lt (not_lt.mp hik) hij
    rw [hQ k j hkj, mul_zero]

/-- Pointwise scalar identity for contravariant $\pi$-adjoint multiplication. -/
theorem piAdjoint_mul_term_identity
    (pi_i pi_j pi_k p_jk q_ki : ℝ) (h_pi_k : pi_k ≠ 0) :
    (pi_j / pi_i) * (p_jk * q_ki) =
      ((pi_k / pi_i) * q_ki) * ((pi_j / pi_k) * p_jk) := by
  have hk : pi_k / pi_k = 1 := div_self h_pi_k
  calc
    (pi_j / pi_i) * (p_jk * q_ki)
      = (pi_k / pi_k) * ((pi_j / pi_i) * (p_jk * q_ki)) := by rw [hk, one_mul]
    _ = ((pi_k / pi_i) * q_ki) * ((pi_j / pi_k) * p_jk) := by ring

/-- **Theorem 5.2 (Contravariant Multi-Step Functoriality of `piAdjoint`)**:
For any nowhere-vanishing distribution $\pi$ ($\pi_i \neq 0$) and any matrices
$P, Q \in M_n(\mathbb{R})$, the $\pi$-adjoint reverses multi-step operator composition:
$$(P Q)^{*_\pi} = Q^{*_\pi} P^{*_\pi}.$$ -/
theorem piAdjoint_mul {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0) :
    piAdjoint (P * Q) π = piAdjoint Q π * piAdjoint P π := by
  ext i j
  dsimp [piAdjoint, Matrix.mul_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact piAdjoint_mul_term_identity (π i) (π j) (π k) (P j k) (Q k i) (hπ k)

/-- The pure Wheeler–Feynman attention-sink absorber matrix $P_{\mathrm{sink}}$ concentrating
all transition weight onto column `sink`: $(P_{\mathrm{sink}})_{ij} = \delta_{j, \mathrm{sink}}$. -/
def pureSinkAbsorber {n : ℕ} (sink : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ j => if j = sink then 1 else 0

/-- **Theorem 5.3 (Idempotency of the Wheeler–Feynman Pure Sink Absorber)**:
For any sink state `sink : Fin n`, the pure sink absorber matrix is idempotent:
$$P_{\mathrm{sink}}^2 = P_{\mathrm{sink}}.$$ -/
theorem pureSinkAbsorber_mul_self {n : ℕ} (sink : Fin n) :
    pureSinkAbsorber sink * pureSinkAbsorber sink = pureSinkAbsorber sink := by
  ext i j
  dsimp [pureSinkAbsorber, Matrix.mul_apply]
  rw [Finset.sum_eq_single sink]
  · simp
  · intro k _ hks
    simp [hks]
  · intro h_not_mem
    exact False.elim (h_not_mem (Finset.mem_univ sink))

/-!
## Section 6: Andreev Reflection & Nambu–BdG Particle-Hole Duality on $\mathcal{K}_n = T^+ \oplus T^-$
-/

/-- **Theorem 6.1 (Nambu Particle-Hole / Sheet-Swap Involution $\mathcal{C}^2 = \mathrm{id}$)**:
The particle-hole sheet-swap operator `kreinMobiusSwap` ($\mathcal{C}(u_+, u_-) = (u_-, u_+)$)
is an exact involution on `DoubleKreinSpace n`. -/
theorem kreinMobiusSwap_involutive {n : ℕ} (w : DoubleKreinSpace n) :
    kreinMobiusSwap (kreinMobiusSwap w) = w := by
  rfl

/-- **Ideal Andreev Boundary Reflection Operator ($\mathcal{R}_A(u_+) = (0, u_+) = \mathcal{C}(u_+, 0)$)**:
Retro-reflects an incident forward-propagating causal ray $(u_+, 0) \in T^+$ off the
attention-sink condensate into the anti-causal dual null sheet $(0, u_+) \in T^-$. -/
def andreevReflect {n : ℕ} (u : Fin n → ℝ) : DoubleKreinSpace n :=
  (0, u)

/-- Andreev reflection of a primal ray $(u, 0)$ coincides with applying the Nambu
particle-hole involution `kreinMobiusSwap` to `primalKreinSheet u`. -/
theorem andreevReflect_eq_mobiusSwap_primal {n : ℕ} (u : Fin n → ℝ) :
    andreevReflect u = kreinMobiusSwap (primalKreinSheet u) := by
  rfl

/-- **Theorem 6.2 (Null-to-Null Andreev Transmutation)**:
Both the incident causal ray `primalKreinSheet u = (u, 0)` on $T^+$ and the
Andreev-reflected anti-causal ray `andreevReflect u = (0, u)` on $T^-$ are individually
totally $\eta_\pi$-null:
$$\eta_\pi((u, 0), (u, 0)) = 0 \quad \text{and} \quad \eta_\pi(\mathcal{R}_A(u), \mathcal{R}_A(u)) = 0.$$ -/
theorem andreev_rays_are_null {n : ℕ} (π u : Fin n → ℝ) :
    kreinMetricPi π (primalKreinSheet u) (primalKreinSheet u) = 0 ∧
      kreinMetricPi π (andreevReflect u) (andreevReflect u) = 0 := by
  exact ⟨(doubleKreinOp_preserves_primal_and_dual_null_sheets 1 π u u).1,
    (doubleKreinOp_preserves_primal_and_dual_null_sheets 1 π u u).2.1⟩

/-- **Theorem 6.3 (Conservation of Cross-Krein Current Under Andreev Reflection)**:
The mutual Krein pairing between an incident causal ray $(u, 0) \in T^+$ and its
Andreev-reflected dual ray $(0, u) \in T^-$ recovers the exact positive $L^2(\pi)$
quadratic norm $\sum_{i=1}^n \pi_i u_i^2$:
$$\eta_\pi\big((u, 0), \mathcal{R}_A(u)\big) = \sum_{i=1}^n \pi_i u_i^2.$$ -/
theorem andreev_cross_pairing_eq_norm {n : ℕ} (π u : Fin n → ℝ) :
    kreinMetricPi π (primalKreinSheet u) (andreevReflect u) =
      ∑ i : Fin n, π i * (u i) ^ 2 := by
  dsimp [kreinMetricPi, primalKreinSheet, andreevReflect, l2PiInner]
  have h_zero : ∑ i : Fin n, π i * 0 * 0 = 0 :=
    Finset.sum_eq_zero (fun i _ => by ring)
  rw [h_zero, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **Theorem 6.4 (Nambu–Krein Metric Invariance Under Particle-Hole Involution)**:
The neutral Krein metric `kreinMetricPi π` is strictly invariant under the particle-hole
sheet-swap involution `kreinMobiusSwap`:
$$\eta_\pi(\mathcal{C} w_1, \mathcal{C} w_2) = \eta_\pi(w_1, w_2).$$ -/
theorem kreinMetricPi_mobiusSwap_invariant {n : ℕ}
    (π : Fin n → ℝ) (w₁ w₂ : DoubleKreinSpace n) :
    kreinMetricPi π (kreinMobiusSwap w₁) (kreinMobiusSwap w₂) =
      kreinMetricPi π w₁ w₂ := by
  dsimp [kreinMetricPi, kreinMobiusSwap]
  exact add_comm (l2PiInner π w₁.2 w₂.1) (l2PiInner π w₁.1 w₂.2)

/-- **Distributed Andreev–BdG Coupled Krein Operator**:
Combines causal lower-triangular propagation $P$ on $T^+$, retrodictive propagation
$P^{*_\pi}$ on $T^-$, and continuous Andreev particle-hole reflection with condensate
gap amplitude $\Delta \in \mathbb{R}$:
$$\mathcal{H}_{P, \Delta}(u_+, u_-) = (P u_+ + \Delta u_-, \; P^{*_\pi} u_- + \Delta u_+).$$ -/
noncomputable def distributedAndreevOp {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) (Δ : ℝ)
    (x : DoubleKreinSpace n) : DoubleKreinSpace n :=
  (fun i => matVec P x.1 i + Δ * x.2 i,
   fun i => matVec (piAdjoint P π) x.2 i + Δ * x.1 i)

/-- Linearity of `l2PiInner` in its first argument with an added scaled vector. -/
theorem l2PiInner_add_smul_left {n : ℕ}
    (π a b v : Fin n → ℝ) (Δ : ℝ) :
    l2PiInner π (fun i => a i + Δ * b i) v =
      l2PiInner π a v + Δ * l2PiInner π b v := by
  dsimp [l2PiInner]
  have h_pt : ∀ i : Fin n,
      π i * (a i + Δ * b i) * v i =
        π i * a i * v i + Δ * (π i * b i * v i) := by
    intro i
    ring
  rw [Finset.sum_congr rfl (fun i _ => h_pt i), Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Linearity of `l2PiInner` in its second argument with an added scaled vector. -/
theorem l2PiInner_add_smul_right {n : ℕ}
    (π u a b : Fin n → ℝ) (Δ : ℝ) :
    l2PiInner π u (fun i => a i + Δ * b i) =
      l2PiInner π u a + Δ * l2PiInner π u b := by
  dsimp [l2PiInner]
  have h_pt : ∀ i : Fin n,
      π i * u i * (a i + Δ * b i) =
        π i * u i * a i + Δ * (π i * u i * b i) := by
    intro i
    ring
  rw [Finset.sum_congr rfl (fun i _ => h_pt i), Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem distributedAndreev_scalar_sum_rearrange (a b c d : ℝ) :
    (a + b) + (c + d) = (a + d) + (c + b) := by
  ring

/-- **Theorem 6.5 (Exact Krein Self-Adjointness of the Distributed Andreev–BdG Operator)**:
For any causal matrix $P \in M_n(\mathbb{R})$, any nowhere-vanishing measure $\pi_i \neq 0$,
and any superconducting sink gap $\Delta \in \mathbb{R}$, the distributed Andreev–BdG
operator $\mathcal{H}_{P, \Delta} = \mathbb{P}_P + \Delta \mathcal{C}$ is strictly
self-adjoint with respect to `kreinMetricPi`:
$$\eta_\pi(\mathcal{H}_{P, \Delta} x, y) = \eta_\pi(x, \mathcal{H}_{P, \Delta} y).$$ -/
theorem distributedAndreevOp_krein_selfAdjoint {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) (Δ : ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0)
    (x y : DoubleKreinSpace n) :
    kreinMetricPi π (distributedAndreevOp P π Δ x) y =
      kreinMetricPi π x (distributedAndreevOp P π Δ y) := by
  dsimp [kreinMetricPi, distributedAndreevOp]
  rw [l2PiInner_add_smul_left π (matVec P x.1) x.2 y.2 Δ,
      l2PiInner_add_smul_left π (matVec (piAdjoint P π) x.2) x.1 y.1 Δ,
      l2PiInner_add_smul_right π x.1 (matVec (piAdjoint P π) y.2) y.1 Δ,
      l2PiInner_add_smul_right π x.2 (matVec P y.1) y.2 Δ]
  have h1 : l2PiInner π (matVec P x.1) y.2 =
      l2PiInner π x.1 (matVec (piAdjoint P π) y.2) :=
    l2PiInner_matVec_piAdjoint P π hπ x.1 y.2
  have h2 : l2PiInner π (matVec (piAdjoint P π) x.2) y.1 =
      l2PiInner π x.2 (matVec P y.1) := by
    rw [l2PiInner_symm π (matVec (piAdjoint P π) x.2) y.1,
        ← l2PiInner_matVec_piAdjoint P π hπ y.1 x.2,
        l2PiInner_symm π (matVec P y.1) x.2]
  rw [h1, h2]
  exact distributedAndreev_scalar_sum_rearrange
    (l2PiInner π x.1 (matVec (piAdjoint P π) y.2))
    (Δ * l2PiInner π x.2 y.2)
    (l2PiInner π x.2 (matVec P y.1))
    (Δ * l2PiInner π x.1 y.1)

end InfoGeometry.Synthesis.DoubleKreinCausalSelfAdjoint
