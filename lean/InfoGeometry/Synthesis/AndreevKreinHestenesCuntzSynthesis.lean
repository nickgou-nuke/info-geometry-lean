/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import InfoGeometry.Synthesis.BohmianCuntzHolomovementPoset

/-!
# Finite Weighted Pairing, Explicit Cl(1,1) Matrices, and Block Corners

This module collects three finite constructions. It proves an off-diagonal weighted
pairing identity on a product function space, identities for explicit 2-by-2
real matrices satisfying the split-signature generator relations, and retraction
identities for block-corner maps between finite matrix carriers. No equivalence
between these carriers is asserted here. The sheet-swap map is an algebraic
involution; no BdG Hamiltonian, scattering process, or Andreev boundary dynamics
is defined. The block-corner maps are not Cuntz isometries in a common operator
algebra and do not furnish a representation of the Cuntz relations.

1. **Weighted product-space pairing.** The form `gPi` is bilinear and off-diagonal.
   The coordinate swap preserves it, and the primal and dual coordinate sheets
   have zero self-pairing. Pairing a primal vector with its sheet-swapped vector
   yields the displayed weighted quadratic sum; positivity requires nonnegative
   weights and is not part of that equality theorem.
2. **Explicit 2-by-2 matrix identities.** The matrices `hestenesE0` and
   `hestenesE1` satisfy the split-signature Clifford generator equations. The
   file proves their products, a matrix expansion in four displayed matrices,
   a reversion operation, its anti-automorphism law, and transpose identity for
   the defined adjoint. It does not define an algebra equivalence to
   `CliffordAlgebra q11Form`.
3. **Finite block-corner maps.** `cornerEmbed1/2` insert a matrix into one of two
   diagonal blocks; `unfold1/2` extract those blocks. The proved identities are
   retractions, a block-sum identity, and equality with the block pinching map
   defined in the imported finite matrix module. These are finite matrix
   identities; they do not define isometries or represent the Cuntz relations.
-/

namespace InfoGeometry.Synthesis.AndreevKreinHestenesCuntzSynthesis

open BigOperators Finset Matrix
open InfoGeometry.Synthesis.BohmianCuntzHolomovementPoset

/-!
## Part I: Weighted Pairing and Coordinate Sheet Swap
-/

section AndreevKrein

variable {n : Type*} [Fintype n]

/-- The doubled function-space carrier $\mathcal{K}_n = T^+ \oplus T^-$. -/
abbrev KreinSpace (n : Type*) := (n → ℝ) × (n → ℝ)

/-- Neutral off-diagonal Krein pairing:
$$g_\pi\big((u_+, u_-), (v_+, v_-)\big) = \langle u_+, v_- \rangle_\pi + \langle u_-, v_+ \rangle_\pi.$$ -/
def gPi (π : n → ℝ) (u v : KreinSpace n) : ℝ :=
  (∑ i : n, π i * u.1 i * v.2 i) + (∑ i : n, π i * u.2 i * v.1 i)

/-- Coordinate sheet-swap involution $\mathcal{C}(u_+, u_-) = (u_-, u_+)$. -/
def sheetSwap (w : KreinSpace n) : KreinSpace n :=
  (w.2, w.1)

omit [Fintype n] in
/-- **Theorem 1.1 (Sheet-Swap Involution)**:
The coordinate swap is an exact involution on `KreinSpace n`. -/
theorem sheetSwap_involutive (w : KreinSpace n) :
    sheetSwap (sheetSwap w) = w := by
  unfold sheetSwap
  dsimp

/-- **Map from the primal coordinate sheet to the dual sheet**:
Maps $(u,0)$ to its coordinate swap $(0,u)$. This is an algebraic sheet exchange only. -/
def sheetExchangeFromPrimal (u : n → ℝ) : KreinSpace n :=
  (0, u)

omit [Fintype n] in
/-- This map is the restriction of `sheetSwap` to the primal coordinate sheet $T^+$. -/
theorem sheetExchangeFromPrimal_eq_sheetSwap (u : n → ℝ) :
    sheetExchangeFromPrimal u = sheetSwap (u, 0) := by
  rfl

/-- **Theorem 1.2 (Nullity of the Two Coordinate Sheets)**:
Vectors supported in either coordinate sheet have zero self-pairing under `gPi π`. -/
theorem sheetExchange_preserves_sheet_nullity (π : n → ℝ) (u : n → ℝ) :
    gPi π (u, 0) (u, 0) = 0 ∧ gPi π (sheetExchangeFromPrimal u) (sheetExchangeFromPrimal u) = 0 := by
  constructor <;> simp [gPi, sheetExchangeFromPrimal]

/-- **Theorem 1.3 (Cross-Pairing Equals a Weighted Quadratic Sum)**:
The pairing between $(u,0)$ and its coordinate swap $(0,u)$ equals the following weighted quadratic sum:
$$g_\pi\big((u, 0), \operatorname{sheetSwap}(u,0)\big) = \sum_{i \in n} \pi_i u(i)^2.$$ -/
theorem sheetExchange_pairing_eq_weighted_quadratic (π : n → ℝ) (u : n → ℝ) :
    gPi π (u, 0) (sheetExchangeFromPrimal u) = ∑ i : n, π i * (u i) ^ 2 := by
  unfold gPi sheetExchangeFromPrimal
  dsimp
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **Theorem 1.4 (Pairing Invariance Under Coordinate Swap)**:
The neutral Krein metric satisfies $g_\pi(\mathcal{C} w_1, \mathcal{C} w_2) = g_\pi(w_1, w_2)$. -/
theorem gPi_sheetSwap_invariant (π : n → ℝ) (w₁ w₂ : KreinSpace n) :
    gPi π (sheetSwap w₁) (sheetSwap w₂) = gPi π w₁ w₂ := by
  unfold gPi sheetSwap
  dsimp
  rw [add_comm]

end AndreevKrein

/-!
## Part II: Explicit 2-by-2 Matrices Satisfying Split Clifford Relations
-/

section HestenesCl11

variable {R : Type*} [CommRing R]

/-- Spacetime vector generator $e_0 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ with $e_0^2 = +\mathbf{1}$. -/
def hestenesE0 : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 1, 0]

/-- Spacetime vector generator $e_1 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$ with $e_1^2 = -\mathbf{1}$. -/
def hestenesE1 : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; -1, 0]

/-- First Majorana Witt null mode $\psi_1 = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$. -/
def majoranaPsi1 : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 0, 0]

/-- Second Majorana Witt null mode $\psi_2 = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$. -/
def majoranaPsi2 : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 1, 0]

/-- Unit paracomplex bivector (pseudoscalar) $\omega = e_0 e_1 = \begin{pmatrix} -1 & 0 \\ 0 & 1 \end{pmatrix}$. -/
def hestenesOmega : Matrix (Fin 2) (Fin 2) R :=
  !![-1, 0; 0, 1]

/-- Internal complex structure $J = e_0 \omega = e_1 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$
satisfying $J^2 = -\mathbf{1}$. -/
def hestenesComplexJ : Matrix (Fin 2) (Fin 2) R :=
  hestenesE0 * hestenesOmega

/-- Left Peircian chiral projector (vacuum number operator)
$P_1 = \psi_1 \psi_2 = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def peircianP1 : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, 0]

/-- Right Peircian chiral projector (occupied number operator)
$P_2 = \psi_2 \psi_1 = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$. -/
def peircianP2 : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 0, 1]

/-- Real specialization of $e_0 \in M_2(\mathbb{R})$. -/
def hestenesE0Real : Matrix (Fin 2) (Fin 2) ℝ :=
  hestenesE0

/-- Real specialization of $e_1 \in M_2(\mathbb{R})$. -/
def hestenesE1Real : Matrix (Fin 2) (Fin 2) ℝ :=
  hestenesE1

/-- Explicit anticommutativity of the Hestenes $\mathrm{Cl}(1,1)$ generators $e_0, e_1 \in M_2(R)$:
$e_0 e_1 + e_1 e_0 = 0$. -/
theorem hestenesE0_anticomm_hestenesE1 :
    hestenesE0 (R := R) * hestenesE1 (R := R) +
      hestenesE1 (R := R) * hestenesE0 (R := R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hestenesE0, hestenesE1]

/-- Explicit non-commutativity of the real Hestenes generators $e_0, e_1 \in M_2(\mathbb{R})$:
$e_0 e_1 \neq e_1 e_0$. -/
theorem hestenesE0_mul_hestenesE1_ne_comm :
    hestenesE0Real * hestenesE1Real ≠ hestenesE1Real * hestenesE0Real := by
  intro h_comm
  have h00 :
      (hestenesE0Real * hestenesE1Real) 0 0 =
        (hestenesE1Real * hestenesE0Real) 0 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h_comm
  revert h00
  norm_num [hestenesE0Real, hestenesE1Real, hestenesE0, hestenesE1,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- **Theorem 2.1 (Split-Signature $\mathrm{Cl}(1,1)$ Generator Relations & Bivector $\omega = e_0 e_1$)**:
The generators $e_0, e_1 \in M_2(R)$ satisfy $e_0^2 = \mathbf{1}$, $e_1^2 = -\mathbf{1}$,
$e_0 e_1 + e_1 e_0 = 0$, $e_0 e_1 = \omega$, and $\omega^2 = +\mathbf{1}$. -/
theorem hestenes_cl11_generator_relations :
    (hestenesE0 : Matrix (Fin 2) (Fin 2) R) * hestenesE0 = 1 ∧
    (hestenesE1 : Matrix (Fin 2) (Fin 2) R) * hestenesE1 = -1 ∧
    (hestenesE0 : Matrix (Fin 2) (Fin 2) R) * hestenesE1 + hestenesE1 * hestenesE0 = 0 ∧
    (hestenesE0 : Matrix (Fin 2) (Fin 2) R) * hestenesE1 = hestenesOmega ∧
    (hestenesOmega : Matrix (Fin 2) (Fin 2) R) * hestenesOmega = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesE0, hestenesE1, hestenesOmega, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Theorem 2.2 (Two Majorana Witt Null Modes & Canonical Anticommutation)**:
The Majorana modes $\psi_1, \psi_2$ decompose $e_0 = \psi_1 + \psi_2$ and
$e_1 = \psi_1 - \psi_2$, are individually nilpotent ($\psi_1^2 = 0$, $\psi_2^2 = 0$),
and anticommute to the identity ($\psi_1 \psi_2 + \psi_2 \psi_1 = \mathbf{1}$). -/
theorem majorana_witt_basis_relations :
    (majoranaPsi1 : Matrix (Fin 2) (Fin 2) R) + majoranaPsi2 = hestenesE0 ∧
    (majoranaPsi1 : Matrix (Fin 2) (Fin 2) R) - majoranaPsi2 = hestenesE1 ∧
    (majoranaPsi1 : Matrix (Fin 2) (Fin 2) R) * majoranaPsi1 = 0 ∧
    (majoranaPsi2 : Matrix (Fin 2) (Fin 2) R) * majoranaPsi2 = 0 ∧
    (majoranaPsi1 : Matrix (Fin 2) (Fin 2) R) * majoranaPsi2 +
      majoranaPsi2 * majoranaPsi1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [majoranaPsi1, majoranaPsi2, hestenesE0, hestenesE1,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- **Theorem 2.3 (A Negative-Square Matrix Product)**:
The displayed matrices satisfy $e_0\omega e_0=-\omega$, and their product $J=e_0\omega$ equals $e_1$ with square $-\mathbf{1}$. -/
theorem hestenesComplexJ_relations :
    (hestenesComplexJ : Matrix (Fin 2) (Fin 2) R) = hestenesE1 ∧
    (hestenesE0 : Matrix (Fin 2) (Fin 2) R) * hestenesOmega * hestenesE0 = -hestenesOmega ∧
    (hestenesComplexJ : Matrix (Fin 2) (Fin 2) R) * hestenesComplexJ = -1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesComplexJ, hestenesE0, hestenesE1, hestenesOmega,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- **Theorem 2.4 (A Matrix Expansion and Trace Formula)**:
Every $2 \times 2$ matrix $M \in M_2(R)$ has the following expansion in the displayed matrix basis
$$M = M_{00} P_1 + M_{01} \psi_1 + M_{10} \psi_2 + M_{11} P_2,$$
and the trace of the specified matrix linear combination is $2\alpha$:
$$\operatorname{Tr}(\alpha I + \mu_+ \psi_1 + \mu_- \psi_2 + \beta \omega) = 2\alpha.$$ -/
theorem hestenes_matrix_expansion_and_trace
    (M : Matrix (Fin 2) (Fin 2) R) (α μ_plus μ_minus β : R) :
    M = M 0 0 • peircianP1 + M 0 1 • majoranaPsi1 +
        M 1 0 • majoranaPsi2 + M 1 1 • peircianP2 ∧
    Matrix.trace (α • (1 : Matrix (Fin 2) (Fin 2) R) +
        μ_plus • majoranaPsi1 + μ_minus • majoranaPsi2 + β • hestenesOmega) =
      2 * α := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peircianP1, peircianP2, majoranaPsi1, majoranaPsi2]
  · simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply_eq, majoranaPsi1, majoranaPsi2,
      hestenesOmega, of_apply, cons_val', cons_val_zero, cons_val_one, smul_eq_mul]
    ring

/-!
## Part III: Defined Matrix Reversion, Adjoint, and Projectors
-/

/-- **Reversion-Inspired Matrix Operation ($\widetilde{M}$)**:
This explicitly defined operation fixes the displayed scalar, vector, and nilpotent
matrices and negates the displayed bivector matrix. In this matrix basis it swaps
the two diagonal entries:
$$\widetilde{\begin{pmatrix} a & b \\ c & d \end{pmatrix}} = \begin{pmatrix} d & b \\ c & a \end{pmatrix}.$$ -/
def hestenesRev (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![M 1 1, M 0 1; M 1 0, M 0 0]

/-- **Hestenes–Krein Adjoint ($M^\sharp := e_0 \widetilde{M} e_0$)**:
Conjugates the Hestenes reversion $\widetilde{M}$ by the fundamental symmetry $e_0$. -/
def hestenesKreinAdjoint (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  hestenesE0 * hestenesRev M * hestenesE0

/-- **Theorem 3.1 (Hestenes Reversion Anti-Automorphism & Grade Action)**:
Hestenes reversion is an involution ($\widetilde{\widetilde{M}} = M$), reverses products
($\widetilde{A B} = \widetilde{B}\widetilde{A}$), fixes $\mathbf{1}, e_0, e_1, \psi_1, \psi_2$,
and negates the bivector $\omega$ ($\widetilde{\omega} = -\omega$). -/
theorem hestenesRev_properties (A B : Matrix (Fin 2) (Fin 2) R) :
    hestenesRev (hestenesRev A) = A ∧
    hestenesRev (A * B) = hestenesRev B * hestenesRev A ∧
    hestenesRev (1 : Matrix (Fin 2) (Fin 2) R) = 1 ∧
    hestenesRev (hestenesE0 : Matrix (Fin 2) (Fin 2) R) = hestenesE0 ∧
    hestenesRev (hestenesE1 : Matrix (Fin 2) (Fin 2) R) = hestenesE1 ∧
    hestenesRev (majoranaPsi1 : Matrix (Fin 2) (Fin 2) R) = majoranaPsi1 ∧
    hestenesRev (majoranaPsi2 : Matrix (Fin 2) (Fin 2) R) = majoranaPsi2 ∧
    hestenesRev (hestenesOmega : Matrix (Fin 2) (Fin 2) R) = -hestenesOmega := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [hestenesRev, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [hestenesRev, hestenesOmega]

/-- **Theorem 3.2 (Krein Adjoint $M^\sharp = e_0 \widetilde{M} e_0$ Coincides with Matrix Transpose $M^T$)**:
For every $M \in M_2(R)$, `hestenesKreinAdjoint M = Mᵀ`, and the Majorana modes are mutual
Krein adjoints ($\psi_1^\sharp = \psi_2$, $\psi_2^\sharp = \psi_1$). -/
theorem hestenesKreinAdjoint_eq_transpose (M : Matrix (Fin 2) (Fin 2) R) :
    hestenesKreinAdjoint M = Mᵀ ∧
    hestenesKreinAdjoint (majoranaPsi1 : Matrix (Fin 2) (Fin 2) R) = majoranaPsi2 ∧
    hestenesKreinAdjoint (majoranaPsi2 : Matrix (Fin 2) (Fin 2) R) = majoranaPsi1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesKreinAdjoint, hestenesE0, hestenesRev, majoranaPsi1, majoranaPsi2,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- **Theorem 3.3 (Peircian Chiral Idempotents as Majorana Number Operators)**:
The Peircian projectors $P_1, P_2 \in M_2(R)$ satisfy:
1. $P_1 = \psi_1 \psi_2$ and $P_2 = \psi_2 \psi_1$,
2. $2 P_1 = \mathbf{1} - \omega$ and $2 P_2 = \mathbf{1} + \omega$,
3. $P_1 + P_2 = \mathbf{1}$, $P_1 P_2 = 0$, $P_2 P_1 = 0$, $P_1^2 = P_1$, $P_2^2 = P_2$,
4. Hestenes reversion exchanges $P_1$ and $P_2$ ($\widetilde{P_1} = P_2$), and both
   are Krein self-adjoint ($P_1^\sharp = P_1$, $P_2^\sharp = P_2$). -/
theorem peircian_chiral_idempotent_algebra :
    (peircianP1 : Matrix (Fin 2) (Fin 2) R) = majoranaPsi1 * majoranaPsi2 ∧
    (peircianP2 : Matrix (Fin 2) (Fin 2) R) = majoranaPsi2 * majoranaPsi1 ∧
    (2 : R) • (peircianP1 : Matrix (Fin 2) (Fin 2) R) = 1 - hestenesOmega ∧
    (2 : R) • (peircianP2 : Matrix (Fin 2) (Fin 2) R) = 1 + hestenesOmega ∧
    (peircianP1 : Matrix (Fin 2) (Fin 2) R) + peircianP2 = 1 ∧
    (peircianP1 : Matrix (Fin 2) (Fin 2) R) * peircianP2 = 0 ∧
    (peircianP1 : Matrix (Fin 2) (Fin 2) R) * peircianP1 = peircianP1 ∧
    hestenesRev (peircianP1 : Matrix (Fin 2) (Fin 2) R) = peircianP2 ∧
    hestenesKreinAdjoint (peircianP1 : Matrix (Fin 2) (Fin 2) R) = peircianP1 ∧
    hestenesKreinAdjoint (peircianP2 : Matrix (Fin 2) (Fin 2) R) = peircianP2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [peircianP1, majoranaPsi1, majoranaPsi2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [peircianP2, majoranaPsi1, majoranaPsi2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; (fin_cases i <;> fin_cases j <;> simp [peircianP1, hestenesOmega]); norm_num
  · ext i j; (fin_cases i <;> fin_cases j <;> simp [peircianP2, hestenesOmega]); norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [peircianP1, peircianP2]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [peircianP1, peircianP2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [peircianP1, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [hestenesRev, peircianP1, peircianP2]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [hestenesKreinAdjoint, hestenesE0, hestenesRev, peircianP1,
        Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [hestenesKreinAdjoint, hestenesE0, hestenesRev, peircianP2,
        Matrix.mul_apply, Fin.sum_univ_two]

end HestenesCl11

/-!
## Part IV: Finite Block-Corner Embeddings and Retractions
-/

section BlockCornerMaps

variable {m : Type*} [Fintype m] [DecidableEq m]
variable {R : Type*} [CommRing R]

/-- **First Block-Corner Embedding**:
Embeds a local stage matrix $M \in M_m(R)$ into the top-left Peircian chiral sector
of $M_{m \oplus m}(R)$:
$$\operatorname{cornerEmbed}_1(M) = \begin{pmatrix} M & 0 \\ 0 & 0 \end{pmatrix} = P_1\,\mathcal{E}(M).$$ -/
def cornerEmbed1 (M : Matrix m m R) : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks M 0 0 0

/-- **Second Block-Corner Embedding**:
Embeds a local stage matrix $M \in M_m(R)$ into the bottom-right Peircian chiral sector
of $M_{m \oplus m}(R)$:
$$\operatorname{cornerEmbed}_2(M) = \begin{pmatrix} 0 & 0 \\ 0 & M \end{pmatrix} = P_2\,\mathcal{E}(M).$$ -/
def cornerEmbed2 (M : Matrix m m R) : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 0 0 0 M

omit [Fintype m] [DecidableEq m] in
/-- **Theorem 4.1 (Block-Corner Retractions and Cross-Corner Zeroes)**:
`unfold1` and `unfold2` extract the indicated diagonal blocks from the two corner embeddings:
$$U_1(\operatorname{cornerEmbed}_1(M)) = M, \quad U_2(\operatorname{cornerEmbed}_2(M)) = M, \quad U_1(\operatorname{cornerEmbed}_2(M)) = 0, \quad U_2(\operatorname{cornerEmbed}_1(M)) = 0.$$ -/
theorem corner_embedding_retractions (M : Matrix m m R) :
    unfold1 (cornerEmbed1 M) = M ∧
    unfold2 (cornerEmbed2 M) = M ∧
    unfold1 (cornerEmbed2 M) = 0 ∧
    unfold2 (cornerEmbed1 M) = 0 := by
  unfold unfold1 unfold2 cornerEmbed1 cornerEmbed2
  exact ⟨Matrix.toBlocks_fromBlocks₁₁ M 0 0 0,
    Matrix.toBlocks_fromBlocks₂₂ 0 0 0 M,
    Matrix.toBlocks_fromBlocks₁₁ 0 0 0 M,
    Matrix.toBlocks_fromBlocks₂₂ M 0 0 0⟩

/-- **Theorem 4.2 (Block-Corner Sum Equals the Diagonal Embedding)**:
Summing the two block-corner embeddings yields the block-diagonal embedding $\mathcal{E}(M) = \mathbf{1} \otimes M$, and each corner embedding is the
projection of $\mathcal{E}(M)$ by $P_1$ or $P_2$:
$$\operatorname{cornerEmbed}_1(M) + \operatorname{cornerEmbed}_2(M) = \mathcal{E}(M).$$
The equations involving `cuntzProj1/2` below use the imported diagonal-block
projector matrices. They establish matrix equalities only, not a representation
by Cuntz isometries. -/
theorem corner_embeddings_sum_eq_enfold (M : Matrix m m R) :
    cornerEmbed1 M + cornerEmbed2 M = enfold M ∧
    cornerEmbed1 M = cuntzProj1 * enfold M ∧
    cornerEmbed2 M = cuntzProj2 * enfold M := by
  unfold cornerEmbed1 cornerEmbed2 enfold cuntzProj1 cuntzProj2
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.fromBlocks_add, add_zero, zero_add]
  · simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, add_zero]
  · simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]

/-- **Theorem 4.3 (Corner Retractions Reproduce Block Pinching)**:
Re-embedding the two diagonal block retractions reproduces
the block pinching map `holomovement`, and acts as
the identity on every enfolded observable $\mathcal{E}(M)$:
$$\operatorname{cornerEmbed}_1(U_1(Y)) + \operatorname{cornerEmbed}_2(U_2(Y)) = \Phi(Y).$$ -/
theorem corner_retractions_eq_pinching
    (Y : Matrix (m ⊕ m) (m ⊕ m) R) (M : Matrix m m R) :
    cornerEmbed1 (unfold1 Y) + cornerEmbed2 (unfold2 Y) = holomovement Y ∧
    cornerEmbed1 (unfold1 (enfold M)) + cornerEmbed2 (unfold2 (enfold M)) = enfold M := by
  constructor
  · rw [holomovement_eq_fromBlocks_unfold]
    unfold cornerEmbed1 cornerEmbed2
    simp only [Matrix.fromBlocks_add, add_zero, zero_add]
  · rw [(bohmian_holographic_retraction M).1,
        (bohmian_holographic_retraction M).2,
        (corner_embeddings_sum_eq_enfold M).1]

end BlockCornerMaps

end InfoGeometry.Synthesis.AndreevKreinHestenesCuntzSynthesis
