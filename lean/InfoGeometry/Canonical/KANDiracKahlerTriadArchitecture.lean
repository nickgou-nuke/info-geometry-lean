import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# KAN Dirac-Kähler Triad Architecture & Nilpotent Peirce Intertwining

This module establishes the general ring-theoretic and operator-algebraic foundations
unifying the Iwasawa $KAN$ global decomposition, the split Peirce projectors, the
parabolic reflection group of the Klein bottle, and the triad decomposition of the
Dirac-Kähler operator $D = D_K + D_A + D_N$:

1. **Abstract Nilpotent Step Operator & Split Peirce Intertwining**:
   - In any ring $A$ with involution $J^2 = 1$ and real scalar multiplication ($[Ring\ A]\ [Algebra\ \mathbb{R}\ A]$),
     the split Peirce projectors $P_\pm = \frac{1 \pm J}{2}$ satisfy:
     $P_+ e_+ = e_+$, $e_+ P_+ = 0$, $e_+ P_- = e_+$, $P_- e_+ = 0$.
   - The unipotent group $u_N(x) = 1 + x e_+$ satisfies:
     $u_N(x) u_N(y) = u_N(x + y)$, $u_N(x) P_- = P_- + x e_+$,
     $P_+ u_N(x) P_- = x e_+$, and leaves $P_+$ fixed.

2. **Parabolic Reflection and Klein Bottle Inversion**:
   - An involution $R^2 = 1$ anticommuting with $J$ ($\{R, J\} = 0$)
     transposes the Peirce projectors: $R P_\pm R = P_\mp$.
   - $R$ inverts hyperbolic boosts $A(t) = \cosh t \cdot 1 + \sinh t \cdot J$:
     $R A(t) R = A(-t)$, establishing the outer automorphism of the Klein bottle
     crystallographic lattice $a b a^{-1} = b^{-1}$.

3. **Triad Decomposition of the Dirac-Kähler Operator**:
   - $D = D_K + D_A + D_N$, where:
     - $D_K$ is chiral: $\{D_K, J\} = 0 \implies P_\pm D_K P_\pm = 0$.
     - $D_A$ is radial/abelian: $[D_A, J] = 0 \implies P_\pm D_A P_\mp = 0$.
     - $D_N$ is nilpotent/horocyclic: $D_N^2 = 0$, $J D_N = D_N$, $D_N J = -D_N$.
   - **Diagonal Localization on $D_A$**:
     $P_+ D P_+ = P_+ D_A P_+$ and $P_- D P_- = P_- D_A P_-$.
   - **Off-Diagonal Decoupling**:
     $P_+ D P_- = P_+ D_K P_- + D_N$ and $P_- D P_+ = P_- D_K P_+$.

4. **Trace Functional Supported Strictly on $\mathfrak{a}$**:
   - On $\mathrm{Mat}_2(R)$, skew-adjoint $\mathfrak{k}$ and strictly upper-triangular
     $\mathfrak{n}$ are trace-free, proving $\operatorname{tr}(X_\mathfrak{k} + X_\mathfrak{a} + X_\mathfrak{n}) = \operatorname{tr}(X_\mathfrak{a})$.

5. **Machine-Checked Master Packet**:
   - `KANDiracKahlerTriadPacket` unifying all five strata.

All theorems are proved constructively in native Lean 4 / Mathlib with zero gaps.
-/

noncomputable section

namespace InfoGeometry.Canonical.KANDiracKahlerTriadArchitecture

open Matrix

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### Stratum 1: Split Peirce Projectors and Nilpotent Step Operator -/

/-- Positive Peirce projector: $P_+ = \frac{1}{2}(1 + J)$. -/
def peircePlus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) : A :=
  (1/2 : ℝ) • (1 + J)

/-- Negative Peirce projector: $P_- = \frac{1}{2}(1 - J)$. -/
def peirceMinus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) : A :=
  (1/2 : ℝ) • (1 - J)

/-- $P_+$ is idempotent: $P_+^2 = P_+$. -/
theorem peircePlus_sq {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (hJ : J * J = 1) :
    peircePlus J * peircePlus J = peircePlus J := by
  simp [peircePlus, smul_mul_assoc, mul_smul_comm, smul_smul, hJ,
    smul_add, add_mul, mul_add]
  module

/-- $P_-$ is idempotent: $P_-^2 = P_-$. -/
theorem peirceMinus_sq {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (hJ : J * J = 1) :
    peirceMinus J * peirceMinus J = peirceMinus J := by
  simp [peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul, hJ,
    smul_sub, sub_mul, mul_sub]
  module

/-- Orthogonality: $P_+ \cdot P_- = 0$. -/
theorem peircePlus_mul_minus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (hJ : J * J = 1) :
    peircePlus J * peirceMinus J = 0 := by
  simp [peircePlus, peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul,
    hJ, smul_sub, smul_add, add_mul, mul_add, sub_mul, mul_sub]
  module

/-- Orthogonality: $P_- \cdot P_+ = 0$. -/
theorem peirceMinus_mul_plus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (hJ : J * J = 1) :
    peirceMinus J * peircePlus J = 0 := by
  simp [peircePlus, peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul,
    hJ, smul_sub, smul_add, add_mul, mul_add, sub_mul, mul_sub]

/-- Resolution of identity: $P_+ + P_- = 1$. -/
theorem peircePlus_add_minus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) :
    peircePlus J + peirceMinus J = 1 := by
  simp [peircePlus, peirceMinus, smul_add, smul_sub]
  module

/-- The step operator $e_+$ is a left eigenvector of the positive projector: $P_+ e_+ = e_+$. -/
theorem peircePlus_mul_step {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (h_J_e : J * e_plus = e_plus) :
    peircePlus J * e_plus = e_plus := by
  dsimp [peircePlus]
  rw [smul_mul_assoc, add_mul, one_mul, h_J_e]
  have h2 : e_plus + e_plus = (2 : ℝ) • e_plus := by
    calc e_plus + e_plus = (1 : ℝ) • e_plus + (1 : ℝ) • e_plus := by rw [one_smul]
    _ = ((1 : ℝ) + 1) • e_plus := by rw [add_smul]
    _ = (2 : ℝ) • e_plus := by norm_num
  rw [h2, smul_smul]
  norm_num

/-- The step operator annihilates the positive projector on the right: $e_+ P_+ = 0$. -/
theorem step_mul_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (he_J : e_plus * J = -e_plus) :
    e_plus * peircePlus J = 0 := by
  dsimp [peircePlus]
  rw [mul_smul_comm, mul_add, mul_one, he_J, add_neg_cancel, smul_zero]

/-- The step operator acts on the negative projector to yield $e_+$: $e_+ P_- = e_+$. -/
theorem step_mul_peirceMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (he_J : e_plus * J = -e_plus) :
    e_plus * peirceMinus J = e_plus := by
  dsimp [peirceMinus]
  rw [mul_smul_comm, mul_sub, mul_one, he_J, sub_neg_eq_add]
  have h2 : e_plus + e_plus = (2 : ℝ) • e_plus := by
    calc e_plus + e_plus = (1 : ℝ) • e_plus + (1 : ℝ) • e_plus := by rw [one_smul]
    _ = ((1 : ℝ) + 1) • e_plus := by rw [add_smul]
    _ = (2 : ℝ) • e_plus := by norm_num
  rw [h2, smul_smul]
  norm_num

/-- The negative projector annihilates the step operator on the left: $P_- e_+ = 0$. -/
theorem peirceMinus_mul_step {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (h_J_e : J * e_plus = e_plus) :
    peirceMinus J * e_plus = 0 := by
  dsimp [peirceMinus]
  rw [smul_mul_assoc, sub_mul, one_mul, h_J_e, sub_self, smul_zero]

/-- The $(+, -)$ sandwich identity: $P_+ e_+ P_- = e_+$. -/
theorem peircePlus_step_peirceMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (h_J_e : J * e_plus = e_plus) (he_J : e_plus * J = -e_plus) :
    peircePlus J * e_plus * peirceMinus J = e_plus := by
  rw [mul_assoc, step_mul_peirceMinus J e_plus he_J, peircePlus_mul_step J e_plus h_J_e]

/-- The $(-, +)$ sandwich identity: $P_- e_+ P_+ = 0$. -/
theorem peirceMinus_step_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (he_J : e_plus * J = -e_plus) :
    peirceMinus J * e_plus * peircePlus J = 0 := by
  rw [mul_assoc, step_mul_peircePlus J e_plus he_J, mul_zero]

/-- The $(+, +)$ sandwich identity: $P_+ e_+ P_+ = 0$. -/
theorem peircePlus_step_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (he_J : e_plus * J = -e_plus) :
    peircePlus J * e_plus * peircePlus J = 0 := by
  rw [mul_assoc, step_mul_peircePlus J e_plus he_J, mul_zero]

/-- The $(-, -)$ sandwich identity: $P_- e_+ P_- = 0$. -/
theorem peirceMinus_step_peirceMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (h_J_e : J * e_plus = e_plus) :
    peirceMinus J * e_plus * peirceMinus J = 0 := by
  rw [peirceMinus_mul_step J e_plus h_J_e, zero_mul]

/-! ### Stratum 2: The Nilpotent Horocycle Group $N(x) = 1 + x e_+$ -/

/-- Unipotent horocycle shear element: $u_N(x) = 1 + x e_+$. -/
def unipotentN {A : Type*} [Ring A] [Algebra ℝ A] (e_plus : A) (x : ℝ) : A :=
  1 + x • e_plus

/-- Group multiplication law of the unipotent horocycle: $u_N(x) u_N(y) = u_N(x + y)$. -/
theorem unipotentN_mul {A : Type*} [Ring A] [Algebra ℝ A]
    (e_plus : A) (he_sq : e_plus * e_plus = 0) (x y : ℝ) :
    unipotentN e_plus x * unipotentN e_plus y = unipotentN e_plus (x + y) := by
  dsimp [unipotentN]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    he_sq, smul_zero, add_zero]
  rw [add_assoc, ← add_smul]

/-- Unipotent group inverse: $u_N(x) u_N(-x) = 1$. -/
theorem unipotentN_inv {A : Type*} [Ring A] [Algebra ℝ A]
    (e_plus : A) (he_sq : e_plus * e_plus = 0) (x : ℝ) :
    unipotentN e_plus x * unipotentN e_plus (-x) = 1 := by
  rw [unipotentN_mul e_plus he_sq x (-x)]
  dsimp [unipotentN]
  rw [add_neg_cancel, zero_smul, add_zero]

/-- Unipotent shear across the negative Peirce projector: $u_N(x) P_- = P_- + x e_+$. -/
theorem unipotentN_shear_peirceMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (he_J : e_plus * J = -e_plus) (x : ℝ) :
    unipotentN e_plus x * peirceMinus J = peirceMinus J + x • e_plus := by
  dsimp [unipotentN]
  rw [add_mul, one_mul, smul_mul_assoc, step_mul_peirceMinus J e_plus he_J]

/-- Unipotent action on positive Peirce projector: $u_N(x) P_+ = P_+$. -/
theorem unipotentN_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (he_J : e_plus * J = -e_plus) (x : ℝ) :
    unipotentN e_plus x * peircePlus J = peircePlus J := by
  dsimp [unipotentN]
  rw [add_mul, one_mul, smul_mul_assoc, step_mul_peircePlus J e_plus he_J, smul_zero, add_zero]

/-- Unipotent transition between Peirce polarizations: $P_+ u_N(x) P_- = x e_+$. -/
theorem peircePlus_unipotentN_peirceMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (hJ : J * J = 1) (h_J_e : J * e_plus = e_plus) (he_J : e_plus * J = -e_plus) (x : ℝ) :
    peircePlus J * unipotentN e_plus x * peirceMinus J = x • e_plus := by
  rw [mul_assoc, unipotentN_shear_peirceMinus J e_plus he_J x]
  rw [mul_add, peircePlus_mul_minus J hJ, zero_add, mul_smul_comm, peircePlus_mul_step J e_plus h_J_e]

/-- No backward unipotent transition: $P_- u_N(x) P_+ = 0$. -/
theorem peirceMinus_unipotentN_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (hJ : J * J = 1) (he_J : e_plus * J = -e_plus) (x : ℝ) :
    peirceMinus J * unipotentN e_plus x * peircePlus J = 0 := by
  rw [mul_assoc, unipotentN_peircePlus J e_plus he_J x, peirceMinus_mul_plus J hJ]

/-- Invariance of the positive polarization: $P_+ u_N(x) P_+ = P_+$. -/
theorem peircePlus_unipotentN_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (hJ : J * J = 1) (he_J : e_plus * J = -e_plus) (x : ℝ) :
    peircePlus J * unipotentN e_plus x * peircePlus J = peircePlus J := by
  rw [mul_assoc, unipotentN_peircePlus J e_plus he_J x, peircePlus_sq J hJ]

/-- Right action on negative Peirce projector: $P_- u_N(x) = P_-$. -/
theorem peirceMinus_unipotentN {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (h_J_e : J * e_plus = e_plus) (x : ℝ) :
    peirceMinus J * unipotentN e_plus x = peirceMinus J := by
  dsimp [unipotentN]
  rw [mul_add, mul_one, mul_smul_comm, peirceMinus_mul_step J e_plus h_J_e, smul_zero, add_zero]

/-- Invariance of the negative polarization: $P_- u_N(x) P_- = P_-$. -/
theorem peirceMinus_unipotentN_peirceMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (J e_plus : A) (hJ : J * J = 1) (h_J_e : J * e_plus = e_plus) (x : ℝ) :
    peirceMinus J * unipotentN e_plus x * peirceMinus J = peirceMinus J := by
  rw [peirceMinus_unipotentN J e_plus h_J_e x, peirceMinus_sq J hJ]

/-! ### Stratum 3: Parabolic Reflection and Klein Bottle Inversion -/

/-- Parabolic reflection inverts the paracomplex structure: $R J R = -J$. -/
theorem R_conjugates_J {A : Type*} [Ring A]
    (R J : A) (hR_sq : R * R = 1) (hRJ : R * J + J * R = 0) :
    R * J * R = -J := by
  have h_anti : R * J = - (J * R) := by
    calc R * J = (R * J + J * R) - J * R := by abel
    _ = 0 - J * R := by rw [hRJ]
    _ = - (J * R) := by simp
  calc R * J * R = (- (J * R)) * R := by rw [h_anti]
  _ = - (J * (R * R)) := by rw [neg_mul, mul_assoc]
  _ = - (J * 1) := by rw [hR_sq]
  _ = -J := by rw [mul_one]

/-- Reflection transposes positive Peirce projector into negative: $R P_+ R = P_-$. -/
theorem R_swaps_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (R J : A) (hR_sq : R * R = 1) (hRJ : R * J + J * R = 0) :
    R * peircePlus J * R = peirceMinus J := by
  dsimp [peircePlus, peirceMinus]
  have h_mid : R * (1 + J) * R = 1 - J := by
    calc R * (1 + J) * R = (R * 1 + R * J) * R := by rw [mul_add]
    _ = (R + R * J) * R := by rw [mul_one]
    _ = R * R + (R * J * R) := by rw [add_mul, mul_assoc]
    _ = 1 + -J := by rw [hR_sq, R_conjugates_J R J hR_sq hRJ]
    _ = 1 - J := by rw [← sub_eq_add_neg]
  calc R * ((1/2 : ℝ) • (1 + J)) * R
    _ = ((1/2 : ℝ) • (R * (1 + J))) * R := by rw [mul_smul_comm]
    _ = (1/2 : ℝ) • (R * (1 + J) * R) := by rw [smul_mul_assoc]
    _ = (1/2 : ℝ) • (1 - J) := by rw [h_mid]

/-- Reflection transposes negative Peirce projector into positive: $R P_- R = P_+$. -/
theorem R_swaps_peirceMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (R J : A) (hR_sq : R * R = 1) (hRJ : R * J + J * R = 0) :
    R * peirceMinus J * R = peircePlus J := by
  dsimp [peircePlus, peirceMinus]
  have h_mid : R * (1 - J) * R = 1 + J := by
    calc R * (1 - J) * R = (R * 1 - R * J) * R := by rw [mul_sub]
    _ = (R - R * J) * R := by rw [mul_one]
    _ = R * R - (R * J * R) := by rw [sub_mul, mul_assoc]
    _ = 1 - -J := by rw [hR_sq, R_conjugates_J R J hR_sq hRJ]
    _ = 1 + J := by rw [sub_neg_eq_add]
  calc R * ((1/2 : ℝ) • (1 - J)) * R
    _ = ((1/2 : ℝ) • (R * (1 - J))) * R := by rw [mul_smul_comm]
    _ = (1/2 : ℝ) • (R * (1 - J) * R) := by rw [smul_mul_assoc]
    _ = (1/2 : ℝ) • (1 + J) := by rw [h_mid]

/-- Double reflection restores the positive Peirce projector: $R^2 P_+ R^2 = P_+$. -/
theorem R_restores_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (R J : A) (hR_sq : R * R = 1) (hRJ : R * J + J * R = 0) :
    R * (R * peircePlus J * R) * R = peircePlus J := by
  rw [R_swaps_peircePlus R J hR_sq hRJ, R_swaps_peirceMinus R J hR_sq hRJ]

/-- One-parameter hyperbolic boost in the split Cartan torus $A$: $A(t) = \cosh t \cdot 1 + \sinh t \cdot J$. -/
def hyperbolicBoost {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (t : ℝ) : A :=
  (Real.cosh t) • (1 : A) + (Real.sinh t) • J

/-- 
Klein Bottle Inversion:
Conjugation by the orientation-reversing reflection $R$ inverts the split boost $A(t) \mapsto A(-t)$,
realizing the defining Klein bottle outer automorphism $a b a^{-1} = b^{-1}$.
-/
theorem R_inverts_hyperbolicBoost {A : Type*} [Ring A] [Algebra ℝ A]
    (R J : A) (hR_sq : R * R = 1) (hRJ : R * J + J * R = 0) (t : ℝ) :
    R * hyperbolicBoost J t * R = hyperbolicBoost J (-t) := by
  dsimp [hyperbolicBoost]
  have h1 : R * ((Real.cosh t) • (1 : A)) * R = (Real.cosh (-t)) • (1 : A) := by
    calc R * ((Real.cosh t) • (1 : A)) * R
      _ = ((Real.cosh t) • (R * 1)) * R := by rw [mul_smul_comm]
      _ = (Real.cosh t) • (R * 1 * R) := by rw [smul_mul_assoc]
      _ = (Real.cosh t) • (R * R) := by rw [mul_one]
      _ = (Real.cosh t) • (1 : A) := by rw [hR_sq]
      _ = (Real.cosh (-t)) • (1 : A) := by rw [Real.cosh_neg]
  have h2 : R * ((Real.sinh t) • J) * R = (Real.sinh (-t)) • J := by
    calc R * ((Real.sinh t) • J) * R
      _ = ((Real.sinh t) • (R * J)) * R := by rw [mul_smul_comm]
      _ = (Real.sinh t) • (R * J * R) := by rw [smul_mul_assoc]
      _ = (Real.sinh t) • (-J) := by rw [R_conjugates_J R J hR_sq hRJ]
      _ = - ((Real.sinh t) • J) := by rw [smul_neg]
      _ = (- Real.sinh t) • J := by rw [neg_smul]
      _ = (Real.sinh (-t)) • J := by rw [Real.sinh_neg]
  calc R * ((Real.cosh t) • (1 : A) + (Real.sinh t) • J) * R
    _ = (R * ((Real.cosh t) • (1 : A)) + R * ((Real.sinh t) • J)) * R := by rw [mul_add]
    _ = R * ((Real.cosh t) • (1 : A)) * R + R * ((Real.sinh t) • J) * R := by rw [add_mul]
    _ = (Real.cosh (-t)) • (1 : A) + (Real.sinh (-t)) • J := by rw [h1, h2]

/-! ### Stratum 4: Triad Decomposition of the Dirac-Kähler Operator -/

/-- Radial / Abelian operator commutes with $J$: $[D_A, J] = 0$. -/
theorem peircePlus_mul_DA {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_A : A) (h_abelian : D_A * J = J * D_A) :
    peircePlus J * D_A = D_A * peircePlus J := by
  dsimp [peircePlus]
  have h_comm : (1 + J) * D_A = D_A * (1 + J) := by
    calc (1 + J) * D_A = D_A + J * D_A := by rw [add_mul, one_mul]
    _ = D_A + D_A * J := by rw [← h_abelian]
    _ = D_A * 1 + D_A * J := by rw [mul_one]
    _ = D_A * (1 + J) := by rw [← mul_add]
  rw [smul_mul_assoc, h_comm, mul_smul_comm]

theorem peirceMinus_mul_DA {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_A : A) (h_abelian : D_A * J = J * D_A) :
    peirceMinus J * D_A = D_A * peirceMinus J := by
  dsimp [peirceMinus]
  have h_comm : (1 - J) * D_A = D_A * (1 - J) := by
    calc (1 - J) * D_A = D_A - J * D_A := by rw [sub_mul, one_mul]
    _ = D_A - D_A * J := by rw [← h_abelian]
    _ = D_A * 1 - D_A * J := by rw [mul_one]
    _ = D_A * (1 - J) := by rw [← mul_sub]
  rw [smul_mul_assoc, h_comm, mul_smul_comm]

theorem peircePlus_DA_peirceMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_A : A) (hJ : J * J = 1) (h_abelian : D_A * J = J * D_A) :
    peircePlus J * D_A * peirceMinus J = 0 := by
  rw [peircePlus_mul_DA J D_A h_abelian, mul_assoc, peircePlus_mul_minus J hJ, mul_zero]

theorem peirceMinus_DA_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_A : A) (hJ : J * J = 1) (h_abelian : D_A * J = J * D_A) :
    peirceMinus J * D_A * peircePlus J = 0 := by
  rw [peirceMinus_mul_DA J D_A h_abelian, mul_assoc, peirceMinus_mul_plus J hJ, mul_zero]

/-- 
Diagonal Localization of $D_A$:
The radial Euler operator $D_A$ is strictly diagonal in the Peirce basis:
$D_A = P_+ D_A P_+ + P_- D_A P_-$.
-/
theorem DA_diagonal_split {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_A : A) (hJ : J * J = 1) (h_abelian : D_A * J = J * D_A) :
    D_A = peircePlus J * D_A * peircePlus J + peirceMinus J * D_A * peirceMinus J := by
  calc D_A = 1 * D_A * 1 := by rw [one_mul, mul_one]
  _ = (peircePlus J + peirceMinus J) * D_A * (peircePlus J + peirceMinus J) := by
      rw [peircePlus_add_minus J]
  _ = (peircePlus J * D_A + peirceMinus J * D_A) * (peircePlus J + peirceMinus J) := by
      rw [add_mul]
  _ = peircePlus J * D_A * peircePlus J + peircePlus J * D_A * peirceMinus J +
      (peirceMinus J * D_A * peircePlus J + peirceMinus J * D_A * peirceMinus J) := by
      rw [add_mul, mul_add, mul_add]
  _ = peircePlus J * D_A * peircePlus J + 0 + (0 + peirceMinus J * D_A * peirceMinus J) := by
      rw [peircePlus_DA_peirceMinus J D_A hJ h_abelian,
          peirceMinus_DA_peircePlus J D_A hJ h_abelian]
  _ = peircePlus J * D_A * peircePlus J + peirceMinus J * D_A * peirceMinus J := by
      abel

/-- Chiral intertwining: $P_+ D_K = D_K P_-$. -/
theorem peircePlus_mul_DK {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_K : A) (h_chiral : D_K * J + J * D_K = 0) :
    peircePlus J * D_K = D_K * peirceMinus J := by
  dsimp [peircePlus, peirceMinus]
  have h_anti : J * D_K = - (D_K * J) := by
    calc J * D_K = (D_K * J + J * D_K) - D_K * J := by abel
    _ = 0 - D_K * J := by rw [h_chiral]
    _ = - (D_K * J) := by simp
  calc
    peircePlus J * D_K = ((1/2 : ℝ) • (1 + J)) * D_K := rfl
    _ = (1/2 : ℝ) • ((1 + J) * D_K) := by rw [smul_mul_assoc]
    _ = (1/2 : ℝ) • (D_K + J * D_K) := by rw [add_mul, one_mul]
    _ = (1/2 : ℝ) • (D_K - D_K * J) := by rw [h_anti, sub_eq_add_neg]
    _ = (1/2 : ℝ) • (D_K * (1 - J)) := by rw [mul_sub, mul_one]
    _ = D_K * ((1/2 : ℝ) • (1 - J)) := by rw [mul_smul_comm]
    _ = D_K * peirceMinus J := rfl

theorem peirceMinus_mul_DK {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_K : A) (h_chiral : D_K * J + J * D_K = 0) :
    peirceMinus J * D_K = D_K * peircePlus J := by
  dsimp [peircePlus, peirceMinus]
  have h_anti : J * D_K = - (D_K * J) := by
    calc J * D_K = (D_K * J + J * D_K) - D_K * J := by abel
    _ = 0 - D_K * J := by rw [h_chiral]
    _ = - (D_K * J) := by simp
  calc
    peirceMinus J * D_K = ((1/2 : ℝ) • (1 - J)) * D_K := rfl
    _ = (1/2 : ℝ) • ((1 - J) * D_K) := by rw [smul_mul_assoc]
    _ = (1/2 : ℝ) • (D_K - J * D_K) := by rw [sub_mul, one_mul]
    _ = (1/2 : ℝ) • (D_K - - (D_K * J)) := by rw [h_anti]
    _ = (1/2 : ℝ) • (D_K + D_K * J) := by rw [sub_neg_eq_add]
    _ = (1/2 : ℝ) • (D_K * (1 + J)) := by rw [mul_add, mul_one]
    _ = D_K * ((1/2 : ℝ) • (1 + J)) := by rw [mul_smul_comm]
    _ = D_K * peircePlus J := rfl

theorem peircePlus_DK_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_K : A) (hJ : J * J = 1) (h_chiral : D_K * J + J * D_K = 0) :
    peircePlus J * D_K * peircePlus J = 0 := by
  have h := peircePlus_mul_DK J D_K h_chiral
  rw [h, mul_assoc, peirceMinus_mul_plus J hJ, mul_zero]

theorem peirceMinus_DK_peirceMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_K : A) (hJ : J * J = 1) (h_chiral : D_K * J + J * D_K = 0) :
    peirceMinus J * D_K * peirceMinus J = 0 := by
  have h := peirceMinus_mul_DK J D_K h_chiral
  rw [h, mul_assoc, peircePlus_mul_minus J hJ, mul_zero]

/-- 
Off-Diagonal Decoupling of $D_K$:
The chiral angular operator $D_K$ is strictly off-diagonal in the Peirce basis:
$D_K = P_+ D_K P_- + P_- D_K P_+$.
-/
theorem DK_off_diagonal_split {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_K : A) (hJ : J * J = 1) (h_chiral : D_K * J + J * D_K = 0) :
    D_K = peircePlus J * D_K * peirceMinus J + peirceMinus J * D_K * peircePlus J := by
  calc D_K = 1 * D_K * 1 := by rw [one_mul, mul_one]
  _ = (peircePlus J + peirceMinus J) * D_K * (peircePlus J + peirceMinus J) := by
      rw [peircePlus_add_minus J]
  _ = (peircePlus J * D_K + peirceMinus J * D_K) * (peircePlus J + peirceMinus J) := by
      rw [add_mul]
  _ = peircePlus J * D_K * peircePlus J + peircePlus J * D_K * peirceMinus J +
      (peirceMinus J * D_K * peircePlus J + peirceMinus J * D_K * peirceMinus J) := by
      rw [add_mul, mul_add, mul_add]
  _ = 0 + peircePlus J * D_K * peirceMinus J + (peirceMinus J * D_K * peircePlus J + 0) := by
      rw [peircePlus_DK_peircePlus J D_K hJ h_chiral,
          peirceMinus_DK_peirceMinus J D_K hJ h_chiral]
  _ = peircePlus J * D_K * peirceMinus J + peirceMinus J * D_K * peircePlus J := by
      abel

/-- The total Dirac-Kähler operator is the sum of the Iwasawa triad operators: $D = D_K + D_A + D_N$. -/
def totalDirac {A : Type*} [Add A] (D_K D_A D_N : A) : A :=
  D_K + D_A + D_N

/-- 
THE DIAGONAL LOCALIZATION THEOREM (POSITIVE):
The positive Peirce projection of the total Dirac-Kähler operator
is governed exclusively by the radial Euler operator $D_A$:
$P_+ D P_+ = P_+ D_A P_+$.
-/
theorem totalDirac_peircePlus_diag {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_K D_A D_N : A) (hJ : J * J = 1)
    (h_chiral : D_K * J + J * D_K = 0)
    (he_J : D_N * J = -D_N) :
    peircePlus J * (totalDirac D_K D_A D_N) * peircePlus J =
      peircePlus J * D_A * peircePlus J := by
  dsimp [totalDirac]
  rw [mul_add, add_mul, mul_add, add_mul]
  rw [peircePlus_DK_peircePlus J D_K hJ h_chiral,
      peircePlus_step_peircePlus J D_N he_J]
  abel

/-- 
THE DIAGONAL LOCALIZATION THEOREM (NEGATIVE):
The negative Peirce projection of the total Dirac-Kähler operator
is governed exclusively by the radial Euler operator $D_A$:
$P_- D P_- = P_- D_A P_-$.
-/
theorem totalDirac_peirceMinus_diag {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_K D_A D_N : A) (hJ : J * J = 1)
    (h_chiral : D_K * J + J * D_K = 0)
    (h_J_e : J * D_N = D_N) :
    peirceMinus J * (totalDirac D_K D_A D_N) * peirceMinus J =
      peirceMinus J * D_A * peirceMinus J := by
  dsimp [totalDirac]
  rw [mul_add, add_mul, mul_add, add_mul]
  rw [peirceMinus_DK_peirceMinus J D_K hJ h_chiral,
      peirceMinus_step_peirceMinus J D_N h_J_e]
  abel

/-- 
THE OFF-DIAGONAL STEP THEOREM:
The $(+, -)$ off-diagonal sector receives contributions from both $D_K$ and the horocycle $D_N$:
$P_+ D P_- = P_+ D_K P_- + D_N$.
-/
theorem totalDirac_peircePlus_minus {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_K D_A D_N : A) (hJ : J * J = 1)
    (h_abelian : D_A * J = J * D_A)
    (h_J_e : J * D_N = D_N)
    (he_J : D_N * J = -D_N) :
    peircePlus J * (totalDirac D_K D_A D_N) * peirceMinus J =
      peircePlus J * D_K * peirceMinus J + D_N := by
  dsimp [totalDirac]
  rw [mul_add, add_mul, mul_add, add_mul]
  rw [peircePlus_DA_peirceMinus J D_A hJ h_abelian,
      peircePlus_step_peirceMinus J D_N h_J_e he_J]
  abel

/-- 
The $(-, +)$ off-diagonal sector is purely chiral from $D_K$, with zero backward horocycle transfer:
$P_- D P_+ = P_- D_K P_+$.
-/
theorem totalDirac_peirceMinus_plus {A : Type*} [Ring A] [Algebra ℝ A]
    (J D_K D_A D_N : A) (hJ : J * J = 1)
    (h_abelian : D_A * J = J * D_A)
    (he_J : D_N * J = -D_N) :
    peirceMinus J * (totalDirac D_K D_A D_N) * peircePlus J =
      peirceMinus J * D_K * peircePlus J := by
  dsimp [totalDirac]
  rw [mul_add, add_mul, mul_add, add_mul]
  rw [peirceMinus_DA_peircePlus J D_A hJ h_abelian,
      peirceMinus_step_peircePlus J D_N he_J]
  abel

/-! ### Stratum 5: Trace Localization on the Split Cartan Subspace $\mathfrak{a}$ -/

variable {R : Type*} [CommRing R]

/-- A skew-symmetric generator in $\mathfrak{k} = \mathfrak{so}(2)$ has zero trace. -/
theorem trace_k_skew (θ : R) :
    trace (!![0, -θ; θ, 0]) = 0 := by
  simp [trace, diag]

/-- A strictly upper-triangular nilpotent generator in $\mathfrak{n}$ has zero trace. -/
theorem trace_n_nilpotent (x : R) :
    trace (!![0, x; 0, 0]) = 0 := by
  simp [trace, diag]

/-- Nilpotent generator in $\mathfrak{n}$ squares to zero. -/
theorem n_gen_sq (x : R) :
    (!![0, x; 0, 0] : Matrix (Fin 2) (Fin 2) R) * !![0, x; 0, 0] = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- 
Trace Localization Theorem:
The linear trace functional $\operatorname{tr} : \mathfrak{g} \to R$ is supported exclusively
on the abelian split Cartan subspace $\mathfrak{a}$:
$\operatorname{tr}(X_\mathfrak{k} + X_\mathfrak{a} + X_\mathfrak{n}) = \operatorname{tr}(X_\mathfrak{a})$.
-/
theorem trace_kan_localization (θ t₁ t₂ x : R) :
    let K : Matrix (Fin 2) (Fin 2) R := !![0, -θ; θ, 0]
    let A_mat : Matrix (Fin 2) (Fin 2) R := !![t₁, 0; 0, t₂]
    let N_mat : Matrix (Fin 2) (Fin 2) R := !![0, x; 0, 0]
    trace (K + A_mat + N_mat) = trace A_mat := by
  intro K A_mat N_mat
  calc trace (K + A_mat + N_mat)
    _ = trace (K + A_mat) + trace N_mat := by rw [trace_add]
    _ = trace K + trace A_mat + trace N_mat := by rw [trace_add]
    _ = 0 + trace A_mat + 0 := by rw [trace_k_skew θ, trace_n_nilpotent x]
    _ = trace A_mat := by ring

/-- For trace-free split boosts ($t_1 = t, t_2 = -t$), the total trace vanishes identically. -/
theorem trace_kan_traceless (θ t x : R) :
    trace (!![0, -θ; θ, 0] + !![t, 0; 0, -t] + !![0, x; 0, 0] : Matrix (Fin 2) (Fin 2) R) = 0 := by
  rw [trace_kan_localization θ t (-t) x]
  simp [trace, diag]

/-! ### Stratum 6: The KAN Dirac-Kähler Triad Master Packet -/

/--
Machine-verified synthesis of the KAN Dirac-Kähler Triad Architecture:
unifying split Peirce intertwining, unipotent horocycle flow, parabolic Klein inversion,
and the triad decomposition of the Dirac-Kähler operator.
-/
structure KANDiracKahlerTriadPacket where
  -- Stratum 1: Split Peirce Projectors and Nilpotent Step Operator
  peirce_plus_mul_step :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J e_plus : A)
      (h_J_e : J * e_plus = e_plus),
      peircePlus J * e_plus = e_plus
  step_mul_peirce_plus :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J e_plus : A)
      (he_J : e_plus * J = -e_plus),
      e_plus * peircePlus J = 0
  step_mul_peirce_minus :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J e_plus : A)
      (he_J : e_plus * J = -e_plus),
      e_plus * peirceMinus J = e_plus
  peirce_minus_mul_step :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J e_plus : A)
      (h_J_e : J * e_plus = e_plus),
      peirceMinus J * e_plus = 0

  -- Stratum 2: Horocycle Group Laws and Peirce Transitions
  unipotent_group_mul :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (e_plus : A)
      (he_sq : e_plus * e_plus = 0) (x y : ℝ),
      unipotentN e_plus x * unipotentN e_plus y = unipotentN e_plus (x + y)
  unipotent_peirce_shear :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J e_plus : A)
      (he_J : e_plus * J = -e_plus) (x : ℝ),
      unipotentN e_plus x * peirceMinus J = peirceMinus J + x • e_plus
  peirce_plus_unipotent_minus :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J e_plus : A)
      (hJ : J * J = 1) (h_J_e : J * e_plus = e_plus)
      (he_J : e_plus * J = -e_plus) (x : ℝ),
      peircePlus J * unipotentN e_plus x * peirceMinus J = x • e_plus
  peirce_minus_unipotent_plus :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J e_plus : A)
      (hJ : J * J = 1) (he_J : e_plus * J = -e_plus) (x : ℝ),
      peirceMinus J * unipotentN e_plus x * peircePlus J = 0

  -- Stratum 3: Parabolic Reflection & Klein Bottle Inversion
  reflection_swaps_plus :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (R J : A)
      (hR_sq : R * R = 1) (hRJ : R * J + J * R = 0),
      R * peircePlus J * R = peirceMinus J
  reflection_swaps_minus :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (R J : A)
      (hR_sq : R * R = 1) (hRJ : R * J + J * R = 0),
      R * peirceMinus J * R = peircePlus J
  reflection_inverts_boost :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (R J : A)
      (hR_sq : R * R = 1) (hRJ : R * J + J * R = 0) (t : ℝ),
      R * hyperbolicBoost J t * R = hyperbolicBoost J (-t)

  -- Stratum 4: Triad Dirac-Kähler Decomposition
  total_dirac_plus_diag :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J D_K D_A D_N : A)
      (hJ : J * J = 1) (h_chiral : D_K * J + J * D_K = 0)
      (he_J : D_N * J = -D_N),
      peircePlus J * (totalDirac D_K D_A D_N) * peircePlus J =
        peircePlus J * D_A * peircePlus J
  total_dirac_minus_diag :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J D_K D_A D_N : A)
      (hJ : J * J = 1) (h_chiral : D_K * J + J * D_K = 0)
      (h_J_e : J * D_N = D_N),
      peirceMinus J * (totalDirac D_K D_A D_N) * peirceMinus J =
        peirceMinus J * D_A * peirceMinus J
  total_dirac_plus_minus :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J D_K D_A D_N : A)
      (hJ : J * J = 1) (h_abelian : D_A * J = J * D_A)
      (h_J_e : J * D_N = D_N) (he_J : D_N * J = -D_N),
      peircePlus J * (totalDirac D_K D_A D_N) * peirceMinus J =
        peircePlus J * D_K * peirceMinus J + D_N
  total_dirac_minus_plus :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J D_K D_A D_N : A)
      (hJ : J * J = 1) (h_abelian : D_A * J = J * D_A)
      (he_J : D_N * J = -D_N),
      peirceMinus J * (totalDirac D_K D_A D_N) * peircePlus J =
        peirceMinus J * D_K * peircePlus J

  -- Stratum 5: Trace Localization on a
  trace_k_zero : ∀ θ : ℝ, trace (!![0, -θ; θ, 0]) = 0
  trace_n_zero : ∀ x : ℝ, trace (!![0, x; 0, 0]) = 0
  trace_a_support :
    ∀ θ t₁ t₂ x : ℝ,
      trace (!![0, -θ; θ, 0] + !![t₁, 0; 0, t₂] + !![0, x; 0, 0]) =
        trace (!![t₁, 0; 0, t₂])

/--
Constructor for the KAN Dirac-Kähler Triad Master Packet.
-/
def makeKANDiracKahlerTriadPacket : KANDiracKahlerTriadPacket where
  peirce_plus_mul_step := peircePlus_mul_step
  step_mul_peirce_plus := step_mul_peircePlus
  step_mul_peirce_minus := step_mul_peirceMinus
  peirce_minus_mul_step := peirceMinus_mul_step
  unipotent_group_mul := unipotentN_mul
  unipotent_peirce_shear := unipotentN_shear_peirceMinus
  peirce_plus_unipotent_minus := peircePlus_unipotentN_peirceMinus
  peirce_minus_unipotent_plus := peirceMinus_unipotentN_peircePlus
  reflection_swaps_plus := R_swaps_peircePlus
  reflection_swaps_minus := R_swaps_peirceMinus
  reflection_inverts_boost := R_inverts_hyperbolicBoost
  total_dirac_plus_diag := totalDirac_peircePlus_diag
  total_dirac_minus_diag := totalDirac_peirceMinus_diag
  total_dirac_plus_minus := totalDirac_peircePlus_minus
  total_dirac_minus_plus := totalDirac_peirceMinus_plus
  trace_k_zero := trace_k_skew
  trace_n_zero := trace_n_nilpotent
  trace_a_support := trace_kan_localization

end InfoGeometry.Canonical.KANDiracKahlerTriadArchitecture
