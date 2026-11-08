import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Section 82: Real Majorana Substrate, Chiral Two-Sheeted Left/Right Ideals, Spinor Bilinears, and Fierz Identities

Module: `InfoGeometry.SuperGrassmannian.RealMajoranaChiralIdeal`

This module formalizes Section 82 of the unified architecture:
1. **The Abstract Two-Sheeted Chiral Ring Substrate**:
   - Chiral grading $\Gamma$ with $\Gamma^2 = 1$.
   - Sheet-swap paracomplex involution $J$ with $J^2 = 1$ and $\{J, \Gamma\} = 0$.
   - Chiral projectors $P_L = \frac{1}{2}(1 + \Gamma)$ and $P_R = \frac{1}{2}(1 - \Gamma)$.
   - Projector completeness $P_L + P_R = 1$, difference $P_L - P_R = \Gamma$, idempotence $P_L^2 = P_L$, $P_R^2 = P_R$, and orthogonality $P_L P_R = 0 = P_R P_L$.
   - Modular sheet-swap action interchanging chiral ideals: $J P_L J = P_R$ and $J P_R J = P_L$.
   - Emergent complex structure $K = J \Gamma$ with $K^2 = -1$, $\{K, J\} = 0$, $\{K, \Gamma\} = 0$.
   - Two-sheeted Peirce decomposition: $X = P_L X P_L + P_L X P_R + P_R X P_L + P_R X P_R$.
   - Transverse Majorana generator $\gamma$ with $\{\gamma, \Gamma\} = 0$.
   - Nilpotent odd chiral supercharges $Q = P_L \gamma P_R$ and $Q^\dagger = P_R \gamma P_L$ with $Q^2 = 0$, $(Q^\dagger)^2 = 0$.
   - Supersymmetric Hamiltonian $H = \{Q, Q^\dagger\}$ with exact conservation $[H, Q] = 0$ and $[H, Q^\dagger] = 0$.
2. **Concrete Real Majorana Matrix Representation**:
   - $2 \times 2$ carrier over an arbitrary commutative ring with $1/2$.
   - Explicit realization of $\Gamma = \sigma_3$, $J = \sigma_1$, $K = -\epsilon$, $P_L = E_{00}$, $P_R = E_{11}$, $Q = E_{01}$, $Q^\dagger = E_{10}$.
3. **Real Spinor Bilinears & Dyadic Outer Product Theorem**:
   - Bilinear channels: scalar $S$, chiral/pseudoscalar $P$, vector/paracomplex $V_1$, axial/symplectic $V_2$.
   - Dyadic outer product theorem:
     $2 \cdot (\psi \phi^\top) = S \cdot \mathbf{1} + P \cdot \Gamma + V_1 \cdot J - V_2 \cdot K$.
4. **Real Chiral Fierz Completeness Identities**:
   - Ideal/supercharge decomposition:
     $\mathrm{Swap} = P_L \otimes P_L + P_R \otimes P_R + Q \otimes Q^\dagger + Q^\dagger \otimes Q$.
   - Pauli/chiral basis decomposition:
     $2 \cdot \mathrm{Swap} = \mathbf{1} \otimes \mathbf{1} + \Gamma \otimes \Gamma + J \otimes J - K \otimes K$.
5. **5-Graded Lie Superalgebra Derivation**:
   - Characteristic polynomial $\mathcal{D}^3(X) = 4 \mathcal{D}(X)$ where $\mathcal{D}(X) = [\Gamma, X]$, establishing the root-space decomposition with eigenvalues $\{0, \pm 2\}$.
6. **Supertrace & Real SUSY Vacuum Energy Cancellation**:
   - $\operatorname{STr}(H_{\mathrm{susy}}) = 0$.
7. **Master Verification Certificate**:
   - `compile_real_majorana_chiral_ideal` with 0 sorry, 0 admit, 0 custom axioms.
-/

namespace InfoGeometry.SuperGrassmannian.RealMajoranaChiralIdeal

/-! ### 1. Abstract Two-Sheeted Chiral Ring Substrate -/

structure ChiralSheetSubstrate (R : Type*) [Ring R] where
  Γ : R
  J : R
  Γ_sq : Γ ^ 2 = 1
  J_sq : J ^ 2 = 1
  J_Γ_anticomm : J * Γ + Γ * J = 0
  half : R
  two_half : half + half = 1
  half_comm : ∀ x : R, half * x = x * half

namespace ChiralSheetSubstrate

variable {R : Type*} [Ring R] (S : ChiralSheetSubstrate R)

lemma Γ_mul_Γ : S.Γ * S.Γ = 1 := by
  have h := S.Γ_sq; rwa [sq] at h

lemma J_mul_J : S.J * S.J = 1 := by
  have h := S.J_sq; rwa [sq] at h

lemma JΓ_eq_neg_ΓJ : S.J * S.Γ = - (S.Γ * S.J) := by
  calc S.J * S.Γ = (S.J * S.Γ + S.Γ * S.J) - S.Γ * S.J := by abel
  _ = 0 - S.Γ * S.J := by rw [S.J_Γ_anticomm]
  _ = - (S.Γ * S.J) := by abel

lemma ΓJ_eq_neg_JΓ : S.Γ * S.J = - (S.J * S.Γ) := by
  rw [JΓ_eq_neg_ΓJ, neg_neg]

lemma two_mul_half : (2 : R) * S.half = 1 := by
  rw [two_mul, S.two_half]

lemma half_mul_two : S.half * (2 : R) = 1 := by
  rw [mul_two, S.two_half]

lemma mul_half_mul_half (x y : R) :
    (S.half * x) * (S.half * y) = (S.half * S.half) * (x * y) := by
  calc
    (S.half * x) * (S.half * y) = S.half * (x * S.half) * y := by noncomm_ring
    _ = S.half * (S.half * x) * y := by rw [S.half_comm x]
    _ = (S.half * S.half) * (x * y) := by noncomm_ring

lemma mul_half_assoc (x y : R) : x * (S.half * y) = S.half * (x * y) := by
  calc
    x * (S.half * y) = (x * S.half) * y := by rw [← mul_assoc]
    _ = (S.half * x) * y := by rw [← S.half_comm x]
    _ = S.half * (x * y) := by rw [mul_assoc]

/-- Left chiral projector $P_L = \frac{1}{2}(1 + \Gamma)$. -/
def PL : R := S.half * (1 + S.Γ)

/-- Right chiral projector $P_R = \frac{1}{2}(1 - \Gamma)$. -/
def PR : R := S.half * (1 - S.Γ)

theorem PL_add_PR : S.PL + S.PR = 1 := by
  unfold PL PR
  rw [← mul_add]
  have h : (1 + S.Γ) + (1 - S.Γ) = (2 : R) := by
    calc (1 + S.Γ) + (1 - S.Γ) = (1 + 1 : R) := by abel
    _ = (2 : R) := by norm_num
  rw [h, half_mul_two]

theorem PL_sub_PR : S.PL - S.PR = S.Γ := by
  unfold PL PR
  rw [← mul_sub]
  have h : (1 + S.Γ) - (1 - S.Γ) = (2 : R) * S.Γ := by
    calc (1 + S.Γ) - (1 - S.Γ) = S.Γ + S.Γ := by abel
    _ = (2 : R) * S.Γ := by rw [two_mul]
  rw [h, ← mul_assoc, S.half_comm, two_mul_half, one_mul]

theorem PL_sq : S.PL ^ 2 = S.PL := by
  unfold PL
  rw [sq, mul_half_mul_half]
  have h_inner : (1 + S.Γ) * (1 + S.Γ) = (2 : R) * (1 + S.Γ) := by
    calc (1 + S.Γ) * (1 + S.Γ) = 1 + S.Γ + S.Γ + S.Γ * S.Γ := by noncomm_ring
    _ = 1 + S.Γ + S.Γ + 1 := by rw [Γ_mul_Γ]
    _ = (2 : R) * (1 + S.Γ) := by
      rw [two_mul (1 + S.Γ)]
      abel
  rw [h_inner, ← mul_assoc, mul_assoc S.half S.half 2, half_mul_two, mul_one]

theorem PR_sq : S.PR ^ 2 = S.PR := by
  unfold PR
  rw [sq, mul_half_mul_half]
  have h_inner : (1 - S.Γ) * (1 - S.Γ) = (2 : R) * (1 - S.Γ) := by
    calc (1 - S.Γ) * (1 - S.Γ) = 1 - S.Γ - S.Γ + S.Γ * S.Γ := by noncomm_ring
    _ = 1 - S.Γ - S.Γ + 1 := by rw [Γ_mul_Γ]
    _ = (2 : R) * (1 - S.Γ) := by
      rw [two_mul (1 - S.Γ)]
      abel
  rw [h_inner, ← mul_assoc, mul_assoc S.half S.half 2, half_mul_two, mul_one]

theorem PL_mul_PR : S.PL * S.PR = 0 := by
  unfold PL PR
  rw [mul_half_mul_half]
  have h_inner : (1 + S.Γ) * (1 - S.Γ) = 0 := by
    calc (1 + S.Γ) * (1 - S.Γ) = 1 - S.Γ * S.Γ := by noncomm_ring
    _ = 1 - 1 := by rw [Γ_mul_Γ]
    _ = 0 := by abel
  rw [h_inner, mul_zero]

theorem PR_mul_PL : S.PR * S.PL = 0 := by
  unfold PL PR
  rw [mul_half_mul_half]
  have h_inner : (1 - S.Γ) * (1 + S.Γ) = 0 := by
    calc (1 - S.Γ) * (1 + S.Γ) = 1 - S.Γ * S.Γ := by noncomm_ring
    _ = 1 - 1 := by rw [Γ_mul_Γ]
    _ = 0 := by abel
  rw [h_inner, mul_zero]

/-! ### Modular Sheet-Swap Action on Chiral Ideals -/

lemma J_mul_PL : S.J * S.PL = S.PR * S.J := by
  unfold PL PR
  rw [mul_half_assoc, mul_assoc]
  congr 1
  calc S.J * (1 + S.Γ) = S.J + S.J * S.Γ := by noncomm_ring
  _ = S.J - S.Γ * S.J := by rw [JΓ_eq_neg_ΓJ]; abel
  _ = (1 - S.Γ) * S.J := by noncomm_ring

lemma J_mul_PR : S.J * S.PR = S.PL * S.J := by
  unfold PL PR
  rw [mul_half_assoc, mul_assoc]
  congr 1
  calc S.J * (1 - S.Γ) = S.J - S.J * S.Γ := by noncomm_ring
  _ = S.J + S.Γ * S.J := by rw [JΓ_eq_neg_ΓJ]; abel
  _ = (1 + S.Γ) * S.J := by noncomm_ring

theorem J_PL_J : S.J * S.PL * S.J = S.PR := by
  rw [J_mul_PL, mul_assoc, J_mul_J, mul_one]

theorem J_PR_J : S.J * S.PR * S.J = S.PL := by
  rw [J_mul_PR, mul_assoc, J_mul_J, mul_one]

/-! ### Emergent Complex Structure -/

/-- Emergent complex structure $K = J \Gamma$. -/
def K : R := S.J * S.Γ

theorem K_sq : S.K ^ 2 = -1 := by
  unfold K
  rw [sq]
  calc (S.J * S.Γ) * (S.J * S.Γ) = S.J * (S.Γ * S.J) * S.Γ := by noncomm_ring
  _ = S.J * (- (S.J * S.Γ)) * S.Γ := by rw [ΓJ_eq_neg_JΓ]
  _ = - ((S.J * S.J) * (S.Γ * S.Γ)) := by noncomm_ring
  _ = - (1 * 1 : R) := by rw [J_mul_J, Γ_mul_Γ]
  _ = -1 := by rw [mul_one]

theorem K_anticomm_J : S.K * S.J + S.J * S.K = 0 := by
  unfold K
  calc (S.J * S.Γ) * S.J + S.J * (S.J * S.Γ)
    = S.J * (S.Γ * S.J) + (S.J * S.J) * S.Γ := by noncomm_ring
  _ = S.J * (- (S.J * S.Γ)) + 1 * S.Γ := by rw [ΓJ_eq_neg_JΓ, J_mul_J]
  _ = - (S.J * (S.J * S.Γ)) + S.Γ := by rw [mul_neg, one_mul]
  _ = - ((S.J * S.J) * S.Γ) + S.Γ := by noncomm_ring
  _ = - (1 * S.Γ) + S.Γ := by rw [J_mul_J]
  _ = - S.Γ + S.Γ := by rw [one_mul]
  _ = 0 := by abel

theorem K_anticomm_Γ : S.K * S.Γ + S.Γ * S.K = 0 := by
  unfold K
  calc (S.J * S.Γ) * S.Γ + S.Γ * (S.J * S.Γ)
    = S.J * (S.Γ * S.Γ) + (S.Γ * S.J) * S.Γ := by noncomm_ring
  _ = S.J * 1 + (- (S.J * S.Γ)) * S.Γ := by rw [Γ_mul_Γ, ΓJ_eq_neg_JΓ]
  _ = S.J - (S.J * S.Γ * S.Γ) := by noncomm_ring
  _ = S.J - S.J * (S.Γ * S.Γ) := by noncomm_ring
  _ = S.J - S.J * 1 := by rw [Γ_mul_Γ]
  _ = 0 := by rw [mul_one, sub_self]

/-! ### Two-Sheeted Peirce Decomposition -/

theorem peirce_decomp (X : R) :
    X = S.PL * X * S.PL + S.PL * X * S.PR + S.PR * X * S.PL + S.PR * X * S.PR := by
  have h1 : X = (S.PL + S.PR) * X * (S.PL + S.PR) := by
    rw [PL_add_PR, one_mul, mul_one]
  calc X = (S.PL + S.PR) * X * (S.PL + S.PR) := h1
  _ = (S.PL * X + S.PR * X) * (S.PL + S.PR) := by rw [add_mul]
  _ = S.PL * X * S.PL + S.PL * X * S.PR + S.PR * X * S.PL + S.PR * X * S.PR := by
    noncomm_ring

/-! ### Transverse Majorana Generator & Nilpotent Supercharges -/

/-- A transverse Majorana generator $\gamma$ anticommutes with chiral grading $\Gamma$. -/
def is_transverse (γ : R) : Prop :=
  γ * S.Γ + S.Γ * γ = 0

lemma transverse_gamma_PL {γ : R} (h : S.is_transverse γ) :
    γ * S.PL = S.PR * γ := by
  unfold PL PR
  have hanticomm : γ * S.Γ = - (S.Γ * γ) := by
    calc γ * S.Γ = (γ * S.Γ + S.Γ * γ) - S.Γ * γ := by abel
    _ = 0 - S.Γ * γ := by rw [h]
    _ = - (S.Γ * γ) := by abel
  rw [mul_half_assoc, mul_assoc]
  congr 1
  calc γ * (1 + S.Γ) = γ + γ * S.Γ := by noncomm_ring
  _ = γ - S.Γ * γ := by rw [hanticomm]; abel
  _ = (1 - S.Γ) * γ := by noncomm_ring

lemma transverse_gamma_PR {γ : R} (h : S.is_transverse γ) :
    γ * S.PR = S.PL * γ := by
  unfold PL PR
  have hanticomm : γ * S.Γ = - (S.Γ * γ) := by
    calc γ * S.Γ = (γ * S.Γ + S.Γ * γ) - S.Γ * γ := by abel
    _ = 0 - S.Γ * γ := by rw [h]
    _ = - (S.Γ * γ) := by abel
  rw [mul_half_assoc, mul_assoc]
  congr 1
  calc γ * (1 - S.Γ) = γ - γ * S.Γ := by noncomm_ring
  _ = γ + S.Γ * γ := by rw [hanticomm]; abel
  _ = (1 + S.Γ) * γ := by noncomm_ring

/-- Odd chiral supercharge $Q = P_L \gamma P_R$. -/
def superchargeQ (γ : R) : R := S.PL * γ * S.PR

/-- Conjugate odd chiral supercharge $Q^\dagger = P_R \gamma P_L$. -/
def superchargeQ_dag (γ : R) : R := S.PR * γ * S.PL

theorem Q_sq (γ : R) : S.superchargeQ γ ^ 2 = 0 := by
  unfold superchargeQ
  rw [sq]
  calc (S.PL * γ * S.PR) * (S.PL * γ * S.PR)
    = S.PL * γ * (S.PR * S.PL) * γ * S.PR := by noncomm_ring
  _ = S.PL * γ * 0 * γ * S.PR := by rw [PR_mul_PL]
  _ = 0 := by noncomm_ring

theorem Q_dag_sq (γ : R) : S.superchargeQ_dag γ ^ 2 = 0 := by
  unfold superchargeQ_dag
  rw [sq]
  calc (S.PR * γ * S.PL) * (S.PR * γ * S.PL)
    = S.PR * γ * (S.PL * S.PR) * γ * S.PL := by noncomm_ring
  _ = S.PR * γ * 0 * γ * S.PL := by rw [PL_mul_PR]
  _ = 0 := by noncomm_ring

theorem PL_mul_Q (γ : R) : S.PL * S.superchargeQ γ = S.superchargeQ γ := by
  unfold superchargeQ
  calc S.PL * (S.PL * γ * S.PR) = (S.PL * S.PL) * γ * S.PR := by noncomm_ring
  _ = (S.PL ^ 2) * γ * S.PR := by rw [sq]
  _ = S.PL * γ * S.PR := by rw [PL_sq]

theorem Q_mul_PR (γ : R) : S.superchargeQ γ * S.PR = S.superchargeQ γ := by
  unfold superchargeQ
  calc (S.PL * γ * S.PR) * S.PR = S.PL * γ * (S.PR * S.PR) := by noncomm_ring
  _ = S.PL * γ * (S.PR ^ 2) := by rw [sq]
  _ = S.PL * γ * S.PR := by rw [PR_sq]

theorem PR_mul_Q (γ : R) : S.PR * S.superchargeQ γ = 0 := by
  unfold superchargeQ
  calc S.PR * (S.PL * γ * S.PR) = (S.PR * S.PL) * γ * S.PR := by noncomm_ring
  _ = 0 * γ * S.PR := by rw [PR_mul_PL]
  _ = 0 := by noncomm_ring

theorem Q_mul_PL (γ : R) : S.superchargeQ γ * S.PL = 0 := by
  unfold superchargeQ
  calc (S.PL * γ * S.PR) * S.PL = S.PL * γ * (S.PR * S.PL) := by noncomm_ring
  _ = S.PL * γ * 0 := by rw [PR_mul_PL]
  _ = 0 := by noncomm_ring

/-- The Supersymmetric Hamiltonian $H = \{Q, Q^\dagger\} = Q Q^\dagger + Q^\dagger Q$. -/
def susyH (γ : R) : R :=
  S.superchargeQ γ * S.superchargeQ_dag γ + S.superchargeQ_dag γ * S.superchargeQ γ

theorem susyH_comm_Q (γ : R) : S.susyH γ * S.superchargeQ γ - S.superchargeQ γ * S.susyH γ = 0 := by
  unfold susyH
  have hQ2 : S.superchargeQ γ * S.superchargeQ γ = 0 := by
    have h := S.Q_sq γ; rwa [sq] at h
  calc (S.superchargeQ γ * S.superchargeQ_dag γ + S.superchargeQ_dag γ * S.superchargeQ γ) * S.superchargeQ γ
      - S.superchargeQ γ * (S.superchargeQ γ * S.superchargeQ_dag γ + S.superchargeQ_dag γ * S.superchargeQ γ)
    = S.superchargeQ γ * S.superchargeQ_dag γ * S.superchargeQ γ
      + S.superchargeQ_dag γ * (S.superchargeQ γ * S.superchargeQ γ)
      - (S.superchargeQ γ * S.superchargeQ γ) * S.superchargeQ_dag γ
      - S.superchargeQ γ * S.superchargeQ_dag γ * S.superchargeQ γ := by noncomm_ring
  _ = S.superchargeQ γ * S.superchargeQ_dag γ * S.superchargeQ γ
      + S.superchargeQ_dag γ * 0
      - 0 * S.superchargeQ_dag γ
      - S.superchargeQ γ * S.superchargeQ_dag γ * S.superchargeQ γ := by rw [hQ2]
  _ = 0 := by noncomm_ring

theorem susyH_comm_Q_dag (γ : R) : S.susyH γ * S.superchargeQ_dag γ - S.superchargeQ_dag γ * S.susyH γ = 0 := by
  unfold susyH
  have hQd2 : S.superchargeQ_dag γ * S.superchargeQ_dag γ = 0 := by
    have h := S.Q_dag_sq γ; rwa [sq] at h
  calc (S.superchargeQ γ * S.superchargeQ_dag γ + S.superchargeQ_dag γ * S.superchargeQ γ) * S.superchargeQ_dag γ
      - S.superchargeQ_dag γ * (S.superchargeQ γ * S.superchargeQ_dag γ + S.superchargeQ_dag γ * S.superchargeQ γ)
    = S.superchargeQ γ * (S.superchargeQ_dag γ * S.superchargeQ_dag γ)
      + S.superchargeQ_dag γ * S.superchargeQ γ * S.superchargeQ_dag γ
      - S.superchargeQ_dag γ * S.superchargeQ γ * S.superchargeQ_dag γ
      - (S.superchargeQ_dag γ * S.superchargeQ_dag γ) * S.superchargeQ γ := by noncomm_ring
  _ = S.superchargeQ γ * 0
      + S.superchargeQ_dag γ * S.superchargeQ γ * S.superchargeQ_dag γ
      - S.superchargeQ_dag γ * S.superchargeQ γ * S.superchargeQ_dag γ
      - 0 * S.superchargeQ γ := by rw [hQd2]
  _ = 0 := by noncomm_ring

end ChiralSheetSubstrate

/-- Matrix Kronecker product shorthand. -/
local notation A "⊗ₖ" B => Matrix.kroneckerMap (fun a b => a * b) A B

/-! ### 2. Concrete 2x2 Real Majorana Matrix Carrier -/

section MatrixCarrier

variable {R : Type*} [CommRing R]

/-- Identity 2x2 matrix. -/
def matOne : Matrix (Fin 2) (Fin 2) R := 1

/-- Chiral grading matrix $\Gamma = \sigma_3 = \operatorname{diag}(1, -1)$. -/
def matGamma : Matrix (Fin 2) (Fin 2) R :=
  !![(1 : R), 0; 0, -1]

/-- Sheet-swap paracomplex involution matrix $J = \sigma_1$. -/
def matJ : Matrix (Fin 2) (Fin 2) R :=
  !![0, (1 : R); 1, 0]

/-- Emergent complex structure matrix $K = J \Gamma = - \epsilon$. -/
def matK : Matrix (Fin 2) (Fin 2) R :=
  !![0, (-1 : R); 1, 0]

/-- Left chiral projector $P_L = \operatorname{diag}(1, 0)$. -/
def matPL : Matrix (Fin 2) (Fin 2) R :=
  !![(1 : R), 0; 0, 0]

/-- Right chiral projector $P_R = \operatorname{diag}(0, 1)$. -/
def matPR : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 0, (1 : R)]

/-- Real nilpotent supercharge $Q = E_{01}$. -/
def matQ : Matrix (Fin 2) (Fin 2) R :=
  !![0, (1 : R); 0, 0]

/-- Conjugate real nilpotent supercharge $Q^\dagger = E_{10}$. -/
def matQ_dag : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; (1 : R), 0]

/-! ### Basic Matrix Relations -/

theorem matGamma_sq : matGamma (R := R) * matGamma = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matGamma]

theorem matJ_sq : matJ (R := R) * matJ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matJ]

theorem matJ_matGamma_anticomm :
    matJ (R := R) * matGamma + matGamma * matJ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matJ, matGamma]

theorem matK_eq_mul : matK (R := R) = matJ * matGamma := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matK, matJ, matGamma]

theorem matK_sq : matK (R := R) * matK = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matK]

theorem matPL_sq : matPL (R := R) * matPL = matPL := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matPL]

theorem matPR_sq : matPR (R := R) * matPR = matPR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matPR]

theorem matPL_mul_matPR : matPL (R := R) * matPR = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matPL, matPR]

theorem matPR_mul_matPL : matPR (R := R) * matPL = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matPL, matPR]

theorem matPL_add_matPR : matPL (R := R) + matPR = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matPL, matPR]

theorem matQ_sq : matQ (R := R) * matQ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matQ]

theorem matQ_dag_sq : matQ_dag (R := R) * matQ_dag = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matQ_dag]

/-! ### 3. Real Spinor Bilinears & Dyadic Expansion -/

/-- Scalar bilinear channel: $S(\psi, \phi) = \psi_0 \phi_0 + \psi_1 \phi_1$. -/
def bilinScalar (ψ φ : Fin 2 → R) : R :=
  ψ 0 * φ 0 + ψ 1 * φ 1

/-- Chiral / Pseudoscalar bilinear channel: $P(\psi, \phi) = \psi_0 \phi_0 - \psi_1 \phi_1$. -/
def bilinChiral (ψ φ : Fin 2 → R) : R :=
  ψ 0 * φ 0 - ψ 1 * φ 1

/-- Paracomplex / Vector channel: $V_1(\psi, \phi) = \psi_0 \phi_1 + \psi_1 \phi_0$. -/
def bilinVector1 (ψ φ : Fin 2 → R) : R :=
  ψ 0 * φ 1 + ψ 1 * φ 0

/-- Symplectic / Axial channel: $V_2(\psi, \phi) = \psi_0 \phi_1 - \psi_1 \phi_0$. -/
def bilinVector2 (ψ φ : Fin 2 → R) : R :=
  ψ 0 * φ 1 - ψ 1 * φ 0

/-- Rank-one spinor dyadic outer product $\psi \phi^\top$. -/
def dyad (ψ φ : Fin 2 → R) : Matrix (Fin 2) (Fin 2) R :=
  fun i j => ψ i * φ j

/-- **Real Dyadic Outer Product Theorem**:
$2 \cdot (\psi \phi^\top) = S \cdot \mathbf{1} + P \cdot \Gamma + V_1 \cdot J - V_2 \cdot K$. -/
theorem real_spinor_dyadic_expansion (ψ φ : Fin 2 → R) :
    (2 : R) • dyad ψ φ =
      bilinScalar ψ φ • matOne +
      bilinChiral ψ φ • matGamma +
      bilinVector1 ψ φ • matJ -
      bilinVector2 ψ φ • matK := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dyad, matOne, matGamma, matJ, matK,
          bilinScalar, bilinChiral, bilinVector1, bilinVector2] <;>
    ring

/-! ### 4. Real Chiral Fierz Completeness Identity -/

/-- Matrix Kronecker product over ring multiplication. -/
def kronMul (A B : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R :=
  Matrix.kroneckerMap (fun a b => a * b) A B

/-- The swap operator exchanging tensor factors: $|ab\rangle \mapsto |ba\rangle$. -/
def Swap2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R :=
  fun ⟨a, b⟩ ⟨c, d⟩ => if a = d ∧ b = c then 1 else 0

/-- **Theorem**: Chiral Fierz Decomposition in terms of Left/Right Ideals and Supercharges:
$\mathrm{Swap} = P_L \otimes P_L + P_R \otimes P_R + Q \otimes Q^\dagger + Q^\dagger \otimes Q$. -/
theorem real_chiral_fierz_ideal_identity :
    kronMul (matPL (R := R)) matPL +
    kronMul matPR matPR +
    kronMul matQ matQ_dag +
    kronMul matQ_dag matQ = Swap2 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [Swap2, kronMul, Matrix.kroneckerMap, matPL, matPR, matQ, matQ_dag]

/-- **Theorem**: Real Fierz Expansion in the Chiral/Pauli Basis:
$2 \cdot \mathrm{Swap} = \mathbf{1} \otimes \mathbf{1} + \Gamma \otimes \Gamma + J \otimes J - K \otimes K$. -/
theorem real_chiral_fierz_pauli_identity :
    (2 : R) • (Swap2 (R := R)) =
      kronMul (matOne (R := R)) matOne +
      kronMul matGamma matGamma +
      kronMul matJ matJ -
      kronMul matK matK := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [Swap2, kronMul, Matrix.kroneckerMap, matOne, matGamma, matJ, matK] <;>
    norm_num

/-! ### 5. 5-Graded Lie Superalgebra Derivation -/

/-- Grading derivation: $\mathcal{D}(X) = [\Gamma, X] = \Gamma X - X \Gamma$. -/
def gradingDeriv (X : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  matGamma * X - X * matGamma

/-- **Theorem**: Characteristic 5-Grading Polynomial of the Derivation:
$\mathcal{D}^3(X) = 4 \mathcal{D}(X)$.
The eigenvalues of $\operatorname{ad}(\Gamma)$ are $\{0, \pm 2\}$. -/
theorem grading_derivation_cube (X : Matrix (Fin 2) (Fin 2) R) :
    gradingDeriv (gradingDeriv (gradingDeriv X)) = (4 : R) • gradingDeriv X := by
  have hG2 : matGamma (R := R) * matGamma = 1 := matGamma_sq
  unfold gradingDeriv
  have h_comm :
      matGamma * (matGamma * (matGamma * X - X * matGamma) - (matGamma * X - X * matGamma) * matGamma) -
      (matGamma * (matGamma * X - X * matGamma) - (matGamma * X - X * matGamma) * matGamma) * matGamma
      =
      (matGamma * (matGamma * matGamma)) * X
      - (matGamma * matGamma) * X * matGamma
      - (matGamma * matGamma) * X * matGamma
      - (matGamma * matGamma) * X * matGamma
      + matGamma * X * (matGamma * matGamma)
      + matGamma * X * (matGamma * matGamma)
      + matGamma * X * (matGamma * matGamma)
      - X * (matGamma * (matGamma * matGamma)) := by
    noncomm_ring
  rw [h_comm, hG2]
  have hG_one : matGamma (R := R) * 1 = matGamma := mul_one matGamma
  rw [hG_one]
  have h_simp :
      matGamma * X - 1 * X * matGamma - 1 * X * matGamma - 1 * X * matGamma
      + matGamma * X * 1 + matGamma * X * 1 + matGamma * X * 1 - X * matGamma
      =
      (4 : R) • (matGamma * X - X * matGamma) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [one_mul, mul_one, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply] <;>
      ring
  exact h_simp

/-! ### 6. Supertrace & Real SUSY Vacuum Energy Cancellation -/

/-- Graded supertrace on $2 \times 2$ matrices: $\operatorname{STr}(M) = M_{00} - M_{11}$. -/
def superTrace2 (M : Matrix (Fin 2) (Fin 2) R) : R :=
  M 0 0 - M 1 1

/-- Linear supertrace of sum: $\operatorname{STr}(A + B) = \operatorname{STr}(A) + \operatorname{STr}(B)$. -/
theorem superTrace2_add (A B : Matrix (Fin 2) (Fin 2) R) :
    superTrace2 (A + B) = superTrace2 A + superTrace2 B := by
  simp [superTrace2]; ring

/-- General supersymmetric Hamiltonian with coupling $v \in R$:
$H(v) = \{Q(v), Q^\dagger(v)\} = v^2 \cdot \mathbf{1}$. -/
def matSusyH (v : R) : Matrix (Fin 2) (Fin 2) R :=
  (v • matQ) * (v • matQ_dag) + (v • matQ_dag) * (v • matQ)

theorem matSusyH_eq (v : R) :
    matSusyH (R := R) v = (v ^ 2) • matOne := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matSusyH, matQ, matQ_dag, matOne] <;>
    ring

/-- **Theorem**: Exact Cancellation of Vacuum Energy in the Real SUSY Hamiltonian:
$\operatorname{STr}(H_{\mathrm{susy}}) = 0$. -/
theorem superTrace2_susyH (v : R) :
    superTrace2 (matSusyH (R := R) v) = 0 := by
  rw [matSusyH_eq]
  simp [superTrace2, matOne]

end MatrixCarrier

/-! ### 7. Master Verification Certificate -/

structure RealMajoranaChiralIdealCertificate : Prop where
  abstract_projector_sum : ∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R),
    S.PL + S.PR = 1
  abstract_projector_ortho : ∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R),
    S.PL * S.PR = 0 ∧ S.PR * S.PL = 0
  abstract_sheet_swap : ∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R),
    S.J * S.PL * S.J = S.PR ∧ S.J * S.PR * S.J = S.PL
  abstract_complex_axis : ∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R),
    S.K ^ 2 = -1
  abstract_supercharge_nilpotence : ∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R) (γ : R),
    S.superchargeQ γ ^ 2 = 0 ∧ S.superchargeQ_dag γ ^ 2 = 0
  abstract_susy_conservation : ∀ (R : Type) [Ring R] (S : ChiralSheetSubstrate R) (γ : R),
    S.susyH γ * S.superchargeQ γ - S.superchargeQ γ * S.susyH γ = 0
  concrete_dyadic_expansion : ∀ (R : Type) [CommRing R] (ψ φ : Fin 2 → R),
    (2 : R) • dyad ψ φ =
      bilinScalar ψ φ • matOne + bilinChiral ψ φ • matGamma +
      bilinVector1 ψ φ • matJ - bilinVector2 ψ φ • matK
  concrete_chiral_fierz_ideal : ∀ (R : Type) [CommRing R],
    kronMul (matPL (R := R)) matPL + kronMul matPR matPR +
    kronMul matQ matQ_dag + kronMul matQ_dag matQ = Swap2
  concrete_chiral_fierz_pauli : ∀ (R : Type) [CommRing R],
    (2 : R) • (Swap2 (R := R)) =
      kronMul (matOne (R := R)) matOne + kronMul matGamma matGamma +
      kronMul matJ matJ - kronMul matK matK
  concrete_five_graded_derivation : ∀ (R : Type) [CommRing R] (X : Matrix (Fin 2) (Fin 2) R),
    gradingDeriv (gradingDeriv (gradingDeriv X)) = (4 : R) • gradingDeriv X
  concrete_vacuum_energy_cancellation : ∀ (R : Type) [CommRing R] (v : R),
    superTrace2 (matSusyH (R := R) v) = 0

theorem compile_real_majorana_chiral_ideal :
    RealMajoranaChiralIdealCertificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros R _ S; exact S.PL_add_PR
  · intros R _ S; exact ⟨S.PL_mul_PR, S.PR_mul_PL⟩
  · intros R _ S; exact ⟨S.J_PL_J, S.J_PR_J⟩
  · intros R _ S; exact S.K_sq
  · intros R _ S γ; exact ⟨S.Q_sq γ, S.Q_dag_sq γ⟩
  · intros R _ S γ; exact S.susyH_comm_Q γ
  · intros R _ ψ φ; exact real_spinor_dyadic_expansion ψ φ
  · intros R _; exact real_chiral_fierz_ideal_identity
  · intros R _; exact real_chiral_fierz_pauli_identity
  · intros R _ X; exact grading_derivation_cube X
  · intros R _ v; exact superTrace2_susyH v

end InfoGeometry.SuperGrassmannian.RealMajoranaChiralIdeal
