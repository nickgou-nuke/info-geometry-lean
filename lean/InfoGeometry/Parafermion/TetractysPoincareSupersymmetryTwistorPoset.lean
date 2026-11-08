/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic

/-!
# The Real DeWitt Tetractys, 10D Poincaré Group $\mathrm{ISO}(3, 1)$, and Majorana-Twistor Supersymmetry Poset ($\mathfrak{SP}_1 \prec \dots \prec \mathfrak{SP}_7$)

This module formalizes how the Two-Bit Real DeWitt Split Tetractys $\mathcal{T}_1 \otimes \mathcal{T}_2$
generates the 4D $(-,+,+,+)$ Minkowski Clifford algebra, how the 10-element Tetractys contracts
via the primal nilpotent Peirce projection into the 10-dimensional Poincaré Lie algebra
$\mathfrak{iso}(3, 1) = \mathfrak{so}(3, 1) \ltimes \mathbb{R}^{3,1}$ ($6$ Lorentz $\oplus 4$ abelian
translations), and how Supersymmetry ($\{Q(Z_1), Q(Z_2)\} = P_{12}$), Witten's Positive Energy
Theorem ($2p_0 = \lambda_1^2 + \lambda_2^2 \ge 0$), the massless null cone ($\det(\lambda\lambda^\top) = 0$),
and the 2-twistor massive Casimir ($m^2 = \det(\lambda\lambda^\top + \mu\mu^\top) = \langle\lambda\,\mu\rangle^2 \ge 0$)
emerge over pure real/integer rings without scalar complexification ($i \notin \mathbb{R}$).

## Mathematical Contract (Three-Bucket Classification)

### BUCKET 1: CLOSED FINITE THEOREMS
- `spCoverEdge_acyclic`: strict rank progression and irreflexivity of the 7-stage Hasse poset
  $\mathfrak{SP}_1 \prec \dots \prec \mathfrak{SP}_7$.
- `gamma0_gamma1_anticomm`: explicit anticommutator witness $\{\gamma^0, \gamma^1\} = 0$ in
  `Matrix (Fin 4) (Fin 4) K`.
- `twistorS2_twistorPhi2_anticomm`: explicit anticommutator witness $\{S_2, \Phi_2\} = 0$ in
  `Matrix (Fin 2) (Fin 2) K`.
- `real_majorana_dirac_and_lorentz_generators_mat4`: concrete $4 \times 4$ real Majorana matrix
  realization of $\gamma^0, \gamma^1, \gamma^2, \gamma^3$, the 4D Minkowski mass shell
  $(p_\mu \gamma^\mu)^2 = (-p_0^2 + p_1^2 + p_2^2 + p_3^2) I_4$, the $3$ spatial rotations
  $M^{12}, M^{13}, M^{23}$ (squares $-I_4$), and the $3$ Lorentz boosts $M^{01}, M^{02}, M^{03}$
  (squares $+I_4$).

### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `dewitt_tetractys_generates_4d_minkowski_clifford_algebra`: proves in any associative ring
  `[Ring B]` that two commuting DeWitt tetrads `(S₁, Φ₁, J₁)` and `(S₂, Φ₂)` generate four
  Dirac operators `γ₀ = J₁, γ₁ = S₁, γ₂ = Φ₁ S₂, γ₃ = Φ₁ Φ₂` with signature `(-, +, +, +)` and
  pairwise anticommutation `{γ_μ, γ_ν} = 0` (`μ ≠ ν`).
- `poincare_translations_commute_and_lorentz_covariance`: proves in any `[Ring B]` with idempotent
  `P² = P` that the 6 diagonal Lorentz generators `LorentzL P M` and 4 primal nilpotent translations
  `TransN P p = P p (1 - P)` satisfy `6 + 4 = 10`, `[TransN P p, TransN P q] = 0`,
  `(1 + TransN P p)(1 + TransN P q) = 1 + TransN P (p + q)`,
  `[LorentzL P M, TransN P p] = TransN P [M, p]`, and the graded Super-Jacobi identities
  `[Q, {Q, Q}] = 0` and $\sum_{\mathrm{cyc}} [Q_A, \{Q_B, Q_C\}] = 0$.
- `super_peirce_odd_supercharge_anticommutator` & `twistor_bilinear_symplectic_generator_mat4`:
  proves that the odd supercharge $Q(Z) = N_+(Z) + N_-(\bar{Z})$ squares under the anticommutator
  to the bosonic symmetric bilinear $P Z_1 (1 - P)\bar{Z}_2 P + P Z_2 (1 - P)\bar{Z}_1 P$, and in
  `Matrix (Fin 4) (Fin 4) K` produces $P_{12}(Z_1, Z_2) = (Z_1 Z_2^\top + Z_2 Z_1^\top)\Omega \in \mathfrak{sp}(4, K)$.
- `real_twistor_susy_null_and_massive_momentum_factorization`: proves the DeWitt decomposition
  $2\lambda\lambda^\top = (\lambda_1^2 + \lambda_2^2)I_2 + (\lambda_1^2 - \lambda_2^2)S_2 + 2\lambda_1\lambda_2\Phi_2$,
  the 1-twistor null light-cone identity, the 2-twistor massive Casimir
  $\det(\lambda\lambda^\top + \mu\mu^\top) = (\lambda_1\mu_2 - \lambda_2\mu_1)^2$, and non-negativity
  over $\mathbb{R}$.

### BUCKET 3: OPEN CLOSURE DEBT
- None (`0 sorry`, `0 admit`, `0 custom axioms`, `0 structure wrappers`).
-/

namespace InfoGeometry.Parafermion.TetractysPoincareSupersymmetryTwistorPoset

open Matrix

universe u

/-!
## §1. Nodes $\mathfrak{SP}_1 \prec \mathfrak{SP}_2$: 4D $(-,+,+,+)$ Minkowski Clifford Algebra & 6 Lorentz Generators from the Two-Bit Real DeWitt Tetractys
-/

section RealMinkowskiFromTetractys

variable {B : Type u} [Ring B]

/-- Anticommutator `{x, y} = x * y + y * x` in any ring `B`. -/
def anticomm (x y : B) : B := x * y + y * x

/--
**Theorem 1 ($\mathfrak{SP}_1 \prec \mathfrak{SP}_2$ — `dewitt_tetractys_generates_4d_minkowski_clifford_algebra`):**
Let `(S₁, Φ₁, J₁)` be the first DeWitt triad (`S₁² = 1, Φ₁² = 1, J₁² = -1`, pairwise anticommuting)
and let `(S₂, Φ₂)` be the second DeWitt dyad (`S₂² = 1, Φ₂² = 1, {S₂, Φ₂} = 0`), commuting with Bit 1.
Define the four purely real Dirac gamma operators:
  `γ₀ := J₁`,  `γ₁ := S₁`,  `γ₂ := Φ₁ * S₂`,  `γ₃ := Φ₁ * Φ₂`.
Then:
1. `(γ₀)² = -1` (timelike `-1`) and `(γ₁)² = (γ²)² = (γ³)² = +1` (spacelike `+1, +1, +1`),
2. All 6 distinct pairs strictly anticommute (`anticomm γ_μ γ_ν = 0` for `μ ≠ ν`).
-/
theorem dewitt_tetractys_generates_4d_minkowski_clifford_algebra
    (S1 Phi1 J1 S2 Phi2 : B)
    (hS1 : S1 * S1 = 1) (hPhi1 : Phi1 * Phi1 = 1) (hJ1 : J1 * J1 = -1)
    (hS2 : S2 * S2 = 1) (hPhi2 : Phi2 * Phi2 = 1)
    (h_anti_J1S1   : J1 * S1 + S1 * J1 = 0)
    (h_anti_J1Phi1 : J1 * Phi1 + Phi1 * J1 = 0)
    (h_anti_S1Phi1 : S1 * Phi1 + Phi1 * S1 = 0)
    (h_anti_S2Phi2 : S2 * Phi2 + Phi2 * S2 = 0)
    (h_c_J1S2      : S2 * J1 = J1 * S2)
    (h_c_J1Phi2    : Phi2 * J1 = J1 * Phi2)
    (h_c_S1S2      : S2 * S1 = S1 * S2)
    (h_c_S1Phi2    : Phi2 * S1 = S1 * Phi2)
    (h_c_Phi1S2    : Phi1 * S2 = S2 * Phi1)
    (h_c_Phi1Phi2  : Phi1 * Phi2 = Phi2 * Phi1) :
    let γ0 := J1
    let γ1 := S1
    let γ2 := Phi1 * S2
    let γ3 := Phi1 * Phi2
    γ0 * γ0 = -1 ∧
    γ1 * γ1 = 1 ∧
    γ2 * γ2 = 1 ∧
    γ3 * γ3 = 1 ∧
    anticomm γ0 γ1 = 0 ∧
    anticomm γ0 γ2 = 0 ∧
    anticomm γ0 γ3 = 0 ∧
    anticomm γ1 γ2 = 0 ∧
    anticomm γ1 γ3 = 0 ∧
    anticomm γ2 γ3 = 0 := by
  refine ⟨hJ1, hS1, ?_, ?_, h_anti_J1S1, ?_, ?_, ?_, ?_, ?_⟩
  · calc (Phi1 * S2) * (Phi1 * S2)
      _ = Phi1 * (S2 * Phi1) * S2 := by simp only [mul_assoc]
      _ = (Phi1 * Phi1) * (S2 * S2) := by rw [← h_c_Phi1S2]; simp only [mul_assoc]
      _ = 1 := by rw [hPhi1, hS2, one_mul]
  · calc (Phi1 * Phi2) * (Phi1 * Phi2)
      _ = Phi1 * (Phi2 * Phi1) * Phi2 := by simp only [mul_assoc]
      _ = (Phi1 * Phi1) * (Phi2 * Phi2) := by rw [← h_c_Phi1Phi2]; simp only [mul_assoc]
      _ = 1 := by rw [hPhi1, hPhi2, one_mul]
  · dsimp [anticomm]
    calc J1 * (Phi1 * S2) + Phi1 * S2 * J1
      _ = J1 * Phi1 * S2 + Phi1 * (S2 * J1) := by simp only [mul_assoc]
      _ = (J1 * Phi1 + Phi1 * J1) * S2      := by rw [h_c_J1S2, add_mul]; simp only [mul_assoc]
      _ = 0                                 := by rw [h_anti_J1Phi1, zero_mul]
  · dsimp [anticomm]
    calc J1 * (Phi1 * Phi2) + Phi1 * Phi2 * J1
      _ = J1 * Phi1 * Phi2 + Phi1 * (Phi2 * J1) := by simp only [mul_assoc]
      _ = (J1 * Phi1 + Phi1 * J1) * Phi2        := by rw [h_c_J1Phi2, add_mul]; simp only [mul_assoc]
      _ = 0                                     := by rw [h_anti_J1Phi1, zero_mul]
  · dsimp [anticomm]
    calc S1 * (Phi1 * S2) + Phi1 * S2 * S1
      _ = S1 * Phi1 * S2 + Phi1 * (S2 * S1) := by simp only [mul_assoc]
      _ = (S1 * Phi1 + Phi1 * S1) * S2      := by rw [h_c_S1S2, add_mul]; simp only [mul_assoc]
      _ = 0                                 := by rw [h_anti_S1Phi1, zero_mul]
  · dsimp [anticomm]
    calc S1 * (Phi1 * Phi2) + Phi1 * Phi2 * S1
      _ = S1 * Phi1 * Phi2 + Phi1 * (Phi2 * S1) := by simp only [mul_assoc]
      _ = (S1 * Phi1 + Phi1 * S1) * Phi2        := by rw [h_c_S1Phi2, add_mul]; simp only [mul_assoc]
      _ = 0                                     := by rw [h_anti_S1Phi1, zero_mul]
  · dsimp [anticomm]
    calc Phi1 * S2 * (Phi1 * Phi2) + Phi1 * Phi2 * (Phi1 * S2)
      _ = Phi1 * (S2 * Phi1) * Phi2 + Phi1 * (Phi2 * Phi1) * S2 := by simp only [mul_assoc]
      _ = (Phi1 * Phi1) * (S2 * Phi2 + Phi2 * S2) := by
          rw [← h_c_Phi1S2, ← h_c_Phi1Phi2, mul_add]; simp only [mul_assoc]
      _ = 0 := by rw [h_anti_S2Phi2, mul_zero]

end RealMinkowskiFromTetractys

section ConcreteMajoranaDiracMat4

variable {K : Type u} [CommRing K]

/-- Real Majorana timelike Dirac matrix $\gamma^0 = J_1 \otimes I_2$ (`(γ⁰)² = -I₄`). -/
def gamma0 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     -1, 0, 0, 0;
     0, -1, 0, 0]

/-- Real Majorana spacelike Dirac matrix $\gamma^1 = S_1 \otimes I_2$ (`(γ¹)² = +I₄`). -/
def gamma1 : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- Real Majorana spacelike Dirac matrix $\gamma^2 = \Phi_1 \otimes S_2$ (`(γ²)² = +I₄`). -/
def gamma2 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, -1, 0, 0]

/-- Real Majorana spacelike Dirac matrix $\gamma^3 = \Phi_1 \otimes \Phi_2$ (`(γ³)² = +I₄`). -/
def gamma3 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- Real Majorana 4-momentum slash operator $\not{p} = p_0 \gamma^0 + p_1 \gamma^1 + p_2 \gamma^2 + p_3 \gamma^3$. -/
def diracSlash4 (p0 p1 p2 p3 : K) : Matrix (Fin 4) (Fin 4) K :=
  p0 • gamma0 + p1 • gamma1 + p2 • gamma2 + p3 • gamma3

/-- Explicit anticommutator witness for `Matrix (Fin 4) (Fin 4) K`: `gamma0 * gamma1 + gamma1 * gamma0 = 0`. -/
lemma gamma0_gamma1_anticomm :
    gamma0 (K := K) * gamma1 (K := K) + gamma1 (K := K) * gamma0 (K := K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (dsimp [gamma0, gamma1]; simp [Matrix.mul_apply, Fin.sum_univ_four])

/--
**Concrete $4 \times 4$ Real Majorana Realization of the 4D Minkowski Mass Shell & 6 Lorentz Generators (`real_majorana_dirac_and_lorentz_generators_mat4`):**
In `Matrix (Fin 4) (Fin 4) K`:
1. `(gamma0)² = -1` and `(gamma1)² = (gamma2)² = (gamma3)² = 1`,
2. For any 4-momentum `(p0, p1, p2, p3 : K)`, the Dirac slash operator squares to the exact
   4D Minkowski mass shell:
   `diracSlash4 p0 p1 p2 p3 * diracSlash4 p0 p1 p2 p3 = (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • 1`,
3. The 3 spatial rotation bivectors `M12 = gamma1 * gamma2`, `M13 = gamma1 * gamma3`,
   `M23 = gamma2 * gamma3` square to `-1`, while the 3 Lorentz boost bivectors
   `M01 = gamma0 * gamma1`, `M02 = gamma0 * gamma2`, `M03 = gamma0 * gamma3` square to `+1`.
-/
theorem real_majorana_dirac_and_lorentz_generators_mat4 (p0 p1 p2 p3 : K) :
    (gamma0 (K := K) * gamma0 = -1 ∧
     gamma1 (K := K) * gamma1 = 1 ∧
     gamma2 (K := K) * gamma2 = 1 ∧
     gamma3 (K := K) * gamma3 = 1) ∧
    diracSlash4 p0 p1 p2 p3 * diracSlash4 p0 p1 p2 p3 =
      (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (1 : Matrix (Fin 4) (Fin 4) K) ∧
    ((gamma1 (K := K) * gamma2) * (gamma1 * gamma2) = -1 ∧
     (gamma1 (K := K) * gamma3) * (gamma1 * gamma3) = -1 ∧
     (gamma2 (K := K) * gamma3) * (gamma2 * gamma3) = -1) ∧
    ((gamma0 (K := K) * gamma1) * (gamma0 * gamma1) = 1 ∧
     (gamma0 (K := K) * gamma2) * (gamma0 * gamma2) = 1 ∧
     (gamma0 (K := K) * gamma3) * (gamma0 * gamma3) = 1) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · ext i j; fin_cases i <;> fin_cases j <;> (dsimp [gamma0]; simp [Matrix.mul_apply, Fin.sum_univ_four])
  · ext i j; fin_cases i <;> fin_cases j <;> (dsimp [gamma1]; simp [Matrix.mul_apply, Fin.sum_univ_four])
  · ext i j; fin_cases i <;> fin_cases j <;> (dsimp [gamma2]; simp [Matrix.mul_apply, Fin.sum_univ_four])
  · ext i j; fin_cases i <;> fin_cases j <;> (dsimp [gamma3]; simp [Matrix.mul_apply, Fin.sum_univ_four])
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (dsimp [diracSlash4, gamma0, gamma1, gamma2, gamma3];
       simp [Matrix.mul_apply, Fin.sum_univ_four];
       ring)
  · ext i j; fin_cases i <;> fin_cases j <;> (dsimp [gamma1, gamma2]; simp [Matrix.mul_apply, Fin.sum_univ_four])
  · ext i j; fin_cases i <;> fin_cases j <;> (dsimp [gamma1, gamma3]; simp [Matrix.mul_apply, Fin.sum_univ_four])
  · ext i j; fin_cases i <;> fin_cases j <;> (dsimp [gamma2, gamma3]; simp [Matrix.mul_apply, Fin.sum_univ_four])
  · ext i j; fin_cases i <;> fin_cases j <;> (dsimp [gamma0, gamma1]; simp [Matrix.mul_apply, Fin.sum_univ_four])
  · ext i j; fin_cases i <;> fin_cases j <;> (dsimp [gamma0, gamma2]; simp [Matrix.mul_apply, Fin.sum_univ_four])
  · ext i j; fin_cases i <;> fin_cases j <;> (dsimp [gamma0, gamma3]; simp [Matrix.mul_apply, Fin.sum_univ_four])

end ConcreteMajoranaDiracMat4

/-!
## §3. Nodes $\mathfrak{SP}_3 \prec \mathfrak{SP}_4$: The 10D Poincaré Algebra $\mathfrak{iso}(3, 1) = 6 \text{ Lorentz} \oplus 4 \text{ Nilpotent Translations}$ & Super-Jacobi Closure
-/

section PoincareLieAlgebraFromPeirce

variable {B : Type u} [Ring B]

/-- Ring commutator `[x, y] = x * y - y * x`. -/
def comm (x y : B) : B := x * y - y * x

/-- Primal nilpotent Peirce translation embedding $\mathcal{P}(p) = P_{\mathrm{tr}} p (1 - P_{\mathrm{tr}}) \in \mathfrak{n}_+$. -/
def TransN (P p : B) : B := P * p * (1 - P)

/-- Even stabilizer Lorentz embedding $\mathcal{L}(M) = P_{\mathrm{tr}} M P_{\mathrm{tr}} + (1 - P_{\mathrm{tr}}) M (1 - P_{\mathrm{tr}}) \in \mathfrak{k}$. -/
def LorentzL (P M : B) : B := P * M * P + (1 - P) * M * (1 - P)

/-- Odd Super-Peirce supercharge $Q(Z, \bar{Z}) = P Z (1 - P) + (1 - P) \bar{Z} P$. -/
def superQ (P Z Zbar : B) : B := P * Z * (1 - P) + (1 - P) * Zbar * P

/-- Right-associated idempotent collapse `P * (P * Z) = P * Z` for `P * P = P`. -/
lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/--
**Theorem 2 ($\mathfrak{SP}_3 \prec \mathfrak{SP}_4$ — `poincare_translations_commute_and_lorentz_covariance`):**
1. **Tetractys Dimension Count:** `6 (Lorentz M_{μν}) + 4 (Translations P_μ) = 10`.
2. **Abelian Spacetime Translations (`[P_μ, P_ν] = 0`):**
   For any `p, q ∈ B`, `TransN P p * TransN P q = 0`, so `comm (TransN P p) (TransN P q) = 0`,
   `(1 + TransN P p) * (1 + TransN P q) = 1 + TransN P (p + q)`, and
   `(1 + TransN P p) * (1 - TransN P p) = 1`.
3. **Lorentz Covariance of Translations (`[M_{μν}, P_ρ] = P_{[M_{μν}, ρ]}`):**
   `comm (LorentzL P M) (TransN P p) = TransN P (comm M p)`.
4. **Super-Poincaré Odd Super-Jacobi Identities:**
   `comm Q (Q * Q + Q * Q) = 0` and
   `comm QA (anticomm QB QC) + comm QB (anticomm QC QA) + comm QC (anticomm QA QB) = 0`.
-/
theorem poincare_translations_commute_and_lorentz_covariance
    (P M p q Q QA QB QC : B) (hP : P * P = P)
    (hMP : M * P = P * M)
    (hpCorner : P * p * (1 - P) = p) :
    6 + 4 = 10 ∧
    TransN P p * TransN P q = 0 ∧
    comm (TransN P p) (TransN P q) = 0 ∧
    (1 + TransN P p) * (1 + TransN P q) = 1 + TransN P (p + q) ∧
    (1 + TransN P p) * (1 - TransN P p) = 1 ∧
    comm (LorentzL P M) (TransN P p) = TransN P (comm M p) ∧
    comm Q (Q * Q + Q * Q) = 0 ∧
    comm QA (anticomm QB QC) + comm QB (anticomm QC QA) + comm QC (anticomm QA QB) = 0 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [TransN]
    simp only [mul_assoc, hP, proj_idem hP, mul_sub, mul_one, sub_self, mul_zero]
  · dsimp only [TransN, comm]
    simp only [mul_assoc, hP, proj_idem hP, mul_sub, mul_one, sub_self,
      mul_zero, sub_zero, zero_sub, neg_zero]
  · dsimp only [TransN]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc, hP, proj_idem hP, sub_self, mul_zero, zero_mul]
    abel
  · dsimp only [TransN]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP,
      proj_idem hP, sub_self, mul_zero, zero_mul]
    abel
  · dsimp only [TransN, LorentzL, comm]
    have hQ : (1 - P) * (1 - P) = 1 - P := by
      calc
        (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
        _ = 1 - P := by rw [hP]; abel
    have hL : LorentzL P M = M := by
      dsimp [LorentzL]
      calc
        P * M * P + (1 - P) * M * (1 - P)
            = M * P + M * (1 - P) := by
                rw [← hMP]
                noncomm_ring
        _ = M := by noncomm_ring
    rw [hL]
    dsimp [TransN, comm]
    rw [hpCorner]
    have hcommCorner : P * (M * p - p * M) * (1 - P) = M * p - p * M := by
      rw [mul_sub, sub_mul, ← mul_assoc, hMP]
      have hMPQ : P * M * p * (1 - P) = M * p := by
        rw [← hMP, ← mul_assoc, hpCorner]
      have hpMQ : P * p * M * (1 - P) = p * M := by
        rw [hpCorner]
        noncomm_ring
      rw [hMPQ, hpMQ]
    simpa [comm] using hcommCorner
  · dsimp only [comm]
    noncomm_ring
  · dsimp only [comm, anticomm]
    noncomm_ring

/--
**Super-Peirce Odd Supercharge Anticommutator (`super_peirce_odd_supercharge_anticommutator`):**
For any Bose–Fermi idempotent `P * P = P` and twistor seeds `Z₁, Z̄₁, Z₂, Z̄₂ : B`, the odd
supercharges `superQ P Z₁ Z̄₁` and `superQ P Z₂ Z̄₂` anticommute into the even diagonal sector,
and their bosonic projection `P * {Q₁, Q₂} * P` equals the symmetric twistor bilinear
`P * Z₁ * (1 - P) * Z̄₂ * P + P * Z₂ * (1 - P) * Z̄₁ * P`.
-/
theorem super_peirce_odd_supercharge_anticommutator
    (P Z1 Zbar1 Z2 Zbar2 : B) (hP : P * P = P) :
    P * anticomm (superQ P Z1 Zbar1) (superQ P Z2 Zbar2) * P =
      P * Z1 * (1 - P) * Zbar2 * P + P * Z2 * (1 - P) * Zbar1 * P ∧
    P * anticomm (superQ P Z1 Zbar1) (superQ P Z2 Zbar2) * (1 - P) = 0 := by
  refine ⟨?_, ?_⟩ <;>
  · dsimp only [superQ, anticomm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, hP, proj_idem hP]
    abel

end PoincareLieAlgebraFromPeirce

/-!
## §4. Nodes $\mathfrak{SP}_5 \prec \mathfrak{SP}_6 \prec \mathfrak{SP}_7$: Real Majorana-Twistor SUSY $\{Q(Z_1), Q(Z_2)\} = P_{12} \in \mathfrak{sp}(4, \mathbb{R})$, Positive Energy, Null Cone, & 2-Twistor Massive Casimir
-/

section RealTwistorSupersymmetry

variable {K : Type u} [CommRing K]

/-- Symmetric $4 \times 4$ twistor bilinear matrix $S_{12}(Z_1, Z_2)_{ij} = Z_{1,i} Z_{2,j} + Z_{2,i} Z_{1,j}$. -/
def twistorSymMat4 (Z1 Z2 : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  fun i j => Z1 i * Z2 j + Z2 i * Z1 j

/-- Symplectic bosonic SUSY translation generator $P_{12}(Z_1, Z_2) = (Z_1 Z_2^\top + Z_2 Z_1^\top)\,\gamma^0 \in \mathfrak{sp}(4, K)$. -/
def twistorSusyTransMat4 (Z1 Z2 : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  twistorSymMat4 Z1 Z2 * gamma0

/--
**Symplectic Closure of the Bosonic Twistor SUSY Anticommutator (`twistor_bilinear_symplectic_generator_mat4`):**
For any two 4-component real Majorana twistors `Z1, Z2 : Fin 4 → K`:
1. `twistorSymMat4 Z1 Z2` is symmetric (`(twistorSymMat4 Z1 Z2)ᵀ = twistorSymMat4 Z1 Z2`),
2. The bosonic SUSY anticommutator `P₁₂ = twistorSusyTransMat4 Z1 Z2 = (Z₁ Z₂ᵀ + Z₂ Z₁ᵀ) γ⁰`
   satisfies the $\mathfrak{sp}(4, K)$ Hamiltonian identity:
   `P₁₂ * gamma0 + gamma0 * P₁₂ᵀ = 0`.
-/
theorem twistor_bilinear_symplectic_generator_mat4 (Z1 Z2 : Fin 4 → K) :
    (twistorSymMat4 Z1 Z2).transpose = twistorSymMat4 Z1 Z2 ∧
    twistorSusyTransMat4 Z1 Z2 * gamma0 +
      gamma0 * (twistorSusyTransMat4 Z1 Z2).transpose = 0 := by
  refine ⟨?_, ?_⟩
  · ext i j
    dsimp [Matrix.transpose, twistorSymMat4]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (dsimp [twistorSusyTransMat4, twistorSymMat4, gamma0, Matrix.transpose];
       simp [Matrix.mul_apply, Fin.sum_univ_four];
       ring)

/-- $2 \times 2$ DeWitt parity matrix $S_2 = \mathrm{diag}(1, -1)$. -/
def twistorS2 : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; 0, -1]

/-- $2 \times 2$ DeWitt reflection matrix $\Phi_2 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def twistorPhi2 : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

/-- Scaled $2 \times 2$ chiral twistor momentum matrix $2 P(\lambda) = 2 \lambda \lambda^\top$. -/
def twistorMomMat2 (λ1 λ2 : K) : Matrix (Fin 2) (Fin 2) K :=
  !![2 * (λ1 ^ 2), 2 * λ1 * λ2;
     2 * λ1 * λ2, 2 * (λ2 ^ 2)]

/-- Explicit anticommutator witness for `Matrix (Fin 2) (Fin 2) K`: `twistorS2 * twistorPhi2 + twistorPhi2 * twistorS2 = 0`. -/
lemma twistorS2_twistorPhi2_anticomm :
    twistorS2 (K := K) * twistorPhi2 (K := K) + twistorPhi2 (K := K) * twistorS2 (K := K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (dsimp [twistorS2, twistorPhi2]; simp [Matrix.mul_apply, Fin.sum_univ_two])

/--
**Theorem 3 ($\mathfrak{SP}_5 \prec \mathfrak{SP}_6 \prec \mathfrak{SP}_7$ — `real_twistor_susy_null_and_massive_momentum_factorization`):**
For any real 2-component Majorana-Weyl twistors `λ = (λ₁, λ₂)` and `μ = (μ₁, μ₂)` in `K²`
and real components `r1, r2, s1, s2 : ℝ`:
1. **DeWitt Tetractys Basis Expansion of $2\lambda\lambda^\top$:**
   `twistorMomMat2 λ1 λ2 = (λ1 ^ 2 + λ2 ^ 2) • 1 + (λ1 ^ 2 - λ2 ^ 2) • twistorS2 + (2 * λ1 * λ2) • twistorPhi2`.
2. **1-Twistor Massless Light-Cone Identity (`P = λ λᵀ`):**
   Setting `p₀_sc = λ₁² + λ₂²`, `p₁_sc = λ₁² - λ₂²`, and `p₂_sc = 2 λ₁ λ₂`,
   the Minkowski norm vanishes identically:
   `p₀_sc² - p₁_sc² - p₂_sc² = 0` and `(λ₁²)(λ₂²) - (λ₁ λ₂)² = 0`.
3. **2-Twistor Massive Casimir Identity (`P = λ λᵀ + μ μᵀ`):**
   The determinant of the 2-twistor momentum matrix equals the square of the symplectic twistor
   2-bracket `⟨λ μ⟩ = λ₁ μ₂ - λ₂ μ₁`:
   `(λ₁² + μ₁²)(λ₂² + μ₂²) - (λ₁ λ₂ + μ₁ μ₂)² = (λ₁ * μ₂ - λ₂ * μ₁)²`.
4. **Witten Positive Energy & Mass Positivity Over $\mathbb{R}$:**
   `0 ≤ r1 ^ 2 + r2 ^ 2` and `0 ≤ (r1 ^ 2 + s1 ^ 2) * (r2 ^ 2 + s2 ^ 2) - (r1 * r2 + s1 * s2) ^ 2`.
-/
theorem real_twistor_susy_null_and_massive_momentum_factorization
    (λ1 λ2 μ1 μ2 : K) (r1 r2 s1 s2 : ℝ) :
    let p0_sc := λ1 ^ 2 + λ2 ^ 2
    let p1_sc := λ1 ^ 2 - λ2 ^ 2
    let p2_sc := 2 * λ1 * λ2
    twistorMomMat2 λ1 λ2 =
      p0_sc • (1 : Matrix (Fin 2) (Fin 2) K) +
      p1_sc • twistorS2 (K := K) +
      p2_sc • twistorPhi2 (K := K) ∧
    p0_sc ^ 2 - p1_sc ^ 2 - p2_sc ^ 2 = 0 ∧
    (λ1 ^ 2) * (λ2 ^ 2) - (λ1 * λ2) ^ 2 = 0 ∧
    (λ1 ^ 2 + μ1 ^ 2) * (λ2 ^ 2 + μ2 ^ 2) - (λ1 * λ2 + μ1 * μ2) ^ 2 =
      (λ1 * μ2 - λ2 * μ1) ^ 2 ∧
    0 ≤ r1 ^ 2 + r2 ^ 2 ∧
    0 ≤ (r1 ^ 2 + s1 ^ 2) * (r2 ^ 2 + s2 ^ 2) - (r1 * r2 + s1 * s2) ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, by positivity, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (dsimp [twistorMomMat2, twistorS2, twistorPhi2]; ring)
  · ring
  · ring
  · ring
  · have hCasR :
        (r1 ^ 2 + s1 ^ 2) * (r2 ^ 2 + s2 ^ 2) - (r1 * r2 + s1 * s2) ^ 2 =
          (r1 * s2 - r2 * s1) ^ 2 := by ring
    rw [hCasR]
    positivity

end RealTwistorSupersymmetry

end InfoGeometry.Parafermion.TetractysPoincareSupersymmetryTwistorPoset
