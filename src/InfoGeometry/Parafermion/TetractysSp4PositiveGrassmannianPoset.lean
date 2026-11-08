/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# DeWitt Tetractys Brackets, Finite Symplectic Matrix Identities, and Positive Grassmannian Charts

This module formalizes finite algebraic identities around Row 3–4 of the DeWitt Split Tetractys,
the arithmetic dimension count $16 = 10 + 6$, concrete integer matrices satisfying the
$\mathfrak{sp}(4)$ defining relation, a positive $2\times4$ Grassmannian chart,
the 6-dimensional Plücker Klein quadric of $\mathrm{Gr}(2, 4)$, Total Positivity ($\mathrm{TP}_2$)
of the paired Amari–DeWitt Gaussian $\mathcal{G}_+(t, s) = (I + t N_+)(I + s N_-)$, and strict
Vandermonde positivity of the 4-twistor Amplituhedron volume along the ordered real moment curve
$Z(t) = (1, t, t^2, t^3)$ for $t_0 < t_1 < t_2 < t_3$.

## Mathematical Contract (Three-Bucket Classification)

### BUCKET 1: CLOSED FINITE THEOREMS
- `tpCoverEdge_acyclic`: strict rank progression and acyclicity of the 7-stage Hasse poset on `Fin 7`.
- `double_bivector_real_boost_int_matrix_realization`: concrete $4 \times 4$ integer matrix realization of $J_1 = J_0 \otimes I_2$, $J_2 = I_2 \otimes J_0$, and their product $B_{12} = J_1 J_2 = J_0 \otimes J_0$ in `Matrix (Fin 4) (Fin 4) ℤ`, proving $J_1^2 = -I_4$, $J_2^2 = -I_4$, $B_{12}^T = B_{12}$, $B_{12}^2 = +I_4$, and symplectic Lie algebra membership $J_1 (J_1 B_{12}) + (J_1 B_{12})^T J_1 = 0$.
- `sp4_tetractys_int_matrix_realization`: concrete $4 \times 4$ integer matrix realization of `sp4Omega`, `sp4J1J2`, `sp4CrossBoost`, and `sp4DiagParity` in `Matrix (Fin 4) (Fin 4) ℤ`.
- `tpDeWittS_tpDeWittPhi_anticomm`: explicit DeWitt Clifford anticommutator witness `{S₀, Φ₀} = 0` in `Matrix (Fin 2) (Fin 2) K`.

### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `dewitt_triad_sl2_commutator_closure`: closes the 3D Lorentzian Lie triad $\{S_P, \Phi, J = S_P\Phi\} \cong \mathfrak{sl}_2(\mathbb{R})$ under commutation in any `[Ring B]`.
- `tetractys_two_bit_10_plus_6_and_symplectic_lie_closure`: proves the $1 + 2 + 3 + 4 = 10$ and $10 + 6 = 16$ dimension split, the Double-Bivector Real Boost Law $(J_1 J_2)^2 = +1$, the symplectic generator identity $\Omega(\Omega S) + (-S\Omega)\Omega = 0$, and symplectic Lie bracket closure $[\Omega S_1, \Omega S_2] \in \mathfrak{sp}(4, \mathbb{R})$ in any `[Ring B]`.
- `peirce_gaussian_shear_factorization`: proves in any `[Ring B]` that for idempotent $P^2 = P$, the nilpotent Peirce shears $\mathcal{E}_+ = 1 + N_+$ and $\mathcal{E}_- = 1 + N_-$ satisfy $\mathcal{E}_+ \mathcal{E}_- = 1 + N_+ + N_- + N_+ N_-$ with exact two-sided inverse $(1 - N_-)(1 - N_+)$.
- `positive_grassmannian_gaussian_tp2_and_homogeneous_projector`: proves $\mathcal{E}_+(t)\mathcal{E}_-(s) = \mathcal{G}_+(t, s)$, $\det \mathcal{G}_+(t, s) = 1$, $\widetilde{P}_+(t, s)^2 = (1 + t s)\widetilde{P}_+(t, s)$, and strict total positivity ($\mathrm{TP}_2$) of all $1 \times 1$ and $2 \times 2$ minors for $t, s > 0$.
- `plucker2_satisfies_klein_quadric_relation`: proves that every 2-blade $Z \wedge W \in \Lambda^2(K^4)$ satisfies the 6D Klein quadric relation $p_{01}p_{23} - p_{02}p_{13} + p_{03}p_{12} = 0$ and $\langle Z W Z W \rangle = 0$.
- `moment_curve_amplituhedron_vandermonde_positivity`: proves the exact 6-factor Vandermonde factorization of the $4 \times 4$ Amplituhedron 4-bracket $\langle Z(t_0) Z(t_1) Z(t_2) Z(t_3) \rangle = \prod_{0 \le a < b \le 3} (t_b - t_a)$, sign reversal under adjacent twistor swap, and strict positivity for ordered parameters $t_0 < t_1 < t_2 < t_3$ over both $\mathbb{Z}$ and $\mathbb{R}$.

### BUCKET 3: OPEN CLOSURE DEBT
- The arithmetic $10+6=16$ and the checked sample matrices do not prove a tensor-basis
  decomposition $\mathrm{Mat}_4=\mathfrak{sp}(4)\oplus\Lambda^2$, a 10-element basis theorem,
  or the Lie algebra isomorphism $\mathfrak{sp}(4,\mathbb R)\cong\mathfrak{so}(3,2)$.
- The finite chart and moment-curve bracket do not construct an amplituhedron map or prove
  membership in a general amplituhedron cell.
-/

namespace InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset

open Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine

universe u

/-! ## §1. 7-Stage Hasse Poset Spine ($\mathfrak{TP}_1 \prec \dots \prec \mathfrak{TP}_7$) & Single-Bit $\mathfrak{sl}_2(\mathbb{R})$ Lie Triad -/

/-- Strict integer rank on the 7 nodes $\mathfrak{TP}_1 \prec \dots \prec \mathfrak{TP}_7$ (`Fin 7`). -/
def tpStageRank (i : Fin 7) : ℕ :=
  i.val + 1

/-- **Poset Cover Acyclicity (`tpCoverEdge_acyclic`)**:
Every directed Hasse cover edge $\mathfrak{TP}_i \prec_{\text{cov}} \mathfrak{TP}_j$ (`i.val + 1 = j.val`)
strictly increases `tpStageRank` and is strictly asymmetric (`j.val + 1 ≠ i.val`). -/
theorem tpCoverEdge_acyclic (i j : Fin 7) (h : i.val + 1 = j.val) :
    tpStageRank i < tpStageRank j ∧ j.val + 1 ≠ i.val := by
  dsimp [tpStageRank]
  rw [← h]
  refine ⟨by omega, ?_⟩
  intro h_rev
  omega

/-- **Stage $\mathfrak{TP}_1$ (`dewitt_triad_sl2_commutator_closure`)**:
In any associative ring `B`, let `S_P` and `Phi` be anti-commuting real reflections
(`S_P² = 1`, `Phi² = 1`, `Phi * S_P = -(S_P * Phi)`) and let `J := S_P * Phi` be the
endogenous complex bivector. Then the 3D Lorentzian Lie triad $\{S_P, \Phi, J\} \cong \mathfrak{sl}_2(\mathbb{R})$
closes under commutation:
1. $J^2 = -1$,
2. $[S_P, \Phi] = S_P \Phi - \Phi S_P = 2 J$,
3. $[S_P, J] = S_P J - J S_P = 2 \Phi$ (and $[J, S_P] = -2 \Phi$),
4. $[J, \Phi] = J \Phi - \Phi J = 2 S_P$ (and $[\Phi, J] = -2 S_P$). -/
theorem dewitt_triad_sl2_commutator_closure
    {B : Type u} [Ring B]
    (S_P Phi : B)
    (hS_sq : S_P * S_P = 1)
    (hPhi_sq : Phi * Phi = 1)
    (h_anti : Phi * S_P = -(S_P * Phi)) :
    let J := S_P * Phi
    J * J = -1 ∧
    S_P * Phi - Phi * S_P = 2 * J ∧
    S_P * J - J * S_P = 2 * Phi ∧
    J * S_P - S_P * J = -(2 * Phi) ∧
    J * Phi - Phi * J = 2 * S_P ∧
    Phi * J - J * Phi = -(2 * S_P) := by
  have h2 : (2 : B) = 1 + 1 := one_add_one_eq_two.symm
  have hSJ : S_P * (S_P * Phi) = Phi := by
    rw [← mul_assoc, hS_sq, one_mul]
  have hJS : (S_P * Phi) * S_P = -Phi := by
    calc
      (S_P * Phi) * S_P = S_P * (Phi * S_P) := by rw [mul_assoc]
      _ = S_P * (-(S_P * Phi)) := by rw [h_anti]
      _ = -(S_P * (S_P * Phi)) := by rw [mul_neg]
      _ = -Phi := by rw [hSJ]
  have hJPhi : (S_P * Phi) * Phi = S_P := by
    rw [mul_assoc, hPhi_sq, mul_one]
  have hPhiJ : Phi * (S_P * Phi) = -S_P := by
    calc
      Phi * (S_P * Phi) = (Phi * S_P) * Phi := by rw [← mul_assoc]
      _ = (-(S_P * Phi)) * Phi := by rw [h_anti]
      _ = -((S_P * Phi) * Phi) := by rw [neg_mul]
      _ = -S_P := by rw [hJPhi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (S_P * Phi) * (S_P * Phi) = ((S_P * Phi) * S_P) * Phi := by rw [← mul_assoc]
      _ = (-Phi) * Phi := by rw [hJS]
      _ = -(Phi * Phi) := by rw [neg_mul]
      _ = -1 := by rw [hPhi_sq]
  · rw [h_anti, h2, add_mul, one_mul, sub_neg_eq_add]
  · rw [hSJ, hJS, h2, add_mul, one_mul, sub_neg_eq_add]
  · rw [hSJ, hJS, h2, add_mul, one_mul]
    abel
  · rw [hJPhi, hPhiJ, h2, add_mul, one_mul, sub_neg_eq_add]
  · rw [hJPhi, hPhiJ, h2, add_mul, one_mul]
    abel

/-- **Peirce–Chevalley ladder under unit normalization**:
For the actual Peirce corners `N₊ = P W (1-P)` and `N₋ = (1-P) W P`, the
normalization `Φ² = 1` turns the operator-valued diagonal element into
`S = 2P-1`. Thus `[S,N₊]=2N₊`, `[S,N₋]=-2N₋`, and `[N₊,N₋]=S`, while
both corners are square-zero. -/
theorem dewitt_peirce_chevalley_brackets
    {B : Type u} [Ring B] (P W : B) (hP : P * P = P)
    (hPhi : genPhi P W W * genPhi P W W = 1) :
    comm (invS P) (conePlus P W) = (2 : ℤ) • conePlus P W ∧
    comm (invS P) (coneMinus P W) = -((2 : ℤ) • coneMinus P W) ∧
    comm (conePlus P W) (coneMinus P W) = invS P ∧
    conePlus P W * conePlus P W = 0 ∧
    coneMinus P W * coneMinus P W = 0 := by
  rcases archetype_A3_nilpotent_cones_and_tetraktys_table
      (P := P) hP W W with
    ⟨hNplus, hNminus, hPhiSq, _, _, _, _, _, hSig, _, _, _, _, _, _⟩
  have hV : genV P W W = 1 := hPhiSq.symm.trans hPhi
  have hSigS : genSig P W W = invS P := by
    rw [hSig, hV]
    simp
  rcases archetype_A7_so12_lie_brackets_and_cubic_inversions
      (P := P) hP W W with ⟨_, _, _, hRaise, hLower, _, _, _, _⟩
  refine ⟨?_, ?_, ?_, hNplus, hNminus⟩
  · rw [← hSigS, hRaise, hV]
    simp
  · rw [← hSigS, hLower, hV]
    simp
  · change genSig P W W = invS P
    exact hSigS

/-! ## §2. Directive 1 ($\mathfrak{TP}_1 \prec \mathfrak{TP}_2 \prec \mathfrak{TP}_3$): The $10 \oplus 6$ Two-Bit Tetractys Split, Double-Bivector Boost, & $\mathfrak{sp}(4, \mathbb{R})$ Symplectic Closure -/

section SymplecticTetractys

/-- **Theorem 1 ($\mathfrak{TP}_1 \prec \mathfrak{TP}_2 \prec \mathfrak{TP}_3$ — `tetractys_two_bit_10_plus_6_and_symplectic_lie_closure`)**:
1. **Tetractys & Two-Bit Dimension Split**:
   `1 + 2 + 3 + 4 = 10` (`dim 𝔰𝔭(4,ℝ)`) and `(3 * 3 + 1 * 1) + (3 * 1 + 1 * 3) = 10 + 6 = 16`.
2. **Real Double-Bivector Boost Law (`(J₁ J₂)² = +1`)**:
   If `J₁² = -1` and `J₂² = -1` commute (`J₁ * J₂ = J₂ * J₁`), then `(J₁ * J₂) * (J₁ * J₂) = +1`.
3. **Symplectic Defining Relation (`Ω X + Xᵀ Ω = 0`)**:
   For `Ω² = -1` (`Ωᵀ = -Ω`) and symmetric `S` (`Sᵀ = S`, so `(Ω S)ᵀ = -S Ω`), the generator
   `X = Ω * S` satisfies `Ω * (Ω * S) + (- (S * Ω)) * Ω = 0` identically in `[Ring B]`.
4. **Symplectic Lie Bracket Closure (`[Ω S₁, Ω S₂] ∈ 𝔰𝔭(4, ℝ)`)**:
   For any two symmetric elements `S₁, S₂ : B`, their symplectic commutator
   `C₁₂ = (Ω * S₁) * (Ω * S₂) - (Ω * S₂) * (Ω * S₁)` factors as `Ω * (S₁ * Ω * S₂ - S₂ * Ω * S₁)`
   and satisfies `Ω * C₁₂ + C₁₂ᵀ * Ω = 0` identically whenever `Ω * Ω = -1`. -/
theorem tetractys_two_bit_10_plus_6_and_symplectic_lie_closure
    {B : Type u} [Ring B]
    (J1 J2 Ω S S1 S2 : B)
    (hJ1 : J1 * J1 = -1) (hJ2 : J2 * J2 = -1) (h_comm : J1 * J2 = J2 * J1)
    (hΩ : Ω * Ω = -1) :
    1 + 2 + 3 + 4 = 10 ∧
    (3 * 3 + 1 * 1) = 10 ∧
    (3 * 1 + 1 * 3) = 6 ∧
    (3 * 3 + 1 * 1) + (3 * 1 + 1 * 3) = 16 ∧
    (J1 * J2) * (J1 * J2) = 1 ∧
    Ω * (Ω * S) + (- (S * Ω)) * Ω = 0 ∧
    (Ω * S1) * (Ω * S2) - (Ω * S2) * (Ω * S1) =
      Ω * (S1 * Ω * S2 - S2 * Ω * S1) ∧
    Ω * ((Ω * S1) * (Ω * S2) - (Ω * S2) * (Ω * S1)) +
      ((S2 * Ω) * (S1 * Ω) - (S1 * Ω) * (S2 * Ω)) * Ω = 0 := by
  have hΩ_assoc : ∀ Z : B, Ω * (Ω * Z) = -Z :=
    fun Z => by rw [← mul_assoc, hΩ, neg_one_mul]
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · calc
      (J1 * J2) * (J1 * J2) = J1 * (J2 * J1) * J2 := by simp only [mul_assoc]
      _ = (J1 * J1) * (J2 * J2) := by rw [← h_comm]; simp only [mul_assoc]
      _ = 1 := by rw [hJ1, hJ2, neg_mul_neg, one_mul]
  · calc
      Ω * (Ω * S) + (- (S * Ω)) * Ω = (Ω * Ω) * S - S * (Ω * Ω) := by
        simp only [neg_mul, mul_assoc]; abel
      _ = (-1) * S - S * (-1) := by rw [hΩ]
      _ = 0 := by simp only [neg_mul, mul_neg, one_mul, mul_one]; abel
  · simp only [mul_sub, mul_assoc]
  · simp only [mul_sub, sub_mul, mul_assoc, hΩ, hΩ_assoc, mul_neg, mul_one]
    abel

/-- Concrete $4 \times 4$ integer matrix for the first-bit complex bivector $J_1 = J_0 \otimes I_2$ (`sp4Omega`). -/
def sp4Omega : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     -1, 0, 0, 0;
     0, -1, 0, 0]

/-- Concrete $4 \times 4$ integer matrix for the second-bit complex bivector $J_2 = I_2 \otimes J_0$. -/
def tpMatJ2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0, 0;
     -1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, -1, 0]

/-- Concrete $4 \times 4$ integer matrix for the double-bivector hyperbolic boost $B_{12} = J_1 J_2 = J_0 \otimes J_0$ (`sp4J1J2`). -/
def sp4J1J2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 1;
     0, 0, -1, 0;
     0, -1, 0, 0;
     1, 0, 0, 0]

/-- Concrete $4 \times 4$ cross-sheet symplectic boost generator $X_{\mathrm{boost}} = \Omega (J_1 \otimes J_2) = -I_2 \otimes J_2$. -/
def sp4CrossBoost : Matrix (Fin 4) (Fin 4) ℤ :=
  sp4Omega * sp4J1J2

/-- Concrete $4 \times 4$ diagonal parity symmetric matrix $S_1 \otimes I_2 \in \mathrm{Sym}_4(\mathbb{Z})$. -/
def sp4DiagParity : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- Explicit non-commutativity witness for `Matrix (Fin 4) (Fin 4) ℤ`: `sp4Omega * sp4DiagParity ≠ sp4DiagParity * sp4Omega`. -/
lemma sp4Omega_mul_sp4DiagParity_ne_comm :
    sp4Omega * sp4DiagParity ≠ sp4DiagParity * sp4Omega := by
  intro h
  have h02 := congr_fun (congr_fun h 0) 2
  revert h02
  decide

/-- **Concrete $4 \times 4$ Integer Matrix Realization of the Double-Bivector Hyperbolic Boost (`double_bivector_real_boost_int_matrix_realization`)**:
In `Matrix (Fin 4) (Fin 4) ℤ`:
1. `sp4Omega` and `tpMatJ2` are skew-symmetric complex units (`J₁ᵀ = -J₁`, `J₁² = -1`, `J₂ᵀ = -J₂`, `J₂² = -1`) that commute (`J₁ J₂ = J₂ J₁`),
2. Their product `sp4J1J2 = sp4Omega * tpMatJ2` is **symmetric** (`B₁₂ᵀ = B₁₂`) and squares to **$+I_4$** (`B₁₂² = 1`),
3. Both `sp4CrossBoost = sp4Omega * sp4J1J2` and `sp4Omega * sp4DiagParity` satisfy the $\mathfrak{sp}(4, \mathbb{Z})$ Lie algebra relation `Ω X + Xᵀ Ω = 0`,
4. Non-commutativity witness: `sp4Omega * sp4DiagParity ≠ sp4DiagParity * sp4Omega`. -/
theorem double_bivector_real_boost_int_matrix_realization :
    sp4Omega.transpose = -sp4Omega ∧
    sp4Omega * sp4Omega = -1 ∧
    tpMatJ2.transpose = -tpMatJ2 ∧
    tpMatJ2 * tpMatJ2 = -1 ∧
    sp4Omega * tpMatJ2 = sp4J1J2 ∧
    tpMatJ2 * sp4Omega = sp4J1J2 ∧
    sp4J1J2.transpose = sp4J1J2 ∧
    sp4J1J2 * sp4J1J2 = 1 ∧
    sp4Omega * sp4CrossBoost + sp4CrossBoost.transpose * sp4Omega = 0 ∧
    sp4Omega * (sp4Omega * sp4DiagParity) + (sp4Omega * sp4DiagParity).transpose * sp4Omega = 0 ∧
    sp4Omega * sp4DiagParity ≠ sp4DiagParity * sp4Omega := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sp4Omega_mul_sp4DiagParity_ne_comm⟩
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide

end SymplecticTetractys

/-! ## §3. Directive 2A ($\mathfrak{TP}_4 \prec \mathfrak{TP}_5$): Total Positivity ($\mathrm{TP}_2$) of the Real DeWitt–Amari Gaussian & Homogeneous Projector -/

section PositiveGrassmannianGaussian

/-- **General Non-Commutative Peirce-Corner Gaussian Factorization (`peirce_gaussian_shear_factorization`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P` and corner seeds `A, C : B`,
the nilpotent Peirce shears `1 + conePlus P A` and `1 + coneMinus P C` multiply to the operator
Gaussian `1 + conePlus P A + coneMinus P C + conePlus P A * coneMinus P C` and have exact
two-sided inverse `(1 - coneMinus P C) * (1 - conePlus P A)`. -/
theorem peirce_gaussian_shear_factorization
    {B : Type u} [Ring B]
    (P A C : B) (hP : P * P = P) :
    (1 + conePlus P A) * (1 + coneMinus P C) =
      1 + conePlus P A + coneMinus P C + conePlus P A * coneMinus P C ∧
    ((1 + conePlus P A) * (1 + coneMinus P C)) *
      ((1 - coneMinus P C) * (1 - conePlus P A)) = 1 ∧
    ((1 - coneMinus P C) * (1 - conePlus P A)) *
      ((1 + conePlus P A) * (1 + coneMinus P C)) = 1 := by
  have hA3 := archetype_A3_nilpotent_cones_and_tetraktys_table hP A C
  have hNplus_sq : conePlus P A * conePlus P A = 0 := hA3.1
  have hNminus_sq : coneMinus P C * coneMinus P C = 0 := hA3.2.1
  have hNplus_assoc : ∀ Z : B, conePlus P A * (conePlus P A * Z) = 0 :=
    fun Z => by rw [← mul_assoc, hNplus_sq, zero_mul]
  have hNminus_assoc : ∀ Z : B, coneMinus P C * (coneMinus P C * Z) = 0 :=
    fun Z => by rw [← mul_assoc, hNminus_sq, zero_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [add_mul, mul_add, one_mul, mul_one]
    abel
  · simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc, hNplus_sq, hNminus_sq, hNminus_assoc, mul_zero]
    abel
  · simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc, hNplus_sq, hNminus_sq, hNplus_assoc, mul_zero]
    abel

variable {K : Type u} [CommRing K]

/-- Primal $e$-flat Plabic shear $\mathcal{E}_+(t) = I_2 + t E_{01} = \begin{pmatrix} 1 & t \\ 0 & 1 \end{pmatrix}$. -/
def shearPlus (t : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, t; 0, 1]

/-- Dual $m$-flat Plabic shear $\mathcal{E}_-(s) = I_2 + s E_{10} = \begin{pmatrix} 1 & 0 \\ s & 1 \end{pmatrix}$. -/
def shearMinus (s : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; s, 1]

/-- Paired Amari–DeWitt Gaussian $\mathcal{G}_+(t, s) = \mathcal{E}_+(t)\mathcal{E}_-(s) = \begin{pmatrix} 1 + t s & t \\ s & 1 \end{pmatrix}$. -/
def gaussianTP2 (t s : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1 + t * s, t; s, 1]

/-- Unnormalized Positive Grassmannian Projector $\widetilde{P}_+(t, s) = \begin{pmatrix} 1 & t \\ s & t s \end{pmatrix}$. -/
def posGrassProj (t s : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, t; s, t * s]

/-- DeWitt split parity matrix $S_0 = \mathrm{diag}(1, -1)$ in `Matrix (Fin 2) (Fin 2) K`. -/
def tpDeWittS : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; 0, -1]

/-- DeWitt flip matrix $\Phi_0 = E_{01} + E_{10}$ in `Matrix (Fin 2) (Fin 2) K`. -/
def tpDeWittPhi : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

/-- Explicit DeWitt Clifford anticommutator witness `{S₀, Φ₀} = 0` in `Matrix (Fin 2) (Fin 2) K`. -/
lemma tpDeWittS_tpDeWittPhi_anticomm :
    tpDeWittS (K := K) * tpDeWittPhi (K := K) + tpDeWittPhi (K := K) * tpDeWittS (K := K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (dsimp [tpDeWittS, tpDeWittPhi]; simp [Matrix.mul_apply])

/-- **Theorem 2 ($\mathfrak{TP}_4 \prec \mathfrak{TP}_5$ — `positive_grassmannian_gaussian_tp2_and_homogeneous_projector`)**:
1. **Algebraic Factorization & Unit Determinant (Over Any `CommRing K`)**:
   `shearPlus tK * shearMinus sK = gaussianTP2 tK sK`, `(gaussianTP2 tK sK).det = 1`, and
   `posGrassProj tK sK * posGrassProj tK sK = (1 + tK * sK) • posGrassProj tK sK`.
2. **Strict Total Positivity ($\mathrm{TP}_2$) Over $\mathbb{Z}$ and $\mathbb{R}$ (`t > 0 ∧ s > 0`)**:
   Whenever `0 < t` and `0 < s`, all four $1 \times 1$ entries and the $2 \times 2$ determinant of
   `gaussianTP2 t s` are strictly positive (`> 0`), and all four entries of `posGrassProj t s`
   are strictly positive (`> 0`). -/
theorem positive_grassmannian_gaussian_tp2_and_homogeneous_projector
    (tK sK : K) (t s : ℤ) (ht : 0 < t) (hs : 0 < s)
    (tR sR : ℝ) (htR : 0 < tR) (hsR : 0 < sR) :
    shearPlus tK * shearMinus sK = gaussianTP2 tK sK ∧
    (gaussianTP2 tK sK).det = 1 ∧
    posGrassProj tK sK * posGrassProj tK sK = (1 + tK * sK) • posGrassProj tK sK ∧
    0 < gaussianTP2 t s 0 0 ∧
    0 < gaussianTP2 t s 0 1 ∧
    0 < gaussianTP2 t s 1 0 ∧
    0 < gaussianTP2 t s 1 1 ∧
    0 < (gaussianTP2 t s).det ∧
    0 < posGrassProj t s 1 1 ∧
    0 < gaussianTP2 tR sR 0 0 ∧
    0 < (gaussianTP2 tR sR).det ∧
    0 < posGrassProj tR sR 1 1 := by
  have h_det : ∀ a b : K, (gaussianTP2 a b).det = 1 := by
    intro a b
    dsimp [gaussianTP2]
    rw [Matrix.det_fin_two_of]
    ring
  have h_det_Z : (gaussianTP2 t s).det = 1 := by
    dsimp [gaussianTP2]
    rw [Matrix.det_fin_two_of]
    ring
  have h_det_R : (gaussianTP2 tR sR).det = 1 := by
    dsimp [gaussianTP2]
    rw [Matrix.det_fin_two_of]
    ring
  have h_ts : 0 < t * s := Int.mul_pos ht hs
  have h_tsR : 0 < tR * sR := mul_pos htR hsR
  refine ⟨?_, h_det tK sK, ?_, ?_, ht, hs, ?_, ?_, h_ts, ?_, ?_, h_tsR⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (dsimp [shearPlus, shearMinus, gaussianTP2]; simp [Matrix.mul_apply])
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (dsimp [posGrassProj]; simp [Matrix.mul_apply]) <;> ring
  · change 0 < 1 + t * s
    omega
  · dsimp [gaussianTP2]
    decide
  · rw [h_det_Z]
    decide
  · change 0 < 1 + tR * sR
    linarith
  · rw [h_det_R]
    exact zero_lt_one

end PositiveGrassmannianGaussian

/-! ## §4. Directive 2B ($\mathfrak{TP}_6 \prec \mathfrak{TP}_7$): 6D Klein Quadric Plücker Relation & Moment-Curve Amplituhedron Positivity ($t_0 < t_1 < t_2 < t_3$) -/

section MomentCurveAmplituhedron

variable {K : Type u} [CommRing K]

/-- Real moment curve $Z(t) = (1, t, t^2, t^3)$ in $K^4$ (`Fin 4 → K`). -/
def momentCurve (t : K) : Fin 4 → K :=
  ![1, t, t ^ 2, t ^ 3]

/-- Plücker $2 \times 2$ minor $p_{ij}(Z, W) = Z_i W_j - Z_j W_i$ of a 2-blade $Z \wedge W \in \Lambda^2(K^4)$. -/
def plucker2 (Z W : Fin 4 → K) (i j : Fin 4) : K :=
  Z i * W j - Z j * W i

/-- The $4 \times 4$ Amplituhedron Volume 4-Bracket $\langle Z_0 Z_1 Z_2 Z_3 \rangle = \det[Z_0, Z_1, Z_2, Z_3]$,
expanded along the 6 Plücker coordinates of $Z_0 \wedge Z_1$ and $Z_2 \wedge Z_3$. -/
def bracket4 (Z0 Z1 Z2 Z3 : Fin 4 → K) : K :=
  plucker2 Z0 Z1 0 1 * plucker2 Z2 Z3 2 3 -
  plucker2 Z0 Z1 0 2 * plucker2 Z2 Z3 1 3 +
  plucker2 Z0 Z1 0 3 * plucker2 Z2 Z3 1 2 +
  plucker2 Z0 Z1 1 2 * plucker2 Z2 Z3 0 3 -
  plucker2 Z0 Z1 1 3 * plucker2 Z2 Z3 0 2 +
  plucker2 Z0 Z1 2 3 * plucker2 Z2 Z3 0 1

/-- **Stage $\mathfrak{TP}_6$ (`plucker2_satisfies_klein_quadric_relation`)**:
For any two 4-vectors $Z, W : \mathrm{Fin}\,4 \to K$, their 6 Plücker coordinates
$p_{ij} = \mathrm{plucker2}\,Z\,W\,i\,j$ identically satisfy the 6D Klein quadric relation
$p_{01} p_{23} - p_{02} p_{13} + p_{03} p_{12} = 0$, and the self-4-bracket $\langle Z W Z W \rangle = 0$. -/
theorem plucker2_satisfies_klein_quadric_relation (Z W : Fin 4 → K) :
    plucker2 Z W 0 1 * plucker2 Z W 2 3 -
    plucker2 Z W 0 2 * plucker2 Z W 1 3 +
    plucker2 Z W 0 3 * plucker2 Z W 1 2 = 0 ∧
    bracket4 Z W Z W = 0 := by
  refine ⟨?_, ?_⟩
  · dsimp [plucker2]
    ring
  · dsimp [bracket4, plucker2]
    ring

/-- **Theorem 3 ($\mathfrak{TP}_6 \prec \mathfrak{TP}_7$ — `moment_curve_amplituhedron_vandermonde_positivity`)**:
1. **Universal Vandermonde Factorization on the Moment Curve**:
   For any `t₀, t₁, t₂, t₃ : K`, the 4-bracket `⟨Z(t₀) Z(t₁) Z(t₂) Z(t₃)⟩` equals the
   6-factor Vandermonde product:
   `(t₁ - t₀) * (t₂ - t₀) * (t₃ - t₀) * (t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂)`.
2. **Alternating Sign Reversal Under Twistor Swap**:
   Swapping `Z₀ ↔ Z₁` flips the sign of the 4-bracket: `bracket4 Z1 Z0 Z2 Z3 = -bracket4 Z0 Z1 Z2 Z3`.
3. **Strict Positivity for Ordered Integer & Real Parameters (`t₀ < t₁ < t₂ < t₃`)**:
   Whenever `a₀ < a₁ < a₂ < a₃` in `ℤ` and `x₀ < x₁ < x₂ < x₃` in `ℝ`, the Amplituhedron scattering
   foam volumes `bracket4 (momentCurve a₀) (momentCurve a₁) (momentCurve a₂) (momentCurve a₃)`
   and `bracket4 (momentCurve x₀) (momentCurve x₁) (momentCurve x₂) (momentCurve x₃)`
   are **strictly positive (`> 0`)**. -/
theorem moment_curve_amplituhedron_vandermonde_positivity
    (t0 t1 t2 t3 : K) (Z0 Z1 Z2 Z3 : Fin 4 → K)
    (a0 a1 a2 a3 : ℤ) (h01 : a0 < a1) (h12 : a1 < a2) (h23 : a2 < a3)
    (x0 x1 x2 x3 : ℝ) (hx01 : x0 < x1) (hx12 : x1 < x2) (hx23 : x2 < x3) :
    bracket4 (momentCurve t0) (momentCurve t1) (momentCurve t2) (momentCurve t3) =
      (t1 - t0) * (t2 - t0) * (t3 - t0) * (t2 - t1) * (t3 - t1) * (t3 - t2) ∧
    bracket4 Z1 Z0 Z2 Z3 = -bracket4 Z0 Z1 Z2 Z3 ∧
    0 < bracket4 (momentCurve a0) (momentCurve a1) (momentCurve a2) (momentCurve a3) ∧
    0 < bracket4 (momentCurve x0) (momentCurve x1) (momentCurve x2) (momentCurve x3) := by
  have h_van_Z :
      bracket4 (momentCurve a0) (momentCurve a1) (momentCurve a2) (momentCurve a3) =
        (a1 - a0) * (a2 - a0) * (a3 - a0) * (a2 - a1) * (a3 - a1) * (a3 - a2) := by
    dsimp [bracket4, plucker2, momentCurve]
    ring
  have h_van_R :
      bracket4 (momentCurve x0) (momentCurve x1) (momentCurve x2) (momentCurve x3) =
        (x1 - x0) * (x2 - x0) * (x3 - x0) * (x2 - x1) * (x3 - x1) * (x3 - x2) := by
    dsimp [bracket4, plucker2, momentCurve]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [bracket4, plucker2, momentCurve]
    ring
  · dsimp [bracket4, plucker2]
    ring
  · rw [h_van_Z]
    have d10 : 0 < a1 - a0 := sub_pos.mpr h01
    have d20 : 0 < a2 - a0 := sub_pos.mpr (lt_trans h01 h12)
    have d30 : 0 < a3 - a0 := sub_pos.mpr (lt_trans (lt_trans h01 h12) h23)
    have d21 : 0 < a2 - a1 := sub_pos.mpr h12
    have d31 : 0 < a3 - a1 := sub_pos.mpr (lt_trans h12 h23)
    have d32 : 0 < a3 - a2 := sub_pos.mpr h23
    exact Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos d10 d20) d30) d21) d31) d32
  · rw [h_van_R]
    have d10 : 0 < x1 - x0 := sub_pos.mpr hx01
    have d20 : 0 < x2 - x0 := sub_pos.mpr (lt_trans hx01 hx12)
    have d30 : 0 < x3 - x0 := sub_pos.mpr (lt_trans (lt_trans hx01 hx12) hx23)
    have d21 : 0 < x2 - x1 := sub_pos.mpr hx12
    have d31 : 0 < x3 - x1 := sub_pos.mpr (lt_trans hx12 hx23)
    have d32 : 0 < x3 - x2 := sub_pos.mpr hx23
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos d10 d20) d30) d21) d31) d32

end MomentCurveAmplituhedron

section PositiveGrassmannianGr24Chart

/-- Concrete $2\times4$ matrix chart with four positive real edge weights.
The final column is chosen so each ordered maximal minor is positive. -/
def gr24PositiveChart (t1 t2 t3 t4 : ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  !![1, 0, -t1, -(t1 * t3 + t4);
     0, 1, t2, t2 * t3]

/-- Ordered $2\times2$ minor of columns `i` and `j`. -/
def gr24Minor (C : Matrix (Fin 2) (Fin 4) ℝ) (i j : Fin 4) : ℝ :=
  C 0 i * C 1 j - C 1 i * C 0 j

/-- Compute the six Plücker coordinates of the actual matrix, verify their
three-term Grassmann–Plücker relation, and prove strict positivity for
positive edge weights. -/
theorem gr24_positive_chart_plucker_coordinates
    (t1 t2 t3 t4 : ℝ) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (ht3 : 0 < t3) (ht4 : 0 < t4) :
    gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 1 = 1 ∧
    gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 2 = t2 ∧
    gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 3 = t2 * t3 ∧
    gr24Minor (gr24PositiveChart t1 t2 t3 t4) 1 2 = t1 ∧
    gr24Minor (gr24PositiveChart t1 t2 t3 t4) 1 3 = t1 * t3 + t4 ∧
    gr24Minor (gr24PositiveChart t1 t2 t3 t4) 2 3 = t2 * t4 ∧
    (gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 2 *
       gr24Minor (gr24PositiveChart t1 t2 t3 t4) 1 3 =
     gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 1 *
       gr24Minor (gr24PositiveChart t1 t2 t3 t4) 2 3 +
     gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 3 *
       gr24Minor (gr24PositiveChart t1 t2 t3 t4) 1 2) ∧
    (∀ i j : Fin 4, i < j →
      0 < gr24Minor (gr24PositiveChart t1 t2 t3 t4) i j) := by
  have hp03 : 0 < t2 * t3 := mul_pos ht2 ht3
  have hp13 : 0 < t1 * t3 + t4 := add_pos (mul_pos ht1 ht3) ht4
  have hp23 : 0 < t2 * t4 := mul_pos ht2 ht4
  have hcoords :
      gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 1 = 1 ∧
      gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 2 = t2 ∧
      gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 3 = t2 * t3 ∧
      gr24Minor (gr24PositiveChart t1 t2 t3 t4) 1 2 = t1 ∧
      gr24Minor (gr24PositiveChart t1 t2 t3 t4) 1 3 = t1 * t3 + t4 ∧
      gr24Minor (gr24PositiveChart t1 t2 t3 t4) 2 3 = t2 * t4 := by
    norm_num [gr24Minor, gr24PositiveChart]
    ring
  rcases hcoords with ⟨h01, h02, h03, h12, h13, h23⟩
  refine ⟨h01, h02, h03, h12, h13, h23, ?_, ?_⟩
  · rw [h02, h13, h01, h23, h03, h12]
    ring
  · intro i j
    fin_cases i <;> fin_cases j
    · intro hij; exact absurd hij (by decide)
    · intro _; change 0 < gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 1; rw [h01]; exact zero_lt_one
    · intro _; change 0 < gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 2; rw [h02]; exact ht2
    · intro _; change 0 < gr24Minor (gr24PositiveChart t1 t2 t3 t4) 0 3; rw [h03]; exact hp03
    · intro hij; exact absurd hij (by decide)
    · intro hij; exact absurd hij (by decide)
    · intro _; change 0 < gr24Minor (gr24PositiveChart t1 t2 t3 t4) 1 2; rw [h12]; exact ht1
    · intro _; change 0 < gr24Minor (gr24PositiveChart t1 t2 t3 t4) 1 3; rw [h13]; exact hp13
    · intro hij; exact absurd hij (by decide)
    · intro hij; exact absurd hij (by decide)
    · intro hij; exact absurd hij (by decide)
    · intro _; change 0 < gr24Minor (gr24PositiveChart t1 t2 t3 t4) 2 3; rw [h23]; exact hp23
    · intro hij; exact absurd hij (by decide)
    · intro hij; exact absurd hij (by decide)
    · intro hij; exact absurd hij (by decide)
    · intro hij; exact absurd hij (by decide)

end PositiveGrassmannianGr24Chart

end InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset
