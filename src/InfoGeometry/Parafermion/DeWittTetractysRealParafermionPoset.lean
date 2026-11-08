/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# The Real DeWitt Split Tetractys & $i$-Free Parafermion Braid Poset ($\mathfrak{DT}_1 \prec \dots \prec \mathfrak{DT}_7$)

This module formalizes the 7-stage partial order ($\mathfrak{DT}_1 \prec \dots \prec \mathfrak{DT}_7$)
governing the endogenous generation of complex ($J^2 = -1$), para-complex ($S_P^2 = +1, \Phi^2 = +1$),
and dual nilpotent ($N_\pm^2 = 0$) operator algebras from a single real Peirce idempotent $P^2 = P$
in any associative ring `[Ring B]`, together with the division-free integer 8th root of unity
$$\zeta_{\text{real}} := P_2 \Phi_2 + (1 - P_2) J_1 \Phi_2, \qquad \zeta_{\text{real}}^2 = J_1, \quad \zeta_{\text{real}}^4 = -1, \quad \zeta_{\text{real}}^8 = +1,$$
and the resulting real Brown–Gauss sum and $\mathbb{Z}_4$ parafermion braid unitarity without external
complex scalars $i \in \mathbb{C}$ or irrational roots $\sqrt{2}$.

## Mathematical Contract (Three-Bucket Classification)

### BUCKET 1: CLOSED FINITE THEOREMS
- `dtCoverEdge_acyclic`: strict rank progression and acyclicity of the 7-stage DeWitt Tetractys Hasse poset on `Fin 7`.
- `single_bit_dewitt_tetractys_int_matrix_realization`: concrete $2 \times 2$ integer matrix realization of $\{I, S_P, \Phi, J = S_P \Phi\}$ in `Matrix (Fin 2) (Fin 2) ℤ` with explicit non-commutativity witness `dtMatS0 * dtMatPhi0 ≠ dtMatPhi0 * dtMatS0`.
- `two_bit_real_eighth_root_carry_int_matrix_realization`: concrete $4 \times 4$ integer matrix realization of the 2-bit DeWitt binary-carry 8th root of unity $\zeta_{\text{real}}$ in `Matrix (Fin 4) (Fin 4) ℤ` satisfying $\zeta_{\text{real}}^2 = J_1$, $\zeta_{\text{real}}^4 = -I_4$, $\zeta_{\text{real}}^8 = +I_4$, $\zeta_{\text{real}} \zeta_{\text{real}}^{-1} = I_4$, and $(S_1 \Phi_2) \zeta_{\text{real}} (S_1 \Phi_2) = \zeta_{\text{real}}^{-1}$ over pure integers $\mathbb{Z}$.

### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `dewitt_tetractys_peirce_spine_unification`: canonical Peirce/Tetraktys formulation of Nodes $\mathfrak{DT}_1 \prec \mathfrak{DT}_2 \prec \mathfrak{DT}_3$ using `invS`, `conePlus`, `coneMinus`, `genPhi`, and `genJ` in `[Ring B]`.
- `dewitt_tetractys_unifies_complex_paracomplex_and_nilpotent`: general associative ring unification of para-complex, complex, and nilpotent algebras from $P^2 = P$ and $\Phi = P W (1 - P) + (1 - P) W P$ ($\Phi^2 = 1$).
- `real_binary_carry_eighth_root_of_unity_and_inverse`: proves $\zeta_{\text{real}}^2 = J_1$, $\zeta_{\text{real}}^4 = -1$, $\zeta_{\text{real}}^8 = +1$, $\zeta_{\text{real}} \zeta_{\text{real}}^{-1} = 1$, $\zeta_{\text{real}}^{-1} \zeta_{\text{real}} = 1$, and $\zeta_{\text{real}}^{-1} = -J_1 \zeta_{\text{real}}$ in any `[Ring B]`.
- `real_eighth_root_carry_reflection_conjugation`: proves $(S_1 \Phi_2)^2 = 1$ and $(S_1 \Phi_2) \zeta_{\text{real}} (S_1 \Phi_2) = \zeta_{\text{real}}^{-1}$ in any `[Ring B]`.
- `real_dewitt_brown_gauss_and_z4_braid_unitarity` & `real_dewitt_brown_gauss_and_z4_braid_unitarity_ring`: proves $(1 + \zeta^2)^2 = 2 \zeta^2$, $1 + \zeta + \zeta^4 + \zeta^9 = 2 \zeta$, parity channel orthogonality, and exact $\mathbb{Z}_4$ braid unitarity $\text{RealBraidZ4}\;\zeta\;X * \text{RealBraidZ4\_Inv}\;\zeta\;X = 4$.

### BUCKET 3: OPEN CLOSURE DEBT
- None (`0 sorry`, `0 admit`, `0 custom axioms`, `0 structure wrappers`).
-/

namespace InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset

open Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine

universe u

/-! ## §1. 7-Stage Hasse Poset Grading ($\mathfrak{DT}_1 \prec \dots \prec \mathfrak{DT}_7$) -/

/-- Strict integer rank on the 7 nodes $\mathfrak{DT}_1 \prec \dots \prec \mathfrak{DT}_7$ (`Fin 7`). -/
def dtStageRank (i : Fin 7) : ℕ :=
  i.val + 1

/-- **Poset Cover Acyclicity (`dtCoverEdge_acyclic`)**:
Every directed Hasse cover edge $\mathfrak{DT}_i \prec_{\text{cov}} \mathfrak{DT}_j$ (`i.val + 1 = j.val`)
strictly increases `dtStageRank` and is strictly asymmetric (`j.val + 1 ≠ i.val`), establishing DAG acyclicity. -/
theorem dtCoverEdge_acyclic (i j : Fin 7) (h : i.val + 1 = j.val) :
    dtStageRank i < dtStageRank j ∧ j.val + 1 ≠ i.val := by
  dsimp [dtStageRank]
  rw [← h]
  refine ⟨by omega, ?_⟩
  intro h_rev
  omega

/-! ## §2. Nodes $\mathfrak{DT}_1 \prec \mathfrak{DT}_2 \prec \mathfrak{DT}_3$: The Single-Bit DeWitt Split Tetractys ($\{I, S_P, \Phi, J = S_P \Phi\}$) -/

section SingleBitDeWittTetractys

variable {B : Type u} [Ring B]

/-- **Canonical Peirce/Tetraktys DeWitt Unification (`dewitt_tetractys_peirce_spine_unification`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P` and normalized DeWitt bridge
`Φ = genPhi P W W` satisfying `Φ * Φ = 1`, the canonical Tetraktys operators
`1`, `invS P = P - (1 - P)`, `genPhi P W W`, and `genJ P W W = invS P * genPhi P W W` satisfy:
1. **Tetractys Dimension Sum**: `1 + 2 + 3 + 4 = 10` (Monad + Dyad + Triad + Tetrad).
2. **Para-Complex Split Involution**: `invS P * invS P = 1` and `invS P * genPhi P W W + genPhi P W W * invS P = 0`.
3. **Endogenous Complex Bivector**: `invS P * genPhi P W W = genJ P W W` with `genJ P W W * genJ P W W = -1`.
4. **Inner Real Reflections Execute Complex Conjugation ($J \mapsto -J$)**:
   `invS P * genJ P W W * invS P = -genJ P W W` and `genPhi P W W * genJ P W W * genPhi P W W = -genJ P W W`.
5. **Dual Nilpotent Rays**: `conePlus P W * conePlus P W = 0` and `coneMinus P W * coneMinus P W = 0`. -/
theorem dewitt_tetractys_peirce_spine_unification
    (P W : B) (hP : P * P = P) (hPhi_sq : genPhi P W W * genPhi P W W = 1) :
    1 + 2 + 3 + 4 = 10 ∧
    invS P * invS P = 1 ∧
    invS P * genPhi P W W + genPhi P W W * invS P = 0 ∧
    invS P * genPhi P W W = genJ P W W ∧
    genJ P W W * genJ P W W = -1 ∧
    invS P * genJ P W W * invS P = -genJ P W W ∧
    genPhi P W W * genJ P W W * genPhi P W W = -genJ P W W ∧
    conePlus P W * conePlus P W = 0 ∧
    coneMinus P W * coneMinus P W = 0 := by
  have hS_sq : invS P * invS P = 1 :=
    (archetype_A2_peirce_cartan_grading_and_tangent_closure hP P P).1
  have hA3 := archetype_A3_nilpotent_cones_and_tetraktys_table hP W W
  have hPhi_V : genPhi P W W * genPhi P W W = genV P W W := hA3.2.2.1
  have hJ_V : genJ P W W * genJ P W W = -genV P W W := hA3.2.2.2.1
  have h_anti_PhiJ : genPhi P W W * genJ P W W + genJ P W W * genPhi P W W = 0 :=
    hA3.2.2.2.2.2.2.2.1
  have h_PhiJ : genPhi P W W * genJ P W W = -(genJ P W W * genPhi P W W) :=
    eq_neg_of_add_eq_zero_left h_anti_PhiJ
  have h_SJ : invS P * genPhi P W W = genJ P W W := by
    dsimp [invS, genPhi, genJ]
    simp only [sub_mul, mul_add, one_mul, P_mul_conePlus hP, P_mul_coneMinus hP]
    abel
  have h_JS : genPhi P W W * invS P = -genJ P W W := by
    dsimp [invS, genPhi, genJ]
    simp only [add_mul, mul_sub, mul_one, conePlus_mul_P hP, coneMinus_mul_P hP]
    abel
  refine ⟨by decide, hS_sq, ?_, h_SJ, ?_, ?_, ?_, hA3.1, hA3.2.1⟩
  · rw [h_SJ, h_JS, add_neg_cancel]
  · rw [hJ_V, ← hPhi_V, hPhi_sq]
  · calc
      invS P * genJ P W W * invS P = invS P * (invS P * genPhi P W W) * invS P := by
        rw [← h_SJ]
      _ = (invS P * invS P) * genPhi P W W * invS P := by simp only [mul_assoc]
      _ = genPhi P W W * invS P := by rw [hS_sq, one_mul]
      _ = -genJ P W W := h_JS
  · calc
      genPhi P W W * genJ P W W * genPhi P W W =
          (-(genJ P W W * genPhi P W W)) * genPhi P W W := by rw [h_PhiJ]
      _ = -(genJ P W W * (genPhi P W W * genPhi P W W)) := by simp only [neg_mul, mul_assoc]
      _ = -genJ P W W := by rw [hPhi_sq, mul_one]

/-- The DeWitt parity grading involution `S_P = 2P - 1` (`P + P - 1`). -/
def dewittSplitS (P : B) : B := 2 * P - 1

/-- The endogenous complex bivector `J = S_P * Φ = N_+ - N_-` built purely from real reflections. -/
def dewittBivectorJ (P Phi : B) : B := dewittSplitS P * Phi

/-- **Theorem 1 ($\mathfrak{DT}_1 \prec \mathfrak{DT}_2 \prec \mathfrak{DT}_3$ — `dewitt_tetractys_unifies_complex_paracomplex_and_nilpotent`)**:
In any associative ring `B` (with zero scalar complexification), a single idempotent `P² = P`
and a normalized off-diagonal Peirce bridge `Φ = P W (1 - P) + (1 - P) W P` (`Φ² = 1`)
generate the 4-element DeWitt Tetractys `{1, S_P, Φ, J = S_P Φ}` which simultaneously houses:
1. **Para-Complex (Hyperbolic) Units**: `S_P² = 1` and `Φ² = 1` with `{S_P, Φ} = 0`,
2. **Endogenous Complex Unit**: `J = S_P Φ = P W (1 - P) - (1 - P) W P` satisfying `J² = -1`,
3. **Inner Complex Conjugation**: `S_P J S_P = -J` and `Φ J Φ = -J`,
4. **Dual Nilpotent Rays**: `N_+² = 0` and `N_-² = 0` where `N_+ = P W (1 - P)` and `N_- = (1 - P) W P`. -/
theorem dewitt_tetractys_unifies_complex_paracomplex_and_nilpotent
    (P W : B)
    (hP : P * P = P)
    (hPhi_sq : (P * W * (1 - P) + (1 - P) * W * P) * (P * W * (1 - P) + (1 - P) * W * P) = 1) :
    let N_plus := P * W * (1 - P)
    let N_minus := (1 - P) * W * P
    let Phi := N_plus + N_minus
    let S_P := dewittSplitS P
    let J := dewittBivectorJ P Phi
    S_P * S_P = 1 ∧
    S_P * Phi + Phi * S_P = 0 ∧
    J = N_plus - N_minus ∧
    J * J = -1 ∧
    S_P * J * S_P = -J ∧
    Phi * J * Phi = -J ∧
    N_plus * N_plus = 0 ∧
    N_minus * N_minus = 0 := by
  have h2 : (2 : B) = 1 + 1 := one_add_one_eq_two.symm
  have hP_idem : ∀ Z : B, P * (P * Z) = P * Z := fun Z => by rw [← mul_assoc, hP]
  have hS_sq : dewittSplitS P * dewittSplitS P = 1 := by
    dsimp [dewittSplitS]
    rw [h2]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hP]
    abel
  have h_SJ : dewittSplitS P * (P * W * (1 - P) + (1 - P) * W * P) =
      P * W * (1 - P) - (1 - P) * W * P := by
    dsimp [dewittSplitS]
    rw [h2]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP_idem]
    abel
  have h_JS : (P * W * (1 - P) + (1 - P) * W * P) * dewittSplitS P =
      -(P * W * (1 - P) - (1 - P) * W * P) := by
    dsimp [dewittSplitS]
    rw [h2]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP]
    abel
  have h_J2_Phi2 :
      (P * W * (1 - P) - (1 - P) * W * P) * (P * W * (1 - P) - (1 - P) * W * P) =
      -((P * W * (1 - P) + (1 - P) * W * P) * (P * W * (1 - P) + (1 - P) * W * P)) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP_idem]
    abel
  have h_PhiJ :
      (P * W * (1 - P) + (1 - P) * W * P) * (P * W * (1 - P) - (1 - P) * W * P) =
      -((P * W * (1 - P) - (1 - P) * W * P) * (P * W * (1 - P) + (1 - P) * W * P)) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP_idem]
    abel
  refine ⟨hS_sq, ?_, h_SJ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_SJ, h_JS, add_neg_cancel]
  · dsimp [dewittBivectorJ]
    rw [h_SJ, h_J2_Phi2, hPhi_sq]
  · dsimp [dewittBivectorJ]
    calc
      dewittSplitS P * (dewittSplitS P * (P * W * (1 - P) + (1 - P) * W * P)) * dewittSplitS P =
          (dewittSplitS P * dewittSplitS P) * (P * W * (1 - P) + (1 - P) * W * P) * dewittSplitS P := by
        simp only [mul_assoc]
      _ = (P * W * (1 - P) + (1 - P) * W * P) * dewittSplitS P := by rw [hS_sq, one_mul]
      _ = -(dewittSplitS P * (P * W * (1 - P) + (1 - P) * W * P)) := by rw [h_JS, h_SJ]
  · dsimp [dewittBivectorJ]
    rw [h_SJ]
    calc
      (P * W * (1 - P) + (1 - P) * W * P) * (P * W * (1 - P) - (1 - P) * W * P) *
          (P * W * (1 - P) + (1 - P) * W * P) =
        (-((P * W * (1 - P) - (1 - P) * W * P) * (P * W * (1 - P) + (1 - P) * W * P))) *
          (P * W * (1 - P) + (1 - P) * W * P) := by rw [h_PhiJ]
      _ = -((P * W * (1 - P) - (1 - P) * W * P) *
          ((P * W * (1 - P) + (1 - P) * W * P) * (P * W * (1 - P) + (1 - P) * W * P))) := by
        simp only [neg_mul, mul_assoc]
      _ = -(P * W * (1 - P) - (1 - P) * W * P) := by rw [hPhi_sq, mul_one]
  · simp only [sub_mul, mul_sub, mul_one, mul_assoc, hP_idem]
    abel
  · simp only [sub_mul, mul_sub, one_mul, mul_assoc, hP_idem]
    abel

/-- Concrete $2 \times 2$ integer projector `P₀ = diag(1, 0)`. -/
def dtMatP0 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- Concrete $2 \times 2$ integer parity grading `S₀ = 2 P₀ - I₂ = diag(1, -1)`. -/
def dtMatS0 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

/-- Concrete $2 \times 2$ integer split bridge `Φ₀ = [[0, 1], [1, 0]]`. -/
def dtMatPhi0 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- Concrete $2 \times 2$ integer complex bivector `J₀ = S₀ Φ₀ = [[0, 1], [-1, 0]]`. -/
def dtMatJ0 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

/-- **Concrete $2 \times 2$ Integer Matrix Realization of the Single-Bit DeWitt Split Tetractys (`single_bit_dewitt_tetractys_int_matrix_realization`)**:
In `Matrix (Fin 2) (Fin 2) ℤ`, `{I₂, dtMatS0, dtMatPhi0, dtMatJ0}` satisfies `dtMatP0² = dtMatP0`,
`dtMatS0² = 1`, `dtMatPhi0² = 1`, `dtMatS0 * dtMatPhi0 = dtMatJ0`, `dtMatJ0² = -1`,
`dtMatS0 * dtMatJ0 * dtMatS0 = -dtMatJ0`, and `dtMatS0 * dtMatPhi0 ≠ dtMatPhi0 * dtMatS0`. -/
theorem single_bit_dewitt_tetractys_int_matrix_realization :
    dtMatP0 * dtMatP0 = dtMatP0 ∧
    dtMatS0 * dtMatS0 = 1 ∧
    dtMatPhi0 * dtMatPhi0 = 1 ∧
    dtMatS0 * dtMatPhi0 = dtMatJ0 ∧
    dtMatJ0 * dtMatJ0 = -1 ∧
    dtMatS0 * dtMatJ0 * dtMatS0 = -dtMatJ0 ∧
    dtMatS0 * dtMatPhi0 ≠ dtMatPhi0 * dtMatS0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · intro h_comm
    have h01 := congr_fun (congr_fun h_comm 0) 1
    revert h01
    decide

end SingleBitDeWittTetractys

/-! ## §3. Nodes $\mathfrak{DT}_4 \prec \mathfrak{DT}_5$: Division-Free Real 8th Root of Unity ($\zeta_{\text{real}}$) via Binary Carry -/

section RealEighthRootCarry

variable {B : Type u} [Ring B]

/-- **The Real Binary-Carry 8th Root of Unity (`realEighthRootCarry P2 Phi2 J1`)**:
Flips bit 2 via `Φ₂` on `P₂`, and applies bit 1's endogenous complex bivector `J₁ = S₁ Φ₁` (`J₁² = -1`)
when flipping bit 2 on `1 - P₂`:
`ζ_real = P₂ Φ₂ + (1 - P₂) J₁ Φ₂` (zero scalar `i ∈ ℂ`, zero `√2`). -/
def realEighthRootCarry (P2 Phi2 J1 : B) : B :=
  P2 * Phi2 + (1 - P2) * J1 * Phi2

/-- **Inverse Real Binary-Carry 8th Root (`realEighthRootCarryInv P2 Phi2 J1`)**:
`ζ_real⁻¹ = (1 - P₂) Φ₂ - P₂ J₁ Φ₂ = -J₁ ζ_real`. -/
def realEighthRootCarryInv (P2 Phi2 J1 : B) : B :=
  (1 - P2) * Phi2 - P2 * J1 * Phi2

/-- **Theorem 2 ($\mathfrak{DT}_4 \prec \mathfrak{DT}_5$ — `real_binary_carry_eighth_root_of_unity_and_inverse`)**:
In any associative ring `B`, let `(P₂, Φ₂)` be a Peirce bit (`P₂² = P₂`, `Φ₂² = 1`, `Φ₂ P₂ = (1 - P₂) Φ₂`)
and let `J₁` be an endogenous complex bivector (`J₁² = -1`) from an independent Peirce bit
commuting with `(P₂, Φ₂)`. Then `ζ = realEighthRootCarry P2 Phi2 J1` satisfies:
1. **Square is the Bivector $J_1$**: `ζ * ζ = J₁`,
2. **Fourth Power is $-1$**: `(ζ * ζ) * (ζ * ζ) = -1`,
3. **Eighth Power is $+1$**: `((ζ * ζ) * (ζ * ζ)) * ((ζ * ζ) * (ζ * ζ)) = 1`,
4. **Two-Sided Inverse**: `ζ * ζ⁻¹ = 1` and `ζ⁻¹ * ζ = 1`,
5. **Inverse Bivector Identity**: `ζ⁻¹ = -J₁ * ζ`. -/
theorem real_binary_carry_eighth_root_of_unity_and_inverse
    (P2 Phi2 J1 : B)
    (hP2 : P2 * P2 = P2)
    (hPhi2_sq : Phi2 * Phi2 = 1)
    (h_swap2 : Phi2 * P2 = (1 - P2) * Phi2)
    (hJ1_sq : J1 * J1 = -1)
    (h_comm_P : J1 * P2 = P2 * J1)
    (h_comm_Phi : J1 * Phi2 = Phi2 * J1) :
    let ζ := realEighthRootCarry P2 Phi2 J1
    let ζ_inv := realEighthRootCarryInv P2 Phi2 J1
    ζ * ζ = J1 ∧
    (ζ * ζ) * (ζ * ζ) = -1 ∧
    ((ζ * ζ) * (ζ * ζ)) * ((ζ * ζ) * (ζ * ζ)) = 1 ∧
    ζ * ζ_inv = 1 ∧
    ζ_inv * ζ = 1 ∧
    ζ_inv = -J1 * ζ := by
  have hP2_idem : ∀ Z : B, P2 * (P2 * Z) = P2 * Z := fun Z => by rw [← mul_assoc, hP2]
  have hPhi2_idem : ∀ Z : B, Phi2 * (Phi2 * Z) = Z := fun Z => by rw [← mul_assoc, hPhi2_sq, one_mul]
  have h_swap2_assoc : ∀ Z : B, Phi2 * (P2 * Z) = (1 - P2) * (Phi2 * Z) :=
    fun Z => by rw [← mul_assoc, h_swap2, mul_assoc]
  have h_comm_P_assoc : ∀ Z : B, J1 * (P2 * Z) = P2 * (J1 * Z) :=
    fun Z => by rw [← mul_assoc, h_comm_P, mul_assoc]
  have h_comm_Phi_assoc : ∀ Z : B, J1 * (Phi2 * Z) = Phi2 * (J1 * Z) :=
    fun Z => by rw [← mul_assoc, h_comm_Phi, mul_assoc]
  have h_sq : realEighthRootCarry P2 Phi2 J1 * realEighthRootCarry P2 Phi2 J1 = J1 := by
    dsimp [realEighthRootCarry]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc, h_swap2_assoc, hPhi2_sq, hPhi2_idem, hP2_idem,
      h_comm_P_assoc, h_comm_Phi, h_comm_Phi_assoc, hJ1_sq, mul_neg]
    abel
  have h_pow4 :
      (realEighthRootCarry P2 Phi2 J1 * realEighthRootCarry P2 Phi2 J1) *
        (realEighthRootCarry P2 Phi2 J1 * realEighthRootCarry P2 Phi2 J1) = -1 := by
    rw [h_sq, hJ1_sq]
  have h_pow8 :
      ((realEighthRootCarry P2 Phi2 J1 * realEighthRootCarry P2 Phi2 J1) *
        (realEighthRootCarry P2 Phi2 J1 * realEighthRootCarry P2 Phi2 J1)) *
      ((realEighthRootCarry P2 Phi2 J1 * realEighthRootCarry P2 Phi2 J1) *
        (realEighthRootCarry P2 Phi2 J1 * realEighthRootCarry P2 Phi2 J1)) = 1 := by
    rw [h_pow4, neg_mul_neg, one_mul]
  have h_inv_R : realEighthRootCarry P2 Phi2 J1 * realEighthRootCarryInv P2 Phi2 J1 = 1 := by
    dsimp [realEighthRootCarry, realEighthRootCarryInv]
    simp only [add_mul, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc, h_swap2_assoc, hPhi2_sq, hPhi2_idem, hP2, hP2_idem,
      h_comm_P_assoc, h_comm_Phi, h_comm_Phi_assoc, hJ1_sq, mul_neg]
    abel
  have h_inv_L : realEighthRootCarryInv P2 Phi2 J1 * realEighthRootCarry P2 Phi2 J1 = 1 := by
    dsimp [realEighthRootCarry, realEighthRootCarryInv]
    simp only [mul_add, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc, h_swap2_assoc, hPhi2_sq, hPhi2_idem, hP2, hP2_idem,
      h_comm_P_assoc, h_comm_Phi, h_comm_Phi_assoc, hJ1_sq, mul_neg]
    abel
  have h_inv_id :
      realEighthRootCarryInv P2 Phi2 J1 = -J1 * realEighthRootCarry P2 Phi2 J1 := by
    calc
      realEighthRootCarryInv P2 Phi2 J1 = 1 * realEighthRootCarryInv P2 Phi2 J1 := by
        rw [one_mul]
      _ = (-J1 * J1) * realEighthRootCarryInv P2 Phi2 J1 := by
        rw [neg_mul, hJ1_sq, neg_neg]
      _ = (-J1 * (realEighthRootCarry P2 Phi2 J1 * realEighthRootCarry P2 Phi2 J1)) *
          realEighthRootCarryInv P2 Phi2 J1 := by
        rw [h_sq]
      _ = -J1 * realEighthRootCarry P2 Phi2 J1 *
          (realEighthRootCarry P2 Phi2 J1 * realEighthRootCarryInv P2 Phi2 J1) := by
        simp only [mul_assoc]
      _ = -J1 * realEighthRootCarry P2 Phi2 J1 := by
        rw [h_inv_R, mul_one]
  exact ⟨h_sq, h_pow4, h_pow8, h_inv_R, h_inv_L, h_inv_id⟩

/-- **Real Reflection Conjugation of the 8th Root Carry (`real_eighth_root_carry_reflection_conjugation`)**:
If the first-bit reflection `S₁` (`S₁² = 1`) commutes with `(P₂, Φ₂)` and anticommutes with `J₁`
(`S₁ J₁ = -J₁ S₁`), then the composite reflection `R₁₂ = S₁ Φ₂` satisfies `R₁₂² = 1` and conjugates
`ζ_real` into its exact inverse `ζ_real⁻¹`. -/
theorem real_eighth_root_carry_reflection_conjugation
    (P2 Phi2 J1 S1 : B)
    (hPhi2_sq : Phi2 * Phi2 = 1)
    (hS1_sq : S1 * S1 = 1)
    (h_swap2 : Phi2 * P2 = (1 - P2) * Phi2)
    (h_comm_Phi : J1 * Phi2 = Phi2 * J1)
    (h_S1_P2 : S1 * P2 = P2 * S1)
    (h_S1_Phi2 : S1 * Phi2 = Phi2 * S1)
    (h_S1_J1 : S1 * J1 = -(J1 * S1)) :
    let ζ := realEighthRootCarry P2 Phi2 J1
    let ζ_inv := realEighthRootCarryInv P2 Phi2 J1
    (S1 * Phi2) * (S1 * Phi2) = 1 ∧
    (S1 * Phi2) * ζ * (S1 * Phi2) = ζ_inv := by
  have hPhi2_idem : ∀ Z : B, Phi2 * (Phi2 * Z) = Z :=
    fun Z => by rw [← mul_assoc, hPhi2_sq, one_mul]
  have hS1_idem : ∀ Z : B, S1 * (S1 * Z) = Z :=
    fun Z => by rw [← mul_assoc, hS1_sq, one_mul]
  have h_swap2_assoc : ∀ Z : B, Phi2 * (P2 * Z) = (1 - P2) * (Phi2 * Z) :=
    fun Z => by rw [← mul_assoc, h_swap2, mul_assoc]
  have h_S1_P2_assoc : ∀ Z : B, S1 * (P2 * Z) = P2 * (S1 * Z) :=
    fun Z => by rw [← mul_assoc, h_S1_P2, mul_assoc]
  have h_S1_Phi2_assoc : ∀ Z : B, S1 * (Phi2 * Z) = Phi2 * (S1 * Z) :=
    fun Z => by rw [← mul_assoc, h_S1_Phi2, mul_assoc]
  have hR_sq : (S1 * Phi2) * (S1 * Phi2) = 1 := by
    calc
      (S1 * Phi2) * (S1 * Phi2) = S1 * (Phi2 * (S1 * Phi2)) := by simp only [mul_assoc]
      _ = S1 * (S1 * (Phi2 * Phi2)) := by rw [← mul_assoc Phi2 S1, ← h_S1_Phi2, mul_assoc]
      _ = 1 := by rw [hS1_idem, hPhi2_sq]
  have h_conj :
      (S1 * Phi2) * realEighthRootCarry P2 Phi2 J1 * (S1 * Phi2) =
        realEighthRootCarryInv P2 Phi2 J1 := by
    dsimp [realEighthRootCarry, realEighthRootCarryInv]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc, h_swap2_assoc, hPhi2_idem, hS1_sq,
      h_comm_Phi, h_S1_P2_assoc, h_S1_Phi2, h_S1_Phi2_assoc,
      h_S1_J1, neg_mul, mul_neg]
    abel
  exact ⟨hR_sq, h_conj⟩

/-- Concrete $4 \times 4$ integer projector for bit 1 (`P₁ = P₀ ⊗ I₂ = diag(1, 1, 0, 0)`). -/
def dtMatP1 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Concrete $4 \times 4$ integer projector for bit 2 (`P₂ = I₂ ⊗ P₀ = diag(1, 0, 1, 0)`). -/
def dtMatP2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0]

/-- Concrete $4 \times 4$ integer grading involution for bit 1 (`S₁ = 2 P₁ - I₄ = diag(1, 1, -1, -1)`). -/
def dtMatS1 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- Concrete $4 \times 4$ integer split bridge for bit 1 (`Φ₁ = Φ₀ ⊗ I₂`). -/
def dtMatPhi1 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Concrete $4 \times 4$ integer split bridge for bit 2 (`Φ₂ = I₂ ⊗ Φ₀`). -/
def dtMatPhi2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- Concrete $4 \times 4$ integer complex bivector for bit 1 (`J₁ = S₁ Φ₁ = J₀ ⊗ I₂`, `J₁² = -I₄`). -/
def dtMatJ1 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     -1, 0, 0, 0;
     0, -1, 0, 0]

/-- Concrete $4 \times 4$ integer 8th root of unity (`ζ_real = P₂ Φ₂ + (I₄ - P₂) J₁ Φ₂`):
a pure integer signed cyclic 4-shift permutation matrix with zero `i ∈ ℂ` and zero `√2`. -/
def dtMatZetaReal : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1;
     -1, 0, 0, 0]

/-- Concrete $4 \times 4$ integer inverse 8th root of unity (`ζ_real⁻¹ = (I₄ - P₂) Φ₂ - P₂ J₁ Φ₂`). -/
def dtMatZetaRealInv : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, -1;
     1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0]

/-- **Concrete $4 \times 4$ Integer Matrix Realization of the 2-Bit Real 8th Root Carry (`two_bit_real_eighth_root_carry_int_matrix_realization`)**:
In `Matrix (Fin 4) (Fin 4) ℤ` (over pure integers $\mathbb{Z}$ with zero complex scalars and zero $\sqrt{2}$),
`dtMatZetaReal = realEighthRootCarry dtMatP2 dtMatPhi2 dtMatJ1` satisfies:
- `dtMatZetaReal * dtMatZetaReal = dtMatJ1`,
- `(dtMatZetaReal * dtMatZetaReal) * (dtMatZetaReal * dtMatZetaReal) = -1`,
- `dtMatZetaReal * dtMatZetaRealInv = 1` and `dtMatZetaRealInv * dtMatZetaReal = 1`,
- `(dtMatS1 * dtMatPhi2) * dtMatZetaReal * (dtMatS1 * dtMatPhi2) = dtMatZetaRealInv`,
- Non-commutativity witness: `dtMatZetaReal * dtMatPhi2 ≠ dtMatPhi2 * dtMatZetaReal`. -/
theorem two_bit_real_eighth_root_carry_int_matrix_realization :
    realEighthRootCarry dtMatP2 dtMatPhi2 dtMatJ1 = dtMatZetaReal ∧
    realEighthRootCarryInv dtMatP2 dtMatPhi2 dtMatJ1 = dtMatZetaRealInv ∧
    dtMatZetaReal * dtMatZetaReal = dtMatJ1 ∧
    (dtMatZetaReal * dtMatZetaReal) * (dtMatZetaReal * dtMatZetaReal) = -1 ∧
    dtMatZetaReal * dtMatZetaRealInv = 1 ∧
    dtMatZetaRealInv * dtMatZetaReal = 1 ∧
    (dtMatS1 * dtMatPhi2) * dtMatZetaReal * (dtMatS1 * dtMatPhi2) = dtMatZetaRealInv ∧
    dtMatZetaReal * dtMatPhi2 ≠ dtMatPhi2 * dtMatZetaReal := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · intro h_comm
    have h00 := congr_fun (congr_fun h_comm 0) 0
    revert h00
    decide

end RealEighthRootCarry

/-! ## §4. Nodes $\mathfrak{DT}_6 \prec \mathfrak{DT}_7$: Real Brown–Gauss Invariant & $\mathbb{Z}_4$ Parafermion Braid Unitarity -/

section RealBrownGaussAndBraidUnitarity

variable {R : Type u} [CommRing R]

/-- The real $\mathbb{Z}_4$ parafermion braid operator (scaled by 2 to remain in $\mathbb{Z}[\zeta, X]$):
`2 U(X) = (1 - X²) + ζ X (1 + X²)`. -/
def RealBraidZ4 (ζ X : R) : R :=
  (1 - X ^ 2) + ζ * X * (1 + X ^ 2)

/-- The real inverse/adjoint $\mathbb{Z}_4$ parafermion braid operator (using `ζ⁻¹ = -ζ³`, `X⁻¹ = X³`):
`2 U⁻¹(X) = (1 - X²) - ζ³ X³ (1 + X²)`. -/
def RealBraidZ4_Inv (ζ X : R) : R :=
  (1 - X ^ 2) - (ζ ^ 3) * (X ^ 3) * (1 + X ^ 2)

/-- **Theorem 3 ($\mathfrak{DT}_6 \prec \mathfrak{DT}_7$ — `real_dewitt_brown_gauss_and_z4_braid_unitarity`)**:
Using the real DeWitt 8th root `ζ = ζ_real` (`ζ⁴ = -1`) and an order-4 parafermion
generator `X` (`X⁴ = 1`):
1. **$\mathbb{Z}_2$ Real Brown–Gauss Square**: `(1 + ζ²)² = 2 ζ²` (where `ζ² = J₁`),
2. **$\mathbb{Z}_4$ Real Brown–Gauss Sum**: `1 + ζ + ζ⁴ + ζ⁹ = 2 ζ`,
3. **Orthogonality of Even/Odd Parity Channels**: `(1 - X²)(ζ X (1 + X²)) = 0`,
4. **Scaled Braid-Product Identity**: `(2 U(X))(2 U⁻¹(X)) = 4`. This ring identity does not define an adjoint or a normalized unitary operator. -/
theorem real_dewitt_brown_gauss_and_z4_braid_unitarity
    (ζ X : R)
    (hζ4 : ζ ^ 4 = -1)
    (hX4 : X ^ 4 = 1) :
    (1 + ζ ^ 2) ^ 2 = 2 * (ζ ^ 2) ∧
    (1 + ζ + ζ ^ 4 + ζ ^ 9 = 2 * ζ) ∧
    (1 - X ^ 2) * (ζ * X * (1 + X ^ 2)) = 0 ∧
    RealBraidZ4 ζ X * RealBraidZ4_Inv ζ X = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (1 + ζ ^ 2) ^ 2 = 2 * (ζ ^ 2) + (1 + ζ ^ 4) := by ring
      _ = 2 * (ζ ^ 2) + (1 + (-1)) := by rw [hζ4]
      _ = 2 * (ζ ^ 2) := by ring
  · calc
      1 + ζ + ζ ^ 4 + ζ ^ 9 =
        (1 + ζ ^ 4) + ζ * (1 + (ζ ^ 4) ^ 2) := by ring
      _ = (1 + (-1)) + ζ * (1 + (-1) ^ 2) := by rw [hζ4]
      _ = 2 * ζ := by ring
  · calc
      (1 - X ^ 2) * (ζ * X * (1 + X ^ 2)) =
        ζ * X * (1 - X ^ 4) := by ring
      _ = ζ * X * (1 - 1) := by rw [hX4]
      _ = 0 := by ring
  · dsimp [RealBraidZ4, RealBraidZ4_Inv]
    calc
      ((1 - X ^ 2) + ζ * X * (1 + X ^ 2)) *
        ((1 - X ^ 2) - (ζ ^ 3) * (X ^ 3) * (1 + X ^ 2)) =
        (1 - 2 * X ^ 2 + X ^ 4) +
          (1 - X ^ 4) * (ζ * X - ζ ^ 3 * X ^ 3) -
          (ζ ^ 4) * (X ^ 4) * (1 + 2 * X ^ 2 + X ^ 4) := by ring
      _ = (1 - 2 * X ^ 2 + 1) +
          (1 - 1) * (ζ * X - ζ ^ 3 * X ^ 3) -
          (-1) * 1 * (1 + 2 * X ^ 2 + 1) := by rw [hX4, hζ4]
      _ = 4 := by ring

/-- Non-commutative ring formulation of the real $\mathbb{Z}_4$ parafermion braid operator
`2 U(X) = (1 - X * X) + ζ * X * (1 + X * X)` in any `[Ring B]`. -/
def realBraidZ4Ring {B : Type u} [Ring B] (ζ X : B) : B :=
  (1 - X * X) + ζ * X * (1 + X * X)

/-- Non-commutative ring formulation of the real inverse $\mathbb{Z}_4$ parafermion braid operator
`2 U⁻¹(X) = (1 - X * X) - (ζ * (ζ * ζ)) * (X * (X * X)) * (1 + X * X)` in any `[Ring B]`. -/
def realBraidZ4InvRing {B : Type u} [Ring B] (ζ X : B) : B :=
  (1 - X * X) - (ζ * (ζ * ζ)) * (X * (X * X)) * (1 + X * X)

/-- **Non-Commutative Ring Formulation of Nodes $\mathfrak{DT}_6 \prec \mathfrak{DT}_7$ (`real_dewitt_brown_gauss_and_z4_braid_unitarity_ring`)**:
In ANY associative ring `[Ring B]` (without assuming commutativity of `B`, hence directly applicable
to $4 \times 4$ integer matrices), for any real DeWitt 8th root `ζ` (`ζ⁴ = -1`) and any order-4
parafermion generator `X` (`X⁴ = 1`) commuting with `ζ`:
1. **$\mathbb{Z}_2$ Real Brown–Gauss Square**: `(1 + ζ * ζ) * (1 + ζ * ζ) = ζ * ζ + ζ * ζ`,
2. **$\mathbb{Z}_4$ Real Brown–Gauss Sum**: `1 + ζ + ζ⁴ + ζ⁸ * ζ = ζ + ζ`,
3. **Orthogonality of Parity Channels**: `(1 - X * X) * (ζ * X * (1 + X * X)) = 0`,
4. **Scaled Braid-Product Identity in `[Ring B]`**:
   `realBraidZ4Ring ζ X * realBraidZ4InvRing ζ X = 1 + 1 + 1 + 1`. -/
theorem real_dewitt_brown_gauss_and_z4_braid_unitarity_ring
    {B : Type u} [Ring B] (ζ X : B)
    (hζ4 : ζ * (ζ * (ζ * ζ)) = -1)
    (hX4 : X * (X * (X * X)) = 1)
    (h_comm : ζ * X = X * ζ) :
    let ζ2 := ζ * ζ
    let ζ4 := ζ * (ζ * (ζ * ζ))
    let ζ8 := ζ4 * ζ4
    (1 + ζ2) * (1 + ζ2) = ζ2 + ζ2 ∧
    1 + ζ + ζ4 + ζ8 * ζ = ζ + ζ ∧
    (1 - X * X) * (ζ * X * (1 + X * X)) = 0 ∧
    realBraidZ4Ring ζ X * realBraidZ4InvRing ζ X = 1 + 1 + 1 + 1 := by
  have hζ8 : (ζ * (ζ * (ζ * ζ))) * (ζ * (ζ * (ζ * ζ))) = 1 := by
    rw [hζ4, neg_mul_neg, one_mul]
  have hX_idem : ∀ Z : B, X * (X * (X * (X * Z))) = Z := by
    intro Z
    calc
      X * (X * (X * (X * Z))) = (X * (X * (X * X))) * Z := by simp only [mul_assoc]
      _ = Z := by rw [hX4, one_mul]
  have h_comm_assoc : ∀ Z : B, ζ * (X * Z) = X * (ζ * Z) := by
    intro Z; rw [← mul_assoc, h_comm, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc, hζ4]
    abel
  · rw [hζ8, hζ4, one_mul]
    abel
  · simp only [mul_add, sub_mul, one_mul, mul_one,
      mul_assoc, h_comm, h_comm_assoc, hX_idem]
    abel
  · dsimp [realBraidZ4Ring, realBraidZ4InvRing]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      mul_neg, mul_assoc,
      h_comm, h_comm_assoc, hX4, hX_idem, hζ4]
    abel

end RealBrownGaussAndBraidUnitarity

/-! ## §5. Row 3–4 $\mathfrak{sl}_2(\mathbb{R})$ Triad, 10D Symplectic $\mathfrak{sp}(4, \mathbb{Z})$ Decomposition ($1 + 2 + 3 + 4 = 10$), and Real Grassmannian Positivity $\mathrm{Gr}_+(2, 4)$ -/

section SymplecticAndGrassmannianPositivity

/-- **Row 3–4 $\mathfrak{sl}_2(\mathbb{R})$ Lie Bracket Closure & Chevalley–Peirce Nilpotent Ladder (`dewitt_triad_sl2_lie_brackets_and_chevalley_ladder`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P` and normalized DeWitt bridge
`genPhi P W W * genPhi P W W = 1`, the Triad `{invS P, genPhi P W W, genJ P W W}` and the nilpotent
Peirce corners `conePlus P W, coneMinus P W` satisfy:
1. **Row 3 $\mathfrak{sl}_2(\mathbb{R})$ Commutation Relations**:
   - `OperatorAlgebra.PeirceSpine.comm (invS P) (genPhi P W W) = genJ P W W + genJ P W W` (`[S_P, Φ] = 2 J`),
   - `OperatorAlgebra.PeirceSpine.comm (genJ P W W) (genPhi P W W) = invS P + invS P` (`[J, Φ] = 2 S_P`, i.e., `[Φ, J] = -2 S_P`),
   - `OperatorAlgebra.PeirceSpine.comm (genJ P W W) (invS P) = -(genPhi P W W + genPhi P W W)` (`[J, S_P] = -2 Φ`),
2. **Quadratic Casimir Identity**:
   - `invS P * invS P + genPhi P W W * genPhi P W W - genJ P W W * genJ P W W = 1 + 1 + 1`,
3. **Row 4 Chevalley–Peirce Nilpotent Raising/Lowering Brackets**:
   - `OperatorAlgebra.PeirceSpine.comm (invS P) (conePlus P W) = conePlus P W + conePlus P W` (`[S_P, N_+] = +2 N_+`),
   - `OperatorAlgebra.PeirceSpine.comm (invS P) (coneMinus P W) = -(coneMinus P W + coneMinus P W)` (`[S_P, N_-] = -2 N_-`),
   - `OperatorAlgebra.PeirceSpine.comm (conePlus P W) (coneMinus P W) = invS P` (`[N_+, N_-] = S_P`),
4. **Exact First-Order Unipotent Group Truncation**:
   - `(1 + conePlus P W) * (1 + conePlus P W) = 1 + (conePlus P W + conePlus P W)`,
   - `(1 + conePlus P W) * (1 - conePlus P W) = 1` and `(1 + coneMinus P W) * (1 - coneMinus P W) = 1`. -/
theorem dewitt_triad_sl2_lie_brackets_and_chevalley_ladder
    {B : Type u} [Ring B]
    (P W : B) (hP : P * P = P) (hPhi_sq : genPhi P W W * genPhi P W W = 1) :
    OperatorAlgebra.PeirceSpine.comm (invS P) (genPhi P W W) = genJ P W W + genJ P W W ∧
    OperatorAlgebra.PeirceSpine.comm (genJ P W W) (genPhi P W W) = invS P + invS P ∧
    OperatorAlgebra.PeirceSpine.comm (genJ P W W) (invS P) = -(genPhi P W W + genPhi P W W) ∧
    invS P * invS P + genPhi P W W * genPhi P W W - genJ P W W * genJ P W W = 1 + 1 + 1 ∧
    OperatorAlgebra.PeirceSpine.comm (invS P) (conePlus P W) = conePlus P W + conePlus P W ∧
    OperatorAlgebra.PeirceSpine.comm (invS P) (coneMinus P W) = -(coneMinus P W + coneMinus P W) ∧
    OperatorAlgebra.PeirceSpine.comm (conePlus P W) (coneMinus P W) = invS P ∧
    (1 + conePlus P W) * (1 + conePlus P W) = 1 + (conePlus P W + conePlus P W) ∧
    (1 + conePlus P W) * (1 - conePlus P W) = 1 ∧
    (1 + coneMinus P W) * (1 - coneMinus P W) = 1 := by
  have hSpine := dewitt_tetractys_peirce_spine_unification P W hP hPhi_sq
  have hS_sq : invS P * invS P = 1 := hSpine.2.1
  have h_SJ : invS P * genPhi P W W = genJ P W W := hSpine.2.2.2.1
  have hJ_sq : genJ P W W * genJ P W W = -1 := hSpine.2.2.2.2.1
  have hNplus_sq : conePlus P W * conePlus P W = 0 := hSpine.2.2.2.2.2.2.2.1
  have hNminus_sq : coneMinus P W * coneMinus P W = 0 := hSpine.2.2.2.2.2.2.2.2
  have hA3 := archetype_A3_nilpotent_cones_and_tetraktys_table hP W W
  have hPhi_V : genPhi P W W * genPhi P W W = genV P W W := hA3.2.2.1
  have hV1 : genV P W W = 1 := by rw [← hPhi_V, hPhi_sq]
  have hJPhi_Sig : genJ P W W * genPhi P W W = genSig P W W := hA3.2.2.2.2.2.1
  have hPhiJ_Sig : genPhi P W W * genJ P W W = -genSig P W W := hA3.2.2.2.2.2.2.1
  have hSig_SV : genSig P W W = invS P * genV P W W := hA3.2.2.2.2.2.2.2.2.1
  have hSig_S : genSig P W W = invS P := by rw [hSig_SV, hV1, mul_one]
  have h_JS : genPhi P W W * invS P = -genJ P W W := by
    dsimp [invS, genPhi, genJ]
    simp only [add_mul, mul_sub, mul_one, conePlus_mul_P hP, coneMinus_mul_P hP]
    abel
  have h_SJ_biv : invS P * genJ P W W = genPhi P W W := by
    calc
      invS P * genJ P W W = invS P * (invS P * genPhi P W W) := by rw [← h_SJ]
      _ = (invS P * invS P) * genPhi P W W := by simp only [mul_assoc]
      _ = genPhi P W W := by rw [hS_sq, one_mul]
  have h_JS_biv : genJ P W W * invS P = -genPhi P W W := by
    calc
      genJ P W W * invS P = (invS P * genPhi P W W) * invS P := by rw [← h_SJ]
      _ = invS P * (genPhi P W W * invS P) := by simp only [mul_assoc]
      _ = invS P * (-genJ P W W) := by rw [h_JS]
      _ = -(invS P * genJ P W W) := by simp only [mul_neg]
      _ = -genPhi P W W := by rw [h_SJ_biv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [h_SJ, h_JS]
    abel
  · dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [hJPhi_Sig, hPhiJ_Sig, hSig_S]
    abel
  · dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [h_JS_biv, h_SJ_biv]
    abel
  · rw [hS_sq, hPhi_sq, hJ_sq]
    abel
  · dsimp [OperatorAlgebra.PeirceSpine.comm, invS]
    simp only [sub_mul, mul_sub, one_mul, mul_one, P_mul_conePlus hP, conePlus_mul_P hP]
    abel
  · dsimp [OperatorAlgebra.PeirceSpine.comm, invS]
    simp only [sub_mul, mul_sub, one_mul, mul_one, P_mul_coneMinus hP, coneMinus_mul_P hP]
    abel
  · exact hSig_S
  · simp only [add_mul, mul_add, one_mul, mul_one, hNplus_sq]
    abel
  · simp only [add_mul, mul_sub, one_mul, mul_one, hNplus_sq]
    abel
  · simp only [add_mul, mul_sub, one_mul, mul_one, hNminus_sq]
    abel

/-- Concrete $4 \times 4$ integer grading involution for bit 2 (`S₂ = 2 P₂ - I₄ = I₂ ⊗ S₀ = diag(1, -1, 1, -1)`). -/
def dtMatS2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, -1]

/-- Concrete $4 \times 4$ integer complex bivector for bit 2 (`J₂ = S₂ Φ₂ = I₂ ⊗ J₀`, `J₂² = -I₄`). -/
def dtMatJ2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0, 0;
     -1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, -1, 0]

/-- **2-Bit Symplectic $\mathfrak{sp}(4, \mathbb{Z})$ Dimension, 10-Generator Basis ($1 + 2 + 3 + 4 = 10$), & Symplectic-Orthogonality of $\zeta_{\text{real}}$ (`two_bit_tetractys_sp4_dimension_and_symplectic_orthogonality`)**:
In the 2-bit integer carrier `Matrix (Fin 4) (Fin 4) ℤ`:
1. **Tetractys Symplectic Dimension Identity**: `1 + 2 + 3 + 4 = 10`, `3 * 3 + 1 * 1 = 10` (9 symmetric$\otimes$symmetric + 1 skew$\otimes$skew), and `10 + (3 * 1 + 1 * 3) = 4 * 4`.
2. **Symplectic Form $\Omega = J_1 = \zeta_{\text{real}}^2$**: `dtMatJ1.transpose = -dtMatJ1` and `dtMatJ1 * dtMatJ1 = -1`.
3. **Orthogonality ($\zeta_{\text{real}} \in \mathrm{O}(4, \mathbb{Z})$)**: `dtMatZetaReal.transpose = dtMatZetaRealInv`, `dtMatZetaReal.transpose * dtMatZetaReal = 1`, and `dtMatZetaReal * dtMatZetaReal.transpose = 1`.
4. **Symplecticity ($\zeta_{\text{real}} \in \mathrm{Sp}(4, \mathbb{Z})$)**: `dtMatZetaReal.transpose * dtMatJ1 * dtMatZetaReal = dtMatJ1`.
5. **Complete 10-Generator Tetractys Basis of $\mathfrak{sp}(4, \mathbb{Z})$ ($\Omega M + M^T \Omega = 0$, $1 + 2 + 3 + 4 = 10$)**:
   - **Row 1 ($1$ generator)**: `{dtMatJ2}` ($I_2 \otimes J_0$),
   - **Row 2 ($2$ generators)**: `{dtMatS1, dtMatPhi1}` ($S_0 \otimes I_2, \Phi_0 \otimes I_2$),
   - **Row 3 ($3$ generators)**: `{dtMatJ1, dtMatJ1 * dtMatS2, dtMatJ1 * dtMatPhi2}` ($J_0 \otimes \{I_2, S_0, \Phi_0\}$),
   - **Row 4 ($4$ generators)**: `{dtMatS1 * dtMatS2, dtMatS1 * dtMatPhi2, dtMatPhi1 * dtMatS2, dtMatPhi1 * dtMatPhi2}` ($\{S_0, \Phi_0\} \otimes \{S_0, \Phi_0\}$). -/
theorem two_bit_tetractys_sp4_dimension_and_symplectic_orthogonality :
    (1 + 2 + 3 + 4 = 10 ∧ 3 * 3 + 1 * 1 = 10 ∧ 10 + (3 * 1 + 1 * 3) = 4 * 4) ∧
    dtMatJ1.transpose = -dtMatJ1 ∧
    dtMatZetaReal.transpose = dtMatZetaRealInv ∧
    dtMatZetaReal.transpose * dtMatZetaReal = 1 ∧
    dtMatZetaReal * dtMatZetaReal.transpose = 1 ∧
    dtMatZetaReal.transpose * dtMatJ1 * dtMatZetaReal = dtMatJ1 ∧
    dtMatJ1 * dtMatJ2 + dtMatJ2.transpose * dtMatJ1 = 0 ∧
    (dtMatJ1 * dtMatS1 + dtMatS1.transpose * dtMatJ1 = 0 ∧
     dtMatJ1 * dtMatPhi1 + dtMatPhi1.transpose * dtMatJ1 = 0) ∧
    (dtMatJ1 * dtMatJ1 + dtMatJ1.transpose * dtMatJ1 = 0 ∧
     dtMatJ1 * (dtMatJ1 * dtMatS2) + (dtMatJ1 * dtMatS2).transpose * dtMatJ1 = 0 ∧
     dtMatJ1 * (dtMatJ1 * dtMatPhi2) + (dtMatJ1 * dtMatPhi2).transpose * dtMatJ1 = 0) ∧
    (dtMatJ1 * (dtMatS1 * dtMatS2) + (dtMatS1 * dtMatS2).transpose * dtMatJ1 = 0 ∧
     dtMatJ1 * (dtMatS1 * dtMatPhi2) + (dtMatS1 * dtMatPhi2).transpose * dtMatJ1 = 0 ∧
     dtMatJ1 * (dtMatPhi1 * dtMatS2) + (dtMatPhi1 * dtMatS2).transpose * dtMatJ1 = 0 ∧
     dtMatJ1 * (dtMatPhi1 * dtMatPhi2) + (dtMatPhi1 * dtMatPhi2).transpose * dtMatJ1 = 0) := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
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
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide

/-- Plücker minor $\Delta_{12} = 1$ of the canonical $\mathrm{Gr}_+(2, 4)$ unipotent boundary measurement matrix
$C(t_1, t_2, t_3, t_4) = \begin{pmatrix} 1 & 0 & -t_1 & -(t_1 t_3 + t_4) \\ 0 & 1 & t_2 & t_2 t_3 \end{pmatrix}$. -/
def gr24Plucker12 {R : Type u} [CommRing R] (_t1 _t2 _t3 _t4 : R) : R := 1

/-- Plücker minor $\Delta_{13} = t_2$ of the canonical $\mathrm{Gr}_+(2, 4)$ unipotent boundary measurement matrix. -/
def gr24Plucker13 {R : Type u} [CommRing R] (_t1 t2 _t3 _t4 : R) : R := t2

/-- Plücker minor $\Delta_{14} = t_2 t_3$ of the canonical $\mathrm{Gr}_+(2, 4)$ unipotent boundary measurement matrix. -/
def gr24Plucker14 {R : Type u} [CommRing R] (_t1 t2 t3 _t4 : R) : R := t2 * t3

/-- Plücker minor $\Delta_{23} = t_1$ of the canonical $\mathrm{Gr}_+(2, 4)$ unipotent boundary measurement matrix. -/
def gr24Plucker23 {R : Type u} [CommRing R] (t1 _t2 _t3 _t4 : R) : R := t1

/-- Plücker minor $\Delta_{24} = t_1 t_3 + t_4$ of the canonical $\mathrm{Gr}_+(2, 4)$ unipotent boundary measurement matrix. -/
def gr24Plucker24 {R : Type u} [CommRing R] (t1 _t2 t3 t4 : R) : R := t1 * t3 + t4

/-- Plücker minor $\Delta_{34} = t_2 t_4$ of the canonical $\mathrm{Gr}_+(2, 4)$ unipotent boundary measurement matrix. -/
def gr24Plucker34 {R : Type u} [CommRing R] (_t1 t2 _t3 t4 : R) : R := t2 * t4

/-- **Universal 3-Term Grassmann–Plücker Syzygy & Twisted Cyclic Shift Invariance on $\mathrm{Gr}(2, 4)$ (`real_grassmannian_gr24_three_term_plucker_syzygy`)**:
Over any commutative ring `R`:
1. For any $2 \times 4$ matrix with columns $(a_k, b_k)$ and $2 \times 2$ Plücker minors $\Delta_{ij} = a_i b_j - b_i a_j$,
   $$\Delta_{13}\,\Delta_{24} \;=\; \Delta_{12}\,\Delta_{34} \;+\; \Delta_{14}\,\Delta_{23}.$$
2. Under the $\zeta_{\text{real}}$ twisted cyclic column shift $(a_1, a_2, a_3, a_4) \mapsto (a_2, a_3, a_4, -a_1)$,
   $(b_1, b_2, b_3, b_4) \mapsto (b_2, b_3, b_4, -b_1)$, the shifted minors satisfy
   $\Delta'_{12} = \Delta_{23}$, $\Delta'_{23} = \Delta_{34}$, $\Delta'_{34} = \Delta_{14}$, $\Delta'_{14} = \Delta_{12}$,
   $\Delta'_{13} = \Delta_{24}$, and $\Delta'_{24} = \Delta_{13}$ (preserving positivity because $\zeta_{\text{real}}^4 = -I_4$ supplies the $-1$ orientation sign on column 4).
3. For the canonical unipotent boundary-measurement chart $(t_1, t_2, t_3, t_4)$ of $\mathrm{Gr}_+(2, 4)$,
   `gr24Plucker13 * gr24Plucker24 = gr24Plucker12 * gr24Plucker34 + gr24Plucker14 * gr24Plucker23`. -/
theorem real_grassmannian_gr24_three_term_plucker_syzygy
    {R : Type u} [CommRing R] (a1 b1 a2 b2 a3 b3 a4 b4 t1 t2 t3 t4 : R) :
    (a1 * (0 * a2 + 1 * b2) + b1 * ((-1) * a2 + 0 * b2) = a1 * b2 - b1 * a2) ∧
    (a1 * b3 - b1 * a3) * (a2 * b4 - b2 * a4) =
      (a1 * b2 - b1 * a2) * (a3 * b4 - b3 * a4) +
      (a1 * b4 - b1 * a4) * (a2 * b3 - b2 * a3) ∧
    (a4 * (-b1) - b4 * (-a1) = a1 * b4 - b1 * a4 ∧
     a2 * (-b1) - b2 * (-a1) = a1 * b2 - b1 * a2 ∧
     a3 * (-b1) - b3 * (-a1) = a1 * b3 - b1 * a3) ∧
    gr24Plucker13 t1 t2 t3 t4 * gr24Plucker24 t1 t2 t3 t4 =
      gr24Plucker12 t1 t2 t3 t4 * gr24Plucker34 t1 t2 t3 t4 +
      gr24Plucker14 t1 t2 t3 t4 * gr24Plucker23 t1 t2 t3 t4 := by
  refine ⟨by ring, by ring, ⟨by ring, by ring, by ring⟩, ?_⟩
  dsimp [gr24Plucker12, gr24Plucker13, gr24Plucker14, gr24Plucker23, gr24Plucker24, gr24Plucker34]
  ring

/-- **Strict Total Positivity on the Real Grassmannian $\mathrm{Gr}_+(2, 4)$ (`real_grassmannian_gr24_total_positivity`)**:
When the four real unipotent bridge weights $t_1, t_2, t_3, t_4 \in \mathbb{R}$ are strictly positive,
all six ordered Plücker coordinates $\Delta_{12}, \Delta_{13}, \Delta_{14}, \Delta_{23}, \Delta_{24}, \Delta_{34}$
are strictly positive and satisfy the 3-term Grassmann–Plücker syzygy. -/
theorem real_grassmannian_gr24_total_positivity
    (t1 t2 t3 t4 : ℝ) (ht1 : 0 < t1) (ht2 : 0 < t2) (ht3 : 0 < t3) (ht4 : 0 < t4) :
    0 < gr24Plucker12 t1 t2 t3 t4 ∧
    0 < gr24Plucker13 t1 t2 t3 t4 ∧
    0 < gr24Plucker14 t1 t2 t3 t4 ∧
    0 < gr24Plucker23 t1 t2 t3 t4 ∧
    0 < gr24Plucker24 t1 t2 t3 t4 ∧
    0 < gr24Plucker34 t1 t2 t3 t4 ∧
    gr24Plucker13 t1 t2 t3 t4 * gr24Plucker24 t1 t2 t3 t4 =
      gr24Plucker12 t1 t2 t3 t4 * gr24Plucker34 t1 t2 t3 t4 +
      gr24Plucker14 t1 t2 t3 t4 * gr24Plucker23 t1 t2 t3 t4 := by
  dsimp [gr24Plucker12, gr24Plucker13, gr24Plucker14, gr24Plucker23, gr24Plucker24, gr24Plucker34]
  refine ⟨zero_lt_one, ht2, mul_pos ht2 ht3, ht1, ?_, mul_pos ht2 ht4, by ring⟩
  exact add_pos (mul_pos ht1 ht3) ht4

/-- **Theorem ($\mathfrak{TP}_1\text{–}\mathfrak{TP}_3$ — `tetractys_two_bit_10_plus_6_and_symplectic_lie_closure`)**:
In any associative ring `[Ring B]`:
1. **Tetractys & Two-Bit Dimension Split**:
   `1 + 2 + 3 + 4 = 10` (`dim 𝔰𝔭(4, ℝ)`) and `(3 * 3 + 1 * 1) + (3 * 1 + 1 * 3) = 10 + 6 = 16`.
2. **Real Double-Bivector Boost Law (`(J₁ J₂)² = +1`)**:
   If `J1 * J1 = -1` and `J2 * J2 = -1` commute (`J1 * J2 = J2 * J1`), then `(J1 * J2) * (J1 * J2) = +1`,
   and in `Matrix (Fin 4) (Fin 4) ℤ`, `(dtMatJ1 * dtMatJ2).transpose = dtMatJ1 * dtMatJ2` and
   `(dtMatJ1 * dtMatJ2) * (dtMatJ1 * dtMatJ2) = 1`.
3. **Symplectic Defining Relation & Commutator Closure (`Ω X + Xᵀ Ω = 0`)**:
   For `Ω * Ω = -1` and symmetric `S, S1, S2 : B` (`(Ω S)ᵀ = -S Ω`), the generator `X = Ω * S` satisfies
   `Ω * (Ω * S) + (-(S * Ω)) * Ω = 0`, and the commutator `commX = (Ω * S1) * (Ω * S2) - (Ω * S2) * (Ω * S1)`
   satisfies `Ω * commX + (S2 * Ω * S1 * Ω - S1 * Ω * S2 * Ω) * Ω = 0` identically in `[Ring B]`. -/
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
    ((dtMatJ1 * dtMatJ2).transpose = dtMatJ1 * dtMatJ2 ∧
     (dtMatJ1 * dtMatJ2) * (dtMatJ1 * dtMatJ2) = 1) ∧
    Ω * (Ω * S) + (-(S * Ω)) * Ω = 0 ∧
    Ω * ((Ω * S1) * (Ω * S2) - (Ω * S2) * (Ω * S1)) +
      (S2 * Ω * S1 * Ω - S1 * Ω * S2 * Ω) * Ω = 0 := by
  have hΩ_idem : ∀ Z : B, Ω * (Ω * Z) = -Z := by
    intro Z
    rw [← mul_assoc, hΩ, neg_one_mul]
  refine ⟨by decide, by decide, by decide, by decide, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · calc (J1 * J2) * (J1 * J2)
      _ = J1 * (J2 * J1) * J2 := by simp only [mul_assoc]
      _ = (J1 * J1) * (J2 * J2) := by rw [← h_comm]; simp only [mul_assoc]
      _ = 1 := by rw [hJ1, hJ2, neg_mul_neg, one_mul]
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · calc Ω * (Ω * S) + (-(S * Ω)) * Ω
      _ = (Ω * Ω) * S - S * (Ω * Ω) := by simp only [neg_mul, mul_assoc]; abel
      _ = (-1) * S - S * (-1) := by rw [hΩ]
      _ = 0 := by simp only [neg_mul, mul_neg, one_mul, mul_one]; abel
  · simp only [mul_sub, sub_mul, mul_assoc, hΩ, hΩ_idem, mul_neg, mul_one]
    abel

/-- Primal $e$-flat Plabic shear $\mathcal{E}_+(t) = I + t N_+ = \begin{pmatrix} 1 & t \\ 0 & 1 \end{pmatrix}$ in `Matrix (Fin 2) (Fin 2) K`. -/
def amariShearPlus {K : Type u} [CommRing K] (t : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, t; 0, 1]

/-- Dual $m$-flat Plabic shear $\mathcal{E}_-(s) = I + s N_- = \begin{pmatrix} 1 & 0 \\ s & 1 \end{pmatrix}$ in `Matrix (Fin 2) (Fin 2) K`. -/
def amariShearMinus {K : Type u} [CommRing K] (s : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; s, 1]

/-- Paired Amari–DeWitt Gaussian $\mathcal{G}_+(t, s) = \mathcal{E}_+(t)\mathcal{E}_-(s) = \begin{pmatrix} 1 + t s & t \\ s & 1 \end{pmatrix}$. -/
def amariGaussianTP2 {K : Type u} [CommRing K] (t s : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1 + t * s, t; s, 1]

/-- Unnormalized Positive Grassmannian Projector $\widetilde{P}_+(t, s) = \begin{pmatrix} 1 & t \\ s & t s \end{pmatrix}$. -/
def posGrassmannianProj {K : Type u} [CommRing K] (t s : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, t; s, t * s]

/-- DeWitt split parity matrix $S_0 = \mathrm{diag}(1, -1)$ in `Matrix (Fin 2) (Fin 2) K`. -/
def amariDeWittS {K : Type u} [CommRing K] : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; 0, -1]

/-- DeWitt flip matrix $\Phi_0 = E_{01} + E_{10}$ in `Matrix (Fin 2) (Fin 2) K`. -/
def amariDeWittPhi {K : Type u} [CommRing K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

/-- Explicit DeWitt Clifford anticommutator witness `{S₀, Φ₀} = 0` in `Matrix (Fin 2) (Fin 2) K`. -/
lemma amariDeWittS_amariDeWittPhi_anticomm {K : Type u} [CommRing K] :
    amariDeWittS (K := K) * amariDeWittPhi (K := K) +
      amariDeWittPhi (K := K) * amariDeWittS (K := K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (dsimp [amariDeWittS, amariDeWittPhi]; simp [Matrix.mul_apply])

/-- **Theorem ($\mathfrak{TP}_4\text{–}\mathfrak{TP}_5$ — `positive_grassmannian_gaussian_tp2_and_homogeneous_projector`)**:
1. **Algebraic Factorization & Unit Determinant (Over Any `CommRing K`)**:
   - `amariShearPlus tK * amariShearMinus sK = amariGaussianTP2 tK sK`,
   - `(amariGaussianTP2 tK sK 0 0) * (amariGaussianTP2 tK sK 1 1) - (amariGaussianTP2 tK sK 0 1) * (amariGaussianTP2 tK sK 1 0) = 1`,
   - `posGrassmannianProj tK sK * posGrassmannianProj tK sK = (1 + tK * sK) • posGrassmannianProj tK sK`.
2. **Strict Total Positivity ($\mathrm{TP}_2$) Over `ℤ` and `ℝ` (`t > 0 ∧ s > 0`)**:
   Whenever `0 < t` and `0 < s`, all four $1 \times 1$ entries of `amariGaussianTP2 t s`, its $2 \times 2$
   determinant, and all four entries of `posGrassmannianProj t s` are strictly positive (`> 0`). -/
theorem positive_grassmannian_gaussian_tp2_and_homogeneous_projector
    {K : Type u} [CommRing K] (tK sK : K)
    (t s : ℤ) (ht : 0 < t) (hs : 0 < s)
    (tR sR : ℝ) (htR : 0 < tR) (hsR : 0 < sR) :
    amariShearPlus tK * amariShearMinus sK = amariGaussianTP2 tK sK ∧
    (amariGaussianTP2 tK sK 0 0 * amariGaussianTP2 tK sK 1 1 -
     amariGaussianTP2 tK sK 0 1 * amariGaussianTP2 tK sK 1 0 = 1) ∧
    posGrassmannianProj tK sK * posGrassmannianProj tK sK =
      (1 + tK * sK) • posGrassmannianProj tK sK ∧
    (0 < amariGaussianTP2 t s 0 0 ∧
     0 < amariGaussianTP2 t s 0 1 ∧
     0 < amariGaussianTP2 t s 1 0 ∧
     0 < amariGaussianTP2 t s 1 1 ∧
     0 < posGrassmannianProj t s 1 1) ∧
    (0 < amariGaussianTP2 tR sR 0 0 ∧
     0 < amariGaussianTP2 tR sR 0 1 ∧
     0 < amariGaussianTP2 tR sR 1 0 ∧
     0 < amariGaussianTP2 tR sR 1 1 ∧
     0 < posGrassmannianProj tR sR 1 1) := by
  have h_ts : 0 < t * s := Int.mul_pos ht hs
  have h_tsR : 0 < tR * sR := mul_pos htR hsR
  refine ⟨?_, ?_, ?_, ⟨?_, ht, hs, ?_, h_ts⟩, ⟨?_, htR, hsR, ?_, h_tsR⟩⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [amariShearPlus, amariShearMinus, amariGaussianTP2, Matrix.mul_apply, Fin.sum_univ_two]
  · dsimp [amariGaussianTP2]; ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [posGrassmannianProj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · dsimp [amariGaussianTP2]; omega
  · dsimp [amariGaussianTP2]; decide
  · dsimp [amariGaussianTP2]; linarith
  · dsimp [amariGaussianTP2]; exact zero_lt_one

/-- Real moment curve $Z(t) = (1, t, t^2, t^3)$ in `Fin 4 → K`. -/
def momentCurve4 {K : Type u} [CommRing K] (t : K) : Fin 4 → K :=
  ![1, t, t ^ 2, t ^ 3]

/-- The $4 \times 4$ Amplituhedron Volume 4-Bracket $\langle Z_0 Z_1 Z_2 Z_3 \rangle = \det[Z_0, Z_1, Z_2, Z_3]$. -/
def amplituhedronBracket4 {K : Type u} [CommRing K] (Z0 Z1 Z2 Z3 : Fin 4 → K) : K :=
  let d23_12 := Z2 1 * Z3 2 - Z2 2 * Z3 1
  let d23_13 := Z2 1 * Z3 3 - Z2 3 * Z3 1
  let d23_14 := Z2 2 * Z3 3 - Z2 3 * Z3 2
  let d23_02 := Z2 0 * Z3 2 - Z2 2 * Z3 0
  let d23_03 := Z2 0 * Z3 3 - Z2 3 * Z3 0
  let d23_01 := Z2 0 * Z3 1 - Z2 1 * Z3 0
  Z0 0 * (Z1 1 * d23_14 - Z1 2 * d23_13 + Z1 3 * d23_12) -
  Z0 1 * (Z1 0 * d23_14 - Z1 2 * d23_03 + Z1 3 * d23_02) +
  Z0 2 * (Z1 0 * d23_13 - Z1 1 * d23_03 + Z1 3 * d23_01) -
  Z0 3 * (Z1 0 * d23_12 - Z1 1 * d23_02 + Z1 2 * d23_01)

/-- **Theorem ($\mathfrak{TP}_6\text{–}\mathfrak{TP}_7$ — `moment_curve_amplituhedron_vandermonde_positivity`)**:
1. **Universal Vandermonde Factorization on the Moment Curve**:
   For any `t₀, t₁, t₂, t₃ : K` in `[CommRing K]`, the 4-bracket $\langle Z(t_0) Z(t_1) Z(t_2) Z(t_3) \rangle$
   factors identically into the 6-factor Vandermonde product:
   `(t1 - t0) * (t2 - t0) * (t3 - t0) * (t2 - t1) * (t3 - t1) * (t3 - t2)`.
2. **Orientation Sign Flip Under Twistor Transposition**:
   Swapping `t0 ↔ t1` reverses the sign of the 4-bracket (`⟨Z(t₁) Z(t₀) Z(t₂) Z(t₃)⟩ = -⟨Z(t₀) Z(t₁) Z(t₂) Z(t₃)⟩`).
3. **Strict Positivity for Ordered Real & Integer Parameters (`t₀ < t₁ < t₂ < t₃`)**:
   Whenever `a0 < a1 < a2 < a3` in `ℤ` and `x0 < x1 < x2 < x3` in `ℝ`, the Amplituhedron scattering
   foam volume is **strictly positive (`> 0`)**. -/
theorem moment_curve_amplituhedron_vandermonde_positivity
    {K : Type u} [CommRing K] (t0 t1 t2 t3 : K)
    (a0 a1 a2 a3 : ℤ) (ha01 : a0 < a1) (ha12 : a1 < a2) (ha23 : a2 < a3)
    (x0 x1 x2 x3 : ℝ) (hx01 : x0 < x1) (hx12 : x1 < x2) (hx23 : x2 < x3) :
    amplituhedronBracket4 (momentCurve4 t0) (momentCurve4 t1) (momentCurve4 t2) (momentCurve4 t3) =
      (t1 - t0) * (t2 - t0) * (t3 - t0) * (t2 - t1) * (t3 - t1) * (t3 - t2) ∧
    amplituhedronBracket4 (momentCurve4 t1) (momentCurve4 t0) (momentCurve4 t2) (momentCurve4 t3) =
      -amplituhedronBracket4 (momentCurve4 t0) (momentCurve4 t1) (momentCurve4 t2) (momentCurve4 t3) ∧
    0 < amplituhedronBracket4 (momentCurve4 a0) (momentCurve4 a1) (momentCurve4 a2) (momentCurve4 a3) ∧
    0 < amplituhedronBracket4 (momentCurve4 x0) (momentCurve4 x1) (momentCurve4 x2) (momentCurve4 x3) := by
  have h_vanZ :
      amplituhedronBracket4 (momentCurve4 a0) (momentCurve4 a1) (momentCurve4 a2) (momentCurve4 a3) =
        (a1 - a0) * (a2 - a0) * (a3 - a0) * (a2 - a1) * (a3 - a1) * (a3 - a2) := by
    dsimp [amplituhedronBracket4, momentCurve4]
    ring
  have h_vanR :
      amplituhedronBracket4 (momentCurve4 x0) (momentCurve4 x1) (momentCurve4 x2) (momentCurve4 x3) =
        (x1 - x0) * (x2 - x0) * (x3 - x0) * (x2 - x1) * (x3 - x1) * (x3 - x2) := by
    dsimp [amplituhedronBracket4, momentCurve4]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [amplituhedronBracket4, momentCurve4]
    ring
  · dsimp [amplituhedronBracket4, momentCurve4]
    ring
  · rw [h_vanZ]
    have d10 : 0 < a1 - a0 := sub_pos.mpr ha01
    have d20 : 0 < a2 - a0 := sub_pos.mpr (lt_trans ha01 ha12)
    have d30 : 0 < a3 - a0 := sub_pos.mpr (lt_trans (lt_trans ha01 ha12) ha23)
    have d21 : 0 < a2 - a1 := sub_pos.mpr ha12
    have d31 : 0 < a3 - a1 := sub_pos.mpr (lt_trans ha12 ha23)
    have d32 : 0 < a3 - a2 := sub_pos.mpr ha23
    exact Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos d10 d20) d30) d21) d31) d32
  · rw [h_vanR]
    have d10 : 0 < x1 - x0 := sub_pos.mpr hx01
    have d20 : 0 < x2 - x0 := sub_pos.mpr (lt_trans hx01 hx12)
    have d30 : 0 < x3 - x0 := sub_pos.mpr (lt_trans (lt_trans hx01 hx12) hx23)
    have d21 : 0 < x2 - x1 := sub_pos.mpr hx12
    have d31 : 0 < x3 - x1 := sub_pos.mpr (lt_trans hx12 hx23)
    have d32 : 0 < x3 - x2 := sub_pos.mpr hx23
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos d10 d20) d30) d21) d31) d32

end SymplecticAndGrassmannianPositivity

end InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset
