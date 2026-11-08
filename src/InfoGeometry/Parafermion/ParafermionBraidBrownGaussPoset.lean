/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.Parafermion.TetraktysRealCarryMatrix

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Majorana-to-Parafermion Condensation, $\mathbb{Z}_4$ Braid Operators & Brown–Gauss Invariant Poset via the Tetraktys Complex Structure ($\mathfrak{PB}_1 \prec \dots \prec \mathfrak{PB}_7$)

This module formalizes the seven-stage causal poset ($\mathfrak{PB}_1 \prec \dots \prec \mathfrak{PB}_7$)
governing Majorana-to-parafermion condensation ($\mathbb{Z}_2 \times \mathbb{Z}_2 \to \mathbb{Z}_4$),
the Fendley–Jones $\mathbb{Z}_4$ braid operator $U(X)$, the Brown–Gauss sum shift ($c_- = 1/2 \to c_- = 1$),
and the $\mathbb{Z}_4$-graded quantum super-Grassmannian $(\eta_1 + \eta_2)^4 = \eta_1^4 + \eta_2^4 = 0$,
replacing the scalar complex unit $i \in \mathbb{C}$ everywhere by the **Tetraktys complex structure**
$$\text{genJ}\;P_0\;A_0\;C_0 = \text{conePlus}\;P_0\;A_0 - \text{coneMinus}\;P_0\;C_0$$
from `InfoGeometry.OperatorAlgebra.PeirceSpine`.

## Mathematical Contract (Three-Bucket Audit)

### BUCKET 1: PROVED (0 sorry, 0 axioms)
- `pbStageRank`, `pbCoverIndicator`, `pbCoverEdge_acyclic`:
  7-stage acyclic Hasse poset spine on `Fin 7`.
- `tetraktysP0`, `tetraktysA0`, `tetraktysC0`, `tetraktysPhi0`, `tetraktysJ0`,
  `tetraktysPhi0_mul_tetraktysJ0_ne_comm`, `tetraktys_integer_complex_structure_laws`:
  Concrete $2 \times 2$ integer matrix realization of the Tetraktys `(Φ₀, J₀, V₀, Σ₀)` with
  `genV = 1`, `J₀² = -1`, `{Φ₀, J₀} = 0`, and `(1 + J₀)² = 2 J₀` over `Matrix (Fin 2) (Fin 2) ℤ`.
- `tauCarry`, `sigmaTetraktysPlus`, `sigmaTetraktysMinus`,
  `binary_carry_z4_parafermion_from_two_peirce_bits`:
  Proves that the binary carry operator $\tau = P_2 \Phi_2 + (1 - P_2)\Phi_1 \Phi_2$ satisfies
  $\tau^2 = \Phi_1$ and $\tau^4 = 1$, proves the off-shell Tetraktys Weyl braiding defect
  $\sigma_- \tau - J_0 \tau \sigma_- = (1 - V_0) P_2 \Phi_2 S_1$, and proves exact $\mathbb{Z}_4$
  Weyl braiding $\sigma_- \tau = J_0 \tau \sigma_-$ and $\tau \sigma_+ = J_0 \sigma_+ \tau$
  on the normalized Tetraktys shell $V_0 = \text{genV}\;P_0\;A_0\;C_0 = 1$.
- `tetraktysGaussZ2`, `BraidZ4_Raw`, `BraidZ4_Factored`, `BraidZ4_Dag`,
  `z4_parafermion_braid_and_brown_gauss_theorem`:
  Derives $J_0^2 = -1$, $\zeta^4 = -1$, and $\zeta^8 = 1$ from the Tetraktys law
  $\zeta^2 = \text{genJ}\;P_0\;A_0\;C_0$ and $\text{genV}\;P_0\;A_0\;C_0 = 1$, proves
  $G_2^2 = (1 + J_0)^2 = 2 J_0$ and $G_4 = 1 + \zeta + \zeta^4 + \zeta^9 = 2\zeta$, and proves
  the even/odd Peirce factorization and exact unitarity $(2U(X))(2U^\dagger(X)) = 4$ of the
  $\mathbb{Z}_4$ braid rotor.
- `z4_quantum_super_grassmannian_fourth_power_nilpotency`:
  Proves that when $\eta_1 \eta_2 = (\text{genJ}\;P_0\;A_0\;C_0)\,\eta_2 \eta_1$ on the normalized
  Tetraktys shell $\text{genV}\;P_0\;A_0\;C_0 = 1$, the 2-body square is weighted by the Tetraktys
  $\mathbb{Z}_2$ Gauss sum $1 + \text{genJ}\;P_0\;A_0\;C_0$ while all 4th-power cross-terms cancel
  identically: $(\eta_1 + \eta_2)^4 = \eta_1^4 + \eta_2^4$.

### BUCKET 2: CONDITIONAL / EXPLICIT OBLIGATIONS
- Generic associative ring theorems state idempotency `hP0 : P0 * P0 = P0`, normalized Tetraktys
  mass `hV0 : genV P0 A0 C0 = 1`, and mutual commutation hypotheses explicitly in their binders.

### BUCKET 3: OPEN RESEARCH / NON-CLAIMS
- Finite algebraic identities do not by themselves construct continuum conformal field theory
  correlators or analytical fractional quantum Hall Laughlin wavefunctions.
-/

namespace InfoGeometry.Parafermion.ParafermionBraidBrownGaussPoset

open Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine

universe u

/-! ## §1. Causal Poset Spine ($\mathfrak{PB}_1 \prec \dots \prec \mathfrak{PB}_7$) & Concrete Integer Tetraktys Realization -/

/-- Integer rank of each stage in `{0, …, 6}` on the 7-stage parafermion-Tetraktys spine `Fin 7`. -/
def pbStageRank (s : Fin 7) : ℕ :=
  s.val

/-- `pbStageRank` is strictly injective on `Fin 7`. -/
theorem pbStageRank_injective : Function.Injective pbStageRank := by
  intro a b h
  exact Fin.ext h

/-- Boolean indicator for immediate Hasse cover edges $\mathfrak{PB}_k \prec \mathfrak{PB}_{k+1}$ on `Fin 7`. -/
def pbCoverIndicator (a b : Fin 7) : Bool :=
  decide (b.val = a.val + 1)

/-- Every immediate Hasse cover edge on `Fin 7` increases `pbStageRank` by `1` and is strictly acyclic. -/
theorem pbCoverEdge_acyclic {a b : Fin 7} (h : pbCoverIndicator a b = true) :
    pbStageRank b = pbStageRank a + 1 ∧ pbStageRank a < pbStageRank b ∧ a ≠ b := by
  unfold pbCoverIndicator pbStageRank at *
  have hb : b.val = a.val + 1 := of_decide_eq_true h
  refine ⟨hb, by omega, ?_⟩
  intro hab
  subst hab
  omega

/-- Concrete $2 \times 2$ integer Peirce idempotent $P_0 = E_{00} = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def tetraktysP0 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, 0]

/-- Concrete $2 \times 2$ integer upper corner seed $A_0 = E_{01} = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$. -/
def tetraktysA0 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 0, 0]

/-- Concrete $2 \times 2$ integer lower corner seed $C_0 = E_{10} = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$. -/
def tetraktysC0 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 0; 1, 0]

/-- Concrete $2 \times 2$ integer Tetraktys solder operator $\Phi_0 = \text{genPhi}\;P_0\;A_0\;C_0 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def tetraktysPhi0 : Matrix (Fin 2) (Fin 2) ℤ :=
  genPhi tetraktysP0 tetraktysA0 tetraktysC0

/-- Concrete $2 \times 2$ integer Tetraktys complex structure $J_0 = \text{genJ}\;P_0\;A_0\;C_0 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$. -/
def tetraktysJ0 : Matrix (Fin 2) (Fin 2) ℤ :=
  genJ tetraktysP0 tetraktysA0 tetraktysC0

/-- Explicit non-commutativity witness: `tetraktysPhi0 * tetraktysJ0 ≠ tetraktysJ0 * tetraktysPhi0`. -/
lemma tetraktysPhi0_mul_tetraktysJ0_ne_comm :
    tetraktysPhi0 * tetraktysJ0 ≠ tetraktysJ0 * tetraktysPhi0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  revert h00
  decide

/-- Concrete $2 \times 2$ integer verification that the Tetraktys `(tetraktysP0, tetraktysA0, tetraktysC0)`
realizes a pure integer complex structure `tetraktysJ0 * tetraktysJ0 = -1` and the $\mathbb{Z}_2$
Brown–Gauss square `(1 + tetraktysJ0) * (1 + tetraktysJ0) = (2 : ℤ) • tetraktysJ0` without complex scalars. -/
theorem tetraktys_integer_complex_structure_laws :
    tetraktysP0 * tetraktysP0 = tetraktysP0 ∧
    genV tetraktysP0 tetraktysA0 tetraktysC0 = 1 ∧
    tetraktysPhi0 * tetraktysPhi0 = 1 ∧
    tetraktysJ0 * tetraktysJ0 = -1 ∧
    tetraktysPhi0 * tetraktysJ0 + tetraktysJ0 * tetraktysPhi0 = 0 ∧
    (1 + tetraktysJ0) * (1 + tetraktysJ0) = (2 : ℤ) • tetraktysJ0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> decide

/-- **Tetraktys Internal Hypercomplex & Complex Structure Law (`tetraktys_internal_hypercomplex_and_complex_structure`)**:
In any associative ring `B`, for any Peirce idempotent `P0 * P0 = P0` and corner seeds `A0, C0 : B`,
the Tetraktys provides both:
- an internal **hypercomplex split unit** `genPhi P0 A0 C0` satisfying `(genPhi P0 A0 C0)² = +genV P0 A0 C0`,
- an internal **complex structure** `genJ P0 A0 C0` satisfying `(genJ P0 A0 C0)² = -genV P0 A0 C0`,
- anticommutation `{genPhi, genJ} = 0` and nilpotent Grassmann combinations `(genPhi ± genJ)² = 0`,
so at unit horizon `genV P0 A0 C0 = 1`, `(genPhi)² = +1`, `(genJ)² = -1`, and `(1 + genJ)² = 2 genJ`
with fourth power `((1 + genJ)²)² = -(1 + 1 + 1 + 1)` without requiring any external complex field $\mathbb{C}$. -/
theorem tetraktys_internal_hypercomplex_and_complex_structure
    {B : Type u} [Ring B] (P0 A0 C0 : B) (hP0 : P0 * P0 = P0) :
    (genPhi P0 A0 C0 * genPhi P0 A0 C0 = genV P0 A0 C0 ∧
     genJ P0 A0 C0 * genJ P0 A0 C0 = -genV P0 A0 C0 ∧
     genPhi P0 A0 C0 * genJ P0 A0 C0 + genJ P0 A0 C0 * genPhi P0 A0 C0 = 0 ∧
     (genPhi P0 A0 C0 + genJ P0 A0 C0) * (genPhi P0 A0 C0 + genJ P0 A0 C0) = 0 ∧
     (genPhi P0 A0 C0 - genJ P0 A0 C0) * (genPhi P0 A0 C0 - genJ P0 A0 C0) = 0) ∧
    (genV P0 A0 C0 = 1 →
      genPhi P0 A0 C0 * genPhi P0 A0 C0 = 1 ∧
      genJ P0 A0 C0 * genJ P0 A0 C0 = -1 ∧
      (1 + genJ P0 A0 C0) * (1 + genJ P0 A0 C0) = genJ P0 A0 C0 + genJ P0 A0 C0 ∧
      ((1 + genJ P0 A0 C0) * (1 + genJ P0 A0 C0)) *
        ((1 + genJ P0 A0 C0) * (1 + genJ P0 A0 C0)) = -(1 + 1 + 1 + 1)) := by
  have hA3 := archetype_A3_nilpotent_cones_and_tetraktys_table hP0 A0 C0
  have hPhi_sq : genPhi P0 A0 C0 * genPhi P0 A0 C0 = genV P0 A0 C0 := hA3.2.2.1
  have hJ_sq : genJ P0 A0 C0 * genJ P0 A0 C0 = -genV P0 A0 C0 := hA3.2.2.2.1
  have h_anti : genPhi P0 A0 C0 * genJ P0 A0 C0 + genJ P0 A0 C0 * genPhi P0 A0 C0 = 0 :=
    hA3.2.2.2.2.2.2.2.1
  have h_nil_plus :
      (genPhi P0 A0 C0 + genJ P0 A0 C0) * (genPhi P0 A0 C0 + genJ P0 A0 C0) = 0 := by
    calc
      (genPhi P0 A0 C0 + genJ P0 A0 C0) * (genPhi P0 A0 C0 + genJ P0 A0 C0) =
          (genPhi P0 A0 C0 * genPhi P0 A0 C0 + genJ P0 A0 C0 * genJ P0 A0 C0) +
            (genPhi P0 A0 C0 * genJ P0 A0 C0 + genJ P0 A0 C0 * genPhi P0 A0 C0) := by
        simp only [add_mul, mul_add]
        abel
      _ = (genV P0 A0 C0 + -genV P0 A0 C0) + 0 := by rw [hPhi_sq, hJ_sq, h_anti]
      _ = 0 := by abel
  have h_nil_minus :
      (genPhi P0 A0 C0 - genJ P0 A0 C0) * (genPhi P0 A0 C0 - genJ P0 A0 C0) = 0 := by
    calc
      (genPhi P0 A0 C0 - genJ P0 A0 C0) * (genPhi P0 A0 C0 - genJ P0 A0 C0) =
          (genPhi P0 A0 C0 * genPhi P0 A0 C0 + genJ P0 A0 C0 * genJ P0 A0 C0) -
            (genPhi P0 A0 C0 * genJ P0 A0 C0 + genJ P0 A0 C0 * genPhi P0 A0 C0) := by
        simp only [sub_mul, mul_sub]
        abel
      _ = (genV P0 A0 C0 + -genV P0 A0 C0) - 0 := by rw [hPhi_sq, hJ_sq, h_anti]
      _ = 0 := by abel
  refine ⟨⟨hPhi_sq, hJ_sq, h_anti, h_nil_plus, h_nil_minus⟩, ?_⟩
  intro hV
  have hPhi1 : genPhi P0 A0 C0 * genPhi P0 A0 C0 = 1 := by rw [hPhi_sq, hV]
  have hJ1 : genJ P0 A0 C0 * genJ P0 A0 C0 = -1 := by rw [hJ_sq, hV]
  have hW_sq : (1 + genJ P0 A0 C0) * (1 + genJ P0 A0 C0) = genJ P0 A0 C0 + genJ P0 A0 C0 := by
    calc
      (1 + genJ P0 A0 C0) * (1 + genJ P0 A0 C0) =
          1 + (genJ P0 A0 C0 + genJ P0 A0 C0) + genJ P0 A0 C0 * genJ P0 A0 C0 := by
        simp only [add_mul, mul_add, one_mul, mul_one]; abel
      _ = 1 + (genJ P0 A0 C0 + genJ P0 A0 C0) + (-1) := by rw [hJ1]
      _ = genJ P0 A0 C0 + genJ P0 A0 C0 := by abel
  have hW_pow4 :
      ((1 + genJ P0 A0 C0) * (1 + genJ P0 A0 C0)) *
        ((1 + genJ P0 A0 C0) * (1 + genJ P0 A0 C0)) = -(1 + 1 + 1 + 1) := by
    rw [hW_sq]
    calc
      (genJ P0 A0 C0 + genJ P0 A0 C0) * (genJ P0 A0 C0 + genJ P0 A0 C0) =
          genJ P0 A0 C0 * genJ P0 A0 C0 + genJ P0 A0 C0 * genJ P0 A0 C0 +
            genJ P0 A0 C0 * genJ P0 A0 C0 + genJ P0 A0 C0 * genJ P0 A0 C0 := by
        simp only [add_mul, mul_add]; abel
      _ = (-1) + (-1) + (-1) + (-1) := by rw [hJ1]
      _ = -(1 + 1 + 1 + 1) := by abel
  exact ⟨hPhi1, hJ1, hW_sq, hW_pow4⟩

/-- Core two-corner DeWitt Tetractys relations for independent upper/lower seeds.
In any associative ring `B` with idempotent `P0 * P0 = P0` and corner seeds `A0, C0 : B`,
the four Tetractys elements `{1, invS P0, genPhi P0 A0 C0, genJ P0 A0 C0}` satisfy:
1. **Para-Complex Split Involution & Anticommutation**:
   `invS P0 * invS P0 = 1` and `invS P0 * genPhi P0 A0 C0 + genPhi P0 A0 C0 * invS P0 = 0`,
2. **Endogenous Complex Bivector Factorization (`J = S_P Φ`)**:
   `invS P0 * genPhi P0 A0 C0 = genJ P0 A0 C0` and `genPhi P0 A0 C0 * invS P0 = -genJ P0 A0 C0`,
3. **Inner Real Reflection as Complex Conjugation (`J ↦ -J`)**:
   `invS P0 * genJ P0 A0 C0 * invS P0 = -genJ P0 A0 C0`,
4. **Dual Nilpotent Rays (`N_+² = N_-² = 0`)**:
   `conePlus P0 A0 * conePlus P0 A0 = 0` and `coneMinus P0 C0 * coneMinus P0 C0 = 0`,
5. **Normalized Complex Square (`J² = -1` when `Φ² = 1`)**:
   `genPhi P0 A0 C0 * genPhi P0 A0 C0 = 1 → genJ P0 A0 C0 * genJ P0 A0 C0 = -1`. -/
theorem dewitt_tetractys_core_relations_for_two_corner_seeds
    {B : Type u} [Ring B] (P0 A0 C0 : B) (hP0 : P0 * P0 = P0) :
    invS P0 * invS P0 = 1 ∧
    invS P0 * genPhi P0 A0 C0 = genJ P0 A0 C0 ∧
    genPhi P0 A0 C0 * invS P0 = -genJ P0 A0 C0 ∧
    invS P0 * genPhi P0 A0 C0 + genPhi P0 A0 C0 * invS P0 = 0 ∧
    invS P0 * genJ P0 A0 C0 * invS P0 = -genJ P0 A0 C0 ∧
    conePlus P0 A0 * conePlus P0 A0 = 0 ∧
    coneMinus P0 C0 * coneMinus P0 C0 = 0 ∧
    (genPhi P0 A0 C0 * genPhi P0 A0 C0 = 1 → genJ P0 A0 C0 * genJ P0 A0 C0 = -1) := by
  have hS_sq : invS P0 * invS P0 = 1 :=
    (archetype_A2_peirce_cartan_grading_and_tangent_closure hP0 P0 P0).1
  have hA3 := archetype_A3_nilpotent_cones_and_tetraktys_table hP0 A0 C0
  have hP0_idem : ∀ Z : B, P0 * (P0 * Z) = P0 * Z := fun Z => by rw [← mul_assoc, hP0]
  have h_SJ : invS P0 * genPhi P0 A0 C0 = genJ P0 A0 C0 := by
    dsimp [invS, genPhi, genJ, conePlus, coneMinus]
    simp only [mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP0_idem]
    abel
  have h_JS : genPhi P0 A0 C0 * invS P0 = -genJ P0 A0 C0 := by
    dsimp [invS, genPhi, genJ, conePlus, coneMinus]
    simp only [add_mul, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP0]
    abel
  have h_anti : invS P0 * genPhi P0 A0 C0 + genPhi P0 A0 C0 * invS P0 = 0 := by
    rw [h_SJ, h_JS, add_neg_cancel]
  have h_conj : invS P0 * genJ P0 A0 C0 * invS P0 = -genJ P0 A0 C0 := by
    dsimp [invS, genJ, conePlus, coneMinus]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP0, hP0_idem]
    abel
  refine ⟨hS_sq, h_SJ, h_JS, h_anti, h_conj, hA3.1, hA3.2.1, ?_⟩
  intro hPhi1
  have hPhi_sq : genPhi P0 A0 C0 * genPhi P0 A0 C0 = genV P0 A0 C0 := hA3.2.2.1
  have hJ_sq : genJ P0 A0 C0 * genJ P0 A0 C0 = -genV P0 A0 C0 := hA3.2.2.2.1
  rw [hJ_sq, ← hPhi_sq, hPhi1]

/-! ## §2. Nodes $\mathfrak{PB}_1 \prec \mathfrak{PB}_2$: Binary-Carry Construction of $\mathbb{Z}_4$ Parafermions from Two Peirce Bits & Tetraktys Complex Structure -/

section BinaryCarryParafermion

variable {B : Type u} [Ring B]

/-- **Binary Carry Shift Operator (`tauCarry P2 Phi1 Phi2`)**:
Flips bit 2 via `Φ₂` when bit 2 is `0` (`P₂`), and flips BOTH bit 1 and bit 2 via `Φ₁ Φ₂`
when bit 2 is `1` (`1 - P₂`, executing the binary carry into bit 1). -/
def tauCarry (P2 Phi1 Phi2 : B) : B :=
  P2 * Phi2 + (1 - P2) * Phi1 * Phi2

/-- **Positive Tetraktys-Twisted Clock Operator (`sigmaTetraktysPlus P0 A0 C0 P1 P2`)**:
Replaces the scalar imaginary unit $i$ in $\sigma = S_1(P_2 + i(1 - P_2))$ with the Tetraktys
complex structure `genJ P0 A0 C0 = conePlus P0 A0 - coneMinus P0 C0`. -/
def sigmaTetraktysPlus (P0 A0 C0 P1 P2 : B) : B :=
  invS P1 * (P2 + genJ P0 A0 C0 * (1 - P2))

/-- **Negative Tetraktys-Twisted Clock Operator (`sigmaTetraktysMinus P0 A0 C0 P1 P2`)**:
$\sigma_- = S_1(P_2 - J_0(1 - P_2))$ with $J_0 = \text{genJ}\;P_0\;A_0\;C_0$ and $S_1 = \text{invS}\;P_1$. -/
def sigmaTetraktysMinus (P0 A0 C0 P1 P2 : B) : B :=
  invS P1 * (P2 - genJ P0 A0 C0 * (1 - P2))

/-- **Theorem 1 ($\mathfrak{PB}_1 \prec \mathfrak{PB}_2$ — `binary_carry_z4_parafermion_from_two_peirce_bits`)**:
Let `(P₁, Φ₁)` and `(P₂, Φ₂)` be two commuting Peirce bits (`P₁² = P₁`, `P₂² = P₂`, `Φ₁² = 1`, `Φ₂² = 1`,
`Φ₂ P₂ = (1 - P₂) Φ₂`, `invS P₁ * Φ₁ + Φ₁ * invS P₁ = 0`), and let `(P₀, A₀, C₀)` be a Tetraktys phase
system (`P₀² = P₀`) whose complex structure `genJ P0 A0 C0` commutes with the bit operators:
1. **Binary Carry Order-4 Shift Law ($\tau^2 = \Phi_1 \ne 1, \; \tau^4 = 1$)**:
   `tauCarry P2 Phi1 Phi2 * tauCarry P2 Phi1 Phi2 = Phi1` and
   `(tauCarry P2 Phi1 Phi2 * tauCarry P2 Phi1 Phi2) * (tauCarry P2 Phi1 Phi2 * tauCarry P2 Phi1 Phi2) = 1`.
2. **Off-Shell Tetraktys Clock Square & Weyl Braiding Defect**:
   Without assuming `genV P0 A0 C0 = 1`, the Tetraktys table `(genJ P0 A0 C0)² = -genV P0 A0 C0` yields:
   - `sigmaTetraktysMinus P0 A0 C0 P1 P2 * sigmaTetraktysMinus P0 A0 C0 P1 P2 = P2 - (1 - P2) * genV P0 A0 C0`,
   - `sigmaTetraktysMinus P0 A0 C0 P1 P2 * tauCarry P2 Phi1 Phi2 - genJ P0 A0 C0 * tauCarry P2 Phi1 Phi2 * sigmaTetraktysMinus P0 A0 C0 P1 P2 = P2 * Phi2 * invS P1 * (1 - genV P0 A0 C0)`.
3. **On-Shell Normalized Tetraktys Lock (`hV0 : genV P0 A0 C0 = 1`)**:
   - `genJ P0 A0 C0 * genJ P0 A0 C0 = -1`,
   - `sigmaTetraktysMinus P0 A0 C0 P1 P2 * sigmaTetraktysMinus P0 A0 C0 P1 P2 = invS P2` and fourth power `= 1`,
   - **Exact Tetraktys Weyl Braiding**:
     `sigmaTetraktysMinus P0 A0 C0 P1 P2 * tauCarry P2 Phi1 Phi2 = genJ P0 A0 C0 * tauCarry P2 Phi1 Phi2 * sigmaTetraktysMinus P0 A0 C0 P1 P2`
     and
     `tauCarry P2 Phi1 Phi2 * sigmaTetraktysPlus P0 A0 C0 P1 P2 = genJ P0 A0 C0 * sigmaTetraktysPlus P0 A0 C0 P1 P2 * tauCarry P2 Phi1 Phi2`. -/
theorem binary_carry_z4_parafermion_from_two_peirce_bits
    (P0 A0 C0 P1 P2 Phi1 Phi2 : B)
    (hP0 : P0 * P0 = P0)
    (hP1 : P1 * P1 = P1)
    (hP2 : P2 * P2 = P2)
    (hPhi1_sq : Phi1 * Phi1 = 1)
    (hPhi2_sq : Phi2 * Phi2 = 1)
    (h_swap2 : Phi2 * P2 = (1 - P2) * Phi2)
    (h_anticomm1 : invS P1 * Phi1 + Phi1 * invS P1 = 0)
    (h_comm_P : Phi1 * P2 = P2 * Phi1)
    (h_comm_Phi : Phi1 * Phi2 = Phi2 * Phi1)
    (h_S1_P2 : invS P1 * P2 = P2 * invS P1)
    (h_S1_Phi2 : invS P1 * Phi2 = Phi2 * invS P1)
    (h_J_S1 : genJ P0 A0 C0 * invS P1 = invS P1 * genJ P0 A0 C0)
    (h_J_P2 : genJ P0 A0 C0 * P2 = P2 * genJ P0 A0 C0)
    (h_J_Phi1 : genJ P0 A0 C0 * Phi1 = Phi1 * genJ P0 A0 C0)
    (h_J_Phi2 : genJ P0 A0 C0 * Phi2 = Phi2 * genJ P0 A0 C0) :
    (tauCarry P2 Phi1 Phi2 * tauCarry P2 Phi1 Phi2 = Phi1 ∧
     (tauCarry P2 Phi1 Phi2 * tauCarry P2 Phi1 Phi2) *
       (tauCarry P2 Phi1 Phi2 * tauCarry P2 Phi1 Phi2) = 1) ∧
    (sigmaTetraktysMinus P0 A0 C0 P1 P2 * sigmaTetraktysMinus P0 A0 C0 P1 P2 =
       P2 - (1 - P2) * genV P0 A0 C0 ∧
     sigmaTetraktysMinus P0 A0 C0 P1 P2 * tauCarry P2 Phi1 Phi2 -
       genJ P0 A0 C0 * tauCarry P2 Phi1 Phi2 * sigmaTetraktysMinus P0 A0 C0 P1 P2 =
       P2 * Phi2 * invS P1 * (1 - genV P0 A0 C0)) ∧
    (genV P0 A0 C0 = 1 →
      genJ P0 A0 C0 * genJ P0 A0 C0 = -1 ∧
      sigmaTetraktysMinus P0 A0 C0 P1 P2 * sigmaTetraktysMinus P0 A0 C0 P1 P2 = invS P2 ∧
      (sigmaTetraktysMinus P0 A0 C0 P1 P2 * sigmaTetraktysMinus P0 A0 C0 P1 P2) *
        (sigmaTetraktysMinus P0 A0 C0 P1 P2 * sigmaTetraktysMinus P0 A0 C0 P1 P2) = 1 ∧
      sigmaTetraktysMinus P0 A0 C0 P1 P2 * tauCarry P2 Phi1 Phi2 =
        genJ P0 A0 C0 * tauCarry P2 Phi1 Phi2 * sigmaTetraktysMinus P0 A0 C0 P1 P2 ∧
      tauCarry P2 Phi1 Phi2 * sigmaTetraktysPlus P0 A0 C0 P1 P2 =
        genJ P0 A0 C0 * sigmaTetraktysPlus P0 A0 C0 P1 P2 * tauCarry P2 Phi1 Phi2) := by
  have hP2_idem : ∀ Z : B, P2 * (P2 * Z) = P2 * Z := by
    intro Z; rw [← mul_assoc, hP2]
  have hPhi2_idem : ∀ Z : B, Phi2 * (Phi2 * Z) = Z := by
    intro Z; rw [← mul_assoc, hPhi2_sq, one_mul]
  have h_swap_assoc : ∀ Z : B, Phi2 * (P2 * Z) = (1 - P2) * (Phi2 * Z) := by
    intro Z; rw [← mul_assoc, h_swap2, mul_assoc]
  have h_comm_P_assoc : ∀ Z : B, Phi1 * (P2 * Z) = P2 * (Phi1 * Z) := by
    intro Z; rw [← mul_assoc, h_comm_P, mul_assoc]
  have h_comm_Phi_assoc : ∀ Z : B, Phi1 * (Phi2 * Z) = Phi2 * (Phi1 * Z) := by
    intro Z; rw [← mul_assoc, h_comm_Phi, mul_assoc]
  have h_tau2 : tauCarry P2 Phi1 Phi2 * tauCarry P2 Phi1 Phi2 = Phi1 := by
    dsimp [tauCarry]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, h_comm_Phi, h_comm_Phi_assoc, h_comm_P_assoc,
               h_swap_assoc, hP2, hP2_idem, hPhi2_sq, hPhi2_idem]
    abel
  have h_tau4 :
      (tauCarry P2 Phi1 Phi2 * tauCarry P2 Phi1 Phi2) *
        (tauCarry P2 Phi1 Phi2 * tauCarry P2 Phi1 Phi2) = 1 := by
    rw [h_tau2, hPhi1_sq]
  have hS1_sq : invS P1 * invS P1 = 1 :=
    (archetype_A2_peirce_cartan_grading_and_tangent_closure hP1 P1 P1).1
  have hS2_sq : invS P2 * invS P2 = 1 :=
    (archetype_A2_peirce_cartan_grading_and_tangent_closure hP2 P2 P2).1
  have hJ0_sq : genJ P0 A0 C0 * genJ P0 A0 C0 = -genV P0 A0 C0 :=
    (archetype_A3_nilpotent_cones_and_tetraktys_table hP0 A0 C0).2.2.2.1
  have hS1_idem : ∀ Z : B, invS P1 * (invS P1 * Z) = Z := by
    intro Z; rw [← mul_assoc, hS1_sq, one_mul]
  have hS1_Phi1 : invS P1 * Phi1 = -(Phi1 * invS P1) := by
    calc
      invS P1 * Phi1 = (invS P1 * Phi1 + Phi1 * invS P1) - Phi1 * invS P1 := by abel
      _ = 0 - Phi1 * invS P1 := by rw [h_anticomm1]
      _ = -(Phi1 * invS P1) := by abel
  have hS1_Phi1_assoc : ∀ Z : B, invS P1 * (Phi1 * Z) = -(Phi1 * (invS P1 * Z)) := by
    intro Z; rw [← mul_assoc, hS1_Phi1, neg_mul, mul_assoc]
  have h_S1_P2_assoc : ∀ Z : B, invS P1 * (P2 * Z) = P2 * (invS P1 * Z) := by
    intro Z; rw [← mul_assoc, h_S1_P2, mul_assoc]
  have h_S1_Phi2_assoc : ∀ Z : B, invS P1 * (Phi2 * Z) = Phi2 * (invS P1 * Z) := by
    intro Z; rw [← mul_assoc, h_S1_Phi2, mul_assoc]
  have h_J_S1_assoc : ∀ Z : B, genJ P0 A0 C0 * (invS P1 * Z) = invS P1 * (genJ P0 A0 C0 * Z) := by
    intro Z; rw [← mul_assoc, h_J_S1, mul_assoc]
  have h_J_P2_assoc : ∀ Z : B, genJ P0 A0 C0 * (P2 * Z) = P2 * (genJ P0 A0 C0 * Z) := by
    intro Z; rw [← mul_assoc, h_J_P2, mul_assoc]
  have h_J_Phi1_assoc : ∀ Z : B, genJ P0 A0 C0 * (Phi1 * Z) = Phi1 * (genJ P0 A0 C0 * Z) := by
    intro Z; rw [← mul_assoc, h_J_Phi1, mul_assoc]
  have h_J_Phi2_assoc : ∀ Z : B, genJ P0 A0 C0 * (Phi2 * Z) = Phi2 * (genJ P0 A0 C0 * Z) := by
    intro Z; rw [← mul_assoc, h_J_Phi2, mul_assoc]
  have h_sig_sq :
      sigmaTetraktysMinus P0 A0 C0 P1 P2 * sigmaTetraktysMinus P0 A0 C0 P1 P2 =
        P2 - (1 - P2) * genV P0 A0 C0 := by
    dsimp [sigmaTetraktysMinus]
    simp only [sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, h_S1_P2, h_S1_P2_assoc, h_J_S1, h_J_S1_assoc,
               h_J_P2, h_J_P2_assoc, hP2, hP2_idem, hS1_sq, hS1_idem,
               hJ0_sq, mul_neg]
    abel
  have h_weyl_defect :
      sigmaTetraktysMinus P0 A0 C0 P1 P2 * tauCarry P2 Phi1 Phi2 -
        genJ P0 A0 C0 * tauCarry P2 Phi1 Phi2 * sigmaTetraktysMinus P0 A0 C0 P1 P2 =
        P2 * Phi2 * invS P1 * (1 - genV P0 A0 C0) := by
    dsimp [sigmaTetraktysMinus, tauCarry]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, h_swap_assoc, h_comm_P_assoc,
               h_comm_Phi,
               h_S1_P2, h_S1_P2_assoc, h_S1_Phi2, h_S1_Phi2_assoc,
               hS1_Phi1, hS1_Phi1_assoc,
               h_J_S1, h_J_S1_assoc, h_J_P2, h_J_P2_assoc,
               h_J_Phi1, h_J_Phi2, h_J_Phi2_assoc,
               hP2_idem, hJ0_sq, mul_neg]
    abel
  refine ⟨⟨h_tau2, h_tau4⟩, ⟨h_sig_sq, h_weyl_defect⟩, ?_⟩
  intro hV0
  have hJ0_neg1 : genJ P0 A0 C0 * genJ P0 A0 C0 = -1 := by
    rw [hJ0_sq, hV0]
  have h_sig_S2 :
      sigmaTetraktysMinus P0 A0 C0 P1 P2 * sigmaTetraktysMinus P0 A0 C0 P1 P2 = invS P2 := by
    rw [h_sig_sq, hV0, mul_one]
    rfl
  have h_sig4 :
      (sigmaTetraktysMinus P0 A0 C0 P1 P2 * sigmaTetraktysMinus P0 A0 C0 P1 P2) *
        (sigmaTetraktysMinus P0 A0 C0 P1 P2 * sigmaTetraktysMinus P0 A0 C0 P1 P2) = 1 := by
    rw [h_sig_S2, hS2_sq]
  have h_weyl_minus :
      sigmaTetraktysMinus P0 A0 C0 P1 P2 * tauCarry P2 Phi1 Phi2 =
        genJ P0 A0 C0 * tauCarry P2 Phi1 Phi2 * sigmaTetraktysMinus P0 A0 C0 P1 P2 := by
    apply sub_eq_zero.mp
    rw [h_weyl_defect, hV0, sub_self, mul_zero]
  have h_weyl_plus :
      tauCarry P2 Phi1 Phi2 * sigmaTetraktysPlus P0 A0 C0 P1 P2 =
        genJ P0 A0 C0 * sigmaTetraktysPlus P0 A0 C0 P1 P2 * tauCarry P2 Phi1 Phi2 := by
    apply sub_eq_zero.mp
    dsimp [sigmaTetraktysPlus, tauCarry]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, h_swap_assoc, h_comm_P_assoc,
               h_comm_Phi,
               h_S1_P2, h_S1_P2_assoc, h_S1_Phi2_assoc,
               hS1_Phi1, hS1_Phi1_assoc,
               h_J_S1, h_J_S1_assoc, h_J_P2, h_J_P2_assoc,
               h_J_Phi1, h_J_Phi2, h_J_Phi2_assoc,
               hP2_idem, hJ0_neg1, neg_mul, mul_neg]
    abel
  exact ⟨hJ0_neg1, h_sig_S2, h_sig4, h_weyl_minus, h_weyl_plus⟩

end BinaryCarryParafermion

/-! ## A real eighth-root carry and reflection conjugation -/

section RealEighthRootCarry

variable {B : Type u} [Ring B]

open InfoGeometry.Parafermion.TetraktysRealCarryMatrix

/-- The modified two-bit carry in which the carry channel is the first bit's
endogenous complex structure `J`, rather than an involution `Φ₁`. -/
def realEighthRootCarry (P Φ J : B) : B :=
  P * Φ + (1 - P) * J * Φ

/-- The algebraic candidate for the inverse of `realEighthRootCarry`. -/
def realEighthRootCarryInv (P Φ J : B) : B :=
  (1 - P) * Φ - P * J * Φ

/-- The generic two-bit real carry specializes to the explicit four-state
integer Tetraktys carry. This identifies the abstract operator definition with
the independently declared matrix representation, and transports its first
power law across that bridge. -/
theorem real_eighth_root_carry_tetraktys_matrix_specialization :
    realEighthRootCarry secondProjector secondFlip firstJ = zetaCarry ∧
    zetaCarry * zetaCarry = firstJ := by
  have h_one : one4 = (1 : Mat) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have h_repr :
      realEighthRootCarry secondProjector secondFlip firstJ = zetaCarry := by
    dsimp [realEighthRootCarry, zetaCarry]
    rw [← h_one]
  rcases tetraktys_real_carry_power_laws with
    ⟨_, _, _, _, h_square, _, _⟩
  exact ⟨h_repr, h_square⟩

/-- A DeWitt second bit, with a commuting square-minus-one carry `J`, gives
`ζ² = J`, `ζ⁴ = -1`, and the displayed two-sided inverse. This records power
identities; exact multiplicative order additionally requires nontriviality
and exclusions of smaller orders in the coefficient ring. -/
theorem real_eighth_root_carry_and_inverse
    (P Φ J : B)
    (hP : P * P = P)
    (hΦ : Φ * Φ = 1)
    (hJ : J * J = -1)
    (hswap : Φ * P = (1 - P) * Φ)
    (hJP : J * P = P * J)
    (hJΦ : J * Φ = Φ * J) :
    let ζ := realEighthRootCarry P Φ J
    let ζinv := realEighthRootCarryInv P Φ J
    ζ * ζ = J ∧
    (ζ * ζ) * (ζ * ζ) = -1 ∧
    ζ * ζinv = 1 ∧ ζinv * ζ = 1 := by
  have hP_idem : ∀ Z : B, P * (P * Z) = P * Z := fun Z => by rw [← mul_assoc, hP]
  have hΦ_idem : ∀ Z : B, Φ * (Φ * Z) = Z := fun Z => by rw [← mul_assoc, hΦ, one_mul]
  have hJ_assoc : ∀ Z : B, J * (J * Z) = -Z := fun Z => by rw [← mul_assoc, hJ, neg_one_mul]
  have hswap_assoc : ∀ Z : B, Φ * (P * Z) = (1 - P) * (Φ * Z) :=
    fun Z => by rw [← mul_assoc, hswap, mul_assoc]
  have hJP_assoc : ∀ Z : B, J * (P * Z) = P * (J * Z) :=
    fun Z => by rw [← mul_assoc, hJP, mul_assoc]
  have hJΦ_assoc : ∀ Z : B, J * (Φ * Z) = Φ * (J * Z) :=
    fun Z => by rw [← mul_assoc, hJΦ, mul_assoc]
  have hζsq : realEighthRootCarry P Φ J * realEighthRootCarry P Φ J = J := by
    dsimp [realEighthRootCarry]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc, hswap_assoc, hΦ, hΦ_idem, hP, hP_idem,
      hJP_assoc, hJΦ, hJΦ_assoc, hJ, mul_neg]
    abel
  have hζinv_left : realEighthRootCarry P Φ J * realEighthRootCarryInv P Φ J = 1 := by
    dsimp [realEighthRootCarry, realEighthRootCarryInv]
    simp only [add_mul, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc, hswap_assoc, hΦ, hΦ_idem, hP, hP_idem,
      hJP_assoc, hJΦ, hJΦ_assoc, hJ, mul_neg]
    abel
  have hζinv_right : realEighthRootCarryInv P Φ J * realEighthRootCarry P Φ J = 1 := by
    dsimp [realEighthRootCarry, realEighthRootCarryInv]
    simp only [mul_add, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc, hswap_assoc, hΦ, hΦ_idem, hP, hP_idem,
      hJP_assoc, hJΦ, hJΦ_assoc, hJ, mul_neg]
    abel
  dsimp
  exact ⟨hζsq, by rw [hζsq, hJ], hζinv_left, hζinv_right⟩

/-- If the first-bit reflection `S` commutes with the second bit and
anticommutes with `J`, then `S Φ` conjugates the real carry to the inverse
carry. Since `(S Φ)² = 1`, the displayed conjugation is its own inverse. -/
theorem real_eighth_root_carry_reflection_conjugation
    (P Φ J S : B)
    (hP : P * P = P)
    (hΦ : Φ * Φ = 1)
    (hS : S * S = 1)
    (hswap : Φ * P = (1 - P) * Φ)
    (hJΦ : J * Φ = Φ * J)
    (hSP : S * P = P * S)
    (hSΦ : S * Φ = Φ * S)
    (hSJ : S * J = -(J * S)) :
    let ζ := realEighthRootCarry P Φ J
    let ζinv := realEighthRootCarryInv P Φ J
    (S * Φ) * (S * Φ) = 1 ∧ (S * Φ) * ζ * (S * Φ) = ζinv := by
  have hP_idem : ∀ Z : B, P * (P * Z) = P * Z := fun Z => by rw [← mul_assoc, hP]
  have hΦ_idem : ∀ Z : B, Φ * (Φ * Z) = Z := fun Z => by rw [← mul_assoc, hΦ, one_mul]
  have hS_idem : ∀ Z : B, S * (S * Z) = Z := fun Z => by rw [← mul_assoc, hS, one_mul]
  have hswap_assoc : ∀ Z : B, Φ * (P * Z) = (1 - P) * (Φ * Z) :=
    fun Z => by rw [← mul_assoc, hswap, mul_assoc]
  have hJΦ_assoc : ∀ Z : B, J * (Φ * Z) = Φ * (J * Z) :=
    fun Z => by rw [← mul_assoc, hJΦ, mul_assoc]
  have hSP_assoc : ∀ Z : B, S * (P * Z) = P * (S * Z) :=
    fun Z => by rw [← mul_assoc, hSP, mul_assoc]
  have hSΦ_assoc : ∀ Z : B, S * (Φ * Z) = Φ * (S * Z) :=
    fun Z => by rw [← mul_assoc, hSΦ, mul_assoc]
  have hSJ_assoc : ∀ Z : B, S * (J * Z) = -(J * (S * Z)) :=
    fun Z => by rw [← mul_assoc, hSJ, neg_mul, mul_assoc]
  have hSΦ_sq : (S * Φ) * (S * Φ) = 1 := by
    calc
      (S * Φ) * (S * Φ) = S * (Φ * (S * Φ)) := by simp only [mul_assoc]
      _ = S * (S * (Φ * Φ)) := by rw [← mul_assoc Φ S, ← hSΦ, mul_assoc]
      _ = 1 := by rw [hS_idem, hΦ]
  have hZ : (S * Φ) * realEighthRootCarry P Φ J * (S * Φ) =
      realEighthRootCarryInv P Φ J := by
    dsimp [realEighthRootCarry, realEighthRootCarryInv]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc, hswap_assoc, hΦ_idem, hS,
      hJΦ, hSP_assoc, hSΦ, hSΦ_assoc,
      hSJ, neg_mul, mul_neg]
    abel
  dsimp
  exact ⟨hSΦ_sq, hZ⟩

end RealEighthRootCarry

/-! ## §3. Nodes $\mathfrak{PB}_3 \prec \mathfrak{PB}_4 \prec \mathfrak{PB}_5$: $\mathbb{Z}_4$ Parafermion Braid Operator $U(X)$ & Brown–Gauss Sum from the Tetraktys Complex Structure -/

section Z4BraidAndBrownGauss

variable {B : Type u} [Ring B]

/-- The $\mathbb{Z}_2$ Brown–Gauss operator $G_2(P_0, A_0, C_0) = 1 + \text{genJ}\;P_0\;A_0\;C_0$
built directly from the Tetraktys complex structure `genJ P0 A0 C0`. -/
def tetraktysGaussZ2 (P0 A0 C0 : B) : B :=
  1 + genJ P0 A0 C0

/-- Raw 4-term Gauss sum braid operator `2 U(X) = 1 + ζ X + ζ⁴ X² + ζ⁹ X³`: -/
def BraidZ4_Raw (ζ X : B) : B :=
  1 + ζ * X + (ζ ^ 4) * (X ^ 2) + (ζ ^ 9) * (X ^ 3)

/-- Factored Peirce-parity braid operator `(1 - X²) + ζ X (1 + X²)`: -/
def BraidZ4_Factored (ζ X : B) : B :=
  (1 - X * X) + ζ * X * (1 + X * X)

/-- Adjoint braid operator `2 U†(X) = (1 - X²) + (-ζ³) X³ (1 + X²)` (using `ζ⁻¹ = -ζ³`, `X⁻¹ = X³`): -/
def BraidZ4_Dag (ζ X : B) : B :=
  (1 - X * X) + (-(ζ * ζ * ζ)) * (X * X * X) * (1 + X * X)

/-- **Theorem 2 ($\mathfrak{PB}_3 \prec \mathfrak{PB}_4 \prec \mathfrak{PB}_5$ — `z4_parafermion_braid_and_brown_gauss_theorem`)**:
Let `(P₀, A₀, C₀)` be a normalized Tetraktys system (`hP0 : P0 * P0 = P0`, `hV0 : genV P0 A0 C0 = 1`),
let `ζ` be a Tetraktys half-turn root satisfying `hζ2 : ζ ^ 2 = genJ P0 A0 C0`, and let `X` satisfy `X ^ 4 = 1`:
1. **Derived 4th and 8th Root Laws from the Tetraktys (`genJ² = -genV`)**:
   `genJ P0 A0 C0 * genJ P0 A0 C0 = -1`, `ζ ^ 4 = -1`, and `ζ ^ 8 = 1`.
2. **Tetraktys Brown–Gauss Sum Modification ($\mathbb{Z}_2 \mapsto \mathbb{Z}_4$)**:
   - `tetraktysGaussZ2 P0 A0 C0 * tetraktysGaussZ2 P0 A0 C0 = 2 * genJ P0 A0 C0`,
   - `(1 + ζ ^ 2) ^ 2 = 2 * genJ P0 A0 C0` ($c_-(\mathbb{Z}_2) = 1/2$),
   - `1 + ζ + ζ ^ 4 + ζ ^ 9 = 2 * ζ` (the $m = 0$ and $m = 2$ terms cancel via $1 + \zeta^4 = 0$,
     doubling $\zeta$ and shifting $c_-(\mathbb{Z}_4) = 2(4-1)/(4+2) = 1$).
3. **Exact Even/Odd Factorization of `2 U(X)`**:
   `BraidZ4_Raw ζ X = BraidZ4_Factored ζ X = (1 - X²) + ζ X (1 + X²)`.
4. **Orthogonality of Even and Odd Parity Sectors**:
   `(1 - X²) * (ζ X (1 + X²)) = 0`.
5. **Exact Unitarity of the $\mathbb{Z}_4$ Parafermion Braid Operator**:
   `BraidZ4_Factored ζ X * BraidZ4_Dag ζ X = 4`. -/
theorem z4_parafermion_braid_and_brown_gauss_theorem
    {K : Type u} [CommRing K] (P0 A0 C0 ζ X : K)
    (hP0 : P0 * P0 = P0)
    (hV0 : genV P0 A0 C0 = 1)
    (hζ2 : ζ ^ 2 = genJ P0 A0 C0)
    (hX4 : X ^ 4 = 1) :
    (genJ P0 A0 C0 * genJ P0 A0 C0 = -1 ∧ ζ ^ 4 = -1 ∧ ζ ^ 8 = 1) ∧
    (tetraktysGaussZ2 P0 A0 C0 * tetraktysGaussZ2 P0 A0 C0 = 2 * genJ P0 A0 C0 ∧
     (1 + ζ ^ 2) ^ 2 = 2 * genJ P0 A0 C0 ∧
     (1 + ζ + ζ ^ 4 + ζ ^ 9) = 2 * ζ ∧
     (2 * (4 - 1)) / (4 + 2) = 1) ∧
    BraidZ4_Raw ζ X = BraidZ4_Factored ζ X ∧
    (1 - X * X) * (ζ * X * (1 + X * X)) = 0 ∧
    BraidZ4_Factored ζ X * BraidZ4_Dag ζ X = 4 := by
  have hJ0_sq : genJ P0 A0 C0 * genJ P0 A0 C0 = -1 := by
    have hA3 := (archetype_A3_nilpotent_cones_and_tetraktys_table hP0 A0 C0).2.2.2.1
    rw [hA3, hV0]
  have hζ4 : ζ ^ 4 = -1 := by
    calc
      ζ ^ 4 = (ζ ^ 2) * (ζ ^ 2) := by ring
      _ = genJ P0 A0 C0 * genJ P0 A0 C0 := by rw [hζ2]
      _ = -1 := hJ0_sq
  have hζ8 : ζ ^ 8 = 1 := by
    calc
      ζ ^ 8 = (ζ ^ 4) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [hζ4]
      _ = 1 := by ring
  have hG2_tet : tetraktysGaussZ2 P0 A0 C0 * tetraktysGaussZ2 P0 A0 C0 = 2 * genJ P0 A0 C0 := by
    dsimp [tetraktysGaussZ2]
    calc
      (1 + genJ P0 A0 C0) * (1 + genJ P0 A0 C0) =
          1 + 2 * genJ P0 A0 C0 + genJ P0 A0 C0 * genJ P0 A0 C0 := by ring
      _ = 1 + 2 * genJ P0 A0 C0 + (-1) := by rw [hJ0_sq]
      _ = 2 * genJ P0 A0 C0 := by ring
  have hG2_zeta : (1 + ζ ^ 2) ^ 2 = 2 * genJ P0 A0 C0 := by
    calc
      (1 + ζ ^ 2) ^ 2 = (1 + genJ P0 A0 C0) * (1 + genJ P0 A0 C0) := by rw [hζ2]; ring
      _ = 2 * genJ P0 A0 C0 := hG2_tet
  have hG4 : 1 + ζ + ζ ^ 4 + ζ ^ 9 = 2 * ζ := by
    calc
      1 + ζ + ζ ^ 4 + ζ ^ 9 = 1 + ζ + ζ ^ 4 + ζ ^ 8 * ζ := by ring
      _ = 1 + ζ + (-1) + 1 * ζ := by rw [hζ4, hζ8]
      _ = 2 * ζ := by ring
  refine ⟨⟨hJ0_sq, hζ4, hζ8⟩, ⟨hG2_tet, hG2_zeta, hG4, by decide⟩, ?_, ?_, ?_⟩
  · dsimp [BraidZ4_Raw, BraidZ4_Factored]
    calc
      1 + ζ * X + ζ ^ 4 * X ^ 2 + ζ ^ 9 * X ^ 3 =
          1 + ζ * X + ζ ^ 4 * X ^ 2 + (ζ ^ 8 * ζ) * X ^ 3 := by ring
      _ = 1 + ζ * X + (-1) * X ^ 2 + (1 * ζ) * X ^ 3 := by rw [hζ4, hζ8]
      _ = (1 - X * X) + ζ * X * (1 + X * X) := by ring
  · calc
      (1 - X * X) * (ζ * X * (1 + X * X)) = ζ * X * (1 - X ^ 4) := by ring
      _ = ζ * X * (1 - 1) := by rw [hX4]
      _ = 0 := by ring
  · dsimp [BraidZ4_Factored, BraidZ4_Dag]
    calc
      ((1 - X * X) + ζ * X * (1 + X * X)) *
          ((1 - X * X) + -(ζ * ζ * ζ) * (X * X * X) * (1 + X * X)) =
          (1 - 2 * X ^ 2 + X ^ 4) +
            (1 - X ^ 4) * (ζ * X - ζ ^ 3 * X ^ 3) -
            (ζ ^ 4) * (X ^ 4) * (1 + 2 * X ^ 2 + X ^ 4) := by ring
      _ = (1 - 2 * X ^ 2 + 1) +
            (1 - 1) * (ζ * X - ζ ^ 3 * X ^ 3) -
            (-1) * 1 * (1 + 2 * X ^ 2 + 1) := by rw [hX4, hζ4]
      _ = 4 := by ring

end Z4BraidAndBrownGauss

/-! ## §4. Nodes $\mathfrak{PB}_6 \prec \mathfrak{PB}_7$: The $\mathbb{Z}_4$-Graded Quantum Super-Grassmannian Braided by the Tetraktys Complex Structure -/

section QuantumSuperGrassmannianZ4

variable {B : Type u} [Ring B]

/-- **Theorem 3 ($\mathfrak{PB}_6 \prec \mathfrak{PB}_7$ — `z4_quantum_super_grassmannian_fourth_power_nilpotency`)**:
Let `(P₀, A₀, C₀)` be a normalized Tetraktys system (`hP0 : P0 * P0 = P0`, `hV0 : genV P0 A0 C0 = 1`)
whose Tetraktys complex structure `genJ P0 A0 C0 = conePlus P0 A0 - coneMinus P0 C0` commutes with
`η₁, η₂ ∈ B` and braids them via:
$$\eta_1 * \eta_2 = \text{genJ}\;P_0\;A_0\;C_0 * (\eta_2 * \eta_1).$$
Then:
1. **Quadratic Condensate Weighted by the Tetraktys $\mathbb{Z}_2$ Gauss Sum**:
   `(η1 + η2) * (η1 + η2) = η1 * η1 + tetraktysGaussZ2 P0 A0 C0 * (η2 * η1) + η2 * η2`.
2. **Derived Diquark Anticommutation & Commutation**:
   `(η1 * η1) * η2 = -(η2 * (η1 * η1))` and `(η1 * η1) * (η2 * η2) = (η2 * η2) * (η1 * η1)`.
3. **Exact 4th-Power Cross-Term Cancellation**:
   `(η1 + η2) * (η1 + η2) * ((η1 + η2) * (η1 + η2)) = (η1 * η1 * (η1 * η1)) + (η2 * η2 * (η2 * η2))`
   (which vanishes whenever `η1⁴ = 0` and `η2⁴ = 0`). -/
theorem z4_quantum_super_grassmannian_fourth_power_nilpotency
    (P0 A0 C0 η1 η2 : B)
    (hP0 : P0 * P0 = P0)
    (hV0 : genV P0 A0 C0 = 1)
    (hJ_c1 : genJ P0 A0 C0 * η1 = η1 * genJ P0 A0 C0)
    (hJ_c2 : genJ P0 A0 C0 * η2 = η2 * genJ P0 A0 C0)
    (h_braid : η1 * η2 = genJ P0 A0 C0 * (η2 * η1)) :
    (pbCoverIndicator 0 1 = true ∧ pbCoverIndicator 1 2 = true ∧ pbCoverIndicator 2 3 = true ∧
     pbCoverIndicator 3 4 = true ∧ pbCoverIndicator 4 5 = true ∧ pbCoverIndicator 5 6 = true) ∧
    (η1 + η2) * (η1 + η2) =
      η1 * η1 + tetraktysGaussZ2 P0 A0 C0 * (η2 * η1) + η2 * η2 ∧
    ((η1 * η1) * η2 = -(η2 * (η1 * η1)) ∧
     (η1 * η1) * (η2 * η2) = (η2 * η2) * (η1 * η1)) ∧
    (η1 + η2) * (η1 + η2) * ((η1 + η2) * (η1 + η2)) =
      (η1 * η1 * (η1 * η1)) + (η2 * η2 * (η2 * η2)) ∧
    (η1 * η1 * (η1 * η1) = 0 → η2 * η2 * (η2 * η2) = 0 →
      (η1 + η2) * (η1 + η2) * ((η1 + η2) * (η1 + η2)) = 0) := by
  set J4 := genJ P0 A0 C0
  have hJ2 : J4 * J4 = -1 := by
    dsimp [J4]
    have hA3 := (archetype_A3_nilpotent_cones_and_tetraktys_table hP0 A0 C0).2.2.2.1
    rw [hA3, hV0]
  have h_sq : (η1 + η2) * (η1 + η2) =
      η1 * η1 + (1 + J4) * (η2 * η1) + η2 * η2 := by
    calc
      (η1 + η2) * (η1 + η2) = η1 * η1 + (η1 * η2 + η2 * η1) + η2 * η2 := by
        simp only [add_mul, mul_add]; abel
      _ = η1 * η1 + (1 + J4) * (η2 * η1) + η2 * η2 := by
        rw [h_braid, add_mul, one_mul]; abel
  have h11_2 : (η1 * η1) * η2 = -(η2 * (η1 * η1)) := by
    calc
      (η1 * η1) * η2 = η1 * (η1 * η2) := by simp only [mul_assoc]
      _ = η1 * (J4 * (η2 * η1)) := by rw [h_braid]
      _ = J4 * ((η1 * η2) * η1) := by rw [← mul_assoc η1 J4, ← hJ_c1]; simp only [mul_assoc]
      _ = (J4 * J4) * (η2 * (η1 * η1)) := by rw [h_braid]; simp only [mul_assoc]
      _ = -(η2 * (η1 * η1)) := by rw [hJ2, neg_mul, one_mul]
  have h1_22 : η1 * (η2 * η2) = -((η2 * η2) * η1) := by
    calc
      η1 * (η2 * η2) = (η1 * η2) * η2 := by simp only [mul_assoc]
      _ = (J4 * (η2 * η1)) * η2 := by rw [h_braid]
      _ = J4 * (η2 * (η1 * η2)) := by simp only [mul_assoc]
      _ = J4 * (η2 * (J4 * (η2 * η1))) := by rw [h_braid]
      _ = (J4 * J4) * ((η2 * η2) * η1) := by rw [← mul_assoc η2 J4, ← hJ_c2]; simp only [mul_assoc]
      _ = -((η2 * η2) * η1) := by rw [hJ2, neg_mul, one_mul]
  have h11_22 : (η1 * η1) * (η2 * η2) = (η2 * η2) * (η1 * η1) := by
    calc
      (η1 * η1) * (η2 * η2) = ((η1 * η1) * η2) * η2 := by simp only [mul_assoc]
      _ = (-(η2 * (η1 * η1))) * η2 := by rw [h11_2]
      _ = -(η2 * ((η1 * η1) * η2)) := by simp only [neg_mul, mul_assoc]
      _ = -(η2 * (-(η2 * (η1 * η1)))) := by rw [h11_2]
      _ = (η2 * η2) * (η1 * η1) := by simp only [mul_neg, neg_neg, mul_assoc]
  have h_mid_sq : (η2 * η1) * (η2 * η1) = J4 * ((η2 * η2) * (η1 * η1)) := by
    calc
      (η2 * η1) * (η2 * η1) = η2 * (η1 * η2) * η1 := by simp only [mul_assoc]
      _ = η2 * J4 * (η2 * (η1 * η1)) := by rw [h_braid]; simp only [mul_assoc]
      _ = J4 * ((η2 * η2) * (η1 * η1)) := by rw [← hJ_c2]; simp only [mul_assoc]
  have h_coeff : (1 + J4) * (1 + J4) * J4 = -(1 + 1) := by
    calc
      (1 + J4) * (1 + J4) * J4 = (1 + (J4 + J4) + J4 * J4) * J4 := by
        simp only [add_mul, mul_add, one_mul, mul_one]; abel
      _ = (J4 + J4) * J4 := by rw [hJ2]; congr 1; abel
      _ = J4 * J4 + J4 * J4 := by rw [add_mul]
      _ = -(1 + 1) := by rw [hJ2]; abel
  have h_odd1 : (η1 * η1) * (η2 * η1) + (η2 * η1) * (η1 * η1) = 0 := by
    calc
      (η1 * η1) * (η2 * η1) + (η2 * η1) * (η1 * η1) =
          ((η1 * η1) * η2) * η1 + (η2 * η1) * (η1 * η1) := by simp only [mul_assoc]
      _ = (-(η2 * (η1 * η1))) * η1 + (η2 * η1) * (η1 * η1) := by rw [h11_2]
      _ = 0 := by simp only [neg_mul, mul_assoc]; abel
  have h_odd2 : (η2 * η2) * (η2 * η1) + (η2 * η1) * (η2 * η2) = 0 := by
    calc
      (η2 * η2) * (η2 * η1) + (η2 * η1) * (η2 * η2) =
          (η2 * η2) * (η2 * η1) + η2 * (η1 * (η2 * η2)) := by simp only [mul_assoc]
      _ = (η2 * η2) * (η2 * η1) + η2 * (-((η2 * η2) * η1)) := by rw [h1_22]
      _ = 0 := by simp only [mul_neg, mul_assoc]; abel
  set A := η1 * η1
  set C := η2 * η2
  set M := η2 * η1
  have hJ_M : (1 + J4) * M = M * (1 + J4) := by
    have hJM : J4 * M = M * J4 := by
      dsimp [M]; rw [← mul_assoc, hJ_c2, mul_assoc, hJ_c1, ← mul_assoc]
    simp only [add_mul, mul_add, one_mul, mul_one, hJM]
  have hJ_A : (1 + J4) * A = A * (1 + J4) := by
    have hJA : J4 * A = A * J4 := by
      dsimp [A]; rw [← mul_assoc, hJ_c1, mul_assoc, hJ_c1, ← mul_assoc]
    simp only [add_mul, mul_add, one_mul, mul_one, hJA]
  have hJ_C : (1 + J4) * C = C * (1 + J4) := by
    have hJC : J4 * C = C * J4 := by
      dsimp [C]; rw [← mul_assoc, hJ_c2, mul_assoc, hJ_c2, ← mul_assoc]
    simp only [add_mul, mul_add, one_mul, mul_one, hJC]
  have h_mid2 : ((1 + J4) * M) * ((1 + J4) * M) = -(C * A + C * A) := by
    calc
      ((1 + J4) * M) * ((1 + J4) * M) = (1 + J4) * (M * (1 + J4)) * M := by simp only [mul_assoc]
      _ = (1 + J4) * (1 + J4) * (M * M) := by rw [← hJ_M]; simp only [mul_assoc]
      _ = ((1 + J4) * (1 + J4) * J4) * (C * A) := by rw [h_mid_sq]; simp only [mul_assoc]
      _ = -(1 + 1) * (C * A) := by rw [h_coeff]
      _ = -(C * A + C * A) := by simp only [neg_mul, add_mul, one_mul]
  have h_AM : A * ((1 + J4) * M) + ((1 + J4) * M) * A = 0 := by
    calc
      A * ((1 + J4) * M) + ((1 + J4) * M) * A =
          (A * (1 + J4)) * M + (1 + J4) * (M * A) := by simp only [mul_assoc]
      _ = ((1 + J4) * A) * M + (1 + J4) * (M * A) := by rw [hJ_A]
      _ = (1 + J4) * (A * M + M * A) := by rw [mul_assoc (1 + J4) A M, ← mul_add]
      _ = 0 := by rw [h_odd1, mul_zero]
  have h_CM : C * ((1 + J4) * M) + ((1 + J4) * M) * C = 0 := by
    calc
      C * ((1 + J4) * M) + ((1 + J4) * M) * C =
          (C * (1 + J4)) * M + (1 + J4) * (M * C) := by simp only [mul_assoc]
      _ = ((1 + J4) * C) * M + (1 + J4) * (M * C) := by rw [hJ_C]
      _ = (1 + J4) * (C * M + M * C) := by rw [mul_assoc (1 + J4) C M, ← mul_add]
      _ = 0 := by rw [h_odd2, mul_zero]
  have h_pow4 :
      (η1 + η2) * (η1 + η2) * ((η1 + η2) * (η1 + η2)) = A * A + C * C := by
    rw [h_sq]
    calc
      (A + (1 + J4) * M + C) * (A + (1 + J4) * M + C) =
          A * A + C * C + (A * C + C * A) +
            ((1 + J4) * M) * ((1 + J4) * M) +
            (A * ((1 + J4) * M) + ((1 + J4) * M) * A) +
            (C * ((1 + J4) * M) + ((1 + J4) * M) * C) := by
        simp only [add_mul, mul_add]; abel
      _ = A * A + C * C + (C * A + C * A) + (-(C * A + C * A)) + 0 + 0 := by
        rw [h11_22, h_mid2, h_AM, h_CM]
      _ = A * A + C * C := by abel
  refine ⟨by decide, h_sq, ⟨h11_2, h11_22⟩, h_pow4, ?_⟩
  intro h14 h24
  rw [h_pow4, h14, h24, add_zero]

/-- Scaled Ivanov Majorana $\frac{\pi}{4}$-braid rotor $R_{12} = 1 + \gamma_1 \gamma_2$ in `[Ring B]`. -/
def ivanovMajoranaRotor (γ1 γ2 : B) : B :=
  1 + γ1 * γ2

/-- **Theorem 4 ($\mathfrak{PB}_1$ Socratic Elenchus — `majorana_ivanov_braid_fourth_power_neg_one_vs_parafermion`)**:
For any two anticommuting Majorana operators $\gamma_1, \gamma_2 \in B$ satisfying $\gamma_1^2 = 1$,
$\gamma_2^2 = 1$, and $\{\gamma_1, \gamma_2\} = \gamma_1 \gamma_2 + \gamma_2 \gamma_1 = 0$:
1. **Bilinear Square ($(\gamma_1 \gamma_2)^2 = -1$)**:
   $(\gamma_1 \gamma_2)^2 = -1$, so $\gamma_1 \gamma_2$ has order $4$.
2. **Ivanov $\frac{\pi}{4}$-Rotor Order-8 Obstruction ($R_{12}^4 = -4$)**:
   The scaled Ivanov braid rotor $R_{12} = 1 + \gamma_1 \gamma_2$ satisfies
   $$R_{12}^2 = 2\,\gamma_1 \gamma_2, \qquad R_{12}^4 = (R_{12}^2)^2 = -4, \qquad (R_{12}^4)^2 = 16,$$
   reflecting the projective spinor sign $(R_{12}/\sqrt{2})^4 = -1$ (linear order $8$, not $4$).
3. **$\mathbb{Z}_2$ Fermion Parity Conservation**:
   $R_{12}$ commutes with the $\mathbb{Z}_2$ fermion parity bilinear $\gamma_1 \gamma_2$
   ($R_{12} (\gamma_1 \gamma_2) = (\gamma_1 \gamma_2) R_{12}$), contrasting with the $\mathbb{Z}_4$
   binary-carry shift $\tau$ which cycles four distinct $\sigma$-eigenvalues $\sigma \tau = J_0 \tau \sigma$. -/
theorem majorana_ivanov_braid_fourth_power_neg_one_vs_parafermion
    (γ1 γ2 : B)
    (h1 : γ1 * γ1 = 1)
    (h2 : γ2 * γ2 = 1)
    (hAnti : γ1 * γ2 + γ2 * γ1 = 0) :
    (γ1 * γ2) * (γ1 * γ2) = -1 ∧
    ivanovMajoranaRotor γ1 γ2 * ivanovMajoranaRotor γ1 γ2 = γ1 * γ2 + γ1 * γ2 ∧
    (ivanovMajoranaRotor γ1 γ2 * ivanovMajoranaRotor γ1 γ2) *
      (ivanovMajoranaRotor γ1 γ2 * ivanovMajoranaRotor γ1 γ2) = -(1 + 1 + 1 + 1) ∧
    ivanovMajoranaRotor γ1 γ2 * (γ1 * γ2) = (γ1 * γ2) * ivanovMajoranaRotor γ1 γ2 := by
  have hSwap : γ2 * γ1 = -(γ1 * γ2) := by
    calc
      γ2 * γ1 = (γ1 * γ2 + γ2 * γ1) - γ1 * γ2 := by abel
      _ = 0 - γ1 * γ2 := by rw [hAnti]
      _ = -(γ1 * γ2) := by abel
  have hM2 : (γ1 * γ2) * (γ1 * γ2) = -1 := by
    calc
      (γ1 * γ2) * (γ1 * γ2) = γ1 * (γ2 * γ1) * γ2 := by noncomm_ring
      _ = γ1 * (-(γ1 * γ2)) * γ2 := by rw [hSwap]
      _ = -((γ1 * γ1) * (γ2 * γ2)) := by noncomm_ring
      _ = -1 := by rw [h1, h2, one_mul]
  have hR2 : ivanovMajoranaRotor γ1 γ2 * ivanovMajoranaRotor γ1 γ2 = γ1 * γ2 + γ1 * γ2 := by
    dsimp [ivanovMajoranaRotor]
    calc
      (1 + γ1 * γ2) * (1 + γ1 * γ2) = 1 + (γ1 * γ2 + γ1 * γ2) + (γ1 * γ2) * (γ1 * γ2) := by
        simp only [add_mul, mul_add, one_mul, mul_one]; abel
      _ = 1 + (γ1 * γ2 + γ1 * γ2) + (-1) := by rw [hM2]
      _ = γ1 * γ2 + γ1 * γ2 := by abel
  have hR4 :
      (ivanovMajoranaRotor γ1 γ2 * ivanovMajoranaRotor γ1 γ2) *
        (ivanovMajoranaRotor γ1 γ2 * ivanovMajoranaRotor γ1 γ2) = -(1 + 1 + 1 + 1) := by
    rw [hR2]
    calc
      (γ1 * γ2 + γ1 * γ2) * (γ1 * γ2 + γ1 * γ2) =
          (γ1 * γ2) * (γ1 * γ2) + (γ1 * γ2) * (γ1 * γ2) +
            (γ1 * γ2) * (γ1 * γ2) + (γ1 * γ2) * (γ1 * γ2) := by
        simp only [add_mul, mul_add]; abel
      _ = (-1) + (-1) + (-1) + (-1) := by rw [hM2]
      _ = -(1 + 1 + 1 + 1) := by abel
  have hComm : ivanovMajoranaRotor γ1 γ2 * (γ1 * γ2) = (γ1 * γ2) * ivanovMajoranaRotor γ1 γ2 := by
    dsimp [ivanovMajoranaRotor]
    simp only [add_mul, mul_add, one_mul, mul_one]
  exact ⟨hM2, hR2, hR4, hComm⟩

/-- Second cyclotomic polynomial $\Phi_2(x) = 1 + x$ in `[Ring B]`. -/
def cyclotomicPhi2 (x : B) : B :=
  1 + x

/-- Fourth cyclotomic polynomial $\Phi_4(x) = 1 + x^2$ in `[Ring B]`. -/
def cyclotomicPhi4 (x : B) : B :=
  1 + x * x

/-- Truncated $\mathbb{Z}_4$ geometric partition sum $1 + x + x^2 + x^3 = \Phi_2(x)\Phi_4(x)$ in `[Ring B]`. -/
def truncatedPartitionSum4 (x : B) : B :=
  1 + x + x * x + x * x * x

/-- Scaled degree-$3$ unipotent super-Grassmannian exponential gate
$6\,\mathcal{E}_4(+\eta) = 6 + 6\eta + 3\eta^2 + \eta^3$ for a nilpotent $\mathbb{Z}_4$ generator ($\eta^4 = 0$). -/
def unipotentExpGate4Pos (η : B) : B :=
  6 + 6 * η + 3 * (η * η) + η * η * η

/-- Scaled degree-$3$ inverse unipotent super-Grassmannian exponential gate
$6\,\mathcal{E}_4(-\eta) = 6 - 6\eta + 3\eta^2 - \eta^3$. -/
def unipotentExpGate4Neg (η : B) : B :=
  6 - 6 * η + 3 * (η * η) - η * η * η

/-- **Theorem 5 ($\mathfrak{PB}_7$ Unipotent Gate & Partition Quotient — `z4_unipotent_exponential_gate_and_cyclotomic_partition_quotient`)**:
For any element $\eta \in K$ in a commutative ring `[CommRing K]`:
1. **Cyclotomic Partition Factorization ($\Phi_2 \Phi_4$)**:
   $$\Phi_2(\eta)\,\Phi_4(\eta) \;=\; (1 + \eta)(1 + \eta^2) \;=\; 1 + \eta + \eta^2 + \eta^3,$$
   and $(1 - \eta)\,\Phi_2(\eta)\,\Phi_4(\eta) = 1 - \eta^4$.
2. **Degree-3 Unipotent Exponential Gate Identity ($\mathcal{E}_4(\eta)\mathcal{E}_4(-\eta)$)**:
   $$\bigl(6\,\mathcal{E}_4(+\eta)\bigr)\bigl(6\,\mathcal{E}_4(-\eta)\bigr) \;=\; 36 - 3\eta^4 - \eta^6,$$
   where all quadratic ($\eta^2$) and odd ($\eta, \eta^3, \eta^5$) cross-terms cancel identically.
3. **Exact Unipotent Inversion on the $\mathbb{Z}_4$-Nilpotent Locus ($\eta^4 = 0$)**:
   Whenever $(\eta \cdot \eta) \cdot (\eta \cdot \eta) = 0$:
   $$(1 - \eta)\,\Phi_2(\eta)\,\Phi_4(\eta) = 1 \quad\text{and}\quad
     \bigl(6\,\mathcal{E}_4(+\eta)\bigr)\bigl(6\,\mathcal{E}_4(-\eta)\bigr) = 36.$$ -/
theorem z4_unipotent_exponential_gate_and_cyclotomic_partition_quotient
    {K : Type u} [CommRing K] (η : K) :
    cyclotomicPhi2 η * cyclotomicPhi4 η = truncatedPartitionSum4 η ∧
    (1 - η) * (cyclotomicPhi2 η * cyclotomicPhi4 η) = 1 - (η * η) * (η * η) ∧
    unipotentExpGate4Pos η * unipotentExpGate4Neg η =
      36 - 3 * ((η * η) * (η * η)) - (η * η) * ((η * η) * (η * η)) ∧
    ((η * η) * (η * η) = 0 →
      (1 - η) * (cyclotomicPhi2 η * cyclotomicPhi4 η) = 1 ∧
      unipotentExpGate4Pos η * unipotentExpGate4Neg η = 36) := by
  have hFact : cyclotomicPhi2 η * cyclotomicPhi4 η = truncatedPartitionSum4 η := by
    dsimp [cyclotomicPhi2, cyclotomicPhi4, truncatedPartitionSum4]
    ring
  have hGeom : (1 - η) * (cyclotomicPhi2 η * cyclotomicPhi4 η) = 1 - (η * η) * (η * η) := by
    dsimp [cyclotomicPhi2, cyclotomicPhi4]
    ring
  have hExp :
      unipotentExpGate4Pos η * unipotentExpGate4Neg η =
        36 - 3 * ((η * η) * (η * η)) - (η * η) * ((η * η) * (η * η)) := by
    dsimp [unipotentExpGate4Pos, unipotentExpGate4Neg]
    ring
  refine ⟨hFact, hGeom, hExp, fun h4 => ?_⟩
  refine ⟨?_, ?_⟩
  · rw [hGeom, h4, sub_zero]
  · rw [hExp, h4, mul_zero, sub_zero, mul_zero, sub_zero]

/-- **Theorem 6 ($\mathfrak{DT}_6 \prec \mathfrak{DT}_7$ — `real_dewitt_brown_gauss_and_z4_braid_unitarity_ring`)**:
In ANY associative ring `[Ring B]` (without commutativity of `B`), for any real DeWitt 8th root
`ζ` (`ζ⁴ = -1`, e.g., `ζ = realEighthRootCarry P2 Phi2 J1`) and any order-4 parafermion generator
`X` (`X⁴ = 1`) commuting with `ζ`:
1. **Real Brown–Gauss Sum**: `1 + ζ + (ζ * (ζ * (ζ * ζ))) + (ζ * (ζ * (ζ * ζ))) * (ζ * (ζ * (ζ * ζ))) * ζ = ζ + ζ`.
2. **Orthogonality of Parity Channels**: `(1 - X * X) * (ζ * X * (1 + X * X)) = 0`.
3. **Exact Real Braid Unitarity in `[Ring B]`**:
   `BraidZ4_Factored ζ X * BraidZ4_Dag ζ X = 1 + 1 + 1 + 1`. -/
theorem real_dewitt_brown_gauss_and_z4_braid_unitarity_ring
    (ζ X : B)
    (hζ4 : ζ * (ζ * (ζ * ζ)) = -1)
    (hX4 : X * (X * (X * X)) = 1)
    (h_comm : ζ * X = X * ζ) :
    let ζ4 := ζ * (ζ * (ζ * ζ))
    let ζ8 := ζ4 * ζ4
    1 + ζ + ζ4 + ζ8 * ζ = ζ + ζ ∧
    (1 - X * X) * (ζ * X * (1 + X * X)) = 0 ∧
    BraidZ4_Factored ζ X * BraidZ4_Dag ζ X = 1 + 1 + 1 + 1 := by
  have hζ8 : (ζ * (ζ * (ζ * ζ))) * (ζ * (ζ * (ζ * ζ))) = 1 := by
    rw [hζ4, neg_mul_neg, one_mul]
  have hX_idem : ∀ Z : B, X * (X * (X * (X * Z))) = Z := by
    intro Z
    calc
      X * (X * (X * (X * Z))) = (X * (X * (X * X))) * Z := by simp only [mul_assoc]
      _ = Z := by rw [hX4, one_mul]
  have h_comm_assoc : ∀ Z : B, ζ * (X * Z) = X * (ζ * Z) := by
    intro Z; rw [← mul_assoc, h_comm, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hζ8, hζ4, one_mul]
    abel
  · simp only [mul_add, sub_mul, one_mul, mul_one,
               mul_assoc, h_comm, h_comm_assoc, hX_idem]
    abel
  · dsimp [BraidZ4_Factored, BraidZ4_Dag]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc,
               h_comm, h_comm_assoc, hX4, hX_idem, hζ4]
    abel

end QuantumSuperGrassmannianZ4

end InfoGeometry.Parafermion.ParafermionBraidBrownGaussPoset
