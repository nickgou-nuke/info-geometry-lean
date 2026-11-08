/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Abel
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Bimetric Peirce Operator Algebra, Double-Commutator Curvature & Sheet Involutions (S₀ ≺ ... ≺ S₄)

Formalized in Lean 4 (`Mathlib`) over an arbitrary non-commutative associative ring `[Ring B]`.
Zero `sorry`s. Zero axioms. Zero commutativity assumptions on `B`.

## Causal Poset Architecture (`BimetricSheetPosetStage`):
- **Archetype S₀ & S₁ (`archetype_S0_S1_bimetric_sheets_and_reflective_intertwining`)**:
  Orthogonality `Q_+ * Q_- = 0` of the two sheet metrics, exact reflective intertwining
  `Q_+ * Φ = Φ * Q_- = N_+ N_- N_+` and `Q_- * Φ = Φ * Q_+ = N_- N_+ N_-`, central commutation
  `[V, Φ] = [V, J] = 0`, and dipole anticommutation `{Σ, Φ} = {Σ, J} = 0`.
- **Archetype S₂ (`archetype_S2_double_commutator_bohm_curvature_and_continuity`)**:
  Proves that the double-commutator curvature operator `Q_Bohm(Φ, Z) = -[Φ, [Φ, Z]]`
  annihilates `V` and `Φ`, while acting as `-4 V J` on `J` and `-4 V Σ` on `Σ`, with
  `[Φ, J] = -2 Σ` and `[S_P, Φ] = 2 J`.
- **Archetype S₃ (`archetype_S3_matrix_sheet_exchange_and_symplectic_adjugate`)**:
  In `Mat2 B`, proves that sheet-exchange `Ex * V * Ex` swaps the two sheet metrics `AC ↔ CA`,
  `Σ + Ex * Σ * Ex = diagScalar([A, C])`, `tr₂(Σ) = [A, C]`, and `-Ey * M * Ey = adj(M)`.
- **Archetype S₄ (`archetype_S4_star_ring_gramian_duality_and_cpt_balance`)**:
  Over `[Ring B] [StarRing B]`, proves that for `Φ = [[0, A], [A⋆, 0]]`, `V` and `Σ` are
  self-adjoint, `J` is skew-adjoint, and `Σ + Ex * Σ⋆ * Ex = diagScalar([A, A⋆])`.
- **PeirceSpine Owner Alignment (`bimetric_peirceSpine_dictionary_alignment`)**:
  Identifies `metricPlus`, `metricMinus`, `genPhi`, `genJ`, `genV`, `genSig`, and `bohmCurv`
  with the canonical `InfoGeometry.OperatorAlgebra.PeirceSpine` owners `qgtPlus`, `qgtMinus`,
  `PeirceSpine.genPhi`, `PeirceSpine.genJ`, `PeirceSpine.genV`, `PeirceSpine.genSig`, and
  `PeirceSpine.derivSqPhi`.
-/

namespace NonCommutativeBimetricSheetGeometry

universe u
variable {B : Type u} [Ring B]

-- ============================================================================
-- 0. ACYCLIC CAUSAL POSET (S₀ ≺ S₁ ≺ S₂ ≺ S₃ ≺ S₄)
-- ============================================================================

/-- Five-stage causal poset $\mathcal{S}_0 \prec \mathcal{S}_1 \prec \mathcal{S}_2 \prec \mathcal{S}_3 \prec \mathcal{S}_4$
    for non-commutative bimetric Peirce sheet geometry. -/
inductive BimetricSheetPosetStage : Type
  | S0_orthogonal_sheet_metrics_and_intertwining
  | S1_metric_commutation_and_dipole_anticommutation
  | S2_double_commutator_bohm_curvature
  | S3_matrix_sheet_exchange_and_symplectic_adjugate
  | S4_star_ring_gramian_duality_and_cpt_balance
  deriving DecidableEq, Repr, Inhabited

namespace BimetricSheetPosetStage

/-- Numerical rank of each stage in the causal poset $\mathcal{S}_0 \prec \dots \prec \mathcal{S}_4$. -/
def toNat : BimetricSheetPosetStage → ℕ
  | S0_orthogonal_sheet_metrics_and_intertwining => 0
  | S1_metric_commutation_and_dipole_anticommutation => 1
  | S2_double_commutator_bohm_curvature => 2
  | S3_matrix_sheet_exchange_and_symplectic_adjugate => 3
  | S4_star_ring_gramian_duality_and_cpt_balance => 4

theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder BimetricSheetPosetStage :=
  LinearOrder.lift' toNat toNat_injective

theorem poset_chain_S0_lt_S1_lt_S2_lt_S3_lt_S4 :
    S0_orthogonal_sheet_metrics_and_intertwining < S1_metric_commutation_and_dipole_anticommutation ∧
    S1_metric_commutation_and_dipole_anticommutation < S2_double_commutator_bohm_curvature ∧
    S2_double_commutator_bohm_curvature < S3_matrix_sheet_exchange_and_symplectic_adjugate ∧
    S3_matrix_sheet_exchange_and_symplectic_adjugate < S4_star_ring_gramian_duality_and_cpt_balance := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end BimetricSheetPosetStage

-- ============================================================================
-- 1. ABSTRACT BIMETRIC PEIRCE ALGEBRA OVER A NON-COMMUTATIVE RING `[Ring B]`
-- ============================================================================

@[simp] def rcomm {A : Type u} [Ring A] (x y : A) : A := x * y - y * x
@[simp] def racomm {A : Type u} [Ring A] (x y : A) : A := x * y + y * x

/-- Sheet grading involution `S_P = P - (1 - P) = 2P - 1`. -/
@[simp] def invS (P : B) : B := P - (1 - P)

/-- Forward and backward inter-sheet nilpotent transition operators `N_+` and `N_-`. -/
@[simp] def conePlus  (P X : B) : B := P * X * (1 - P)
@[simp] def coneMinus (P Y : B) : B := (1 - P) * Y * P

/-- Reflective boundary operator `Φ = N_+ + N_-` and skew phase current `J = N_+ - N_-`. -/
@[simp] def genPhi (P X Y : B) : B := conePlus P X + coneMinus P Y
@[simp] def genJ   (P X Y : B) : B := conePlus P X - coneMinus P Y

/-- Sheet-+ metric `Q_+ = N_+ N_-` and Sheet-- metric `Q_- = N_- N_+`. -/
@[simp] def metricPlus  (P X Y : B) : B := conePlus P X * coneMinus P Y
@[simp] def metricMinus (P X Y : B) : B := coneMinus P Y * conePlus P X

/-- Total bimetric sum `V = Q_+ + Q_-` and bimetric asymmetry dipole `Σ = Q_+ - Q_-`. -/
@[simp] def genV   (P X Y : B) : B := metricPlus P X Y + metricMinus P X Y
@[simp] def genSig (P X Y : B) : B := metricPlus P X Y - metricMinus P X Y

/-- Double-commutator curvature superoperator `Q_Bohm(Φ, Z) = -[Φ, [Φ, Z]]`. -/
@[simp] def bohmCurv (P X Y Z : B) : B :=
  -rcomm (genPhi P X Y) (rcomm (genPhi P X Y) Z)

lemma P_assoc {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc]
  rw [hP]

/-- Exact dictionary alignment between `NonCommutativeBimetricSheetGeometry` and
    `InfoGeometry.OperatorAlgebra.PeirceSpine`. -/
theorem bimetric_peirceSpine_dictionary_alignment (P X Y Z : B) :
    invS P = InfoGeometry.OperatorAlgebra.PeirceSpine.invS P ∧
    conePlus P X = InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P X ∧
    coneMinus P Y = InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P Y ∧
    genPhi P X Y = InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y ∧
    genJ P X Y = InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y ∧
    metricPlus P X Y = InfoGeometry.OperatorAlgebra.PeirceSpine.qgtPlus P X Y ∧
    metricMinus P X Y = InfoGeometry.OperatorAlgebra.PeirceSpine.qgtMinus P X Y ∧
    genV P X Y = InfoGeometry.OperatorAlgebra.PeirceSpine.genV P X Y ∧
    genSig P X Y = InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P X Y ∧
    bohmCurv P X Y Z = InfoGeometry.OperatorAlgebra.PeirceSpine.derivSqPhi P X Y Z := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

macro "peirce_bimetric_abel" hP:ident : tactic =>
  `(tactic| (
    simp only [bohmCurv, genV, genSig, metricPlus, metricMinus,
               genPhi, genJ, invS, conePlus, coneMinus, rcomm, racomm,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg, neg_add_rev, neg_sub,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub,
               mul_assoc, $hP:ident, P_assoc $hP:ident];
    try abel))

/--
**Archetype S₀ & S₁ (`archetype_S0_S1_bimetric_sheets_and_reflective_intertwining`):**
For ANY idempotent `P * P = P` and ANY non-commuting operators `X, Y ∈ B`:
1. **Orthogonal Sheet Localization:**
   `P * Q_+ * P = Q_+`, `(1 - P) * Q_- * (1 - P) = Q_-`, `Q_+ * Q_- = 0`, and `Q_- * Q_+ = 0`.
2. **Reflective Boundary Intertwining (`Q_+ Φ = Φ Q_-` and `Q_- Φ = Φ Q_+`):**
   Multiplying the reflective boundary `Φ` on the left by the Sheet-+ metric `Q_+` is
   identically equal to multiplying `Φ` on the right by the Sheet-- metric `Q_-`.
3. **Total Metric Centrality vs. Dipole Anticommutation:**
   `[V, Φ] = 0` and `[V, J] = 0`, whereas `{Σ, Φ} = 0` and `{Σ, J} = 0`.
-/
theorem archetype_S0_S1_bimetric_sheets_and_reflective_intertwining
    {P : B} (hP : P * P = P) (X Y : B) :
    let Qp  := metricPlus P X Y
    let Qm  := metricMinus P X Y
    let Phi := genPhi P X Y
    let J   := genJ P X Y
    let V   := genV P X Y
    let Sig := genSig P X Y
    -- 1. Orthogonal localization of the two sheet metrics Q_+ and Q_-:
    P * Qp * P = Qp ∧
    (1 - P) * Qm * (1 - P) = Qm ∧
    Qp * Qm = 0 ∧
    Qm * Qp = 0 ∧
    -- 2. Exact bimetric intertwining across the reflective boundary Φ:
    Qp * Phi = Phi * Qm ∧
    Qm * Phi = Phi * Qp ∧
    Qp * Phi = conePlus P X * coneMinus P Y * conePlus P X ∧
    Qm * Phi = coneMinus P Y * conePlus P X * coneMinus P Y ∧
    -- 3. Commutation of V vs. Anticommutation of Σ with Φ and J:
    rcomm V Phi   = 0 ∧
    rcomm V J     = 0 ∧
    racomm Sig Phi = 0 ∧
    racomm Sig J   = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_bimetric_abel hP

/--
**Archetype S₂ (`archetype_S2_double_commutator_bohm_curvature_and_continuity`):**
For ANY idempotent `P * P = P` and ANY `X, Y ∈ B`:
1. **Continuity & Grading Relations:** `[S_P, Φ] = 2 J` and `[Φ, J] = -2 Σ`.
2. **Kernel of the Double-Commutator Curvature `Q_Bohm(Φ, ·) = -[Φ, [Φ, ·]]`:**
   `Q_Bohm(Φ, V) = 0` and `Q_Bohm(Φ, Φ) = 0`.
3. **Harmonic Eigenvalue Restoration on `J` and `Σ`:**
   `Q_Bohm(Φ, J) = -4 V J` and `Q_Bohm(Φ, Σ) = -4 V Σ`.
-/
theorem archetype_S2_double_commutator_bohm_curvature_and_continuity
    {P : B} (hP : P * P = P) (X Y : B) :
    let SP  := invS P
    let Phi := genPhi P X Y
    let J   := genJ P X Y
    let V   := genV P X Y
    let Sig := genSig P X Y
    -- 1. Continuity & chiral grading commutators:
    rcomm SP Phi  = J + J ∧
    rcomm Phi J   = -(Sig + Sig) ∧
    -- 2. Vanishing of double-commutator curvature on V and Φ:
    bohmCurv P X Y V   = 0 ∧
    bohmCurv P X Y Phi = 0 ∧
    -- 3. Exact -4 V restoration on J and Σ:
    bohmCurv P X Y J   = -((V + V + V + V) * J) ∧
    bohmCurv P X Y Sig = -((V + V + V + V) * Sig) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_bimetric_abel hP

-- ============================================================================
-- 2. 2x2 BLOCK OPERATOR REALIZATION `Mat2 B`: SHEET EXCHANGE & CPT BALANCE
-- ============================================================================

/-- Formal $2 \times 2$ block matrix carrier over $\alpha$. -/
@[ext]
structure Mat2 (α : Type u) where
  a11 : α
  a12 : α
  a21 : α
  a22 : α
  deriving DecidableEq, Repr

namespace Mat2

@[simp] def zero : Mat2 B := ⟨0, 0, 0, 0⟩
@[simp] def one  : Mat2 B := ⟨1, 0, 0, 1⟩
@[simp] def add (M N : Mat2 B) : Mat2 B := ⟨M.a11 + N.a11, M.a12 + N.a12, M.a21 + N.a21, M.a22 + N.a22⟩
@[simp] def neg (M : Mat2 B)   : Mat2 B := ⟨-M.a11, -M.a12, -M.a21, -M.a22⟩
@[simp] def sub (M N : Mat2 B) : Mat2 B := ⟨M.a11 - N.a11, M.a12 - N.a12, M.a21 - N.a21, M.a22 - N.a22⟩
@[simp] def mul (M N : Mat2 B) : Mat2 B :=
  ⟨M.a11 * N.a11 + M.a12 * N.a21, M.a11 * N.a12 + M.a12 * N.a22,
   M.a21 * N.a11 + M.a22 * N.a21, M.a21 * N.a12 + M.a22 * N.a22⟩

instance : Zero (Mat2 B) := ⟨zero⟩
instance : One (Mat2 B)  := ⟨one⟩
instance : Inhabited (Mat2 B) := ⟨zero⟩
instance : Add (Mat2 B)  := ⟨add⟩
instance : Neg (Mat2 B)  := ⟨neg⟩
instance : Sub (Mat2 B)  := ⟨sub⟩
instance : Mul (Mat2 B)  := ⟨mul⟩

@[simp] lemma zero_a11 : (0 : Mat2 B).a11 = 0 := by
  have h : (0 : Mat2 B) = zero := Eq.refl _
  exact congrArg Mat2.a11 h

@[simp] lemma zero_a12 : (0 : Mat2 B).a12 = 0 := by
  have h : (0 : Mat2 B) = zero := Eq.refl _
  exact congrArg Mat2.a12 h

@[simp] lemma zero_a21 : (0 : Mat2 B).a21 = 0 := by
  have h : (0 : Mat2 B) = zero := Eq.refl _
  exact congrArg Mat2.a21 h

@[simp] lemma zero_a22 : (0 : Mat2 B).a22 = 0 := by
  have h : (0 : Mat2 B) = zero := Eq.refl _
  exact congrArg Mat2.a22 h

@[simp] lemma one_a11 : (1 : Mat2 B).a11 = 1 := by
  have h : (1 : Mat2 B) = one := Eq.refl _
  exact congrArg Mat2.a11 h

@[simp] lemma one_a12 : (1 : Mat2 B).a12 = 0 := by
  have h : (1 : Mat2 B) = one := Eq.refl _
  exact congrArg Mat2.a12 h

@[simp] lemma one_a21 : (1 : Mat2 B).a21 = 0 := by
  have h : (1 : Mat2 B) = one := Eq.refl _
  exact congrArg Mat2.a21 h

@[simp] lemma one_a22 : (1 : Mat2 B).a22 = 1 := by
  have h : (1 : Mat2 B) = one := Eq.refl _
  exact congrArg Mat2.a22 h

@[simp] lemma add_a11 (M N : Mat2 B) : (M + N).a11 = M.a11 + N.a11 := by
  have h : M + N = add M N := Eq.refl _
  exact congrArg Mat2.a11 h

@[simp] lemma add_a12 (M N : Mat2 B) : (M + N).a12 = M.a12 + N.a12 := by
  have h : M + N = add M N := Eq.refl _
  exact congrArg Mat2.a12 h

@[simp] lemma add_a21 (M N : Mat2 B) : (M + N).a21 = M.a21 + N.a21 := by
  have h : M + N = add M N := Eq.refl _
  exact congrArg Mat2.a21 h

@[simp] lemma add_a22 (M N : Mat2 B) : (M + N).a22 = M.a22 + N.a22 := by
  have h : M + N = add M N := Eq.refl _
  exact congrArg Mat2.a22 h

@[simp] lemma neg_a11 (M : Mat2 B) : (-M).a11 = -M.a11 := by
  have h : -M = neg M := Eq.refl _
  exact congrArg Mat2.a11 h

@[simp] lemma neg_a12 (M : Mat2 B) : (-M).a12 = -M.a12 := by
  have h : -M = neg M := Eq.refl _
  exact congrArg Mat2.a12 h

@[simp] lemma neg_a21 (M : Mat2 B) : (-M).a21 = -M.a21 := by
  have h : -M = neg M := Eq.refl _
  exact congrArg Mat2.a21 h

@[simp] lemma neg_a22 (M : Mat2 B) : (-M).a22 = -M.a22 := by
  have h : -M = neg M := Eq.refl _
  exact congrArg Mat2.a22 h

@[simp] lemma sub_a11 (M N : Mat2 B) : (M - N).a11 = M.a11 - N.a11 := by
  have h : M - N = sub M N := Eq.refl _
  exact congrArg Mat2.a11 h

@[simp] lemma sub_a12 (M N : Mat2 B) : (M - N).a12 = M.a12 - N.a12 := by
  have h : M - N = sub M N := Eq.refl _
  exact congrArg Mat2.a12 h

@[simp] lemma sub_a21 (M N : Mat2 B) : (M - N).a21 = M.a21 - N.a21 := by
  have h : M - N = sub M N := Eq.refl _
  exact congrArg Mat2.a21 h

@[simp] lemma sub_a22 (M N : Mat2 B) : (M - N).a22 = M.a22 - N.a22 := by
  have h : M - N = sub M N := Eq.refl _
  exact congrArg Mat2.a22 h

@[simp] lemma mul_a11 (M N : Mat2 B) : (M * N).a11 = M.a11 * N.a11 + M.a12 * N.a21 := by
  have h : M * N = mul M N := Eq.refl _
  exact congrArg Mat2.a11 h

@[simp] lemma mul_a12 (M N : Mat2 B) : (M * N).a12 = M.a11 * N.a12 + M.a12 * N.a22 := by
  have h : M * N = mul M N := Eq.refl _
  exact congrArg Mat2.a12 h

@[simp] lemma mul_a21 (M N : Mat2 B) : (M * N).a21 = M.a21 * N.a11 + M.a22 * N.a21 := by
  have h : M * N = mul M N := Eq.refl _
  exact congrArg Mat2.a21 h

@[simp] lemma mul_a22 (M N : Mat2 B) : (M * N).a22 = M.a21 * N.a12 + M.a22 * N.a22 := by
  have h : M * N = mul M N := Eq.refl _
  exact congrArg Mat2.a22 h

/-- Sheet-exchange involution `Ex = [[0, 1], [1, 0]]` swapping Sheet + and Sheet -. -/
@[simp] def Ex : Mat2 B := ⟨0, 1, 1, 0⟩

/-- Symplectic sheet-reversal `Ey = [[0, -1], [1, 0]]`. -/
@[simp] def Ey : Mat2 B := ⟨0, -1, 1, 0⟩

/-- Sheet grading `Ez = [[1, 0], [0, -1]]`. -/
@[simp] def Ez : Mat2 B := ⟨1, 0, 0, -1⟩

@[simp] def tr2 (M : Mat2 B) : B := M.a11 + M.a22
@[simp] def trp (M : Mat2 B) : Mat2 B := ⟨M.a11, M.a21, M.a12, M.a22⟩
@[simp] def adj (M : Mat2 B) : Mat2 B := ⟨M.a22, -M.a12, -M.a21, M.a11⟩
@[simp] def diagScalar (c : B) : Mat2 B := ⟨c, 0, 0, c⟩

/-- Reflective boundary matrix `Φ(A, C) = [[0, A], [C, 0]]`. -/
@[simp] def matPhi (A C : B) : Mat2 B := ⟨0, A, C, 0⟩

/-- Skew phase current matrix `J(A, C) = [[0, A], [-C, 0]]`. -/
@[simp] def matJ (A C : B) : Mat2 B := ⟨0, A, -C, 0⟩

/-- Total bimetric matrix `V(A, C) = [[A C, 0], [0, C A]]`. -/
@[simp] def matV (A C : B) : Mat2 B := ⟨A * C, 0, 0, C * A⟩

/-- Bimetric asymmetry dipole matrix `Σ(A, C) = [[A C, 0], [0, -C A]]`. -/
@[simp] def matSig (A C : B) : Mat2 B := ⟨A * C, 0, 0, -(C * A)⟩

/-- Conjugate-transpose star operation on `Mat2 B` when `[StarRing B]`. -/
@[simp] def starMat [StarRing B] (M : Mat2 B) : Mat2 B :=
  ⟨star M.a11, star M.a21, star M.a12, star M.a22⟩

macro "nc_mat2_full" : tactic =>
  `(tactic| (
    (try ext) <;>
    (simp only [matPhi, matJ, matV, matSig, Ex, Ey, Ez, trp, adj, tr2, diagScalar, rcomm,
                zero_a11, zero_a12, zero_a21, zero_a22,
                one_a11, one_a12, one_a21, one_a22,
                add_a11, add_a12, add_a21, add_a22,
                neg_a11, neg_a12, neg_a21, neg_a22,
                sub_a11, sub_a12, sub_a21, sub_a22,
                mul_a11, mul_a12, mul_a21, mul_a22,
                mul_add, add_mul, sub_mul, mul_sub,
                mul_zero, zero_mul, mul_one, one_mul,
                add_zero, zero_add, sub_zero, zero_sub,
                neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
                mul_assoc];
     try abel)))

/--
**Archetype S₃ (`archetype_S3_matrix_sheet_exchange_and_symplectic_adjugate`):**
In `Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. `Φ² = V`, `J² = -V`, and `Ez * V = Σ`.
2. **Sheet-Exchange Duality (`Ex · Ex`):**
   - `Ex * V(A, C) * Ex = V(C, A)` (swaps the two sheet metrics `A C ↔ C A`),
   - `Σ(A, C) + Ex * Σ(A, C) * Ex = diagScalar([A, C])` and `tr₂(Σ(A, C)) = [A, C]`.
3. **Symplectic Adjugate Realization (`-Ey * trp M * Ey = adj M` and `-Ey * M * Ey = trp (adj M)`):**
   Conjugating `trp M` by `Ey` realizes the formal adjugate `adj M = [[D_-, -A], [-C, D_+]]`,
   while conjugating `M` directly by `Ey` realizes the transposed adjugate `trp (adj M) = [[D_-, -C], [-A, D_+]]`.
-/
theorem archetype_S3_matrix_sheet_exchange_and_symplectic_adjugate
    (A C : B) (M : Mat2 B) :
    let Phi := matPhi A C
    let J   := matJ A C
    let V   := matV A C
    let Sig := matSig A C
    -- 1. Squares and grading:
    Phi * Phi = V ∧
    J * J     = -V ∧
    Ez * V    = Sig ∧
    -- 2. Sheet-exchange duality & global dipole commutator law:
    Ex * V * Ex = matV C A ∧
    Sig + Ex * Sig * Ex = diagScalar (rcomm A C) ∧
    tr2 Sig = rcomm A C ∧
    -- 3. Symplectic sheet-reversal realizes the formal adjugate on `trp M` and transposed adjugate on `M`:
    -(Ey * trp M * Ey) = adj M ∧
    -(Ey * M * Ey) = trp (adj M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nc_mat2_full

/--
**Archetype S₄ (`archetype_S4_star_ring_gramian_duality_and_cpt_balance`):**
Over ANY non-commutative `[Ring B] [StarRing B]`, for `C = star A`:
1. `Φ = [[0, A], [A⋆, 0]]`, `V = [[A A⋆, 0], [0, A⋆ A]]`, and `Σ = [[A A⋆, 0], [0, -A⋆ A]]`
   are strictly self-adjoint under `starMat`, while `J = [[0, A], [-A⋆, 0]]` is skew-adjoint.
2. Under the combined CPT sheet-reflection `Θ_CPT(Z) = Ex * starMat(Z) * Ex`,
   the global twin-sheet sum `Σ + Θ_CPT(Σ)` equals `diagScalar([A, A⋆])`.
-/
theorem archetype_S4_star_ring_gramian_duality_and_cpt_balance
    [StarRing B] (A : B) :
    let Phi := matPhi A (star A)
    let J   := matJ A (star A)
    let V   := matV A (star A)
    let Sig := matSig A (star A)
    starMat Phi = Phi ∧
    starMat J   = -J ∧
    starMat V   = V ∧
    starMat Sig = Sig ∧
    Sig + Ex * starMat Sig * Ex = diagScalar (rcomm A (star A)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp only [starMat, matPhi, star_zero, star_star]
  · ext <;> simp only [starMat, matJ, neg_a11, neg_a12, neg_a21, neg_a22,
                       star_zero, star_neg, star_star, neg_zero, neg_neg]
  · ext <;> simp only [starMat, matV, star_mul, star_star, star_zero]
  · ext <;> simp only [starMat, matSig, star_mul, star_neg, star_star, star_zero]
  · ext <;> (simp only [starMat, matSig, Ex, diagScalar, rcomm,
                       mul_a11, mul_a12, mul_a21, mul_a22,
                       add_a11, add_a12, add_a21, add_a22,
                       star_mul, star_neg, star_star, star_zero,
                       mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]; try abel)

end Mat2
end NonCommutativeBimetricSheetGeometry
