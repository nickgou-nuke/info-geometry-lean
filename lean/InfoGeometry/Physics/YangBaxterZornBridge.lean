import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import InfoGeometry.Physics.SplitOctonionBraidSU3
import InfoGeometry.Physics.YangBaxterQSwap
import InfoGeometry.Physics.B3PresentedGroup

/-!
# Yang-Baxter Zorn Bridge

This file formalizes the bridge between the **associative** Yang-Baxter 
q-swap tensor embeddings (M₂ ⊗ M₂ ⊗ M₂) and the **non-associative** 
complexified split-octonion Zorn multiplication.
-/

noncomputable section

namespace InfoGeometry.Physics.YangBaxterZornBridge

open Matrix
open SplitOctonionBraidSU3
open YangBaxterQSwap

/-! ## 1. Zorn ↔ Fin 8 Phase Space Isomorphism -/

/-- Embed a Zorn matrix into the standard 8D quantum phase space -/
def zornToFin8 (X : Zorn) : Fin 8 → ℂ :=
  ![X.a, X.u 0, X.u 1, X.u 2, X.v 0, X.v 1, X.v 2, X.b]

/-- Project the 8D phase space back into a non-associative Zorn matrix -/
def fin8ToZorn (v : Fin 8 → ℂ) : Zorn where
  a := v 0
  u := fun i =>
    match i with
    | ⟨0, _⟩ => v 1
    | ⟨1, _⟩ => v 2
    | ⟨2, _⟩ => v 3
  v := fun i =>
    match i with
    | ⟨0, _⟩ => v 4
    | ⟨1, _⟩ => v 5
    | ⟨2, _⟩ => v 6
  b := v 7

def LeftMulQ (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j =>
    let e_j : Fin 8 → ℂ := fun x => if x = j then (1 : ℂ) else 0
    zornToFin8 (zornMul (Q_k k) (fin8ToZorn e_j)) i

def Id8 : Matrix (Fin 8) (Fin 8) ℂ := 1

/-- 
The fundamental isomorphism: Left-multiplication by the Braid generator R_k 
acts as an 8×8 complex matrix over the state vector.
-/
def LeftMulR (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => 
    let e_j := fun (x : Fin 8) => if x = j then (1 : ℂ) else 0
    let Z_j := fin8ToZorn e_j
    let R_Z_j := zornMul (R_k k) Z_j
    (zornToFin8 R_Z_j) i

/-! ## 2. The Yang-Baxter Operator Bridge -/

theorem fin8ToZorn_zornToFin8 (X : Zorn) :
    fin8ToZorn (zornToFin8 X) = X := by
  apply zorn_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem zornToFin8_fin8ToZorn (v : Fin 8 → ℂ) :
    zornToFin8 (fin8ToZorn v) = v := by
  funext i
  fin_cases i <;> rfl

theorem zornToFin8_add (X Y : Zorn) :
    zornToFin8 (zornAdd X Y) = zornToFin8 X + zornToFin8 Y := by
  funext i; fin_cases i <;> rfl

theorem zornToFin8_smul (c : ℂ) (X : Zorn) :
    zornToFin8 (zornSmul c X) = c • zornToFin8 X := by
  funext i; fin_cases i <;> rfl

theorem LeftMulR_eq (k : Fin 3) :
    LeftMulR k = Id8 + Complex.I • LeftMulQ k := by
  ext row col
  dsimp [LeftMulR, Id8, LeftMulQ, R_k, unnormalizedR_k]
  have h1 : zornMul (zornAdd I_zorn (zornSmul I_c (Q_k k))) (fin8ToZorn (fun x => if x = col then (1 : ℂ) else 0)) = 
            zornAdd (zornMul I_zorn (fin8ToZorn (fun x => if x = col then (1 : ℂ) else 0))) 
                    (zornMul (zornSmul I_c (Q_k k)) (fin8ToZorn (fun x => if x = col then (1 : ℂ) else 0))) := add_zornMul _ _ _
  rw [h1]
  rw [zornToFin8_add, smul_zornMul, I_zorn_zornMul, zornToFin8_smul]
  rw [Pi.add_apply, Pi.smul_apply]
  have h_id : zornToFin8 (fin8ToZorn (fun x => if x = col then (1 : ℂ) else 0)) row = if row = col then (1 : ℂ) else 0 := by
    rw [zornToFin8_fin8ToZorn]
  rw [h_id]
  split_ifs with h
  · simp [h, I_c]
    change (1 : ℂ) = (1 : Matrix (Fin 8) (Fin 8) ℂ) row col
    rw [Matrix.one_apply, if_pos h]
  · simp [h, I_c]

theorem LeftMulQ_apply (k : Fin 3) (v : Fin 8 → ℂ) :
    LeftMulQ k *ᵥ v = zornToFin8 (zornMul (Q_k k) (fin8ToZorn v)) := by
  ext r
  fin_cases k <;> fin_cases r <;>
  simp [LeftMulQ, Matrix.mulVec, dotProduct, Q_k, e_k, zornToFin8, fin8ToZorn, zornMul, dot3, cross3]

/-- The Zorn composition norm transported to the standard eight coordinates. -/
def fin8ZornNorm (v : Fin 8 → ℂ) : ℂ :=
  zornNorm (fin8ToZorn v)

/-- Every Clifford generator has split-octonion norm `-1`. -/
theorem zornNorm_Q_k (k : Fin 3) :
    zornNorm (Q_k k) = -1 := by
  fin_cases k <;> simp [zornNorm, Q_k, e_k, dot3]

/-- Clifford left multiplication reverses the transported composition norm. -/
theorem fin8ZornNorm_LeftMulQ (k : Fin 3) (v : Fin 8 → ℂ) :
    fin8ZornNorm (LeftMulQ k *ᵥ v) = -fin8ZornNorm v := by
  simp [fin8ZornNorm, LeftMulQ_apply, fin8ToZorn_zornToFin8,
    zornNorm_mul, zornNorm_Q_k]

theorem Q_k_sq_zorn (k : Fin 3) (Z : Zorn) :
    zornMul (Q_k k) (zornMul (Q_k k) Z) = Z := by
  apply zorn_ext
  · fin_cases k <;> (simp [zornMul, Q_k, e_k, dot3, cross3]; try ring)
  · funext i; fin_cases k <;> fin_cases i <;> (simp [zornMul, Q_k, e_k, dot3, cross3]; try ring)
  · funext i; fin_cases k <;> fin_cases i <;> (simp [zornMul, Q_k, e_k, dot3, cross3]; try ring)
  · fin_cases k <;> (simp [zornMul, Q_k, e_k, dot3, cross3]; try ring)

theorem Q_k_anticommute_zorn (i j : Fin 3) (h : i ≠ j) (Z : Zorn) :
    zornAdd (zornMul (Q_k i) (zornMul (Q_k j) Z))
            (zornMul (Q_k j) (zornMul (Q_k i) Z)) = zornZero := by
  apply zorn_ext
  · fin_cases i <;> fin_cases j <;> (first | exact (h rfl).elim | (simp [zornMul, zornAdd, zornZero, Q_k, e_k, dot3, cross3]; try ring))
  · funext idx; fin_cases i <;> fin_cases j <;> fin_cases idx <;> (first | exact (h rfl).elim | (simp [zornMul, zornAdd, zornZero, Q_k, e_k, dot3, cross3]; try ring))
  · funext idx; fin_cases i <;> fin_cases j <;> fin_cases idx <;> (first | exact (h rfl).elim | (simp [zornMul, zornAdd, zornZero, Q_k, e_k, dot3, cross3]; try ring))
  · fin_cases i <;> fin_cases j <;> (first | exact (h rfl).elim | (simp [zornMul, zornAdd, zornZero, Q_k, e_k, dot3, cross3]; try ring))

theorem leftMulQ_sq (k : Fin 3) :
    LeftMulQ k * LeftMulQ k = Id8 := by
  ext r c
  have h1 : (LeftMulQ k * LeftMulQ k) r c = (LeftMulQ k *ᵥ (LeftMulQ k *ᵥ (fun x => if x = c then (1:ℂ) else 0))) r := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [h1, LeftMulQ_apply, LeftMulQ_apply, fin8ToZorn_zornToFin8, Q_k_sq_zorn, zornToFin8_fin8ToZorn]
  change (if r = c then (1 : ℂ) else 0) = (1 : Matrix (Fin 8) (Fin 8) ℂ) r c
  simp [Matrix.one_apply]

theorem zornToFin8_zero : zornToFin8 zornZero = 0 := by
  ext i
  fin_cases i <;> rfl

theorem leftMulQ_anticommute (i j : Fin 3) (h : i ≠ j) :
    LeftMulQ i * LeftMulQ j = -(LeftMulQ j * LeftMulQ i) := by
  ext r c
  have h_add : (LeftMulQ i * LeftMulQ j) r c + (LeftMulQ j * LeftMulQ i) r c = 0 := by
    have h1 : (LeftMulQ i * LeftMulQ j) r c = (LeftMulQ i *ᵥ (LeftMulQ j *ᵥ (fun x => if x = c then (1:ℂ) else 0))) r := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    have h2 : (LeftMulQ j * LeftMulQ i) r c = (LeftMulQ j *ᵥ (LeftMulQ i *ᵥ (fun x => if x = c then (1:ℂ) else 0))) r := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [h1, h2, LeftMulQ_apply, LeftMulQ_apply, LeftMulQ_apply, LeftMulQ_apply]
    rw [fin8ToZorn_zornToFin8, fin8ToZorn_zornToFin8]
    rw [← Pi.add_apply, ← zornToFin8_add, Q_k_anticommute_zorn i j h]
    rw [zornToFin8_zero, Pi.zero_apply]
  exact eq_neg_iff_add_eq_zero.mpr h_add

/-- 
The left-multiplication matrices associated with distinct Clifford
generators satisfy the Artin braid relation.
-/
theorem leftMulR_braid_relation
    (i j : Fin 3) (h : i ≠ j) :
    LeftMulR i * LeftMulR j * LeftMulR i =
      LeftMulR j * LeftMulR i * LeftMulR j := by
  simp only [LeftMulR_eq]
  have hi := leftMulQ_sq i
  have hj := leftMulQ_sq j
  have hij := leftMulQ_anticommute i j h
  have hji := leftMulQ_anticommute j i h.symm
  dsimp [Id8] at hi hj
  dsimp [Id8]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, 
             Matrix.one_mul, Matrix.mul_one, smul_smul, smul_add]
  have i_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [i_sq, neg_smul, add_assoc]
  have hLHS : LeftMulQ i * LeftMulQ j * LeftMulQ i = -LeftMulQ j := by
    rw [hij, Matrix.neg_mul, Matrix.mul_assoc, hi, Matrix.mul_one]
  have hRHS : LeftMulQ j * LeftMulQ i * LeftMulQ j = -LeftMulQ i := by
    rw [hji, Matrix.neg_mul, Matrix.mul_assoc, hj, Matrix.mul_one]
  rw [hi, hj, hLHS, hRHS, hij]
  module

/-! ## 3. Invertible B₃ generator data -/

def LeftMulRInv (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℂ :=
  (2 : ℂ)⁻¹ • (Id8 - Complex.I • LeftMulQ k)

theorem LeftMulR_mul_LeftMulRInv (k : Fin 3) :
    LeftMulR k * LeftMulRInv k = Id8 := by
  rw [LeftMulR_eq]
  dsimp [LeftMulRInv, Id8]
  have hi := leftMulQ_sq k
  dsimp [Id8] at hi
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  have i_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [hi]
  simp only [sub_eq_add_neg]
  ext r c
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs with h
  · ring_nf
  · ring_nf

theorem LeftMulRInv_mul_LeftMulR (k : Fin 3) :
    LeftMulRInv k * LeftMulR k = Id8 := by
  rw [LeftMulR_eq]
  dsimp [LeftMulRInv, Id8]
  have hi := leftMulQ_sq k
  dsimp [Id8] at hi
  simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.one_mul, Matrix.mul_one]
  have i_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [hi]
  simp only [sub_eq_add_neg]
  ext r c
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs with h
  · ring_nf; try { simp [Complex.I_sq]; norm_num }
  · ring_nf

theorem isUnit_LeftMulR (k : Fin 3) :
    IsUnit (LeftMulR k) := by
  exact ⟨⟨LeftMulR k, LeftMulRInv k, LeftMulR_mul_LeftMulRInv k, LeftMulRInv_mul_LeftMulR k⟩, rfl⟩

abbrev GL8 := Matrix.GeneralLinearGroup (Fin 8) ℂ

def braidGen1 : GL8 where
  val := LeftMulR 0
  inv := LeftMulRInv 0
  val_inv := LeftMulR_mul_LeftMulRInv 0
  inv_val := LeftMulRInv_mul_LeftMulR 0

def braidGen2 : GL8 where
  val := LeftMulR 1
  inv := LeftMulRInv 1
  val_inv := LeftMulR_mul_LeftMulRInv 1
  inv_val := LeftMulRInv_mul_LeftMulR 1

theorem leftMulR_B3_braid :
    LeftMulR 0 * LeftMulR 1 * LeftMulR 0 =
      LeftMulR 1 * LeftMulR 0 * LeftMulR 1 := by
  exact leftMulR_braid_relation 0 1 (by decide)

/-- The packaged invertible generators satisfy the defining `B₃` braid relation. -/
theorem braidGen_B3_braid :
    braidGen1 * braidGen2 * braidGen1 =
      braidGen2 * braidGen1 * braidGen2 := by
  apply Units.ext
  exact leftMulR_B3_braid

/-! ### Presented-group representation -/

/-- Assignment of the two abstract Artin generators to the Zorn matrix units. -/
def zornBraidMap : B3PresentedGroup.B3Gen → GL8
  | .sig0 => braidGen1
  | .sig1 => braidGen2

/-- The defining `B₃` relation evaluates to the identity under the Zorn assignment. -/
theorem zorn_b3_relation_holds :
    FreeGroup.lift zornBraidMap B3PresentedGroup.b3Relation = 1 := by
  simp only [B3PresentedGroup.b3Relation, map_mul, map_inv,
    FreeGroup.lift_apply_of, zornBraidMap]
  rw [braidGen_B3_braid]
  group

/-- The Zorn/Clifford representation of the presented braid group `B₃`. -/
def zornPhi : B3PresentedGroup.B3 →* GL8 :=
  PresentedGroup.toGroup
    (f := zornBraidMap)
    (rels := B3PresentedGroup.b3Relations) (by
      intro r hr
      simp [B3PresentedGroup.b3Relations] at hr
      subst r
      exact zorn_b3_relation_holds)

/-- The first abstract braid generator is represented by `braidGen1`. -/
theorem zornPhi_sig0 :
    zornPhi (PresentedGroup.of B3PresentedGroup.B3Gen.sig0 : B3PresentedGroup.B3) =
      braidGen1 := by
  change PresentedGroup.toGroup
      (f := zornBraidMap) (rels := B3PresentedGroup.b3Relations) _
      (PresentedGroup.of B3PresentedGroup.B3Gen.sig0) = braidGen1
  rw [PresentedGroup.toGroup.of]
  simp [zornBraidMap]

/-- The second abstract braid generator is represented by `braidGen2`. -/
theorem zornPhi_sig1 :
    zornPhi (PresentedGroup.of B3PresentedGroup.B3Gen.sig1 : B3PresentedGroup.B3) =
      braidGen2 := by
  change PresentedGroup.toGroup
      (f := zornBraidMap) (rels := B3PresentedGroup.b3Relations) _
      (PresentedGroup.of B3PresentedGroup.B3Gen.sig1) = braidGen2
  rw [PresentedGroup.toGroup.of]
  simp [zornBraidMap]

/-! ## 4. The Inequivalence Theorem (Mathematical Guardrail) -/

def ProjectivelyEquivalentGeneratorPairs (q : ℂ) : Prop :=
  ∃ c₀ c₁ : ℂ,
    c₀ ≠ 0 ∧ c₁ ≠ 0 ∧
    ∃ P : GL8,
      LeftMulR 0 = c₀ • (P.inv * C12 q * P.val) ∧
      LeftMulR 1 = c₁ • (P.inv * C23 q * P.val)

theorem trace_GL8_conjugate (P : GL8) (A : Matrix (Fin 8) (Fin 8) ℂ) :
    Matrix.trace (P.inv * A * P.val) = Matrix.trace A := by
  calc
    Matrix.trace (P.inv * A * P.val)
        = Matrix.trace (P.val * (P.inv * A)) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((P.val * P.inv) * A) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace A := by rw [P.val_inv, Matrix.one_mul]

theorem GL8_conjugate_mul (P : GL8) (A B : Matrix (Fin 8) (Fin 8) ℂ) :
    (P.inv * A * P.val) * (P.inv * B * P.val) =
      P.inv * (A * B) * P.val := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P.val P.inv (B * P.val), P.val_inv, Matrix.one_mul]

theorem trace_LeftMulQ_zero (k : Fin 3) :
    Matrix.trace (LeftMulQ k) = 0 := by
  fin_cases k <;>
    simp [Matrix.trace, Matrix.diag, LeftMulQ, zornToFin8, fin8ToZorn,
      zornMul, Q_k, e_k, dot3, cross3, Fin.sum_univ_eight]

/-- The square collapses by the Clifford relation `LeftMulQ k * LeftMulQ k = 1`. -/
theorem LeftMulR_sq (k : Fin 3) :
    LeftMulR k * LeftMulR k = (2 * Complex.I) • LeftMulQ k := by
  rw [LeftMulR_eq]
  dsimp [Id8]
  have hq := leftMulQ_sq k
  dsimp [Id8] at hq
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  rw [hq]
  ext r c
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Complex.I_mul_I]
  split_ifs <;> ring

/-- The first trace moment of the axis-zero Zorn braid generator. -/
theorem trace_LeftMulR0 : Matrix.trace (LeftMulR 0) = 8 := by
  rw [LeftMulR_eq, Matrix.trace_add, Matrix.trace_smul, trace_LeftMulQ_zero]
  simp [Id8, Matrix.trace, Matrix.diag]

/-- The squared trace moment vanishes for every Zorn braid generator. -/
theorem trace_sq_LeftMulR (k : Fin 3) :
    Matrix.trace (LeftMulR k * LeftMulR k) = 0 := by
  rw [LeftMulR_sq, Matrix.trace_smul, trace_LeftMulQ_zero]
  simp

theorem trace_sq_LeftMulR_zero : Matrix.trace (LeftMulR 0 * LeftMulR 0) = 0 := by
  exact trace_sq_LeftMulR 0

theorem trace_C12 (q : ℂ) :
    Matrix.trace (YangBaxterQSwap.C12 q) = 4 * q := by
  dsimp [Matrix.trace, Matrix.diag, YangBaxterQSwap.C12, YangBaxterQSwap.C_q, Matrix.smul_apply, Matrix.of_apply]
  simp [Fin.sum_univ_eight]
  ring

theorem trace_sq_C12 (q : ℂ) : Matrix.trace (YangBaxterQSwap.C12 q * YangBaxterQSwap.C12 q) = 8 * q ^ 2 := by
  dsimp [Matrix.trace, Matrix.diag, YangBaxterQSwap.C12, YangBaxterQSwap.C_q, Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply]
  simp [Fin.sum_univ_eight]
  ring

/--
The Clifford/Zorn generator pair is not projectively equivalent to the
`q`-scaled tensor-swap generator pair for nonzero `q`.

The obstruction already appears for the first generator: its squared
trace vanishes, while the squared trace of `C12 q` is `8 * q ^ 2`.
-/
theorem not_projectively_equivalent (q : ℂ) (hq : q ≠ 0) :
    ¬ ProjectivelyEquivalentGeneratorPairs q := by
  rintro ⟨c₀, c₁, hc₀, hc₁, P, hP₀, hP₁⟩
  
  have hsq : LeftMulR 0 * LeftMulR 0 =
      (c₀ • (P.inv * YangBaxterQSwap.C12 q * P.val)) * (c₀ • (P.inv * YangBaxterQSwap.C12 q * P.val)) := by
    rw [hP₀]

  have htrace : Matrix.trace (LeftMulR 0 * LeftMulR 0) =
      Matrix.trace ((c₀ • (P.inv * YangBaxterQSwap.C12 q * P.val)) * (c₀ • (P.inv * YangBaxterQSwap.C12 q * P.val))) := by
    rw [hsq]
    
  have hconj : (P.inv * YangBaxterQSwap.C12 q * P.val) * (P.inv * YangBaxterQSwap.C12 q * P.val) =
        P.inv * (YangBaxterQSwap.C12 q * YangBaxterQSwap.C12 q) * P.val :=
    GL8_conjugate_mul P _ _
    
  rw [trace_sq_LeftMulR_zero] at htrace
  
  have hRHS : Matrix.trace ((c₀ • (P.inv * YangBaxterQSwap.C12 q * P.val)) * (c₀ • (P.inv * YangBaxterQSwap.C12 q * P.val))) =
      c₀ ^ 2 * (8 * q ^ 2) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hconj]
    rw [Matrix.trace_smul, trace_GL8_conjugate, trace_sq_C12]
    simp only [smul_eq_mul]
    ring
    
  rw [hRHS] at htrace
  
  have hc₀sq : c₀ ^ 2 ≠ 0 := pow_ne_zero 2 hc₀
  have hqsq : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
  
  symm at htrace
  have hzero : c₀ ^ 2 * (8 * q ^ 2) ≠ 0 := mul_ne_zero hc₀sq (mul_ne_zero (by norm_num) hqsq)
  exact hzero htrace

end InfoGeometry.Physics.YangBaxterZornBridge
