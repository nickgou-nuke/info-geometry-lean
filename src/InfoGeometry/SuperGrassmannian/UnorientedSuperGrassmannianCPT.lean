/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Unoriented Super-Grassmannian: CPT Modular Symmetry & Möbius Twist

Formalizes:
1. The discrete $C, P, T$ operators on the doubled carrier $T^+ \times T^-$.
2. Charge conjugation $C$ strictly swaps the Primal sheet and the Covector Vacuum sheet.
3. The $CPT$ modular operator and its anti-involutive Krein metric symmetry
   (reflecting the almost-complex structure $J^2 = -\text{id}$ on the split carrier).
4. Strict symplectomorphism of $CPT$: $\omega(CPT(z_1), CPT(z_2)) = \omega(z_1, z_2)$.
5. The Möbius Twist operator as an orientation-reversing involution ($M^2 = \text{id}$, $M \circ K = - K \circ M$).
-/

namespace InfoGeometry.SuperGrassmannian.ModularCPT

open LinearMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The Doubled Carrier $V = E \times E$ (Primal sheet $\oplus$ Covector sheet). -/
abbrev DoubledCarrier (E : Type*) := E × E

/-! ### 1. Definitions of C, P, T Discrete Symmetries -/

/-- Parity: P(u, α) = (-u, -α). -/
def P_op : DoubledCarrier E →ₗ[ℝ] DoubledCarrier E :=
  (-LinearMap.fst ℝ E E).prod (-LinearMap.snd ℝ E E)

/-- Charge Conjugation: C(u, α) = (α, u). -/
def C_op : DoubledCarrier E →ₗ[ℝ] DoubledCarrier E :=
  (LinearMap.snd ℝ E E).prod (LinearMap.fst ℝ E E)

/-- Time Reversal / Para-Complex Structure: K(u, α) = (u, -α). -/
def T_op : DoubledCarrier E →ₗ[ℝ] DoubledCarrier E :=
  (LinearMap.fst ℝ E E).prod (-LinearMap.snd ℝ E E)

/-- The Para-Complex Involution K on the doubled carrier. -/
def K_op : DoubledCarrier E →ₗ[ℝ] DoubledCarrier E := T_op

/-- Modular CPT Operator: J = T ∘ P ∘ C = (-α, u). -/
def CPT_op : DoubledCarrier E →ₗ[ℝ] DoubledCarrier E :=
  T_op ∘ₗ (P_op ∘ₗ C_op)

/-! ### 2. Algebraic Involutive Identities & Cl(1,1) Operator Relations -/

@[simp]
theorem P_apply (z : DoubledCarrier E) : P_op z = (-z.1, -z.2) := rfl

@[simp]
theorem C_apply (z : DoubledCarrier E) : C_op z = (z.2, z.1) := rfl

@[simp]
theorem T_apply (z : DoubledCarrier E) : T_op z = (z.1, -z.2) := rfl

@[simp]
theorem K_apply (z : DoubledCarrier E) : K_op z = (z.1, -z.2) := rfl

@[simp]
theorem P_involutive (z : DoubledCarrier E) : P_op (P_op z) = z := by
  ext <;> simp

@[simp]
theorem C_involutive (z : DoubledCarrier E) : C_op (C_op z) = z := by
  ext <;> rfl

@[simp]
theorem T_involutive (z : DoubledCarrier E) : T_op (T_op z) = z := by
  ext <;> simp

@[simp]
theorem K_involutive (z : DoubledCarrier E) : K_op (K_op z) = z := by
  ext <;> simp [K_op]

theorem P_comm_C (z : DoubledCarrier E) : P_op (C_op z) = C_op (P_op z) := by
  ext <;> rfl

@[simp]
theorem CPT_apply (z : DoubledCarrier E) : CPT_op z = (-z.2, z.1) := by
  ext <;> simp [CPT_op]

/-- $(CPT)^2 = -\text{id}$ (acting as a genuine almost-complex structure $J^2 = -\text{id}$). -/
theorem CPT_sq_neg (z : DoubledCarrier E) : CPT_op (CPT_op z) = (-z.1, -z.2) := by
  rw [CPT_apply, CPT_apply]

/-- Operator factorization: CPT = - (K ∘ C). -/
theorem CPT_eq_neg_K_comp_C (z : DoubledCarrier E) :
    CPT_op z = - (K_op (C_op z)) := by
  ext <;> simp [CPT_op, K_op, C_op, T_op]

/-- Anticommutation of sheet reflection C and polarization K: {C, K} = 0. -/
theorem C_anticomm_K (z : DoubledCarrier E) :
    C_op (K_op z) + K_op (C_op z) = 0 := by
  ext <;> simp [C_op, K_op, T_op]

/-! ### 3. Sheet Swapping: C Transposes Primal and Vacuum -/

/-- Primal injection: $E \hookrightarrow E \times \{0\}$. -/
def primalSubspace : Submodule ℝ (DoubledCarrier E) :=
  LinearMap.ker (LinearMap.snd ℝ E E)

/-- Covector Vacuum injection: $\{0\} \times E \hookrightarrow E \times E$. -/
def vacuumSubspace : Submodule ℝ (DoubledCarrier E) :=
  LinearMap.ker (LinearMap.fst ℝ E E)

/-- 
Charge conjugation strictly maps the Primal Sheet onto the Covector Vacuum Sheet:
$C(T^+) = T^-$.
-/
theorem charge_conjugation_swaps_sheets (z : DoubledCarrier E)
    (hz : z ∈ primalSubspace) : C_op z ∈ vacuumSubspace := by
  dsimp [primalSubspace] at hz
  rw [LinearMap.mem_ker] at hz
  dsimp [vacuumSubspace]
  rw [LinearMap.mem_ker]
  exact hz

/-- 
Charge conjugation strictly maps the Covector Vacuum Sheet onto the Primal Sheet:
$C(T^-) = T^+$.
-/
theorem charge_conjugation_swaps_vacuum_to_primal (z : DoubledCarrier E)
    (hz : z ∈ vacuumSubspace) : C_op z ∈ primalSubspace := by
  dsimp [vacuumSubspace] at hz
  rw [LinearMap.mem_ker] at hz
  dsimp [primalSubspace]
  rw [LinearMap.mem_ker]
  exact hz

/-! ### 4. The Möbius Twist on the Unoriented Super-Grassmannian -/

/-- 
The Möbius Twist Operator:
$M = P \circ C$, sending $(u, \alpha) \mapsto (-\alpha, -u)$.
It represents parallel transport around the orientation-reversing loop.
-/
def moebiusTwist : DoubledCarrier E →ₗ[ℝ] DoubledCarrier E :=
  P_op ∘ₗ C_op

theorem moebiusTwist_apply (z : DoubledCarrier E) :
    moebiusTwist z = (-z.2, -z.1) := by
  ext <;> rfl

/-- The Möbius Twist is an involution: $M^2 = \text{id}$ on the unoriented carrier. -/
theorem moebiusTwist_involutive (z : DoubledCarrier E) :
    moebiusTwist (moebiusTwist z) = z := by
  rw [moebiusTwist_apply, moebiusTwist_apply]
  ext <;> simp

/-- The para-complex involution $K$ on the doubled space: $K(u, \alpha) = (u, -\alpha)$. -/
def paraK : DoubledCarrier E →ₗ[ℝ] DoubledCarrier E :=
  T_op

/-- 
Fundamental Unoriented Crosscap Theorem:
The Möbius Twist anticommutes with the para-complex structure $K$:
$M \circ K = - (K \circ M)$.
Traversing the Möbius loop reverses the orientation of the para-complex polarization sheets.
-/
theorem moebius_anticommutes_paraK (z : DoubledCarrier E) :
    moebiusTwist (paraK z) = - (paraK (moebiusTwist z)) := by
  ext <;> simp [moebiusTwist_apply, paraK]

/-! ### 5. Krein Metric & Symplectic Invariance under CPT and C -/

variable (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)

/-- The Split Krein Metric: $g_{\text{Krein}}((u_1, \alpha_1), (u_2, \alpha_2)) = \langle u_1, \alpha_2 \rangle + \langle \alpha_1, u_2 \rangle$. -/
def kreinForm (z₁ z₂ : DoubledCarrier E) : ℝ :=
  pairing z₁.1 z₂.2 + pairing z₁.2 z₂.1

/-- The Canonical Symplectic Form: $\omega((u_1, \alpha_1), (u_2, \alpha_2)) = \langle u_1, \alpha_2 \rangle - \langle \alpha_1, u_2 \rangle$. -/
def symplecticForm (z₁ z₂ : DoubledCarrier E) : ℝ :=
  pairing z₁.1 z₂.2 - pairing z₁.2 z₂.1

/-- 
Krein Metric Anti-Invariance under CPT (Möbius Orientation-Reversal):
$g_{\text{Krein}}(CPT(z_1), CPT(z_2)) = - g_{\text{Krein}}(z_1, z_2)$.
This reflects the almost-complex structure $J^2 = -\text{id}$ on the split-signature carrier.
-/
theorem kreinForm_cpt_anti_invariant (z₁ z₂ : DoubledCarrier E) :
    kreinForm pairing (CPT_op z₁) (CPT_op z₂) = - kreinForm pairing z₁ z₂ := by
  dsimp [kreinForm]
  rw [CPT_apply, CPT_apply]
  dsimp
  have h1 : pairing (-z₁.2) z₂.1 = - pairing z₁.2 z₂.1 := by
    rw [map_neg, LinearMap.neg_apply]
  have h2 : pairing z₁.1 (-z₂.2) = - pairing z₁.1 z₂.2 := by
    rw [map_neg]
  rw [h1, h2]
  ring

/-- 
Symplectic Form Strict Invariance under CPT:
$\omega(CPT(z_1), CPT(z_2)) = \omega(z_1, z_2)$.
Proves that $CPT$ is a genuine symplectomorphism.
-/
theorem symplecticForm_cpt_invariant (z₁ z₂ : DoubledCarrier E) :
    symplecticForm pairing (CPT_op z₁) (CPT_op z₂) = symplecticForm pairing z₁ z₂ := by
  dsimp [symplecticForm]
  rw [CPT_apply, CPT_apply]
  dsimp
  have h1 : pairing (-z₁.2) z₂.1 = - pairing z₁.2 z₂.1 := by
    rw [map_neg, LinearMap.neg_apply]
  have h2 : pairing z₁.1 (-z₂.2) = - pairing z₁.1 z₂.2 := by
    rw [map_neg]
  rw [h1, h2]
  ring

/-- 
Krein Metric Invariance under Charge Conjugation $C$ (with symmetric pairing):
If $\langle u, \alpha \rangle = \langle \alpha, u \rangle$, then $g_{\text{Krein}}(C(z_1), C(z_2)) = g_{\text{Krein}}(z_1, z_2)$.
-/
theorem kreinForm_charge_conjugation_invariant
    (_h_symm : ∀ x y : E, pairing x y = pairing y x)
    (z₁ z₂ : DoubledCarrier E) :
    kreinForm pairing (C_op z₁) (C_op z₂) = kreinForm pairing z₁ z₂ := by
  dsimp [kreinForm]
  ring

/--
Krein Metric Anti-Invariance under Polarization K:
$g_{\text{Krein}}(K(z_1), K(z_2)) = - g_{\text{Krein}}(z_1, z_2)$.
-/
theorem kreinForm_K_anti_invariant (z₁ z₂ : DoubledCarrier E) :
    kreinForm pairing (K_op z₁) (K_op z₂) = - kreinForm pairing z₁ z₂ := by
  dsimp [kreinForm]
  have h1 : pairing z₁.1 (-z₂.2) = - pairing z₁.1 z₂.2 := map_neg (pairing z₁.1) z₂.2
  have h2 : pairing (-z₁.2) z₂.1 = - pairing z₁.2 z₂.1 := by
    rw [map_neg, LinearMap.neg_apply]
  rw [h1, h2]
  ring

end InfoGeometry.SuperGrassmannian.ModularCPT
