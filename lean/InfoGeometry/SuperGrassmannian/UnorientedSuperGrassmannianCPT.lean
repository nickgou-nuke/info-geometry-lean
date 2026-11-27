/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import InfoGeometry.Algebra.DeWittPeirceSuperalgebra

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

/-! ### 6. Peirce–DeWitt Four-Corner Split, Pin⁺/Pin⁻ Holonomy, & Antiperiodicity -/

section PeirceDeWittPinCPTHolonomy

open InfoGeometry.Algebra.DeWittPeirceSuperalgebra

/-- Endomorphism ring on the doubled carrier `E × E`. -/
abbrev EndDoubled (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  Module.End ℝ (DoubledCarrier E)

/-- Primal sheet projector `PL(u, α) = (u, 0)` on `DoubledCarrier E`. -/
def projPrimal : EndDoubled E :=
  (LinearMap.fst ℝ E E).prod (0 : DoubledCarrier E →ₗ[ℝ] E)

/-- Vacuum sheet projector `PR(u, α) = (0, α)` on `DoubledCarrier E`. -/
def projVacuum : EndDoubled E :=
  (0 : DoubledCarrier E →ₗ[ℝ] E).prod (LinearMap.snd ℝ E E)

/-- Canonical `ChiralPeirceSystem` structure on `EndDoubled E`. -/
@[instance_reducible]
def endDoubledChiralPeirceSystem : ChiralPeirceSystem (EndDoubled E) where
  PL := projPrimal
  PR := projVacuum
  h_PL_sq := by
    ext x <;> rfl
  h_PR_sq := by
    ext x <;> rfl
  h_sum := by
    ext x <;> simp [projPrimal, projVacuum]
  h_PL_PR := by
    ext x <;> simp [projPrimal, projVacuum]

local instance : ChiralPeirceSystem (EndDoubled E) := endDoubledChiralPeirceSystem

/-- The DeWitt chiral grading `PL - PR` coincides identically with `K_op`. -/
theorem peirceGrading_eq_K_op :
    (G (A := EndDoubled E)) = K_op := by
  change (projPrimal - projVacuum : EndDoubled E) = K_op
  ext x <;> simp [projPrimal, projVacuum, K_op, T_op]

/-- In `EndDoubled E`: `CPT = K ∘ M`, the Möbius twist is a `Pin⁺` involution (`M² = +1`),
and `CPT` is a `Pin⁻` square-`-1` lift (`CPT² = -1`). -/
theorem cpt_moebius_pin_signatures :
    (CPT_op : EndDoubled E) = K_op * moebiusTwist ∧
    (moebiusTwist : EndDoubled E) * moebiusTwist = 1 ∧
    (CPT_op : EndDoubled E) * CPT_op = -1 ∧
    (K_op : EndDoubled E) * moebiusTwist = -(moebiusTwist * K_op) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x <;> simp [CPT_op, K_op, moebiusTwist, T_op, P_op, C_op]
  · ext x <;> simp [moebiusTwist, P_op, C_op]
  · ext x <;> simp [CPT_op, T_op, P_op, C_op]
  · ext x <;> simp [K_op, moebiusTwist, T_op, P_op, C_op]

/-- Non-commutativity witness on `EndDoubled ℝ`: Möbius twist and `K_op` do not commute. -/
theorem moebiusTwist_K_noncommutative_real :
    (moebiusTwist : EndDoubled ℝ) * K_op ≠ K_op * moebiusTwist := by
  intro h
  have hv := congrArg (fun f : EndDoubled ℝ => (f ((0 : ℝ), (1 : ℝ))).1) h
  simp [moebiusTwist, K_op, T_op, P_op, C_op] at hv
  linarith

/-- The `Pin⁺` Möbius twist exchanges the primal and vacuum Peirce sheet projectors. -/
theorem moebiusTwist_swaps_sheets :
    (moebiusTwist : EndDoubled E) * projPrimal = projVacuum * moebiusTwist ∧
    (moebiusTwist : EndDoubled E) * projVacuum = projPrimal * moebiusTwist := by
  constructor <;> ext x <;> simp [moebiusTwist, P_op, C_op, projPrimal, projVacuum]

/-- Relative `Pin⁻` (`CPT_op`) vs. `Pin⁺` (`moebiusTwist`) adjoint holonomy on Peirce–DeWitt
body and soul components: the even `body` receives `+1` relative holonomy, while the odd `soul`
receives `-1` relative holonomy. -/
theorem cpt_vs_moebius_body_soul_holonomy (X : EndDoubled E) :
    (CPT_op : EndDoubled E) * X * (-CPT_op) =
      K_op * (moebiusTwist * X * moebiusTwist) * K_op ∧
    (CPT_op : EndDoubled E) * body X * (-CPT_op) =
      moebiusTwist * body X * moebiusTwist ∧
    (CPT_op : EndDoubled E) * soul X * (-CPT_op) =
      -(moebiusTwist * soul X * moebiusTwist) := by
  have hPin := cpt_moebius_pin_signatures (E := E)
  have hSwap := moebiusTwist_swaps_sheets (E := E)
  have hInv : -(CPT_op : EndDoubled E) = (moebiusTwist : EndDoubled E) * K_op := by
    rw [hPin.1, hPin.2.2.2, neg_neg]
  have hConj :
      (CPT_op : EndDoubled E) * X * (-CPT_op) =
        K_op * (moebiusTwist * X * moebiusTwist) * K_op := by
    rw [hInv, hPin.1]
    simp only [mul_assoc]
  have hBodyM :
      (moebiusTwist : EndDoubled E) * body X * moebiusTwist =
        body (moebiusTwist * X * moebiusTwist) := by
    have hPL : (moebiusTwist : EndDoubled E) * projPrimal = projVacuum * moebiusTwist := hSwap.1
    have hPR : (moebiusTwist : EndDoubled E) * projVacuum = projPrimal * moebiusTwist := hSwap.2
    have hPL' : projPrimal * (moebiusTwist : EndDoubled E) = moebiusTwist * projVacuum := hPR.symm
    have hPR' : projVacuum * (moebiusTwist : EndDoubled E) = moebiusTwist * projPrimal := hPL.symm
    change (moebiusTwist : EndDoubled E) * (projPrimal * X * projPrimal + projVacuum * X * projVacuum) * moebiusTwist =
      projPrimal * (moebiusTwist * X * moebiusTwist) * projPrimal +
        projVacuum * (moebiusTwist * X * moebiusTwist) * projVacuum
    calc
      (moebiusTwist : EndDoubled E) * (projPrimal * X * projPrimal + projVacuum * X * projVacuum) * moebiusTwist
          = (moebiusTwist * projPrimal) * X * (projPrimal * moebiusTwist) +
              (moebiusTwist * projVacuum) * X * (projVacuum * moebiusTwist) := by
            simp only [mul_add, add_mul, mul_assoc]
      _ = (projVacuum * moebiusTwist) * X * (moebiusTwist * projVacuum) +
            (projPrimal * moebiusTwist) * X * (moebiusTwist * projPrimal) := by
            rw [hPL, hPL', hPR, hPR']
      _ = projPrimal * (moebiusTwist * X * moebiusTwist) * projPrimal +
            projVacuum * (moebiusTwist * X * moebiusTwist) * projVacuum := by
            simp only [mul_assoc]; exact add_comm _ _
  have hSoulM :
      (moebiusTwist : EndDoubled E) * soul X * moebiusTwist =
        soul (moebiusTwist * X * moebiusTwist) := by
    have hPL : (moebiusTwist : EndDoubled E) * projPrimal = projVacuum * moebiusTwist := hSwap.1
    have hPR : (moebiusTwist : EndDoubled E) * projVacuum = projPrimal * moebiusTwist := hSwap.2
    have hPL' : projPrimal * (moebiusTwist : EndDoubled E) = moebiusTwist * projVacuum := hPR.symm
    have hPR' : projVacuum * (moebiusTwist : EndDoubled E) = moebiusTwist * projPrimal := hPL.symm
    change (moebiusTwist : EndDoubled E) * (projPrimal * X * projVacuum + projVacuum * X * projPrimal) * moebiusTwist =
      projPrimal * (moebiusTwist * X * moebiusTwist) * projVacuum +
        projVacuum * (moebiusTwist * X * moebiusTwist) * projPrimal
    calc
      (moebiusTwist : EndDoubled E) * (projPrimal * X * projVacuum + projVacuum * X * projPrimal) * moebiusTwist
          = (moebiusTwist * projPrimal) * X * (projVacuum * moebiusTwist) +
              (moebiusTwist * projVacuum) * X * (projPrimal * moebiusTwist) := by
            simp only [mul_add, add_mul, mul_assoc]
      _ = (projVacuum * moebiusTwist) * X * (moebiusTwist * projPrimal) +
            (projPrimal * moebiusTwist) * X * (moebiusTwist * projVacuum) := by
            rw [hPL, hPR', hPR, hPL']
      _ = projPrimal * (moebiusTwist * X * moebiusTwist) * projVacuum +
            projVacuum * (moebiusTwist * X * moebiusTwist) * projPrimal := by
            simp only [mul_assoc]; exact add_comm _ _
  refine ⟨hConj, ?_, ?_⟩
  · have hConjBody :
        (CPT_op : EndDoubled E) * body X * (-CPT_op) =
          K_op * (moebiusTwist * body X * moebiusTwist) * K_op := by
      rw [hInv, hPin.1]
      simp only [mul_assoc]
    rw [hConjBody, hBodyM, ← peirceGrading_eq_K_op (E := E),
      G_body_parity_even (moebiusTwist * X * moebiusTwist)]
  · have hConjSoul :
        (CPT_op : EndDoubled E) * soul X * (-CPT_op) =
          K_op * (moebiusTwist * soul X * moebiusTwist) * K_op := by
      rw [hInv, hPin.1]
      simp only [mul_assoc]
    rw [hConjSoul, hSoulM, ← peirceGrading_eq_K_op (E := E),
      G_soul_parity_odd (moebiusTwist * X * moebiusTwist)]

/-- A `Pin⁻` (`CPT_op² = -id`) equivariant section over any glide step `g` is double-glide
antiperiodic (`-1`), while its symplectic and Krein bilinear forms are periodic across the double glide. -/
theorem cpt_double_glide_antiperiodic_and_bilinear_periodic
    {α : Type*} (g : α → α) (ψ φ : α → DoubledCarrier E)
    (hψ : ∀ p, ψ (g p) = CPT_op (ψ p)) (hφ : ∀ p, φ (g p) = CPT_op (φ p)) (p : α) :
    ψ (g (g p)) = -ψ p ∧
    symplecticForm pairing (ψ (g p)) (φ (g p)) = symplecticForm pairing (ψ p) (φ p) ∧
    kreinForm pairing (ψ (g p)) (φ (g p)) = -kreinForm pairing (ψ p) (φ p) ∧
    symplecticForm pairing (ψ (g (g p))) (φ (g (g p))) = symplecticForm pairing (ψ p) (φ p) ∧
    kreinForm pairing (ψ (g (g p))) (φ (g (g p))) = kreinForm pairing (ψ p) (φ p) := by
  have hAnti : ψ (g (g p)) = -ψ p := by
    rw [hψ (g p), hψ p]
    exact Prod.ext (congrArg Prod.fst (CPT_sq_neg (ψ p)))
      (congrArg Prod.snd (CPT_sq_neg (ψ p)))
  have hSym1 :
      symplecticForm pairing (ψ (g p)) (φ (g p)) = symplecticForm pairing (ψ p) (φ p) := by
    rw [hψ p, hφ p, symplecticForm_cpt_invariant]
  have hKr1 :
      kreinForm pairing (ψ (g p)) (φ (g p)) = -kreinForm pairing (ψ p) (φ p) := by
    rw [hψ p, hφ p, kreinForm_cpt_anti_invariant]
  refine ⟨hAnti, hSym1, hKr1, ?_, ?_⟩
  · rw [hψ (g p), hφ (g p), symplecticForm_cpt_invariant, hψ p, hφ p, symplecticForm_cpt_invariant]
  · rw [hψ (g p), hφ (g p), kreinForm_cpt_anti_invariant, hψ p, hφ p, kreinForm_cpt_anti_invariant,
      neg_neg]

/-- Any `CPT_op`-equivariant section that is strictly periodic under the double glide must vanish identically. -/
theorem cpt_periodic_section_eq_zero {α : Type*} (g : α → α) (ψ : α → DoubledCarrier E)
    (hψ : ∀ p, ψ (g p) = CPT_op (ψ p)) (hper : ∀ p, ψ (g (g p)) = ψ p) :
    ψ = 0 := by
  funext p
  have hAnti : ψ (g (g p)) = -ψ p := by
    rw [hψ (g p), hψ p]
    exact Prod.ext (congrArg Prod.fst (CPT_sq_neg (ψ p)))
      (congrArg Prod.snd (CPT_sq_neg (ψ p)))
  have hEq : -ψ p = ψ p := hAnti.symm.trans (hper p)
  have hTwo : (2 : ℝ) • ψ p = 0 := by
    calc
      (2 : ℝ) • ψ p = ψ p + ψ p := two_smul ℝ (ψ p)
      _ = ψ p + (-ψ p) := by conv_rhs => rw [hEq]
      _ = 0 := add_neg_cancel (ψ p)
  exact (smul_eq_zero.mp hTwo).resolve_left (by norm_num)

end PeirceDeWittPinCPTHolonomy

end InfoGeometry.SuperGrassmannian.ModularCPT
