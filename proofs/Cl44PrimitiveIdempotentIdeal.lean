/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Construction of the Primitive Idempotent $f$ and the 16-Dimensional Minimal Left Ideal of $\mathrm{Cl}(4,4)$

This module formalizes the matrix representation of $\mathrm{Cl}(4,4) \cong M_{16}(\mathbb{R})$,
the primitive vacuum idempotent $f = E_{0,0}$, the four Witt fermionic annihilation and creation
operators $u_k, v_k \in M_{16}(\mathbb{R})$, the minimal left ideal
$\mathcal{S}_L = \mathrm{Cl}(4,4) \cdot f$, its constructive 16-dimensional linear isomorphism
$\mathcal{S}_L \simeq_{\mathbb{R}} \mathbb{R}^{16}$, and its chiral semi-spinor decomposition
$\mathcal{S}_L \cong S^+ \oplus S^-$ ($8 + 8 = 16$).
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators

namespace InfoGeometry.Cl44IdempotentIdeal

/-! =========================================================================
    1. CARRIER ALGEBRA Cl(4,4) ≅ M₁₆(ℝ) AND THE PRIMITIVE IDEMPOTENT f
    ========================================================================= -/

/-- The split Clifford algebra Cl(4,4) faithfully represented as M₁₆(ℝ). -/
abbrev Cl44 := Matrix (Fin 16) (Fin 16) ℝ

/-- The canonical primitive idempotent f = E₀₀ in Cl(4,4).
    Corresponds to the mutual Fock vacuum projector f = ∏_{k=0}^3 P_k. -/
def primIdem : Cl44 :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- **Theorem 1.1 (Idempotence):**
    The primitive idempotent satisfies f² = f. -/
theorem primIdem_mul_self : primIdem * primIdem = primIdem := by
  ext i j
  rw [Matrix.mul_apply]
  have h_zero : ∀ m : Fin 16, m ≠ 0 → primIdem i m * primIdem m j = 0 := by
    intro m hm
    unfold primIdem
    have : ¬(m = 0 ∧ j = 0) := fun h => hm h.1
    simp [this]
  rw [Finset.sum_eq_single 0]
  · by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [primIdem, hi, hj]
  · intro m _ hm
    exact h_zero m hm
  · intro h0
    exact False.elim (h0 (Finset.mem_univ 0))

/-- **Theorem 1.2 (Non-Triviality):**
    The idempotent is strictly non-zero. -/
theorem primIdem_ne_zero : primIdem ≠ 0 := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  unfold primIdem at h00
  simp at h00

/-! =========================================================================
    2. WITT NULL MODES AND VACUUM ANNIHILATION
    ========================================================================= -/

/-- Bit extraction: returns the k-th bit (0 or 1) of state index i ∈ {0,...,15}. -/
def bitVal (k : Fin 4) (i : Fin 16) : Nat :=
  match k with
  | 0 => i.val % 2
  | 1 => (i.val / 2) % 2
  | 2 => (i.val / 4) % 2
  | 3 => (i.val / 8) % 2

/-- The four Witt fermionic annihilation operators u_k (k ∈ {0, 1, 2, 3}) in Cl(4,4).
    Each u_k acts on the Fock basis by lowering bit k from 1 to 0. -/
def uWitt (k : Fin 4) : Cl44 :=
  fun i j =>
    match k with
    | 0 => if j.val = i.val + 1 ∧ bitVal 0 j = 1 then 1 else 0
    | 1 => if j.val = i.val + 2 ∧ bitVal 1 j = 1 then 1 else 0
    | 2 => if j.val = i.val + 4 ∧ bitVal 2 j = 1 then 1 else 0
    | 3 => if j.val = i.val + 8 ∧ bitVal 3 j = 1 then 1 else 0

/-- The first Witt annihilation operator u_0 = uWitt 0 in Cl(4,4). -/
def uWitt0 : Cl44 :=
  uWitt 0

/-- The transpose creation operator v_0 = (u_0)ᵀ on the first Witt mode. -/
def vWitt0 : Cl44 :=
  (uWitt 0)ᵀ

/-- Explicit non-commutativity of the first Witt annihilation operator `uWitt0` and its
transpose creation operator `vWitt0` (`T16`/`T17` non-commutativity witness). -/
theorem uWitt0_mul_vWitt0_ne_comm :
    uWitt0 * vWitt0 ≠ vWitt0 * uWitt0 := by
  intro h
  have h00 : (uWitt0 * vWitt0) 0 0 = (vWitt0 * uWitt0) 0 0 := by rw [h]
  have hL : (uWitt0 * vWitt0) 0 0 = 1 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (1 : Fin 16)]
    · dsimp [uWitt0, uWitt, vWitt0, Matrix.transpose_apply, bitVal]
      norm_num
    · intro m _ hm
      dsimp [uWitt0, uWitt, vWitt0, Matrix.transpose_apply, bitVal]
      fin_cases m <;> simp at hm ⊢
    · intro h1
      exact False.elim (h1 (Finset.mem_univ 1))
  have hR : (vWitt0 * uWitt0) 0 0 = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro m _
    dsimp [uWitt0, uWitt, vWitt0, Matrix.transpose_apply, bitVal]
    fin_cases m <;> norm_num
  rw [hL, hR] at h00
  exact one_ne_zero h00

/-- **Theorem 2.1 (Witt Vacuum Annihilation):**
    All four Witt annihilation operators strictly annihilate the primitive
    idempotent: u_k · f = 0 for all k ∈ Fin 4. -/
theorem uWitt_mul_primIdem_zero (k : Fin 4) :
    uWitt k * primIdem = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro m _
  unfold primIdem
  split_ifs with hm
  · rcases hm with ⟨rfl, _⟩
    unfold uWitt
    fin_cases k <;> (dsimp [bitVal]; norm_num)
  · simp

/-! =========================================================================
    3. THE MINIMAL LEFT IDEAL S_L = Cl(4,4) · f
    ========================================================================= -/

/-- Right multiplication by f as an ℝ-linear map on Cl(4,4). -/
def mulRightMap (f : Cl44) : Cl44 →ₗ[ℝ] Cl44 where
  toFun M := M * f
  map_add' M N := Matrix.add_mul M N f
  map_smul' c M := Matrix.smul_mul c M f

/-- The Minimal Left Ideal S_L = Cl(4,4) · f = range(R_f). -/
def LeftIdeal (f : Cl44) : Submodule ℝ Cl44 :=
  LinearMap.range (mulRightMap f)

/-- **Theorem 3.1 (Left-Ideal Invariance):**
    S_L is closed under arbitrary left multiplication by Cl(4,4). -/
theorem left_ideal_closed (A : Cl44) (X : Cl44) (hX : X ∈ LeftIdeal primIdem) :
    A * X ∈ LeftIdeal primIdem := by
  rcases hX with ⟨M, rfl⟩
  use (A * M)
  dsimp [mulRightMap]
  rw [Matrix.mul_assoc]

lemma leftIdeal_col_zero (X : Cl44) (hX : X ∈ LeftIdeal primIdem)
    (i j : Fin 16) (hj : j ≠ 0) : X i j = 0 := by
  rcases hX with ⟨M, rfl⟩
  dsimp [mulRightMap]
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  unfold primIdem
  have : ¬(m = 0 ∧ j = 0) := fun h => hj h.2
  simp [this]

lemma leftIdeal_val_eq (X : Cl44) (hX : X ∈ LeftIdeal primIdem) (i j : Fin 16) :
    X i j = if j = 0 then X i 0 else 0 := by
  by_cases hj : j = 0
  · subst hj; simp
  · rw [leftIdeal_col_zero X hX i j hj]
    simp [hj]

/-! =========================================================================
    4. CONSTRUCTIVE 16-DIMENSIONAL LINEAR EQUIVALENCE S_L ≃ₗ[ℝ] ℝ¹⁶
    ========================================================================= -/

/-- Projection from S_L to the 16-component spinor vector (column 0). -/
def toSpinor (f : Cl44) : LeftIdeal f →ₗ[ℝ] (Fin 16 → ℝ) where
  toFun X i := X.1 i 0
  map_add' _ _ := by ext i; rfl
  map_smul' _ _ := by ext i; rfl

/-- Embedding a 16-component spinor vector into column 0 of a matrix. -/
def fromSpinorMat (v : Fin 16 → ℝ) : Cl44 :=
  fun i j => if j = 0 then v i else 0

lemma fromSpinorMat_mem_ideal (v : Fin 16 → ℝ) :
    fromSpinorMat v ∈ LeftIdeal primIdem := by
  use fromSpinorMat v
  dsimp [mulRightMap]
  ext i j
  rw [Matrix.mul_apply]
  have h_zero : ∀ m : Fin 16, m ≠ 0 → fromSpinorMat v i m * primIdem m j = 0 := by
    intro m hm
    unfold primIdem
    have : ¬(m = 0 ∧ j = 0) := fun h => hm h.1
    simp [this]
  rw [Finset.sum_eq_single 0]
  · by_cases hj : j = 0 <;> simp [primIdem, fromSpinorMat, hj]
  · intro m _ hm
    exact h_zero m hm
  · intro h0
    exact False.elim (h0 (Finset.mem_univ 0))

/-- Reconstruction map from ℝ¹⁶ into the minimal left ideal S_L. -/
def fromSpinor : (Fin 16 → ℝ) →ₗ[ℝ] LeftIdeal primIdem where
  toFun v := ⟨fromSpinorMat v, fromSpinorMat_mem_ideal v⟩
  map_add' _ _ := by
    ext i j
    dsimp [fromSpinorMat]
    split_ifs <;> ring
  map_smul' _ _ := by
    ext i j
    dsimp [fromSpinorMat]
    split_ifs <;> ring

/-- **Theorem 4.1 (Exact 16-Dimensional Linear Isomorphism):**
    The minimal left ideal S_L = Cl(4,4) · f is constructively isomorphic
    to the 16-dimensional Euclidean space ℝ¹⁶. -/
def leftIdealEquiv : LeftIdeal primIdem ≃ₗ[ℝ] (Fin 16 → ℝ) where
  toFun := toSpinor primIdem
  invFun := fromSpinor
  left_inv := by
    intro ⟨X, hX⟩
    ext i j
    dsimp [toSpinor, fromSpinor, fromSpinorMat]
    exact (leftIdeal_val_eq X hX i j).symm
  right_inv := by
    intro v
    ext i
    dsimp [toSpinor, fromSpinor, fromSpinorMat]
  map_add' := (toSpinor primIdem).map_add
  map_smul' := (toSpinor primIdem).map_smul

/-! =========================================================================
    5. CHIRAL SEMI-SPINOR DECOMPOSITION S_L = S⁺ ⊕ S⁻ (8 + 8 = 16)
    ========================================================================= -/

/-- Total fermionic occupation parity of state index i ∈ Fin 16. -/
def stateParity (i : Fin 16) : Nat :=
  (bitVal 0 i + bitVal 1 i + bitVal 2 i + bitVal 3 i) % 2

/-- Every state index `i : Fin 16` has occupation parity either `0` or `1`. -/
lemma stateParity_eq_zero_or_one (i : Fin 16) :
    stateParity i = 0 ∨ stateParity i = 1 := by
  fin_cases i <;> decide

/-- Positive semi-spinor subspace S⁺ (even occupation, carries 𝕆_s). -/
def SemiSpinorPlus : Submodule ℝ (Fin 16 → ℝ) where
  carrier := { v | ∀ i, stateParity i = 1 → v i = 0 }
  add_mem' := by intro u v hu hv i hi; simp [hu i hi, hv i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by intro c v hv i hi; simp [hv i hi]

/-- Negative semi-spinor subspace S⁻ (odd occupation, carries 𝕆_s · ℓ). -/
def SemiSpinorMinus : Submodule ℝ (Fin 16 → ℝ) where
  carrier := { v | ∀ i, stateParity i = 0 → v i = 0 }
  add_mem' := by intro u v hu hv i hi; simp [hu i hi, hv i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by intro c v hv i hi; simp [hv i hi]

/-- **Theorem 5.1 (Chiral Disjointness):**
    S⁺ ∩ S⁻ = {0}. -/
theorem semiSpinor_disjoint : Disjoint SemiSpinorPlus SemiSpinorMinus := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  ext i
  rcases stateParity_eq_zero_or_one i with hp0 | hp1
  · exact hy i hp0
  · exact hx i hp1

/-- **Theorem 5.2 (Chiral Completeness):**
    S⁺ ⊔ S⁻ = ⊤ (every spinor decomposes uniquely into even + odd). -/
theorem semiSpinor_span_top : SemiSpinorPlus ⊔ SemiSpinorMinus = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  let v_plus : Fin 16 → ℝ := fun i => if stateParity i = 0 then v i else 0
  let v_minus : Fin 16 → ℝ := fun i => if stateParity i = 1 then v i else 0
  have h_plus : v_plus ∈ SemiSpinorPlus := by
    intro i hi
    dsimp [v_plus]
    rw [hi]
    simp
  have h_minus : v_minus ∈ SemiSpinorMinus := by
    intro i hi
    dsimp [v_minus]
    rw [hi]
    simp
  have h_sum : v = v_plus + v_minus := by
    ext i
    dsimp [v_plus, v_minus]
    rcases stateParity_eq_zero_or_one i with hp0 | hp1
    · rw [hp0]
      simp
    · rw [hp1]
      simp
  rw [h_sum]
  exact Submodule.add_mem_sup h_plus h_minus

/-- **Theorem 5.3 (Exact Dimension Audit):**
    The positive chiral subspace S⁺ has exactly 8 basis states. -/
theorem even_states_card :
    (Finset.univ.filter (fun i : Fin 16 => stateParity i = 0)).card = 8 := by
  decide

/-- **Theorem 5.4 (Exact Dimension Audit):**
    The negative chiral subspace S⁻ has exactly 8 basis states. -/
theorem odd_states_card :
    (Finset.univ.filter (fun i : Fin 16 => stateParity i = 1)).card = 8 := by
  decide

end InfoGeometry.Cl44IdempotentIdeal
