import os

content = """import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace InfoGeometry.SylvesterBraid

variable {R : Type*} [CommRing R]
variable {I : Type*}

/-! ### 1. Phased Tensor Basis States -/

@[ext]
structure PhasedState (n : ℕ) (I R : Type*) [CommRing R] where
  phase : Rˣ
  state : Fin n → I

def swapCoord {n : ℕ} (i j : Fin n) (s : Fin n → I) : Fin n → I :=
  fun x => if x = i then s j else if x = j then s i else s x

lemma swapCoord_apply_left {n : ℕ} (i j : Fin n) (s : Fin n → I) :
    swapCoord i j s i = s j := by
  dsimp [swapCoord]
  rw [if_pos rfl]

lemma swapCoord_apply_right {n : ℕ} (i j : Fin n) (s : Fin n → I) (hij : j ≠ i) :
    swapCoord i j s j = s i := by
  dsimp [swapCoord]
  rw [if_neg hij, if_pos rfl]

lemma swapCoord_apply_other {n : ℕ} (i j k : Fin n) (s : Fin n → I)
    (hki : k ≠ i) (hkj : k ≠ j) :
    swapCoord i j s k = s k := by
  dsimp [swapCoord]
  rw [if_neg hki, if_neg hkj]

lemma swapCoord_involutive {n : ℕ} (i j : Fin n) (s : Fin n → I) :
    swapCoord i j (swapCoord i j s) = s := by
  ext k
  dsimp [swapCoord]
  split_ifs <;> rfl

/-! ### 2. The Sylvester R-Matrix Generator -/

def sylvesterBraidGen {n : ℕ} (β : I → I → Rˣ) (i j : Fin n) (p : PhasedState n I R) :
    PhasedState n I R :=
  ⟨p.phase * β (p.state i) (p.state j), swapCoord i j p.state⟩

def sylvesterBraidInv {n : ℕ} (β : I → I → Rˣ) (i j : Fin n) (p : PhasedState n I R) :
    PhasedState n I R :=
  ⟨p.phase * (β (p.state j) (p.state i))⁻¹, swapCoord i j p.state⟩

/-! ### 3. Unitarity and Invertibility -/

theorem sylvesterBraid_left_inv {n : ℕ} (β : I → I → Rˣ) (i j : Fin n)
    (hij : i ≠ j) (p : PhasedState n I R) :
    sylvesterBraidInv β i j (sylvesterBraidGen β i j p) = p := by
  dsimp [sylvesterBraidInv, sylvesterBraidGen]
  ext1
  · dsimp
    rw [swapCoord_apply_right i j p.state hij.symm, swapCoord_apply_left i j p.state]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  · exact swapCoord_involutive i j p.state

theorem sylvesterBraid_right_inv {n : ℕ} (β : I → I → Rˣ) (i j : Fin n)
    (hij : i ≠ j) (p : PhasedState n I R) :
    sylvesterBraidGen β i j (sylvesterBraidInv β i j p) = p := by
  dsimp [sylvesterBraidInv, sylvesterBraidGen]
  ext1
  · dsimp
    rw [swapCoord_apply_left i j p.state, swapCoord_apply_right i j p.state hij.symm]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  · exact swapCoord_involutive i j p.state

/-! ### 4. The Artin Braid Relation (Yang-Baxter Equation) -/

lemma mul_four_swap {G : Type*} [CommMonoid G] (P A B C : G) :
    P * A * B * C = P * C * B * A := by
  calc P * A * B * C
    _ = P * (A * B * C) := by rw [mul_assoc]
    _ = P * (C * B * A) := by
      have h : A * B * C = C * B * A := by ring
      rw [h]
    _ = P * C * B * A := by simp only [mul_assoc]

lemma swapCoord_braid_state {n : ℕ} (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s : Fin n → I) :
    swapCoord i j (swapCoord j k (swapCoord i j s)) =
    swapCoord j k (swapCoord i j (swapCoord j k s)) := by
  ext x
  dsimp [swapCoord]
  split_ifs <;> rfl

theorem sylvester_artin_braid_relation {n : ℕ}
    (β : I → I → Rˣ) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (p : PhasedState n I R) :
    sylvesterBraidGen β i j (sylvesterBraidGen β j k (sylvesterBraidGen β i j p)) =
    sylvesterBraidGen β j k (sylvesterBraidGen β i j (sylvesterBraidGen β j k p)) := by
  ext1
  · dsimp [sylvesterBraidGen]
    have h1 : swapCoord i j p.state j = p.state i :=
      swapCoord_apply_right i j p.state hij.symm
    have h2 : swapCoord i j p.state k = p.state k :=
      swapCoord_apply_other i j k p.state hik.symm hjk.symm
    have h3 : swapCoord j k (swapCoord i j p.state) i = p.state j := by
      rw [swapCoord_apply_other j k i _ hij hik]
      exact swapCoord_apply_left i j p.state
    have h4 : swapCoord j k (swapCoord i j p.state) j = p.state k := by
      rw [swapCoord_apply_left j k _]
      exact h2
    rw [h1, h2, h3, h4]
    have g1 : swapCoord j k p.state i = p.state i :=
      swapCoord_apply_other j k i p.state hij hik
    have g2 : swapCoord j k p.state j = p.state k :=
      swapCoord_apply_left j k p.state
    have g3 : swapCoord i j (swapCoord j k p.state) j = p.state i := by
      rw [swapCoord_apply_right i j _ hij.symm]
      exact g1
    have g4 : swapCoord i j (swapCoord j k p.state) k = p.state j := by
      rw [swapCoord_apply_other i j k _ hik.symm hjk.symm]
      exact swapCoord_apply_right j k p.state hjk.symm
    rw [g1, g2, g3, g4]
    exact mul_four_swap p.phase (β (p.state i) (p.state j))
                                (β (p.state i) (p.state k))
                                (β (p.state j) (p.state k))
  · exact swapCoord_braid_state i j k hij hjk hik p.state

/-! ### 5. Far Commutativity of Disjoint Generators -/

lemma swapCoord_commute_disjoint {n : ℕ} (i j k l : Fin n)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (s : Fin n → I) :
    swapCoord i j (swapCoord k l s) = swapCoord k l (swapCoord i j s) := by
  ext x
  dsimp [swapCoord]
  split_ifs <;> rfl

theorem sylvester_far_commutativity {n : ℕ}
    (β : I → I → Rˣ) (i j k l : Fin n)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (p : PhasedState n I R) :
    sylvesterBraidGen β i j (sylvesterBraidGen β k l p) =
    sylvesterBraidGen β k l (sylvesterBraidGen β i j p) := by
  ext1
  · dsimp [sylvesterBraidGen]
    rw [swapCoord_apply_other k l i _ hik hil]
    rw [swapCoord_apply_other k l j _ hjk hjl]
    rw [swapCoord_apply_other i j k _ hik.symm hjk.symm]
    rw [swapCoord_apply_other i j l _ hil.symm hjl.symm]
    calc p.phase * β (p.state k) (p.state l) * β (p.state i) (p.state j)
        = p.phase * (β (p.state k) (p.state l) * β (p.state i) (p.state j)) := mul_assoc _ _ _
      _ = p.phase * (β (p.state i) (p.state j) * β (p.state k) (p.state l)) := by
        rw [mul_comm (β (p.state k) (p.state l))]
      _ = p.phase * β (p.state i) (p.state j) * β (p.state k) (p.state l) := (mul_assoc _ _ _).symm
  · exact swapCoord_commute_disjoint i j k l hik hil hjk hjl p.state

/-! ### 6. Realization on Sylvester Clock-and-Shift Phases -/

def sylvesterBicharacter (ω : Rˣ) (u v : ℕ) : Rˣ :=
  ω ^ (u * v)

theorem sylvesterBicharacter_symm (ω : Rˣ) (u v : ℕ) :
    sylvesterBicharacter ω u v = sylvesterBicharacter ω v u := by
  dsimp [sylvesterBicharacter]
  rw [mul_comm u v]

theorem sylvesterBicharacter_add_left (ω : Rˣ) (u₁ u₂ v : ℕ) :
    sylvesterBicharacter ω (u₁ + u₂) v =
    sylvesterBicharacter ω u₁ v * sylvesterBicharacter ω u₂ v := by
  dsimp [sylvesterBicharacter]
  -- Units multiplication is pow_add
  rw [add_mul, pow_add]

theorem sylvesterBicharacter_add_right (ω : Rˣ) (u v₁ v₂ : ℕ) :
    sylvesterBicharacter ω u (v₁ + v₂) =
    sylvesterBicharacter ω u v₁ * sylvesterBicharacter ω u v₂ := by
  dsimp [sylvesterBicharacter]
  rw [mul_add, pow_add]

def clockEigenvalue (ω : Rˣ) (v : ℕ) : Rˣ :=
  ω ^ v

theorem clock_power_eq_sylvester_phase (ω : Rˣ) (u v : ℕ) :
    (clockEigenvalue ω v) ^ u = sylvesterBicharacter ω u v := by
  dsimp [clockEigenvalue, sylvesterBicharacter]
  rw [← pow_mul, mul_comm v u]

end InfoGeometry.SylvesterBraid
"""
with open("lean/InfoGeometry/Categorical/SylvesterBraidRepresentation.lean", "w") as f:
    f.write(content)
