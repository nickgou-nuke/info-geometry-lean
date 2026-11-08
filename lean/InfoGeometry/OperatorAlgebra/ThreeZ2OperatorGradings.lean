import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Three independent operator gradings

The three involutions are parameters in one noncommutative ring.  No matrix
model is used: the grading actions are inner conjugations by the given
involutions, and their commutation is proved directly from ring laws.
-/

namespace InfoGeometry.OperatorAlgebra

section

variable {A : Type*} [Ring A]

def gradingConjugation (g x : A) : A := g * x * g

def hasZ2Parity (g x : A) (ε : Fin 2) : Prop :=
  gradingConjugation g x = if ε = 0 then x else -x

def triZ2Parity (gW gχ gN x : A) (εW εχ εN : Fin 2) : Prop :=
  hasZ2Parity gW x εW ∧ hasZ2Parity gχ x εχ ∧ hasZ2Parity gN x εN

theorem gradingConjugation_involutive (g : A) (hg : g * g = 1) (x : A) :
    gradingConjugation g (gradingConjugation g x) = x := by
  dsimp [gradingConjugation]
  calc
    g * (g * x * g) * g = (g * g) * x * (g * g) := by noncomm_ring
    _ = x := by simp [hg]

theorem gradingConjugations_commute
    (g h : A) (hgh : g * h = h * g) (x : A) :
    gradingConjugation g (gradingConjugation h x) =
      gradingConjugation h (gradingConjugation g x) := by
  dsimp [gradingConjugation]
  calc
    g * (h * x * h) * g = (g * h) * x * (h * g) := by noncomm_ring
    _ = (h * g) * x * (g * h) := by rw [hgh]
    _ = h * (g * x * g) * h := by noncomm_ring

theorem gradingConjugation_mul
    (g : A) (hg : g * g = 1) (x y : A) :
    gradingConjugation g (x * y) =
      gradingConjugation g x * gradingConjugation g y := by
  dsimp [gradingConjugation]
  calc
    g * (x * y) * g = g * x * (g * g) * y * g := by
      rw [hg]
      simp only [one_mul, mul_assoc]
    _ = g * x * g * g * y * g := by simp only [mul_assoc]
    _ = (g * x * g) * (g * y * g) := by simp only [mul_assoc]
    _ = gradingConjugation g x * gradingConjugation g y := rfl

theorem hasZ2Parity_mul
    (g : A) (hg : g * g = 1) (x y : A)
    (ε δ : Fin 2)
    (hx : hasZ2Parity g x ε)
    (hy : hasZ2Parity g y δ) :
    gradingConjugation g (x * y) =
      (if ε = δ then x * y else -(x * y)) := by
  rw [gradingConjugation_mul g hg x y, hx, hy]
  fin_cases ε <;> fin_cases δ <;> simp

theorem hasZ2Parity_add
    (g x y : A) (ε : Fin 2)
    (hx : hasZ2Parity g x ε) (hy : hasZ2Parity g y ε) :
    hasZ2Parity g (x + y) ε := by
  simp only [hasZ2Parity, gradingConjugation] at hx hy ⊢
  rw [mul_add, add_mul, hx, hy]
  fin_cases ε <;> simp [add_comm]

theorem hasZ2Parity_neg
    (g x : A) (ε : Fin 2)
    (hx : hasZ2Parity g x ε) :
    hasZ2Parity g (-x) ε := by
  simp only [hasZ2Parity, gradingConjugation] at hx ⊢
  rw [mul_neg, neg_mul, hx]
  fin_cases ε <;> simp

lemma z2Parity_add_bridge (x : A) (ε δ : Fin 2) :
    (if ε = δ then x else -x) =
      (if ε + δ = 0 then x else -x) := by
  fin_cases ε <;> fin_cases δ <;> simp

theorem triZ2Parity_mul
    (gW gχ gN x y : A) (εW εχ εN δW δχ δN : Fin 2)
    (hgW : gW * gW = 1) (hgχ : gχ * gχ = 1) (hgN : gN * gN = 1)
    (hx : triZ2Parity gW gχ gN x εW εχ εN)
    (hy : triZ2Parity gW gχ gN y δW δχ δN) :
    triZ2Parity gW gχ gN (x * y)
      (εW + δW) (εχ + δχ) (εN + δN) := by
  rcases hx with ⟨hxW, hxχ, hxN⟩
  rcases hy with ⟨hyW, hyχ, hyN⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hasZ2Parity, hasZ2Parity_mul gW hgW x y εW δW hxW hyW]
    exact z2Parity_add_bridge _ _ _
  · rw [hasZ2Parity, hasZ2Parity_mul gχ hgχ x y εχ δχ hxχ hyχ]
    exact z2Parity_add_bridge _ _ _
  · rw [hasZ2Parity, hasZ2Parity_mul gN hgN x y εN δN hxN hyN]
    exact z2Parity_add_bridge _ _ _

theorem triZ2Parity_add
    (gW gχ gN x y : A) (εW εχ εN : Fin 2)
    (hx : triZ2Parity gW gχ gN x εW εχ εN)
    (hy : triZ2Parity gW gχ gN y εW εχ εN) :
    triZ2Parity gW gχ gN (x + y) εW εχ εN := by
  rcases hx with ⟨hxW, hxχ, hxN⟩
  rcases hy with ⟨hyW, hyχ, hyN⟩
  exact ⟨hasZ2Parity_add gW x y εW hxW hyW,
    hasZ2Parity_add gχ x y εχ hxχ hyχ,
    hasZ2Parity_add gN x y εN hxN hyN⟩

theorem triZ2Parity_neg
    (gW gχ gN x : A) (εW εχ εN : Fin 2)
    (hx : triZ2Parity gW gχ gN x εW εχ εN) :
    triZ2Parity gW gχ gN (-x) εW εχ εN := by
  rcases hx with ⟨hxW, hxχ, hxN⟩
  exact ⟨hasZ2Parity_neg gW x εW hxW,
    hasZ2Parity_neg gχ x εχ hxχ,
    hasZ2Parity_neg gN x εN hxN⟩

theorem RingHom.map_hasZ2Parity
    {B : Type*} [Ring B] (φ : A →+* B)
    (g x : A) (ε : Fin 2) (hx : hasZ2Parity g x ε) :
    hasZ2Parity (φ g) (φ x) ε := by
  simp only [hasZ2Parity, gradingConjugation] at hx ⊢
  rw [← map_mul, ← map_mul, hx]
  fin_cases ε <;> simp

theorem RingHom.map_triZ2Parity
    {B : Type*} [Ring B] (φ : A →+* B)
    (gW gχ gN x : A) (εW εχ εN : Fin 2)
    (hx : triZ2Parity gW gχ gN x εW εχ εN) :
    triZ2Parity (φ gW) (φ gχ) (φ gN) (φ x) εW εχ εN := by
  rcases hx with ⟨hxW, hxχ, hxN⟩
  exact ⟨RingHom.map_hasZ2Parity φ gW x εW hxW,
    RingHom.map_hasZ2Parity φ gχ x εχ hxχ,
    RingHom.map_hasZ2Parity φ gN x εN hxN⟩

theorem triZ2Parity_sub
    (gW gχ gN x y : A) (εW εχ εN : Fin 2)
    (hx : triZ2Parity gW gχ gN x εW εχ εN)
    (hy : triZ2Parity gW gχ gN y εW εχ εN) :
    triZ2Parity gW gχ gN (x - y) εW εχ εN := by
  rw [sub_eq_add_neg]
  exact triZ2Parity_add gW gχ gN x (-y) εW εχ εN hx
    (triZ2Parity_neg gW gχ gN y εW εχ εN hy)

theorem triZ2Parity_coordinate_swap
    (gW gχ gN x : A) (εW εχ εN : Fin 2) :
    triZ2Parity gW gχ gN x εW εχ εN ↔
      triZ2Parity gχ gW gN x εχ εW εN := by
  constructor <;> intro h
  · rcases h with ⟨hW, hχ, hN⟩
    exact ⟨hχ, hW, hN⟩
  · rcases h with ⟨hχ, hW, hN⟩
    exact ⟨hW, hχ, hN⟩

end

end InfoGeometry.OperatorAlgebra
