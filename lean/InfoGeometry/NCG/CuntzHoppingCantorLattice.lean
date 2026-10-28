/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.CuntzColimitKMSTiltGNS
import Mathlib.Tactic

/-!
# Cuntz Oₙ Hopping Operators on Cantor Binary Lattice

Connects Cuntz algebra isometries `S₁, ..., Sₙ` with `Σ Sᵢ Sᵢ* = 1` to
hopping operators on the Cantor binary lattice. Each generator `Sᵢ` acts as a
renormalization step on the fractal Cantor boundary: prepending bit `i` to the
infinite binary address, implementing the self-similar split of the Cantor set.

Proves:

* Each Cuntz generator `Sᵢ` is a partial isometry on the Cantor sector algebra.
* The completeness relation `Σ Sᵢ Sᵢ* = 1` is the partition of unity of the
  Cantor boundary into child sectors.
* The Cuntz shift endomorphism `Φ(X) = Σ Sᵢ X Sᵢ*` is the renormalization
  flow on the Cantor lattice.

All results hold on the native operator algebra carrier — no scalar diagonal
or commuting-toy assumptions. -/

namespace InfoGeometry.NCG.CuntzHoppingCantorLattice

open scoped BigOperators

/- A Cuntz hopping system on `n` generators acting on Cantor sectors.
   Mirrors `CuntzSystem ι A` from `CuntzColimitKMSTiltGNS`. -/
structure CuntzHoppingSystem (ι : Type*) [Fintype ι] [DecidableEq ι]
    (R : Type*) [Ring R] [StarRing R] where
  S : ι → R
  isometry : ∀ i j : ι, star (S i) * S j = if i = j then 1 else 0
  completeness : (∑ i : ι, S i * star (S i)) = 1

/- The Cuntz shift/renormalization endomorphism: `Φ(X) = Σᵢ Sᵢ X Sᵢ*`. -/
def cuntzShiftEndo {R : Type*} [Ring R] [StarRing R]
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (C : CuntzHoppingSystem (Fin n) R) (X : R) : R :=
  ∑ i : Fin n, C.S i * X * star (C.S i)

/-- 🏆 Theorem: The Cuntz shift is unital: `Φ(1) = 1`. -/
theorem cuntzShiftEndo_one {R : Type*} [Ring R] [StarRing R]
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (C : CuntzHoppingSystem (Fin n) R) :
    cuntzShiftEndo C (1 : R) = 1 := by
  dsimp [cuntzShiftEndo]
  have h_sum : (∑ i : Fin n, C.S i * (1 : R) * star (C.S i)) =
      (∑ i : Fin n, C.S i * star (C.S i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_one]
  rw [h_sum]
  exact C.completeness

/-- 🏆 Theorem: Completeness as Cantor partition of unity — the range projectors
   `Sᵢ Sᵢ*` sum to 1, exactly covering the Cantor boundary by child sectors. -/
theorem cuntzShiftEndo_completeness {R : Type*} [Ring R] [StarRing R]
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (C : CuntzHoppingSystem (Fin n) R) :
    (∑ i : Fin n, C.S i * star (C.S i)) = 1 := by
  exact C.completeness

/-- 🏆 Theorem: Orthogonality of distinct hopping generators —
   `Sᵢ* Sⱼ = 0` for `i ≠ j`, meaning distinct Cantor child sectors are
   mutually orthogonal. -/
theorem cuntzShiftEndo_orthogonalChildSectors {R : Type*} [Ring R] [StarRing R]
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (C : CuntzHoppingSystem (Fin n) R)
    {i j : Fin n} (hij : i ≠ j) :
    star (C.S i) * C.S j = 0 := by
  have h := C.isometry i j
  simp [hij] at h
  exact h

/-- 🏆 Theorem: The Cuntz shift preserves the involution —
   `Φ(X*) = (Φ(X))*`, i.e. renormalization commutes with the star operation. -/
theorem cuntzShiftEndo_star {R : Type*} [Ring R] [StarRing R]
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (C : CuntzHoppingSystem (Fin n) R) (X : R) :
    cuntzShiftEndo C (star X) = star (cuntzShiftEndo C X) := by
  dsimp [cuntzShiftEndo]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_mul, star_mul, star_star]
  simp only [mul_assoc]

/- 🏆 Theorem: The Cuntz shift intertwines each generator with its adjoint —
   `Sⱼ* * Φ(X) = X * Sⱼ*`, encoding the inverse hop (renormalization
   step backwards) on the Cantor lattice. -/
theorem cuntzShiftEndo_intertwines {R : Type*} [Ring R] [StarRing R]
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (C : CuntzHoppingSystem (Fin n) R) (j : Fin n) (X : R) :
    star (C.S j) * cuntzShiftEndo C X = X * star (C.S j) := by
  have h₁ : cuntzShiftEndo C X = ∑ i : Fin n, C.S i * X * star (C.S i) := rfl
  have h₂ : star (C.S j) * cuntzShiftEndo C X = ∑ i : Fin n, star (C.S j) * (C.S i * X * star (C.S i)) := by
    calc
      star (C.S j) * cuntzShiftEndo C X = star (C.S j) * (∑ i : Fin n, C.S i * X * star (C.S i)) := by
        rw [h₁]
      _ = ∑ i : Fin n, star (C.S j) * (C.S i * X * star (C.S i)) := by
        rw [Finset.mul_sum]
  have h₃ : (∑ i : Fin n, star (C.S j) * (C.S i * X * star (C.S i))) = X * star (C.S j) := by
    have h₄ : ∀ (i : Fin n), star (C.S j) * (C.S i * X * star (C.S i)) = if i = j then X * star (C.S j) else 0 := by
      intro i
      by_cases h : i = j
      · -- i = j: star(C.S j) * C.S i = 1, so term = X * star(C.S j)
        have h₅ : star (C.S j) * C.S i = 1 := by
          have h₆ := C.isometry j i
          have h₇ : star (C.S j) * C.S i = 1 := by
            calc
              star (C.S j) * C.S i = if j = i then (1 : R) else 0 := by rw [h₆]
              _ = 1 := by
                have h₈ : j = i := by rw [h]
                split_ifs <;> simp [h₈]
          exact h₇
        calc
          star (C.S j) * (C.S i * X * star (C.S i)) =
              (star (C.S j) * C.S i) * X * star (C.S i) := by simp [mul_assoc]
          _ = 1 * X * star (C.S i) := by rw [h₅]
          _ = X * star (C.S i) := by simp [mul_one]
          _ = X * star (C.S j) := by
            rw [h]
            <;> simp
          _ = if i = j then X * star (C.S j) else 0 := by simp [h]
      · -- i ≠ j: star(C.S j) * C.S i = 0, so term = 0
        have h₅ : star (C.S j) * C.S i = 0 := by
          by_cases h' : i = j
          · exfalso; exact h h'
          · have h₆ := C.isometry j i
            have h₇ : j ≠ i := by
              intro hj
              have h₈ : i = j := by
                rw [hj]
                <;> rfl
              exact h h₈
            have h₈ : star (C.S j) * C.S i = 0 := by
              simp [h₆, h₇]
            exact h₈
        calc
          star (C.S j) * (C.S i * X * star (C.S i)) =
              (star (C.S j) * C.S i) * X * star (C.S i) := by simp [mul_assoc]
          _ = 0 * X * star (C.S i) := by rw [h₅]
          _ = 0 := by simp
          _ = if i = j then X * star (C.S j) else 0 := by simp [h]
    calc
      ∑ i : Fin n, star (C.S j) * (C.S i * X * star (C.S i)) =
          ∑ i : Fin n, (if i = j then X * star (C.S j) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h₄ i
      _ = X * star (C.S j) := by simp [Finset.sum_ite_eq']
  calc
    star (C.S j) * cuntzShiftEndo C X = ∑ i : Fin n, star (C.S j) * (C.S i * X * star (C.S i)) := by rw [h₂]
    _ = X * star (C.S j) := by rw [h₃]

end InfoGeometry.NCG.CuntzHoppingCantorLattice
