/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics

/-! # Even observables and Peirce coarse graining

Pinching is trace-dual to the inclusion of the even Peirce sector. This turns
an equality of even blocks into equality of all even observable expectations.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceEvenObservables

open Matrix InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- Left multiplication by an even element commutes with Peirce pinching. -/
theorem evenGrade_left_module (P O X : Mat) (hP : P * P = P) :
    evenGrade P (evenGrade P O * X) = evenGrade P O * evenGrade P X := by
  unfold evenGrade
  peirce_nf hP

/-- The expectation of any even observable depends only on the even block. -/
theorem trace_even_observable (P O X : Mat) (hP : P * P = P)
    (hPs : star P = P) (hO : evenGrade P O = O) :
    Matrix.trace (O * X) = Matrix.trace (O * evenGrade P X) := by
  calc
    Matrix.trace (O * X) = Matrix.trace (evenGrade P (O * X)) :=
      (pinching_trace P (O * X) hP hPs).symm
    _ = Matrix.trace (O * evenGrade P X) := by
      rw [← hO, evenGrade_left_module P O X hP, hO]

/-- Peirce pinching is additive with respect to subtraction. -/
theorem evenGrade_sub (P X Y : Mat) :
    evenGrade P (X - Y) = evenGrade P X - evenGrade P Y := by
  unfold evenGrade
  simp only [mul_sub, sub_mul]
  abel

/-- The even block is characterized exactly by its trace pairings with all
even observables; no commutativity of the matrices is required. -/
theorem even_expectations_iff_equal_blocks (P X Y : Mat) (hP : P * P = P)
    (hPs : star P = P) :
    (∀ O : Mat, evenGrade P O = O → Matrix.trace (O * X) = Matrix.trace (O * Y)) ↔
      evenGrade P X = evenGrade P Y := by
  constructor
  · intro h
    let T : Mat := evenGrade P X - evenGrade P Y
    have hT : evenGrade P T = T := by
      dsimp [T]
      rw [evenGrade_sub, pinching_idempotent P X hP, pinching_idempotent P Y hP]
    have hStarT : evenGrade P (star T) = star T := by
      rw [← star_evenGrade P T hPs, hT]
    have hpair := h (star T) hStarT
    rw [trace_even_observable P (star T) X hP hPs hStarT,
      trace_even_observable P (star T) Y hP hPs hStarT] at hpair
    have hzero : Matrix.trace (star T * T) = 0 := by
      dsimp [T]
      rw [mul_sub, Matrix.trace_sub, hpair, sub_self]
    have hTzero : T = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hzero
    exact sub_eq_zero.mp hTzero
  · intro h O hO
    rw [trace_even_observable P O X hP hPs hO,
      trace_even_observable P O Y hP hPs hO, h]

/-- For Hermitian matrices, self-adjoint even observables already determine
the full even block. In particular, this applies to density matrices. -/
theorem hermitian_even_expectations_iff_equal_blocks (P X Y : Mat)
    (hP : P * P = P) (hPs : star P = P) (hX : star X = X) (hY : star Y = Y) :
    (∀ O : Mat, evenGrade P O = O → star O = O →
      Matrix.trace (O * X) = Matrix.trace (O * Y)) ↔ evenGrade P X = evenGrade P Y := by
  constructor
  · intro h
    let T : Mat := evenGrade P X - evenGrade P Y
    have hT : evenGrade P T = T := by
      dsimp [T]
      rw [evenGrade_sub, pinching_idempotent P X hP, pinching_idempotent P Y hP]
    have hTs : star T = T := by
      dsimp [T]
      rw [star_sub, star_evenGrade P X hPs, star_evenGrade P Y hPs, hX, hY]
    have hpair := h T hT hTs
    rw [trace_even_observable P T X hP hPs hT,
      trace_even_observable P T Y hP hPs hT] at hpair
    have hzero : Matrix.trace (star T * T) = 0 := by
      rw [hTs]
      dsimp [T]
      rw [mul_sub, Matrix.trace_sub, hpair, sub_self]
    have hTzero : T = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hzero
    exact sub_eq_zero.mp hTzero
  · intro h O hO _
    rw [trace_even_observable P O X hP hPs hO,
      trace_even_observable P O Y hP hPs hO, h]

/-- Distinct Hermitian matrices with equal even blocks are distinguished by
an explicitly constructed self-adjoint observable in the odd sector. -/
theorem exists_odd_hermitian_observable_separating (P X Y : Mat)
    (hX : star X = X) (hY : star Y = Y) (hne : X ≠ Y)
    (heven : evenGrade P X = evenGrade P Y) :
    ∃ O : Mat, star O = O ∧ evenGrade P O = 0 ∧
      Matrix.trace (O * X) ≠ Matrix.trace (O * Y) := by
  let O : Mat := X - Y
  have hOs : star O = O := by
    dsimp [O]
    rw [star_sub, hX, hY]
  have hOdd : evenGrade P O = 0 := by
    dsimp [O]
    rw [evenGrade_sub, heven, sub_self]
  have hOne : O ≠ 0 := by
    intro h
    exact hne (sub_eq_zero.mp h)
  have htrace : Matrix.trace (O * X) ≠ Matrix.trace (O * Y) := by
    intro h
    apply hOne
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    change Matrix.trace (star O * O) = 0
    rw [hOs]
    dsimp [O]
    rw [mul_sub, Matrix.trace_sub, h, sub_self]
  exact ⟨O, hOs, hOdd, htrace⟩

/-- For a nontrivial cut, one pair of density matrices is invisible to all
even observables throughout the evolution, yet distinguished initially by
a self-adjoint odd observable. -/
theorem exists_density_pair_even_invisible_odd_separated
    (P A W : Mat) (hP : P * P = P) (hPs : star P = P)
    (hW : evenGrade P W = W) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ∃ ρ σ O : Mat, ρ.PosSemidef ∧ σ.PosSemidef ∧
      Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      star O = O ∧ evenGrade P O = 0 ∧
      Matrix.trace (O * ρ) ≠ Matrix.trace (O * σ) ∧
      ∀ (k : ℕ) (E : Mat), evenGrade P E = E →
        Matrix.trace (E * evolve P A W k ρ) = Matrix.trace (E * evolve P A W k σ) := by
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ :=
    exists_densities_colliding_after_evolution P A W hP hPs hW hP0 hP1
  have hEven : evenGrade P ρ = evenGrade P σ := heq 0
  have hρs : star ρ = ρ := hρ.isHermitian.eq
  have hσs : star σ = σ := hσ.isHermitian.eq
  obtain ⟨O, hOs, hOdd, hsep⟩ :=
    exists_odd_hermitian_observable_separating P ρ σ hρs hσs hne hEven
  refine ⟨ρ, σ, O, hρ, hσ, htρ, htσ, hne, hOs, hOdd, hsep, ?_⟩
  intro k E hE
  rw [trace_even_observable P E (evolve P A W k ρ) hP hPs hE,
    trace_even_observable P E (evolve P A W k σ) hP hPs hE, heq k]

/-- A single pair of distinct density matrices has identical expectations
for every even observable at every finite time. -/
theorem exists_density_pair_same_even_expectations
    (P A W : Mat) (hP : P * P = P) (hPs : star P = P)
    (hW : evenGrade P W = W) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ∃ ρ σ : Mat, ρ.PosSemidef ∧ σ.PosSemidef ∧
      Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      ∀ (k : ℕ) (O : Mat), evenGrade P O = O →
        Matrix.trace (O * evolve P A W k ρ) = Matrix.trace (O * evolve P A W k σ) := by
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ :=
    exists_densities_colliding_after_evolution P A W hP hPs hW hP0 hP1
  refine ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, ?_⟩
  intro k O hO
  rw [trace_even_observable P O (evolve P A W k ρ) hP hPs hO,
    trace_even_observable P O (evolve P A W k σ) hP hPs hO, heq k]

end InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceEvenObservables

end
