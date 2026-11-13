/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SupermatrixKoszul

/-!
# Additive cocycle of an odd operator lift

For an arbitrary associative ring `R`, the map `W(a,b) = 1 + oddBlock a b`
has the ordered multiplicative defect `C(a,b,c,d) = evenBlock (a*d) (b*c)`.
The defect is a normalized, biadditive group 2-cocycle on the additive group
`R × R`, with trivial action on the additive group of matrices. The displayed
cocycle equation is not a Hochschild cocycle equation.

Subtracting `C` from one product recovers the additive lift. This does not
trivialize the cocycle: in every nontrivial ring no global additive 1-cochain
has this coboundary, since a coboundary on an abelian group is symmetric and
`C` is not. No invertibility of `W` is asserted.

The genuine two-unit diagonal gauge `diag(u,v)` acts by conjugation. The
balanced choice `diag(u,u⁻¹)` gives the submitted covariance identity, but is
not asserted to be a group homomorphism in `u` for noncommuting units.
-/

namespace InfoGeometry.Algebra.FreedAdditiveCocycle

open Matrix InfoGeometry.Algebra.SupermatrixKoszul

variable {R : Type*} [Ring R]

/-- The identity plus an odd operator block. -/
def operatorLift (a b : R) : Matrix (Fin 2) (Fin 2) R :=
  1 + oddBlock a b

/-- The ordered even defect in multiplication of two odd lifts. -/
def productDefect (a b c d : R) : Matrix (Fin 2) (Fin 2) R :=
  evenBlock (a * d) (b * c)

/-- Exact failure of the additive lift to preserve multiplication. -/
theorem operatorLift_mul (a b c d : R) :
    operatorLift a b * operatorLift c d =
      operatorLift (a + c) (b + d) + productDefect a b c d := by
  have hadd : oddBlock a b + oddBlock c d = oddBlock (a + c) (b + d) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [oddBlock]
  change (1 + oddBlock a b) * (1 + oddBlock c d) =
    1 + oddBlock (a + c) (b + d) + evenBlock (a * d) (b * c)
  rw [← hadd, ← oddBlock_mul_oddBlock]
  noncomm_ring

@[simp] theorem productDefect_zero_left (c d : R) :
    productDefect 0 0 c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [productDefect, evenBlock]

@[simp] theorem productDefect_zero_right (a b : R) :
    productDefect a b 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [productDefect, evenBlock]

/-- Additivity in the first pair, with coefficient multiplication in its original order. -/
theorem productDefect_add_left (a b c d e f : R) :
    productDefect (a + c) (b + d) e f =
      productDefect a b e f + productDefect c d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [productDefect, evenBlock, add_mul]

/-- Additivity in the second pair. -/
theorem productDefect_add_right (a b c d e f : R) :
    productDefect a b (c + e) (d + f) =
      productDefect a b c d + productDefect a b e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [productDefect, evenBlock, mul_add]

/-- The group 2-cocycle law for the additive group `R × R` and trivial action. -/
theorem productDefect_additive_cocycle (a b c d e f : R) :
    productDefect a b c d + productDefect (a + c) (b + d) e f =
      productDefect a b (c + e) (d + f) + productDefect c d e f := by
  rw [productDefect_add_left, productDefect_add_right]
  abel

/-- A pair-dependent correction cancels this particular product defect. -/
theorem operatorLift_mul_sub_defect (a b c d : R) :
    operatorLift a b * operatorLift c d - productDefect a b c d =
      operatorLift (a + c) (b + d) := by
  rw [operatorLift_mul, add_sub_cancel_right]

/-- Opposite ordered pairs have distinct defects in every nontrivial ring. -/
theorem productDefect_not_symmetric [Nontrivial R] :
    productDefect (1 : R) 0 0 1 ≠ productDefect 0 1 1 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  simp [productDefect] at h00

/-- There is no global 1-cochain whose additive coboundary is this cocycle.
The obstruction holds even when the cochain may take values in all matrices,
rather than only in the diagonal coefficient subgroup. -/
theorem productDefect_not_additive_coboundary [Nontrivial R] :
    ¬ ∃ f : R × R → Matrix (Fin 2) (Fin 2) R,
      ∀ x y : R × R,
        productDefect x.1 x.2 y.1 y.2 = f x + f y - f (x + y) := by
  rintro ⟨f, hf⟩
  apply productDefect_not_symmetric (R := R)
  calc
    productDefect (1 : R) 0 0 1 =
        f (1, 0) + f (0, 1) - f ((1, 0) + (0, 1)) := hf (1, 0) (0, 1)
    _ = f (0, 1) + f (1, 0) - f ((0, 1) + (1, 0)) := by
      rw [add_comm (f (1, 0)) (f (0, 1)), add_comm ((1, 0) : R × R) (0, 1)]
    _ = productDefect 0 1 1 0 := (hf (0, 1) (1, 0)).symm

/-- The two independent invertible diagonal entries of a block gauge. -/
def diagonalGauge (u v : Rˣ) : Matrix (Fin 2) (Fin 2) R :=
  evenBlock (u : R) (v : R)

/-- Unlike the balanced specialization, the two-unit gauge preserves products. -/
theorem diagonalGauge_mul (u₁ v₁ u₂ v₂ : Rˣ) :
    diagonalGauge u₁ v₁ * diagonalGauge u₂ v₂ =
      diagonalGauge (u₁ * u₂) (v₁ * v₂) := by
  exact evenBlock_mul_evenBlock (u₁ : R) (v₁ : R) (u₂ : R) (v₂ : R)

@[simp] theorem diagonalGauge_one : diagonalGauge (1 : Rˣ) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalGauge, evenBlock]

@[simp] theorem diagonalGauge_mul_inverse (u v : Rˣ) :
    diagonalGauge u v * diagonalGauge u⁻¹ v⁻¹ = 1 := by
  rw [diagonalGauge_mul]
  simp

@[simp] theorem diagonalGauge_inverse_mul (u v : Rˣ) :
    diagonalGauge u⁻¹ v⁻¹ * diagonalGauge u v = 1 := by
  rw [diagonalGauge_mul]
  simp

/-- The diagonal gauge as an explicitly constructed unit of the matrix ring. -/
def diagonalGaugeUnit (u v : Rˣ) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := diagonalGauge u v
  inv := diagonalGauge u⁻¹ v⁻¹
  val_inv := diagonalGauge_mul_inverse u v
  inv_val := diagonalGauge_inverse_mul u v

/-- The actual group homomorphism from two independent units to invertible matrices. -/
def diagonalGaugeHom : (Rˣ × Rˣ) →* (Matrix (Fin 2) (Fin 2) R)ˣ where
  toFun p := diagonalGaugeUnit p.1 p.2
  map_one' := Units.ext diagonalGauge_one
  map_mul' p q := Units.ext (diagonalGauge_mul p.1 p.2 q.1 q.2).symm

/-- Ordered transport of an odd block by an invertible diagonal gauge. -/
theorem diagonalGauge_conjugate_odd (u v : Rˣ) (a b : R) :
    diagonalGauge u v * oddBlock a b * diagonalGauge u⁻¹ v⁻¹ =
      oddBlock ((u : R) * a * (↑v⁻¹ : R)) ((v : R) * b * (↑u⁻¹ : R)) := by
  unfold diagonalGauge
  rw [evenBlock_mul_oddBlock, oddBlock_mul_evenBlock]

/-- Covariance of the lift under the two-unit diagonal gauge. -/
theorem diagonalGauge_conjugate_lift (u v : Rˣ) (a b : R) :
    diagonalGauge u v * operatorLift a b * diagonalGauge u⁻¹ v⁻¹ =
      operatorLift ((u : R) * a * (↑v⁻¹ : R)) ((v : R) * b * (↑u⁻¹ : R)) := by
  simp only [operatorLift, mul_add, mul_one, add_mul,
    diagonalGauge_mul_inverse, diagonalGauge_conjugate_odd]

/-- Equivariance of the ordered defect, without commuting any coefficients. -/
theorem diagonalGauge_conjugate_defect (u v : Rˣ) (a b c d : R) :
    diagonalGauge u v * productDefect a b c d * diagonalGauge u⁻¹ v⁻¹ =
      productDefect
        ((u : R) * a * (↑v⁻¹ : R)) ((v : R) * b * (↑u⁻¹ : R))
        ((u : R) * c * (↑v⁻¹ : R)) ((v : R) * d * (↑u⁻¹ : R)) := by
  simp only [diagonalGauge, productDefect, evenBlock_mul_evenBlock]
  congr 1 <;> simp [mul_assoc]

/-- The balanced diagonal conjugation formula from the source proposal.
This is a pointwise identity for each unit, not a renormalization-group action. -/
theorem balancedGauge_conjugate_lift (u : Rˣ) (a b : R) :
    diagonalGauge u u⁻¹ * operatorLift a b * diagonalGauge u⁻¹ u =
      operatorLift ((u : R) * a * (u : R)) ((↑u⁻¹ : R) * b * (↑u⁻¹ : R)) := by
  simpa using diagonalGauge_conjugate_lift u u⁻¹ a b

/-- Pointwise covariance of the defect under the balanced specialization. -/
theorem balancedGauge_conjugate_defect (u : Rˣ) (a b c d : R) :
    diagonalGauge u u⁻¹ * productDefect a b c d * diagonalGauge u⁻¹ u =
      productDefect
        ((u : R) * a * (u : R)) ((↑u⁻¹ : R) * b * (↑u⁻¹ : R))
        ((u : R) * c * (u : R)) ((↑u⁻¹ : R) * d * (↑u⁻¹ : R)) := by
  simpa using diagonalGauge_conjugate_defect u u⁻¹ a b c d

end InfoGeometry.Algebra.FreedAdditiveCocycle
