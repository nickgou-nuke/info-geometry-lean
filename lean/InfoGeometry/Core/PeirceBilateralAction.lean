/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceRotor
import InfoGeometry.Algebra.AlternativeDerivations

/-!
# Bilateral Peirce actions

These are algebraic left/right multiplication operators, not integral Laplace
transforms. The active identity is `carrierSupport`, not the ambient `1`.
The four corner multipliers are separable and satisfy a determinant-zero law.
-/

namespace InfoGeometry.Core.PeirceBilateralAction

open InfoGeometry.Core.DualSeedPeirce InfoGeometry.Core.PeirceRotor
open InfoGeometry.Core.DiracSuperalgebra InfoGeometry.Algebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Bundle the existing left/right multiplication maps on the actual algebra. -/
def bilateral (u v : A) : A →ₗ[R] A := (R_map v).comp (L_map u)

@[simp] theorem bilateral_apply (u v x : A) : bilateral (R := R) u v x = u * x * v := rfl

/-- The right factors compose in the opposite order. -/
theorem bilateral_comp (u v a b : A) :
    (bilateral (R := R) u v).comp (bilateral a b) = bilateral (u * a) (b * v) := by
  ext x
  simp only [LinearMap.comp_apply, bilateral_apply, mul_assoc]

/-- Units on the two sides give a linear equivalence, without a metric. -/
def bilateralEquiv (u v : Aˣ) : A ≃ₗ[R] A where
  toLinearMap := bilateral (u : A) (v : A)
  invFun := bilateral (R := R) (↑(u⁻¹)) (↑(v⁻¹))
  left_inv x := by simp [bilateral_apply, mul_assoc]
  right_inv x := by simp [bilateral_apply, mul_assoc]

/-- The diagonal specialization of the existing supported block evaluator. -/
def diagonal (d b : A) (lam mu : R) : A := peirceBlock d b lam 0 0 mu

@[simp] theorem diagonal_formula (d b : A) (lam mu : R) :
    diagonal d b lam mu = lam • polePlus d b + mu • poleMinus d b := by
  simp [diagonal, peirceBlock]

/-- Expansion is valid for every ambient signal; it does not assert active support. -/
theorem four_corner_expansion (d b x : A) (l m r s : R) :
    bilateral (diagonal d b l m) (diagonal d b r s) x =
      (l * r) • (polePlus d b * x * polePlus d b) +
      (l * s) • (polePlus d b * x * poleMinus d b) +
      (m * r) • (poleMinus d b * x * polePlus d b) +
      (m * s) • (poleMinus d b * x * poleMinus d b) := by
  simp only [bilateral_apply, diagonal_formula, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  module

/-- The four corners reconstruct the active compression, not an arbitrary signal. -/
theorem active_corner_sum (d b x : A) :
    polePlus d b * x * polePlus d b + polePlus d b * x * poleMinus d b +
    poleMinus d b * x * polePlus d b + poleMinus d b * x * poleMinus d b =
      carrierSupport d b * x * carrierSupport d b := by
  change _ = (polePlus d b + poleMinus d b) * x * (polePlus d b + poleMinus d b)
  noncomm_ring

/-- A product of two scalar weight vectors cannot prescribe four independent weights. -/
theorem weights_separable (l m r s : R) :
    (l * r) * (m * s) = (l * s) * (m * r) := by ring

/-- A reusable corner eigen-scaling contract on an arbitrary algebra. -/
theorem corner_scaling (u v p q x : A) (l r : R)
    (hl : u * p = l • p) (hr : q * v = r • q) :
    bilateral u v (p * x * q) = (l * r) • (p * x * q) := by
  calc
    _ = (u * p) * x * (q * v) := by simp only [bilateral_apply, mul_assoc]
    _ = _ := by rw [hl, hr]; simp only [smul_mul_assoc, mul_smul_comm, smul_smul]

variable {d b : A}

/-- Full supported-block action, rather than four unrelated generator calculations. -/
theorem diagonal_block_action (h : IsDualSeedPair d b) (l m r s a x y z : R) :
    bilateral (diagonal d b l m) (diagonal d b r s) (peirceBlock d b a x y z) =
      peirceBlock d b ((l * r) * a) ((l * s) * x) ((m * r) * y) ((m * s) * z) := by
  simp only [bilateral_apply, diagonal, peirceBlock_mul h]
  congr 1 <;> ring

/-- The two regimes in the intake are distinct specializations of one operator. -/
theorem symmetric_adjoint_selectivity (h : IsDualSeedPair d b)
    {l m : R} (hlm : l * m = 1) (a x y z : R) :
    bilateral (diagonal d b l m) (diagonal d b l m) (peirceBlock d b a x y z) =
      peirceBlock d b ((l * l) * a) x y ((m * m) * z) ∧
    bilateral (diagonal d b l m) (diagonal d b m l) (peirceBlock d b a x y z) =
      peirceBlock d b a ((l * l) * x) ((m * m) * y) z := by
  have hml : m * l = 1 := by simpa [mul_comm] using hlm
  constructor <;> rw [diagonal_block_action h] <;> simp only [hlm, hml, one_mul]

/-- Complete the reciprocal diagonal operator by the identity on the harmonic part. -/
theorem completed_diagonal_inverse (h : IsDualSeedPair d b)
    {l m : R} (hlm : l * m = 1) :
    completedBlock d b l 0 0 m * completedBlock d b m 0 0 l = 1 ∧
    completedBlock d b m 0 0 l * completedBlock d b l 0 0 m = 1 := by
  have hml : m * l = 1 := by simpa [mul_comm] using hlm
  have hid : completedBlock d b (1 : R) 0 0 1 = 1 := by
    simpa [phaseRotor] using (phaseRotor_one_zero (R := R) (d := d) (b := b))
  constructor <;> rw [completedBlock_mul h] <;>
    simpa only [mul_zero, zero_mul, zero_add, add_zero, hlm, hml] using hid

/-- An ambient unit with both inverse equations proved from the seed equations. -/
def diagonalUnit (h : IsDualSeedPair d b) {l m : R} (hlm : l * m = 1) : Aˣ where
  val := completedBlock d b l 0 0 m
  inv := completedBlock d b m 0 0 l
  val_inv := (completed_diagonal_inverse h hlm).1
  inv_val := (completed_diagonal_inverse h hlm).2

/-- An ordered product, without assuming the two factors commute. -/
def mixedUnit (h : IsDualSeedPair d b) {l m c s : R}
    (hlm : l * m = 1) (hcs : c * c + s * s = 1) : Aˣ :=
  diagonalUnit h hlm * phaseRotorUnit h hcs

/-- Inversion reverses the diagonal/rotor order. -/
theorem mixedUnit_inverse (h : IsDualSeedPair d b) {l m c s : R}
    (hlm : l * m = 1) (hcs : c * c + s * s = 1) :
    (↑((mixedUnit h hlm hcs)⁻¹) : A) =
      phaseRotor c (-s) d b * completedBlock d b m 0 0 l := rfl

/-- The exact obstruction to commuting a diagonal factor with an active rotor. -/
theorem diagonal_rotor_commutator (h : IsDualSeedPair d b) (l m c s : R) :
    diagonal d b l m * peirceBlock d b c s (-s) c -
      peirceBlock d b c s (-s) c * diagonal d b l m =
      (s * (l - m)) • transitionVelocity d b := by
  simp only [diagonal, peirceBlock_mul h]
  unfold peirceBlock transitionVelocity majoranaPlus
  module

end InfoGeometry.Core.PeirceBilateralAction
