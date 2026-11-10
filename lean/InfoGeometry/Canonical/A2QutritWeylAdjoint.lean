/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.A2QutritTransitionRootBridge
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl

/-!
# Weyl adjoint transport of the `A₂` qutrit transition roots

The colour shift acts on the concrete transition-root realization by cyclic
transport of both matrix indices.  This is an actual matrix equality, not a
representation contract or a supplied equivariance witness.

BUCKET 1: The finite cyclic action and its conjugation formulas on qutrit
matrix units are proved directly.
BUCKET 2: No conditional theorem is asserted.
BUCKET 3: No Lie-group integration or infinite-dimensional orbit is claimed.
-/

noncomputable section

namespace InfoGeometry.Canonical.A2QutritWeylAdjoint

open Matrix
open InfoGeometry.Canonical.A2InsideD5RootSubsystem
open InfoGeometry.Canonical.A2QutritTransitionRootBridge
open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

theorem next3_injective : Function.Injective next3 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [next3] at h ⊢

def shiftRoot (r : A2Root) : A2Root :=
  ⟨(next3 r.1.1, next3 r.1.2), by
    intro h
    exact r.property (next3_injective h)⟩

@[simp] theorem next3_three (i : Fin 3) :
    next3 (next3 (next3 i)) = i := by
  fin_cases i <;> rfl

@[simp] theorem shiftRoot_three (r : A2Root) :
    shiftRoot (shiftRoot (shiftRoot r)) = r := by
  apply Subtype.ext
  apply Prod.ext <;> simp [shiftRoot, next3_three]

/-- The cyclic colour shift acts freely on the six ordered roots: an `A₂`
root cannot be fixed by a simultaneous nontrivial cyclic shift of both
coordinates. -/
theorem shiftRoot_ne_self (r : A2Root) : shiftRoot r ≠ r := by
  intro h
  have hfst := congrArg (fun s : A2Root => s.1.1) h
  have hnextfst : next3 r.1.1 = r.1.1 := by simpa [shiftRoot] using hfst
  exact (next3_ne r.1.1) hnextfst.symm

theorem shiftRoot_injective : Function.Injective shiftRoot := by
  intro r s h
  calc
    r = shiftRoot (shiftRoot (shiftRoot r)) := (shiftRoot_three r).symm
    _ = shiftRoot (shiftRoot (shiftRoot s)) := by rw [h]
    _ = s := shiftRoot_three s

/-- Each root has a genuine orbit of length three under the cyclic Weyl
action; the two nonidentity translates are distinct from each other and from
the original root. -/
theorem shiftRoot_orbit_three_distinct (r : A2Root) :
    r ≠ shiftRoot r ∧ r ≠ shiftRoot (shiftRoot r) ∧
      shiftRoot r ≠ shiftRoot (shiftRoot r) := by
  have h₁ := shiftRoot_ne_self r
  have h₂ := shiftRoot_ne_self (shiftRoot r)
  refine ⟨Ne.symm h₁, ?_, ?_⟩
  · intro h
    have h₃ : r ≠ shiftRoot (shiftRoot r) := by
      simpa [shiftRoot_three] using shiftRoot_ne_self (shiftRoot (shiftRoot r))
    exact h₃ h
  · intro h
    exact h₂ h.symm

def shiftRootEquiv : Equiv.Perm A2Root where
  toFun := shiftRoot
  invFun := fun r => shiftRoot (shiftRoot r)
  left_inv r := shiftRoot_three r
  right_inv r := shiftRoot_three r

@[simp] theorem shiftRoot_opposite (r : A2Root) :
    shiftRoot (oppositeRoot r) = oppositeRoot (shiftRoot r) := by
  apply Subtype.ext
  apply Prod.ext <;> simp [shiftRoot, oppositeRoot]

theorem shiftRootEquiv_cube : shiftRootEquiv ^ 3 = 1 := by
  apply Equiv.ext
  intro r
  change shiftRoot (shiftRoot (shiftRoot r)) = r
  exact shiftRoot_three r

theorem colorShift_conj_single (i j : Fin 3) :
    colorShift * Matrix.single i j (1 : ℂ) * colorShift ^ 2 =
      Matrix.single (next3 i) (next3 j) (1 : ℂ) := by
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [colorShift, next3, Matrix.single, Matrix.mul_apply,
      pow_two, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem colorShift_sq_conj_single (i j : Fin 3) :
    colorShift ^ 2 * Matrix.single i j (1 : ℂ) * colorShift =
      Matrix.single (next3 (next3 i)) (next3 (next3 j)) (1 : ℂ) := by
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [colorShift, next3, Matrix.single, Matrix.mul_apply,
      pow_two, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem colorShift_conj_transitionMatrix (r : A2Root) :
    colorShift * transitionMatrix r * colorShift ^ 2 =
      transitionMatrix (shiftRoot r) := by
  simpa [transitionMatrix, shiftRoot] using
    colorShift_conj_single r.1.1 r.1.2

theorem colorShift_sq_conj_transitionMatrix (r : A2Root) :
    colorShift ^ 2 * transitionMatrix r * colorShift =
      transitionMatrix (shiftRootEquiv.symm r) := by
  simpa [transitionMatrix, shiftRootEquiv, shiftRoot] using
    colorShift_sq_conj_single r.1.1 r.1.2

theorem diagonal_conj_single (d : Fin 3 → ℂ) (i j : Fin 3) :
    Matrix.diagonal d * Matrix.single i j (1 : ℂ) *
        Matrix.diagonal (fun k => (d k)⁻¹) =
      (d i * (d j)⁻¹) • Matrix.single i j (1 : ℂ) := by
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply]
  by_cases ha : a = i
  · subst a
    by_cases hb : b = j
    · subst b
      simp [Matrix.single]
    · have hb' : j ≠ b := Ne.symm hb
      simp [Matrix.single, hb']
  · have ha' : i ≠ a := Ne.symm ha
    by_cases hb : b = j
    · subst b
      simp [Matrix.single, ha']
    · have hb' : j ≠ b := Ne.symm hb
      simp [Matrix.single, ha', hb']

def clockWeight (ω : ℂ) (i : Fin 3) : ℂ := ω ^ (i : ℕ)

theorem colorClock_eq_diagonal (ω : ℂ) :
    colorClock ω = Matrix.diagonal (clockWeight ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorClock, clockWeight, Matrix.diagonal]

theorem colorClock_sq_eq_diagonal_inv (ω : ℂ) (hω : ω ^ 3 = 1) :
    colorClock ω ^ 2 =
      Matrix.diagonal (fun k => (clockWeight ω k)⁻¹) := by
  rw [colorClock_eq_diagonal, pow_two, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  have hne : ω ≠ 0 := by
    intro hz
    rw [hz] at hω
    norm_num at hω
  fin_cases k
  · simp [clockWeight]
  · simp only [clockWeight]
    field_simp [hne]
    simpa [pow_three] using hω
  · simp only [clockWeight]
    field_simp [hne]
    calc
      ω ^ 6 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω]; norm_num

theorem colorClock_conj_single (ω : ℂ) (hω : ω ^ 3 = 1) (i j : Fin 3) :
    colorClock ω * Matrix.single i j (1 : ℂ) * colorClock ω ^ 2 =
      (clockWeight ω i * (clockWeight ω j)⁻¹) •
        Matrix.single i j (1 : ℂ) := by
  rw [colorClock_sq_eq_diagonal_inv ω hω, colorClock_eq_diagonal]
  exact diagonal_conj_single (clockWeight ω) i j

theorem colorClock_conj_transitionMatrix
    (ω : ℂ) (hω : ω ^ 3 = 1) (r : A2Root) :
    colorClock ω * transitionMatrix r * colorClock ω ^ 2 =
      (clockWeight ω r.1.1 * (clockWeight ω r.1.2)⁻¹) •
        transitionMatrix r := by
  simpa [transitionMatrix] using
    colorClock_conj_single ω hω r.1.1 r.1.2

end InfoGeometry.Canonical.A2QutritWeylAdjoint

end noncomputable section
