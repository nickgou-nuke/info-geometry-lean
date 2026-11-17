/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.RealSpacetimeQuaternion
import Mathlib.Data.Matrix.Basis
import Mathlib.Order.Atoms
import Mathlib.RingTheory.Ideal.Span

/-!
# The primitive time projector and its real spinor ideal

The native Clifford idempotent `(1 + γ₀) / 2` is represented by the first
diagonal matrix unit in `M₂(ℍ)`. Its principal left ideal is the native
`Ideal.span {timeProjector}`, with the full Clifford left action. First-column
coordinates give a real linear equivalence with two real quaternions.

A nonzero vector in this ideal has a nonzero quaternion coordinate. Its
inverse constructs a left multiplier recovering the projector. This proves
minimality in the left-ideal lattice and the explicit supported-idempotent
criterion for primitivity. No classification of other ideals is asserted.
-/

noncomputable section

namespace InfoGeometry.Clifford.RealSpacetimeIdeal

open HestenesCl14
open InfoGeometry.Clifford.RealSpacetimeQuaternion
open scoped Matrix

/-- The time projector is an idempotent in the actual Clifford algebra. -/
theorem timeProjector_isIdempotentElem : IsIdempotentElem timeProjector := by
  change timeProjector * timeProjector = timeProjector
  apply quaternionRep_injective
  simp only [map_mul, quaternionRep_timeProjector]
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem timeProjector_ne_zero : timeProjector ≠ 0 := by
  intro h
  have hentry := congrArg (fun x : Cl14 => quaternionRep x 0 0) h
  have hone : (1 : Quaternion ℝ) = 0 := by simpa using hentry
  exact one_ne_zero hone

/-- The principal left ideal uses the native noncommutative ideal carrier. -/
def timeProjectorLeftIdeal : Ideal Cl14 := Ideal.span {timeProjector}

/-- Membership is exactly invariance under right multiplication by the projector. -/
theorem mem_timeProjectorLeftIdeal_iff (x : Cl14) :
    x ∈ timeProjectorLeftIdeal ↔ x * timeProjector = x := by
  rw [timeProjectorLeftIdeal, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    rw [mul_assoc, timeProjector_isIdempotentElem.eq]
  · intro hx
    exact ⟨x, hx⟩

/-- Every element of the left ideal has zero second column. -/
theorem quaternionRep_second_column_eq_zero {x : Cl14}
    (hx : x ∈ timeProjectorLeftIdeal) (i : Fin 2) :
    quaternionRep x i 1 = 0 := by
  have hentry := congrArg (fun a : Cl14 => quaternionRep a i 1)
    ((mem_timeProjectorLeftIdeal_iff x).mp hx)
  simpa [map_mul, Matrix.mul_apply, Fin.sum_univ_two] using hentry.symm

/-- The first column determines an element of the left ideal. -/
theorem quaternionRep_eq_first_column {x : Cl14}
    (hx : x ∈ timeProjectorLeftIdeal) :
    quaternionRep x = !![quaternionRep x 0 0, 0; quaternionRep x 1 0, 0] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact quaternionRep_second_column_eq_zero hx 0
  · rfl
  · exact quaternionRep_second_column_eq_zero hx 1

/-- Every first-column quaternion matrix has an intrinsic ideal preimage. -/
theorem matrixPreimage_first_column_mem (p q : Quaternion ℝ) :
    matrixPreimage !![p, 0; q, 0] ∈ timeProjectorLeftIdeal := by
  rw [mem_timeProjectorLeftIdeal_iff]
  apply quaternionRep_injective
  simp only [map_mul, quaternionRep_matrixPreimage, quaternionRep_timeProjector]
  apply Matrix.ext
  intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Actual first-column coordinates for the native Clifford left ideal. -/
def timeProjectorLeftIdealEquiv :
    timeProjectorLeftIdeal ≃ₗ[ℝ] (Quaternion ℝ × Quaternion ℝ) where
  toFun x := (quaternionRep (x : Cl14) 0 0, quaternionRep (x : Cl14) 1 0)
  invFun z := ⟨matrixPreimage !![z.1, 0; z.2, 0],
    matrixPreimage_first_column_mem z.1 z.2⟩
  left_inv x := by
    apply Subtype.ext
    apply quaternionRep_injective
    rw [quaternionRep_matrixPreimage]
    exact (quaternionRep_eq_first_column x.2).symm
  right_inv z := by
    simpa only [quaternionRep_matrixPreimage] using (Prod.eta z)
  map_add' x y :=
    congrArg (fun A : QuaternionMatrix => (A 0 0, A 1 0))
      (quaternionRep.map_add (x : Cl14) (y : Cl14))
  map_smul' r x :=
    congrArg (fun A : QuaternionMatrix => (A 0 0, A 1 0))
      (quaternionRep.map_smul r (x : Cl14))

/-- The native principal left ideal has real dimension eight. -/
theorem timeProjectorLeftIdeal_finrank :
    Module.finrank ℝ timeProjectorLeftIdeal = 8 := by
  calc
    Module.finrank ℝ timeProjectorLeftIdeal =
        Module.finrank ℝ (Quaternion ℝ × Quaternion ℝ) :=
      timeProjectorLeftIdealEquiv.finrank_eq
    _ = 8 := by norm_num [Module.finrank_prod, Quaternion.finrank_eq_four]

/-- A nonzero ideal element has a nonzero quaternion entry in its first column. -/
theorem exists_first_column_ne_zero {x : Cl14}
    (hx : x ∈ timeProjectorLeftIdeal) (hx0 : x ≠ 0) :
    ∃ j : Fin 2, quaternionRep x j 0 ≠ 0 := by
  classical
  by_contra h
  apply hx0
  apply quaternionRep_injective
  rw [map_zero]
  apply Matrix.ext
  intro i j
  fin_cases j
  · exact not_not.mp ((not_exists.mp h) i)
  · exact quaternionRep_second_column_eq_zero hx i

/-- An explicit quaternion inverse recovers the projector by left multiplication. -/
theorem exists_left_mul_eq_timeProjector {x : Cl14}
    (hx : x ∈ timeProjectorLeftIdeal) (hx0 : x ≠ 0) :
    ∃ a : Cl14, a * x = timeProjector := by
  obtain ⟨j, hj⟩ := exists_first_column_ne_zero hx hx0
  refine ⟨matrixPreimage (Matrix.single 0 j (quaternionRep x j 0)⁻¹), ?_⟩
  apply quaternionRep_injective
  simp only [map_mul, quaternionRep_matrixPreimage, quaternionRep_timeProjector]
  apply Matrix.ext
  intro i k
  fin_cases i <;> fin_cases k
  · rw [Matrix.single_mul_apply_same]
    exact inv_mul_cancel₀ hj
  · rw [Matrix.single_mul_apply_same, quaternionRep_second_column_eq_zero hx, mul_zero]
  · exact Matrix.single_mul_apply_of_ne
      (quaternionRep x j 0)⁻¹ (0 : Fin 2) j 1 0 (by decide) (quaternionRep x)
  · exact Matrix.single_mul_apply_of_ne
      (quaternionRep x j 0)⁻¹ (0 : Fin 2) j 1 1 (by decide) (quaternionRep x)

/-- Supported idempotents are zero or the whole projector: the primitive criterion. -/
theorem timeProjector_supported_idempotent_eq_zero_or_self (f : Cl14)
    (hf : IsIdempotentElem f)
    (hleft : timeProjector * f = f) (hright : f * timeProjector = f) :
    f = 0 ∨ f = timeProjector := by
  by_cases hf0 : f = 0
  · exact Or.inl hf0
  · obtain ⟨a, ha⟩ := exists_left_mul_eq_timeProjector
      ((mem_timeProjectorLeftIdeal_iff f).mpr hright) hf0
    right
    calc
      f = timeProjector * f := hleft.symm
      _ = (a * f) * f := congrArg (· * f) ha.symm
      _ = a * (f * f) := mul_assoc a f f
      _ = a * f := congrArg (a * ·) hf.eq
      _ = timeProjector := ha

theorem timeProjectorLeftIdeal_ne_bot : timeProjectorLeftIdeal ≠ ⊥ := by
  intro h
  exact timeProjector_ne_zero (Ideal.span_singleton_eq_bot.mp h)

/-- Minimality is in the lattice of left ideals for the full Clifford action. -/
theorem timeProjectorLeftIdeal_isAtom : IsAtom timeProjectorLeftIdeal := by
  refine isAtom_iff_le_of_ge.mpr ⟨timeProjectorLeftIdeal_ne_bot, ?_⟩
  intro J hJ hJI
  obtain ⟨x, hx, hx0⟩ := J.ne_bot_iff.mp hJ
  obtain ⟨a, ha⟩ := exists_left_mul_eq_timeProjector (hJI hx) hx0
  apply (Ideal.span_singleton_le_iff_mem J).mpr
  simpa only [ha] using J.mul_mem_left a hx

end InfoGeometry.Clifford.RealSpacetimeIdeal
