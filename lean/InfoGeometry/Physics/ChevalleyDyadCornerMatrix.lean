import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic
import InfoGeometry.Physics.ChevalleyDyads

/-!
# CAR matrix coordinates over the vacuum corner

This module reuses the repository's CAR dyads and Mathlib's native idempotent
corner ring. The vacuum projector supplies the corner unit; no identification
of that corner with the scalar ring is assumed.
-/

namespace InfoGeometry.Physics.ChevalleyDyadCornerMatrix

open CategoryTheory
open InfoGeometry.Physics.ChevalleyDyads

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

section CornerRing

variable {A : Type*} [Ring A] (e : A)

/-- The corner ring `eAe`, using Mathlib's native idempotent-corner type. -/
abbrev CornerRing := NonUnitalRing.corner e

/-- Mathlib's corner carrier, equipped with the idempotent `e` as its unit.
The non-unital operations are inherited from `NonUnitalRing.corner`. -/
def cornerRing (he : e * e = e) : Ring (CornerRing e) := by
  letI : One (CornerRing e) := ⟨⟨e, by
    change e ∈ Set.range (e * · * e)
    exact ⟨1, by simp [he]⟩⟩⟩
  exact Ring.ofMinimalAxioms
    (fun a b c => by apply Subtype.ext; exact add_assoc _ _ _)
    (fun a => by apply Subtype.ext; exact zero_add _)
    (fun a => by apply Subtype.ext; exact neg_add_cancel _)
    (fun a b c => by apply Subtype.ext; exact mul_assoc _ _ _)
    (fun a => by
      apply Subtype.ext
      exact (Subsemigroup.mem_corner_iff he).mp a.2 |>.1)
    (fun a => by
      apply Subtype.ext
      exact (Subsemigroup.mem_corner_iff he).mp a.2 |>.2)
    (fun a b c => by apply Subtype.ext; exact mul_add _ _ _)
    (fun a b c => by apply Subtype.ext; exact add_mul _ _ _)

end CornerRing

section MatrixUnits

variable {A : Type*} [Ring A] (n p : A)

/-- The four CAR matrix units in row-column order. -/
def carMatrixUnit (i j : Fin 2) : A :=
  if i = 0 then
    if j = 0 then n * p else n
  else if j = 0 then p else p * n

/-- CAR implies the reverse product relation. -/
theorem car_reverse_mul (hn : n * n = 0) (hp : p * p = 0)
    (hcar : n * p + p * n = 1) :
    p * n = 1 - n * p := by
  rw [← hcar]
  abel

/-- The CAR elements form a complete system of four matrix units. -/
theorem carMatrixUnit_mul (hn : n * n = 0) (hp : p * p = 0)
    (hcar : n * p + p * n = 1) (i j k l : Fin 2) :
    carMatrixUnit n p i j * carMatrixUnit n p k l =
      if j = k then carMatrixUnit n p i l else 0 := by
  have hpn := car_reverse_mul n p hn hp hcar
  have hnpn : n * p * n = n := by
    calc
      n * p * n = (n * p + p * n) * n := by
        rw [add_mul, mul_assoc p n n, hn, mul_zero, add_zero]
      _ = n := by rw [hcar, one_mul]
  have hpnp : p * n * p = p := by
    have hcar' : p * n + n * p = 1 := by rw [add_comm]; exact hcar
    calc
      p * n * p = (p * n + n * p) * p := by
        rw [add_mul, mul_assoc n p p, hp, mul_zero, add_zero]
      _ = p := by rw [hcar', one_mul]
  have hnpp : n * p * p = 0 := by
    calc
      n * p * p = n * (p * p) := by rw [mul_assoc]
      _ = n * 0 := by rw [hp]
      _ = 0 := mul_zero n
  have hpnn : p * n * n = 0 := by
    calc
      p * n * n = p * (n * n) := by rw [mul_assoc]
      _ = p * 0 := by rw [hn]
      _ = 0 := mul_zero p
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [carMatrixUnit, hnpn, hpnp, hnpp, hpnn, hn, hp, ← mul_assoc]

end MatrixUnits

end InfoGeometry.Physics.ChevalleyDyadCornerMatrix
