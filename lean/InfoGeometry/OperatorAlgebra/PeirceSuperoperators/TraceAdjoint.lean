/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.MixedActions
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.Group.Pi.Torsion

/-!
# Native bilinear trace adjoints and the mixed-action defect

The form is the native bilinear multiplication map followed by matrix trace.
Its adjoints reverse composition order. Bilinear trace symmetry is distinct
from self-adjointness for the complex Hilbert–Schmidt metric.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators

open Matrix
open InfoGeometry.Core.JordanMultiplicationClosure

attribute [local instance] LieRing.ofAssociativeRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

local notation "D" => LieAlgebra.ad R (Matrix n n R)
local notation "J" => jordanLeft (R := R)
local notation "E" => Module.End R (Matrix n n R)
local notation "B" =>
  LinearMap.compr₂ (LinearMap.mul R (Matrix n n R)) (Matrix.traceLinearMap n R R)

/-- The actual trace bilinear form pairs an inner action with its negative. -/
theorem trace_adjoint_ad (u : Matrix n n R) :
    LinearMap.IsAdjointPair B B (D u) (-D u : E) := by
  intro X Y
  change trace ((u * X - X * u) * Y) = trace (X * -(u * Y - Y * u))
  rw [mul_neg, trace_neg]
  exact eq_neg_of_add_eq_zero_right
    (trace_adjoint_identity (traceAddMonoidHom n R) trace_mul_comm u X Y)

/-- Jordan multiplication is self-adjoint for the same native bilinear form. -/
theorem trace_adjoint_jordan (u : Matrix n n R) :
    LinearMap.IsAdjointPair B B (J u) (J u) := by
  intro X Y
  change trace ((u * X + X * u) * Y) = trace (X * (u * Y + Y * u))
  rw [add_mul, mul_add, trace_add, trace_add, trace_mul_cycle u X Y,
    trace_mul_cycle Y u X]
  simp only [mul_assoc]
  rw [add_comm]

/-- The symmetric double inner action is trace-self-adjoint for arbitrary coefficients. -/
theorem trace_adjoint_double_lie (u v : Matrix n n R) :
    LinearMap.IsAdjointPair B B
      (-(D u * D v + D v * D u) : E) (-(D u * D v + D v * D u) : E) := by
  have h₁ := LinearMap.IsAdjointPair.mul (f := D u) (g := -D u)
    (f' := D v) (g' := -D v) (trace_adjoint_ad u) (trace_adjoint_ad v)
  have h₂ := LinearMap.IsAdjointPair.mul (f := D v) (g := -D v)
    (f' := D u) (g' := -D u) (trace_adjoint_ad v) (trace_adjoint_ad u)
  simpa only [neg_mul_neg, neg_one_smul, add_comm] using
    LinearMap.IsAdjointPair.smul (-1 : R) (h₁.add h₂)

/-- The mixed action's trace adjoint has reversed composition order. -/
theorem trace_adjoint_mixed_difference (u v : Matrix n n R) :
    LinearMap.IsAdjointPair B B
      (D u * J v - D v * J u : E) (J u * D v - J v * D u : E) := by
  have h₁ := LinearMap.IsAdjointPair.mul (f := D u) (g := -D u)
    (f' := J v) (g' := J v) (trace_adjoint_ad u) (trace_adjoint_jordan v)
  have h₂ := LinearMap.IsAdjointPair.mul (f := D v) (g := -D v)
    (f' := J u) (g' := J u) (trace_adjoint_ad v) (trace_adjoint_jordan u)
  simpa only [mul_neg, neg_sub_neg] using h₁.sub h₂

/-- Adding an inner action changes its sign in the bilinear trace adjoint. -/
theorem trace_adjoint_commutator_perturbation (u v : Matrix n n R) :
    LinearMap.IsAdjointPair B B
      (D (u * v + v * u) - (D u * D v + D v * D u) : E)
      (-D (u * v + v * u) - (D u * D v + D v * D u) : E) := by
  have h := (trace_adjoint_ad (u * v + v * u)).add (trace_adjoint_double_lie u v)
  simpa only [sub_eq_add_neg] using h

/-- The failure of mixed trace-skewness is exactly the Jordan commutator term. -/
theorem trace_mixed_skew_defect (u v X Y : Matrix n n R) :
    trace (((D u * J v - D v * J u) X) * Y) +
      trace (X * ((D u * J v - D v * J u) Y)) =
        2 • trace (X * (J ⁅u, v⁆ Y)) := by
  have hsum : (J u * D v - J v * D u) + (D u * J v - D v * J u) =
      2 • J ⁅u, v⁆ := by
    rw [jordan_lie_difference, lie_jordan_difference]
    abel
  have h := trace_adjoint_mixed_difference u v X Y
  change trace (((D u * J v - D v * J u) X) * Y) =
    trace (X * ((J u * D v - J v * D u) Y)) at h
  rw [h, ← trace_add, ← mul_add]
  have hy := LinearMap.congr_fun hsum Y
  change (J u * D v - J v * D u) Y + (D u * J v - D v * J u) Y =
    2 • (J ⁅u, v⁆ Y) at hy
  rw [hy, mul_nsmul, trace_smul]

/-- The exact skewness obstruction is valid without a characteristic restriction. -/
theorem trace_mixed_isSkewAdjoint_iff (u v : Matrix n n R) :
    LinearMap.IsSkewAdjoint B (D u * J v - D v * J u : E) ↔
      (2 : ℕ) • J ⁅u, v⁆ = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro Y
    apply (Matrix.ext_iff_trace_mul_left).mpr
    intro X
    have hd := trace_mixed_skew_defect u v X Y
    have hs := h X Y
    change trace (((D u * J v - D v * J u) X) * Y) =
      trace (X * -((D u * J v - D v * J u) Y)) at hs
    rw [mul_neg, trace_neg] at hs
    rw [hs, neg_add_cancel] at hd
    simpa only [LinearMap.smul_apply, LinearMap.zero_apply, mul_nsmul,
      trace_smul, mul_zero, trace_zero] using hd.symm
  · intro h
    have hsum : (J u * D v - J v * D u) + (D u * J v - D v * J u) = 0 := by
      rw [jordan_lie_difference, lie_jordan_difference]
      calc
        _ = 2 • J ⁅u, v⁆ := by abel
        _ = 0 := h
    have heq := eq_neg_of_add_eq_zero_left hsum
    change LinearMap.IsAdjointPair B B (D u * J v - D v * J u : E)
      (-(D u * J v - D v * J u) : E)
    rw [← heq]
    exact trace_adjoint_mixed_difference u v

/-- With additive torsion excluded, mixed trace-skewness is equivalent to commutation. -/
theorem trace_mixed_isSkewAdjoint_iff_commute [IsAddTorsionFree R]
    (u v : Matrix n n R) :
    LinearMap.IsSkewAdjoint B (D u * J v - D v * J u : E) ↔ Commute u v := by
  let : IsAddTorsionFree (Matrix n n R) :=
    inferInstanceAs (IsAddTorsionFree (n → n → R))
  rw [trace_mixed_isSkewAdjoint_iff]
  constructor
  · intro h
    have h1 := LinearMap.congr_fun h (1 : Matrix n n R)
    change (2 : ℕ) • (⁅u, v⁆ * 1 + 1 * ⁅u, v⁆) = 0 at h1
    rw [mul_one, one_mul, ← two_nsmul] at h1
    have h2 : (2 : ℕ) • ⁅u, v⁆ = 0 :=
      nsmul_right_injective (M := Matrix n n R) (by decide : (2 : ℕ) ≠ 0)
        (by simpa only [nsmul_zero] using h1)
    have hz : ⁅u, v⁆ = 0 :=
      nsmul_right_injective (M := Matrix n n R) (by decide : (2 : ℕ) ≠ 0)
        (by simpa only [nsmul_zero] using h2)
    exact sub_eq_zero.mp hz
  · intro h
    apply LinearMap.ext
    intro X
    change (2 : ℕ) • ((u * v - v * u) * X + X * (u * v - v * u)) = 0
    rw [h.eq, sub_self, zero_mul, mul_zero, add_zero, nsmul_zero]

/-- The symmetric double inner action annihilates matrix trace. -/
theorem trace_double_lie (u v X : Matrix n n R) :
    trace ((-(D u * D v + D v * D u)) X) = 0 := by
  have hz (a b : Matrix n n R) : trace (D a b) = 0 := by
    change trace (a * b - b * a) = 0
    rw [trace_sub, trace_mul_comm a b, sub_self]
  change trace (-(D u (D v X) + D v (D u X))) = 0
  rw [trace_neg, trace_add, hz, hz, add_zero, neg_zero]

/-- The mixed difference also annihilates trace, despite generally not being skew-adjoint. -/
theorem trace_mixed_difference (u v X : Matrix n n R) :
    trace ((D u * J v - D v * J u) X) = 0 := by
  have hz (a b : Matrix n n R) : trace (D a b) = 0 := by
    change trace (a * b - b * a) = 0
    rw [trace_sub, trace_mul_comm a b, sub_self]
  change trace (D u (J v X) - D v (J u X)) = 0
  rw [trace_sub, hz, hz, sub_self]

/-- The source's raw commutator perturbation annihilates trace. -/
theorem trace_commutator_perturbation (u v X : Matrix n n R) :
    trace ((D (u * v + v * u) - (D u * D v + D v * D u)) X) = 0 := by
  rw [sub_eq_add_neg, LinearMap.add_apply, trace_add, trace_double_lie, add_zero]
  change trace ((u * v + v * u) * X - X * (u * v + v * u)) = 0
  rw [trace_sub, trace_mul_comm, sub_self]

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators
