/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55BivectorVectorRepresentation
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge

namespace InfoGeometry.CliffordExteriorLiftDraft

open InfoGeometry.Clifford.BivectorVectorRepresentation
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open ExteriorAlgebra

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem cliffordExteriorLiftDraft_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- In any non-commutative ring `[Ring B]`, if `x * x = 0`, `y * y = 0`, and `x * y + y * x = 0`,
then `(x + y) * (x + y) = 0`. -/
theorem ring_sq_zero_add_of_anticomm
    {B : Type*} [Ring B] {x y : B}
    (hx : x * x = 0) (hy : y * y = 0) (hxy : x * y + y * x = 0) :
    (x + y) * (x + y) = 0 := by
  calc
    (x + y) * (x + y) = x * x + (x * y + y * x) + y * y := by noncomm_ring
    _ = 0 + 0 + 0 := by rw [hx, hxy, hy]
    _ = 0 := by abel

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Canonical universal lift evaluation on a generator `ι R v`. -/
theorem exteriorAlgebra_lift_ι_apply
    {A : Type*} [Semiring A] [Algebra R A]
    (f : V →ₗ[R] A) (hf : ∀ v, f v * f v = 0) (v : V) :
    ExteriorAlgebra.lift R ⟨f, hf⟩ (ι R v) = f v := by
  simp

end InfoGeometry.CliffordExteriorLiftDraft
