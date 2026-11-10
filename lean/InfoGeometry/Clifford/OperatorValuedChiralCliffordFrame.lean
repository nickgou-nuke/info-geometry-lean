/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.OperatorValuedJones
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Operator-valued chiral Clifford frames

This owner reuses the existing `OperatorValuedJones` coordinates and its
strict Dirac-system predicate.  The parameter is an abstract state/orbit
index; no spacetime or differentiability claim is made here.
-/

namespace InfoGeometry.Clifford.OperatorValuedChiralCliffordFrame

open InfoGeometry.Clifford

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem chiralCliffordFrame_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

section Ring

variable {ι R Op : Type*} [Ring R] [Ring Op]

structure Frame (ι R Op : Type*) [Ring R] [Ring Op] where
  gamma : ι → Op
  metric : ι → ι → R

def anticommutator (F : Frame ι R Op) (i j : ι) : Op :=
  operatorAnticommutator (F.gamma i) (F.gamma j)

theorem anticommutator_comm (F : Frame ι R Op) (i j : ι) :
    anticommutator F i j = anticommutator F j i := by
  dsimp [anticommutator, operatorAnticommutator]
  exact add_comm _ _

end Ring

section DivisionRing

variable {ι R Op : Type*} [DivisionRing R] [Ring Op] [Module R Op]

def symmetricChannel (F : Frame ι R Op) (i j : ι) : Op :=
  ((2 : R)⁻¹) • anticommutator F i j

def bivectorChannel (F : Frame ι R Op) (i j : ι) : Op :=
  ((2 : R)⁻¹) • (F.gamma i * F.gamma j - F.gamma j * F.gamma i)

theorem bivectorChannel_swap (F : Frame ι R Op) (i j : ι) :
    bivectorChannel F j i = -bivectorChannel F i j := by
  dsimp [bivectorChannel]
  simp [sub_eq_add_neg]

end DivisionRing

theorem anticommutator_eq_metric
    {ι R Op : Type*} [CommRing R] [Ring Op] [Algebra R Op]
    (F : Frame ι R Op)
    (hF : IsDiracMatrixSystem F.metric F.gamma) (i j : ι) :
    anticommutator F i j = algebraMap R Op (2 * F.metric i j) :=
  hF i j

variable {ι R Op : Type*} [Field R] [CharZero R] [Ring Op] [Algebra R Op]

theorem symmetricChannel_eq_metric (F : Frame ι R Op)
    (hF : IsDiracMatrixSystem F.metric F.gamma) (i j : ι) :
    symmetricChannel F i j = algebraMap R Op (F.metric i j) := by
  rw [symmetricChannel, anticommutator_eq_metric F hF]
  rw [Algebra.smul_def, ← map_mul]
  simp

end InfoGeometry.Clifford.OperatorValuedChiralCliffordFrame
