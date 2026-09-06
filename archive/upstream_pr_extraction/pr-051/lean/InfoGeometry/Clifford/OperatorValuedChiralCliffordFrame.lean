import InfoGeometry.Clifford.OperatorValuedJones

/-!
# Operator-valued chiral Clifford frames

This owner reuses the existing `OperatorValuedJones` coordinates and its
strict Dirac-system predicate.  The parameter is an abstract state/orbit
index; no spacetime or differentiability claim is made here.
-/

namespace InfoGeometry.Clifford.OperatorValuedChiralCliffordFrame

open InfoGeometry.Clifford

variable {ι R Op : Type*} [Field R] [CharZero R] [Ring Op] [Algebra R Op]

structure Frame (ι R Op : Type*) [Field R] [CharZero R] [Ring Op] [Algebra R Op] where
  gamma : ι → Op
  metric : ι → ι → R

def anticommutator (F : Frame ι R Op) (i j : ι) : Op :=
  operatorAnticommutator (F.gamma i) (F.gamma j)

theorem anticommutator_eq_metric (F : Frame ι R Op)
    (hF : IsDiracMatrixSystem F.metric F.gamma) (i j : ι) :
    anticommutator F i j = algebraMap R Op (2 * F.metric i j) :=
  hF i j

def symmetricChannel (F : Frame ι R Op) (i j : ι) : Op :=
  ((2 : R)⁻¹) • anticommutator F i j

def bivectorChannel (F : Frame ι R Op) (i j : ι) : Op :=
  ((2 : R)⁻¹) • (F.gamma i * F.gamma j - F.gamma j * F.gamma i)

theorem symmetricChannel_eq_metric (F : Frame ι R Op)
    (hF : IsDiracMatrixSystem F.metric F.gamma) (i j : ι) :
    symmetricChannel F i j = algebraMap R Op (F.metric i j) := by
  rw [symmetricChannel, anticommutator_eq_metric F hF]
  rw [Algebra.smul_def, ← map_mul]
  simp

theorem bivectorChannel_swap (F : Frame ι R Op) (i j : ι) :
    bivectorChannel F j i = -bivectorChannel F i j := by
  dsimp [bivectorChannel]
  simp [sub_eq_add_neg]

end InfoGeometry.Clifford.OperatorValuedChiralCliffordFrame
