import InfoGeometry.Canonical.TwoSheetThreeColorWeyl

/-!
# Finite two-sheet Krein adjoint

The sheet flip is used as the fundamental Krein metric.  This owner records
only the finite matrix adjoint identities; modular/Tomita structure is separate.
-/

noncomputable section
namespace TwoSheetKreinAdjoint

open TwoSheetThreeColorWeyl

/-- The two-sheet Krein metric, acting trivially on colour. -/
def kreinMetric : M6C := tensor sheetFlip (1 : M3C)

@[simp] theorem kreinMetric_sq :
    kreinMetric * kreinMetric = (1 : M6C) := by
  simp only [kreinMetric, tensor_mul]
  rw [sheet_parity.2.1]
  simp [tensor_one]

/-- Finite Krein adjoint `A× = J A† J`. -/
def kreinAdjoint (A : M6C) : M6C :=
  kreinMetric * Matrix.conjTranspose A * kreinMetric

@[simp] theorem kreinAdjoint_zero : kreinAdjoint (0 : M6C) = 0 := by
  simp [kreinAdjoint]

@[simp] theorem kreinAdjoint_add (A B : M6C) :
    kreinAdjoint (A + B) = kreinAdjoint A + kreinAdjoint B := by
  simp [kreinAdjoint, Matrix.conjTranspose_add, Matrix.mul_add, add_mul]

theorem kreinMetric_conjTranspose :
    Matrix.conjTranspose kreinMetric = kreinMetric := by
  ext ⟨s, a⟩ ⟨t, b⟩
  fin_cases s <;> fin_cases a <;> fin_cases t <;> fin_cases b <;>
    simp [kreinMetric, tensor, sheetFlip, Matrix.kroneckerMap_apply]

@[simp] theorem kreinAdjoint_involutive (A : M6C) :
    kreinAdjoint (kreinAdjoint A) = A := by
  unfold kreinAdjoint
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    kreinMetric_conjTranspose]
  simp only [Matrix.conjTranspose_conjTranspose]
  calc
    kreinMetric * (kreinMetric * (A * kreinMetric)) * kreinMetric =
        (kreinMetric * kreinMetric) * A *
          (kreinMetric * kreinMetric) := by noncomm_ring
    _ = A := by simp [kreinMetric_sq]

end TwoSheetKreinAdjoint
end noncomputable section
