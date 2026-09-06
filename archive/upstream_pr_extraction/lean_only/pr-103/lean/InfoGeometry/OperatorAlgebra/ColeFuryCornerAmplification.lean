import InfoGeometry.OperatorAlgebra.ColeFuryEmbedding
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace InfoGeometry.OperatorAlgebra.ColeFury

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open Matrix

abbrev Corner2 := Matrix (Fin 2) (Fin 2) ℤ

def cornerReadout (X : SplitOct) : Corner2 :=
  !![X.a, X.x0; X.y0, X.b]

def cornerInclusion (A : Corner2) : SplitOct :=
  ⟨A 0 0, A 1 1, A 0 1, 0, 0, A 1 0, 0, 0⟩

theorem cornerReadout_inclusion (A : Corner2) :
    cornerReadout (cornerInclusion A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cornerInclusion_readout (X : SplitOct)
    (hX : isAssociativeSubalgebra X) :
    cornerInclusion (cornerReadout X) = X := by
  rcases hX with ⟨hx1, hx2, hy1, hy2⟩
  ext <;> simp [cornerInclusion, cornerReadout, hx1, hx2, hy1, hy2]

theorem cornerInclusion_mul (A B : Corner2) :
    mulZ (cornerInclusion A) (cornerInclusion B) =
      cornerInclusion (A * B) := by
  ext <;>
    simp [cornerInclusion, mulZ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

def amp16 (A : Corner2) : Matrix (Fin 2 × Fin 16) (Fin 2 × Fin 16) ℤ :=
  Matrix.kronecker A (1 : Matrix (Fin 16) (Fin 16) ℤ)

noncomputable def pairToFin32 : Fin 2 × Fin 16 ≃ Fin 32 :=
  (Fintype.equivFin (Fin 2 × Fin 16)).trans (finCongr (by decide))

noncomputable def amp16Fin32 (A : Corner2) : Spin32Matrix :=
  Matrix.reindexAlgEquiv ℤ ℤ pairToFin32 (amp16 A)

theorem amp16_mul (A B : Corner2) :
    amp16 (A * B) = amp16 A * amp16 B := by
  simpa [amp16, Matrix.kronecker] using
    (Matrix.mul_kronecker_mul A B
      (1 : Matrix (Fin 16) (Fin 16) ℤ)
      (1 : Matrix (Fin 16) (Fin 16) ℤ))

theorem amp16Fin32_mul (A B : Corner2) :
    amp16Fin32 (A * B) = amp16Fin32 A * amp16Fin32 B := by
  unfold amp16Fin32
  rw [amp16_mul]
  exact (Matrix.reindexAlgEquiv ℤ ℤ pairToFin32).map_mul _ _

theorem corner_amp16_mul (X Y : SplitOct)
    (hX : isAssociativeSubalgebra X) (hY : isAssociativeSubalgebra Y) :
    amp16 (cornerReadout (mulZ X Y)) =
      amp16 (cornerReadout X) * amp16 (cornerReadout Y) := by
  have hmul : cornerReadout (mulZ X Y) = cornerReadout X * cornerReadout Y := by
    calc
      cornerReadout (mulZ X Y) =
          cornerReadout
            (mulZ (cornerInclusion (cornerReadout X))
              (cornerInclusion (cornerReadout Y))) := by
        rw [cornerInclusion_readout X hX, cornerInclusion_readout Y hY]
      _ = cornerReadout
          (cornerInclusion (cornerReadout X * cornerReadout Y)) := by
        rw [cornerInclusion_mul]
      _ = cornerReadout X * cornerReadout Y :=
        cornerReadout_inclusion _
  rw [hmul]
  exact amp16_mul _ _

end InfoGeometry.OperatorAlgebra.ColeFury
