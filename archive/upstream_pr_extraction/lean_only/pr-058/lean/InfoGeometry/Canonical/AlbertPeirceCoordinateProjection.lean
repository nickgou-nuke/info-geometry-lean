import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Canonical.AlbertAlgebraGenerationsBridge

namespace InfoGeometry.Canonical

variable {R V : Type*} [Field R] [CharZero R] [AddCommGroup V] [Module R V]

/-- **1. Diagonal Part на Алберт Матрица**:
    Извлича 3-те класически скаларни масови диагонала (c₁, c₂, c₃). -/
def diagonalPart (X : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨X.diag1, X.diag2, X.diag3, 0, 0, 0⟩

/-- **2. Off-Diagonal Part на Алберт Матрица**:
    Извлича 3-те октонионни оф-диагонала (Трите поколения фермиони). -/
def offDiagonalPart (X : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨0, 0, 0, X.gen1, X.gen2, X.gen3⟩

/-- **Теорема 1**: Реконструиране на Алберт Матрица от Диагонална и Оф-Диагонална част. -/
theorem diagonal_offDiagonal_reconstruction (X : AlbertMatrix R V) :
    albertAdd (diagonalPart X) (offDiagonalPart X) = X := by
  dsimp [diagonalPart, offDiagonalPart, albertAdd]
  ext
  · ring
  · ring
  · ring
  · abel
  · abel
  · abel

/-- **Теорема 2**: Ортогоналност на Диагоналната и Оф-Диагоналната част (координатно). -/
theorem diagonal_offDiagonal_orthogonality (X : AlbertMatrix R V) :
    (diagonalPart X).gen1 = 0 ∧ (offDiagonalPart X).diag1 = 0 := ⟨rfl, rfl⟩

/-- **Master Synthesis**: Coordinate split & Peirce Frame Unification. -/
theorem master_peirce_coordinate_synthesis (X : AlbertMatrix R V) :
    (albertAdd (diagonalPart X) (offDiagonalPart X) = X) ∧
    (jordanMul (peirceIdempotent1 (R:=R) (V:=V)) (peirceIdempotent1 (R:=R) (V:=V)) = peirceIdempotent1) := ⟨
  diagonal_offDiagonal_reconstruction X,
  peirce1_idempotent
⟩

end InfoGeometry.Canonical
