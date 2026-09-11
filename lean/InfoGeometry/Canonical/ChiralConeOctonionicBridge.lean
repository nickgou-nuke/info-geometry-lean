import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

namespace InfoGeometry.Canonical

variable {R : Type*} [Field R] [CharZero R]

/-- **1. Светлинен Вейлов Проектор P₊(u) = (1/2)(1 + u)** за хиперболична единица u² = 1 -/
def lightconePlus (u : R) : R :=
  (1 / 2 : R) * (1 + u)

/-- **2. Светлинен Вейлов Проектор P₋(u) = (1/2)(1 - u)** за хиперболична единица u² = 1 -/
def lightconeMinus (u : R) : R :=
  (1 / 2 : R) * (1 - u)

/-- **Теорема 1**: Идемпотентност на Светлинния Проектор P₊(u)² = P₊(u) при u² = 1. -/
theorem lightconePlus_idempotent (u : R) (hu : u * u = 1) :
    lightconePlus u * lightconePlus u = lightconePlus u := by
  dsimp [lightconePlus]
  calc (1 / 2 : R) * (1 + u) * ((1 / 2 : R) * (1 + u))
      = (1 / 4 : R) * (1 + 2 * u + u * u) := by ring
    _ = (1 / 4 : R) * (1 + 2 * u + 1) := by rw [hu]
    _ = (1 / 2 : R) * (1 + u) := by ring

theorem lightconeMinus_idempotent (u : R) (hu : u * u = 1) :
    lightconeMinus u * lightconeMinus u = lightconeMinus u := by
  dsimp [lightconeMinus]
  calc
    (1 / 2 : R) * (1 - u) * ((1 / 2 : R) * (1 - u)) =
        (1 / 4 : R) * (1 - 2 * u + u * u) := by ring
    _ = (1 / 4 : R) * (1 - 2 * u + 1) := by rw [hu]
    _ = (1 / 2 : R) * (1 - u) := by ring

theorem lightcone_orthogonality (u : R) (hu : u * u = 1) :
    lightconePlus u * lightconeMinus u = 0 := by
  dsimp [lightconePlus, lightconeMinus]
  calc ((1 / 2 : R) * (1 + u)) * ((1 / 2 : R) * (1 - u))
      = (1 / 4 : R) * (1 - u * u) := by ring
    _ = (1 / 4 : R) * (1 - 1) := by rw [hu]
    _ = 0 := by ring

theorem lightcone_resolution (u : R) :
    lightconePlus u + lightconeMinus u = 1 := by
  dsimp [lightconePlus, lightconeMinus]
  ring

end InfoGeometry.Canonical
