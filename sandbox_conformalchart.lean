import Mathlib.Tactic
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Clifford.CartanInstance

namespace InfoGeometry.Causal

open scoped BigOperators
open InfoGeometry.Singular

variable {n : ℕ}

abbrev Mat := InfoGeometry.Clifford.TowerMatrix.Mat n

/-- Core projectors based on a Moore-Penrose relationship. -/
noncomputable def Pleft  {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) : Mat := A * Aplus
noncomputable def Pright {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) : Mat := Aplus * A
noncomputable def Qleft  {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) : Mat := 1 - Pleft h
noncomputable def Qright {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) : Mat := 1 - Pright h

-- Idempotence of the Moore–Penrose projectors (uses only Penrose 1 and 2).
theorem Pleft_idempotent {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) :
    Pleft h * Pleft h = Pleft h := by
  have h1 : A * Aplus * A = A := h.penrose1
  calc
    Pleft h * Pleft h
        = (A * Aplus) * (A * Aplus) := by simp [Pleft]
    _   = (A * Aplus * A) * Aplus := by simp [mul_assoc]
    _   = A * Aplus := by simpa [h1, mul_assoc]
    _   = Pleft h := by simp [Pleft]

theorem Pright_idempotent {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) :
    Pright h * Pright h = Pright h := by
  have h2 : Aplus * A * Aplus = Aplus := h.penrose2
  calc
    Pright h * Pright h
        = (Aplus * A) * (Aplus * A) := by simp [Pright]
    _   = (Aplus * A * Aplus) * A := by simp [mul_assoc]
    _   = Aplus * A := by simpa [h2, mul_assoc]
    _   = Pright h := by simp [Pright]

-- Complementarity on each side (the “mirror boundary” algebra: P*(I−P)=0).
theorem Pleft_mul_Qleft {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) :
    Pleft h * Qleft h = 0 := by
  simp [Qleft, sub_eq_add_neg, mul_add, add_mul, Pleft_idempotent h, Pleft]

theorem Qleft_mul_Pleft {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) :
    Qleft h * Pleft h = 0 := by
  simp [Qleft, sub_eq_add_neg, mul_add, add_mul, Pleft_idempotent h, Pleft]

theorem Pright_mul_Qright {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) :
    Pright h * Qright h = 0 := by
  simp [Qright, sub_eq_add_neg, mul_add, add_mul, Pright_idempotent h, Pright]

theorem Qright_mul_Pright {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) :
    Qright h * Pright h = 0 := by
  simp [Qright, sub_eq_add_neg, mul_add, add_mul, Pright_idempotent h, Pright]

theorem Pleft_add_Qleft {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) :
    Pleft h + Qleft h = 1 := by
  simp [Qleft]

theorem Pright_add_Qright {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) :
    Pright h + Qright h = 1 := by
  simp [Qright]

-- The definitive “Double Conformal Chart” decomposition: four chart blocks.
theorem ConformalChart {⋆ : AdjointLike Mat} {A Aplus : Mat} (h : IsMoorePenrose ⋆ A Aplus) (X : Mat) :
    X
      = (Pleft h)  * X * (Pright h)
      + (Pleft h)  * X * (Qright h)
      + (Qleft h)  * X * (Pright h)
      + (Qleft h)  * X * (Qright h) := by
  calc
    X = (1 : Mat) * X * (1 : Mat) := by simp
    _ = (Pleft h + Qleft h) * X * (Pright h + Qright h) := by
          simp [Pleft_add_Qleft h, Pright_add_Qright h]
    _ = ((Pleft h) * X + (Qleft h) * X) * (Pright h + Qright h) := by
          simp [mul_add, add_mul, mul_assoc]
    _ = (Pleft h) * X * (Pright h)
      + (Pleft h) * X * (Qright h)
      + (Qleft h) * X * (Pright h)
      + (Qleft h) * X * (Qright h) := by
          simp [mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm]

end InfoGeometry.Causal
