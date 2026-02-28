import Mathlib.Tactic
import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Clifford.TowerMatrix

namespace InfoGeometry.Singular

open scoped Matrix
open Matrix

variable {n : ℕ}

/-- An "adjoint-like" involution for matrices, used in place of conjugate-transpose. -/
structure AdjointLike (M : Type*) [Ring M] where
  adj : M → M
  invol : ∀ A, adj (adj A) = A
  mul_rev : ∀ A B, adj (A * B) = adj B * adj A
  add : ∀ A B, adj (A + B) = adj A + adj B
  one : adj 1 = (1 : M)
  zero : adj 0 = (0 : M)
  neg : ∀ A, adj (-A) = - adj A

attribute [simp] AdjointLike.one AdjointLike.zero AdjointLike.neg

/-- The four Penrose equations relative to an adjoint-like operation `star`.
    (1) A A⁺ A = A
    (2) A⁺ A A⁺ = A⁺
    (3) (A A⁺)† = A A⁺
    (4) (A⁺ A)† = A⁺ A -/
structure IsMoorePenrose {M : Type*} [Ring M] (star : AdjointLike M) (A Aplus : M) : Prop where
  penrose1 : A * Aplus * A = A
  penrose2 : Aplus * A * Aplus = Aplus
  penrose3 : star.adj (A * Aplus) = (A * Aplus)
  penrose4 : star.adj (Aplus * A) = (Aplus * A)

namespace IsMoorePenrose

variable {star : AdjointLike (InfoGeometry.Clifford.TowerMatrix.Mat n)}
variable {A Aplus : InfoGeometry.Clifford.TowerMatrix.Mat n}

/-- Support projector is idempotent on the left: (AA⁺)² = AA⁺. -/
theorem Pleft_idempotent (h : IsMoorePenrose star A Aplus) :
    (A * Aplus) * (A * Aplus) = A * Aplus := by
  calc
    (A * Aplus) * (A * Aplus)
        = (A * Aplus * A) * Aplus := by simp [mul_assoc]
    _ = A * Aplus := by simp [h.penrose1, mul_assoc]

/-- Support projector is idempotent on the right: (A⁺A)² = A⁺A. -/
theorem Pright_idempotent (h : IsMoorePenrose star A Aplus) :
    (Aplus * A) * (Aplus * A) = Aplus * A := by
  calc
    (Aplus * A) * (Aplus * A)
        = (Aplus * A * Aplus) * A := by simp [mul_assoc]
    _ = Aplus * A := by simp [h.penrose2, mul_assoc]

/-- The projectors are †-selfadjoint. -/
theorem Pleft_selfadjoint (h : IsMoorePenrose star A Aplus) :
    star.adj (A * Aplus) = A * Aplus := h.penrose3

theorem Pright_selfadjoint (h : IsMoorePenrose star A Aplus) :
    star.adj (Aplus * A) = Aplus * A := h.penrose4

/-- Orthogonality with the complement: P(1−P)=0. -/
theorem Pleft_mul_Qleft (h : IsMoorePenrose star A Aplus) :
    (A * Aplus) * ((1 : InfoGeometry.Clifford.TowerMatrix.Mat n) - (A * Aplus)) = 0 := by
  simp [mul_sub, mul_one, Pleft_idempotent (h := h), sub_self]

theorem Qleft_mul_Pleft (h : IsMoorePenrose star A Aplus) :
    ((1 : InfoGeometry.Clifford.TowerMatrix.Mat n) - (A * Aplus)) * (A * Aplus) = 0 := by
  simp [sub_mul, one_mul, Pleft_idempotent (h := h), sub_self]

theorem Pright_mul_Qright (h : IsMoorePenrose star A Aplus) :
    (Aplus * A) * ((1 : InfoGeometry.Clifford.TowerMatrix.Mat n) - (Aplus * A)) = 0 := by
  simp [mul_sub, mul_one, Pright_idempotent (h := h), sub_self]

theorem Qright_mul_Pright (h : IsMoorePenrose star A Aplus) :
    ((1 : InfoGeometry.Clifford.TowerMatrix.Mat n) - (Aplus * A)) * (Aplus * A) = 0 := by
  simp [sub_mul, one_mul, Pright_idempotent (h := h), sub_self]

/-- The “double conformal chart” decomposition: four blocks from left/right support splits. -/
theorem conformalChart (h : IsMoorePenrose star A Aplus)
    (X : InfoGeometry.Clifford.TowerMatrix.Mat n) :
    X
      = (A * Aplus) * X * (Aplus * A)
      + (A * Aplus) * X * ((1 : InfoGeometry.Clifford.TowerMatrix.Mat n) - (Aplus * A))
      + ((1 : InfoGeometry.Clifford.TowerMatrix.Mat n) - (A * Aplus)) * X * (Aplus * A)
      + ((1 : InfoGeometry.Clifford.TowerMatrix.Mat n) - (A * Aplus)) * X * ((1 : InfoGeometry.Clifford.TowerMatrix.Mat n) - (Aplus * A)) := by
  let P : InfoGeometry.Clifford.TowerMatrix.Mat n := A * Aplus
  let Q : InfoGeometry.Clifford.TowerMatrix.Mat n := (1 : _) - P
  let R : InfoGeometry.Clifford.TowerMatrix.Mat n := Aplus * A
  let S : InfoGeometry.Clifford.TowerMatrix.Mat n := (1 : _) - R

  have hPQ : P + Q = (1 : InfoGeometry.Clifford.TowerMatrix.Mat n) := by
    simp [Q]
  have hRS : R + S = (1 : InfoGeometry.Clifford.TowerMatrix.Mat n) := by
    simp [S]

  calc
    X = (1 : InfoGeometry.Clifford.TowerMatrix.Mat n) * X * (1 : InfoGeometry.Clifford.TowerMatrix.Mat n) := by simp
    _ = (P + Q) * X * (R + S) := by simpa [hPQ, hRS]
    _ = (P * X + Q * X) * (R + S) := by simp [add_mul, mul_assoc]
    _ = (P * X) * (R + S) + (Q * X) * (R + S) := by simp [add_mul]
    _ = (P * X * R + P * X * S) + (Q * X * R + Q * X * S) := by
          simp [mul_add, add_mul, mul_assoc]
    _ = P * X * R + P * X * S + Q * X * R + Q * X * S := by
          abel
    _ = _ := by
          simp [P, Q, R, S, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc]

end IsMoorePenrose

end InfoGeometry.Singular
