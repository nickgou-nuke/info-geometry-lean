/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixPeirceOperatorGeometryD62
import InfoGeometry.OperatorAlgebra.OperatorExtensionExamples

/-!
# D₆₃: Idempotency defect in a nondiagonal matrix operator algebra

The equation `x * x - x = 0` says that `x` is idempotent; it does not force
`x = 1`. This module records a nonzero, nondiagonal star projection from the
existing matrix geometry owner as a concrete counterexample to that stronger
claim. It makes no claim about minima of a physical potential.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ## The D₆₃ causal archetypes -/

inductive D63Stage where
  | defectCriterion
  | matrixProjection
  deriving DecidableEq, Repr

def D63Stage.rank : D63Stage → ℕ
  | .defectCriterion => 0
  | .matrixProjection => 1

def D63Stage.edge : D63Stage → D63Stage → Prop
  | .defectCriterion, .matrixProjection =>
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
          InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P = 0 ∧
        InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P ≠ 0 ∧
        InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P ≠ 1 ∧
        InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P 0 1 ≠ 0
  | _, _ => False

def D63Stage.causalLE : D63Stage → D63Stage → Prop
  | .defectCriterion, .defectCriterion => True
  | .defectCriterion, .matrixProjection => D63Stage.edge .defectCriterion .matrixProjection
  | .matrixProjection, .matrixProjection => True
  | _, _ => False

theorem D63Stage.causalLE_refl (a : D63Stage) : a.causalLE a := by
  cases a <;> simp [causalLE]

theorem D63Stage.causalLE_trans {a b c : D63Stage}
    (hab : a.causalLE b) (hbc : b.causalLE c) : a.causalLE c := by
  cases a <;> cases b <;> cases c <;> simp_all [causalLE]

theorem D63Stage.causalLE_antisymm {a b : D63Stage}
    (hab : a.causalLE b) (hba : b.causalLE a) : a = b := by
  by_cases hEq : a = b
  · exact hEq
  · cases a <;> cases b <;> simp_all [causalLE]

theorem D63Stage.edge_causal {a b : D63Stage} (h : a.edge b) : a.causalLE b := by
  cases a <;> cases b <;> simpa [edge, causalLE] using h

theorem D63Stage.edge_rank_strict {a b : D63Stage} (h : a.edge b) :
    a.rank < b.rank := by
  cases a <;> cases b <;> simp [edge, rank] at h ⊢

theorem D63Stage.reachable_rank_strict_of_ne {a b : D63Stage}
    (h : a.causalLE b) (hne : a ≠ b) : a.rank < b.rank := by
  cases a <;> cases b <;> simp_all [causalLE, rank]

/-! ## Nondiagonal idempotent counterexample -/

/-- The existing nondiagonal star projection has zero idempotency defect, yet
is neither zero nor the ambient identity and has a nonzero off-diagonal entry.
Thus defect-zero operators in a matrix algebra need not equal the identity. -/
theorem d63_nondiagonal_projection_defect_zero_nontrivial :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P = 0 ∧
    InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P ≠ 0 ∧
    InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P ≠ 1 ∧
    InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P 0 1 ≠ 0 := by
  have hP :
      InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P *
          InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P =
        InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P :=
    InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P_isStarProjection.isIdempotentElem.eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_eq_zero_iff).2 hP
  · intro h
    have h00 := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) h
    norm_num [InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P] at h00
  · intro h
    have h00 := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) h
    norm_num [InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P] at h00
  · norm_num [InfoGeometry.OperatorAlgebra.OperatorExtensionExamples.P]

theorem D63Stage.edge_defect_projection :
    D63Stage.edge .defectCriterion .matrixProjection :=
  d63_nondiagonal_projection_defect_zero_nontrivial

end InfoGeometry.OperatorAlgebra.PeirceSpine
