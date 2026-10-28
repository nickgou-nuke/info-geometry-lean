/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CliffordDirac.MatrixModel
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Noncommuting symmetries in a joint matrix centralizer

Three full matrix factors separate the Clifford generators, the noncommuting
coefficient operators, and the noncommuting symmetries. The ambient algebra is
the full complex matrix algebra indexed by `Fin 2 × (Fin 2 × Fin 2)`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CliffordDirac

abbrev ThreeFactorMatrix := SpinMatrix (Fin 2 × Fin 2)

theorem coefficientLift_commute {n : Type*} [Fintype n]
    {A B : Matrix n n ℂ} (h : Commute A B) :
    Commute (coefficientLift A) (coefficientLift B) := by
  change coefficientLift A * coefficientLift B = coefficientLift B * coefficientLift A
  rw [← coefficientLift_mul, ← coefficientLift_mul, h.eq]

/-- An arbitrary matrix acting on the third factor. -/
def spectator (S : Matrix (Fin 2) (Fin 2) ℂ) : ThreeFactorMatrix :=
  coefficientLift (coefficientLift S)

/-- The spin generators act on the first factor, and the coefficients on the second. -/
def threeFactorGenerators (A B : Matrix (Fin 2) (Fin 2) ℂ) : Set ThreeFactorMatrix :=
  {spinX, spinY, coefficientLift (spinLift (n := Fin 2) A),
    coefficientLift (spinLift (n := Fin 2) B)}

theorem spectator_mem_centralizer (A B S : Matrix (Fin 2) (Fin 2) ℂ) :
    spectator S ∈ Subalgebra.centralizer ℂ (threeFactorGenerators A B) := by
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  simp only [threeFactorGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact (spinX_commute (coefficientLift S)).eq
  · exact (spinY_commute (coefficientLift S)).eq
  · exact (coefficientLift_commute (spinLift_commute A S)).eq
  · exact (coefficientLift_commute (spinLift_commute B S)).eq

theorem spectator_isHermitian {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S.IsHermitian) : (spectator S).IsHermitian :=
  coefficientLift_isHermitian (coefficientLift_isHermitian hS)

theorem spectator_lie_ne_zero_iff (S T : Matrix (Fin 2) (Fin 2) ℂ) :
    ⁅spectator S, spectator T⁆ ≠ 0 ↔ ⁅S, T⁆ ≠ 0 := by
  exact (coefficientLift_lie_ne_zero_iff (coefficientLift S) (coefficientLift T)).trans
    (coefficientLift_lie_ne_zero_iff S T)

theorem spectator_witness_lie_ne_zero : ⁅spectator witnessA, spectator witnessB⁆ ≠ 0 :=
  (spectator_lie_ne_zero_iff _ _).2 witness_lie_ne_zero

/-- The native joint centralizer contains two noncommuting Hermitian matrices. -/
theorem joint_centralizer_has_noncommuting_hermitian_members :
    ∃ C ∈ Subalgebra.centralizer ℂ (threeFactorGenerators witnessA witnessB),
      ∃ D ∈ Subalgebra.centralizer ℂ (threeFactorGenerators witnessA witnessB),
        C.IsHermitian ∧ D.IsHermitian ∧ ⁅C, D⁆ ≠ 0 := by
  exact ⟨spectator witnessA, spectator_mem_centralizer _ _ _,
    spectator witnessB, spectator_mem_centralizer _ _ _,
    spectator_isHermitian witnessA_isHermitian,
    spectator_isHermitian witnessB_isHermitian, spectator_witness_lie_ne_zero⟩

theorem spinLift_finTwo_injective : Function.Injective (spinLift (n := Fin 2)) := by
  intro A B h
  ext i j
  have hij := congrArg (fun M : SpinMatrix (Fin 2) => M (i, 0) (j, 0)) h
  simpa [spinLift, Matrix.kroneckerMap_apply, Matrix.one_apply] using hij

theorem spinLift_lie {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ⁅spinLift (n := n) A, spinLift B⁆ = spinLift ⁅A, B⁆ := by
  simp only [Ring.lie_def, ← spinLift_mul]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [spinLift, Matrix.kroneckerMap_apply, sub_mul]

theorem spinLift_finTwo_lie_ne_zero_iff (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ⁅spinLift (n := Fin 2) A, spinLift B⁆ ≠ 0 ↔ ⁅A, B⁆ ≠ 0 := by
  rw [spinLift_lie]
  constructor
  · intro h hz
    exact h (by rw [hz, spinLift_zero])
  · intro h hz
    apply h
    apply spinLift_finTwo_injective
    simpa only [spinLift_zero] using hz

/-- The same eight-dimensional model retains a nonzero coefficient-curvature term. -/
theorem threeFactor_curvature_ne_zero :
    matrixCurvature (spinLift (n := Fin 2) witnessA) (spinLift witnessB) ≠ 0 :=
  (matrixCurvature_ne_zero_iff _ _).2
    ((spinLift_finTwo_lie_ne_zero_iff _ _).2 witness_lie_ne_zero)

end InfoGeometry.OperatorAlgebra.CliffordDirac
