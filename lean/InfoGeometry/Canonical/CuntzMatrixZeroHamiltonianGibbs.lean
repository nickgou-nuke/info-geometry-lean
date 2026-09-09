import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional

/-!
# Zero-Hamiltonian Gibbs readout on the concrete matrix tower

The finite functional-calculus Gibbs construction specializes at zero
Hamiltonian to the already existing normalized matrix trace.  Consequently
the concrete Kronecker successor preserves this specialization.  This is the
proved bridge available without asserting a nonexistent compatible arbitrary
Hamiltonian tower.
-/

noncomputable section

open scoped MatrixOrder ComplexOrder Kronecker
open Matrix

namespace InfoGeometry.Canonical.CuntzMatrixZeroHamiltonianGibbs

open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit

theorem zero_gibbs_eq_matrixTraceFunctional (n : ℕ) :
    gibbsFunctional (0 : MatrixStage n) (by simp) 0 =
      matrixTraceFunctional n := by
  ext X
  rw [gibbsFunctional_apply]
  have hzero : gibbsDensity (0 : MatrixStage n) (by simp) 0 = 1 := by
    rw [gibbsDensity, ← (show (0 : MatrixStage n).IsHermitian by simp).cfc_eq]
    rw [show expWeight 0 = (fun _ : ℝ => (1 : ℝ)) by
      funext r
      simp [expWeight]]
    exact cfc_const_one ℝ 0
  rw [hzero]
  simp [matrixTraceFunctional_apply]

theorem zero_gibbs_stage_compatibility (n : ℕ) (A : MatrixStage n) :
    gibbsFunctional (0 : MatrixStage (n + 1)) (by simp) 0
        (concreteStep n A) =
      gibbsFunctional (0 : MatrixStage n) (by simp) 0 A := by
  rw [show gibbsFunctional (0 : MatrixStage (n + 1)) (by simp) 0 =
      matrixTraceFunctional (n + 1) by
        exact zero_gibbs_eq_matrixTraceFunctional (n + 1)]
  rw [show gibbsFunctional (0 : MatrixStage n) (by simp) 0 =
      matrixTraceFunctional n by
        exact zero_gibbs_eq_matrixTraceFunctional n]
  exact concreteData.trace_compatible n A

theorem traceFunctional_stage_eq_zero_gibbs (n : ℕ) (A : MatrixStage n) :
    traceFunctional (stageInjection n A) =
      gibbsFunctional (0 : MatrixStage n) (by simp) 0 A := by
  rw [traceFunctional_stage, zero_gibbs_eq_matrixTraceFunctional]
  rfl


end InfoGeometry.Canonical.CuntzMatrixZeroHamiltonianGibbs
