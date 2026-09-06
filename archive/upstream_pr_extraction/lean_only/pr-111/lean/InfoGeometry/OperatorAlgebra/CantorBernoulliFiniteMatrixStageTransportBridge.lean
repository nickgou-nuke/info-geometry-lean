import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Index transport for the finite Bernoulli matrix stages

`BitWord n` and `Fin (2^n)` are canonically equivalent finite index types.
This owner transports the corresponding matrix stages by the native
`Matrix.reindexAlgEquiv`; it does not identify the two dyadic transition maps.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge

open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzMatrixTraceTower

def bitWordIndexEquiv (n : ℕ) : BitWord n ≃ Fin (2 ^ n) :=
  (Fintype.equivFin (BitWord n)).trans
    (finCongr (by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]))

def bitWordStageStarAlgEquiv (n : ℕ) :
    BitWordMatrixStage n ≃⋆ₐ[ℂ] MatrixStage n :=
  StarAlgEquiv.ofAlgEquiv
    (Matrix.reindexAlgEquiv ℂ ℂ (bitWordIndexEquiv n))
    (fun A => by
      ext i j
      simp [Matrix.reindexAlgEquiv, Matrix.star_apply])

@[simp] theorem bitWordStageStarAlgEquiv_apply (n : ℕ)
    (A : BitWordMatrixStage n) :
    bitWordStageStarAlgEquiv n A =
      Matrix.reindexAlgEquiv ℂ ℂ (bitWordIndexEquiv n) A := rfl

@[simp] theorem bitWordStageStarAlgEquiv_map_one (n : ℕ) :
    bitWordStageStarAlgEquiv n (1 : BitWordMatrixStage n) = 1 := by
  exact (bitWordStageStarAlgEquiv n).map_one

@[simp] theorem bitWordStageStarAlgEquiv_map_mul (n : ℕ)
    (A B : BitWordMatrixStage n) :
    bitWordStageStarAlgEquiv n (A * B) =
      bitWordStageStarAlgEquiv n A * bitWordStageStarAlgEquiv n B := by
  exact (bitWordStageStarAlgEquiv n).map_mul A B

@[simp] theorem bitWordStageStarAlgEquiv_map_star (n : ℕ)
    (A : BitWordMatrixStage n) :
    bitWordStageStarAlgEquiv n (star A) =
      star (bitWordStageStarAlgEquiv n A) := by
  exact map_star (bitWordStageStarAlgEquiv n) A

theorem bitWordStageTrace_transport (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordMatrixTraceFunctional n A =
      matrixTraceFunctional n (bitWordStageStarAlgEquiv n A) := by
  rw [bitWordMatrixTraceFunctional_apply, matrixTraceFunctional_apply]
  rw [bitWordStageStarAlgEquiv_apply]
  rw [trace_reindex]
  have hcard : Fintype.card (BitWord n) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [hcard]
  push_cast
  ring

/-! The gauge readout is transported to the native normalized matrix trace.
This is a scalar fixed-depth compatibility theorem; it does not construct a
state on an infinite completion. -/

theorem bitWordMatrixGaugeReadout_transport (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordMatrixGaugeReadout n A =
      matrixTraceState n (bitWordStageStarAlgEquiv n A) := by
  rw [bitWordMatrixGaugeReadout_eq_trace, bitWordStageTrace_transport]
  rfl

end InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
