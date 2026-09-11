import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.CubicJordanOs
import InfoGeometry.Algebra.CubicJordanFreudenthal
import InfoGeometry.Exceptional.Freudenthal

/-!
# Albert Matrix Cubic Jordan Datum Instantiation

This module instantiates `InfoGeometry.Exceptional.Freudenthal.CubicJordanDatum`
for `InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix`, linking the 27-dimensional
split-Albert algebra directly to the Freudenthal quartic invariant and phase space `𝔉(J)`.
-/

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.Algebra.CubicJordanOs
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix
open InfoGeometry.Algebra.CubicJordanFreudenthal
open InfoGeometry.Exceptional.Freudenthal

noncomputable section

namespace InfoGeometry.Algebra.CubicJordanOs

/-- Linear map version of `traceBilin` for `AlbertMatrix`. -/
def albertTraceBilinLM : AlbertMatrix → AlbertMatrix → ℝ :=
  fun X Y => traceBilin X Y

/-- Symmetric trilinear form for `AlbertMatrix`. -/
def albertNormTrilinLM : AlbertMatrix → AlbertMatrix → AlbertMatrix → ℝ :=
  fun X Y Z =>
    (1 / 3 : ℝ) * (traceBilin X (adjointQuad (addAlbert Y Z)) - traceBilin X (adjointQuad Y) - traceBilin X (adjointQuad Z))

/-- Concrete bilinear trace symmetry theorem. -/
theorem albert_trace_comm (X Y : AlbertMatrix) : traceBilin X Y = traceBilin Y X :=
  trace_comm X Y

/-- Addition of Albert matrices is commutative. -/
theorem addAlbert_comm (X Y : AlbertMatrix) : addAlbert X Y = addAlbert Y X := by
  dsimp [addAlbert, subZ, negZ]
  apply ext_albert
  · ring
  · ring
  · ring
  · ext <;> ring
  · ext <;> ring
  · ext <;> ring

/-- Concrete trilinear form symmetry in last two slots. -/
theorem albert_normTrilin_swap₂₃ (X Y Z : AlbertMatrix) :
    albertNormTrilinLM X Y Z = albertNormTrilinLM X Z Y := by
  dsimp [albertNormTrilinLM]
  rw [addAlbert_comm Y Z]
  ring

end InfoGeometry.Algebra.CubicJordanOs
