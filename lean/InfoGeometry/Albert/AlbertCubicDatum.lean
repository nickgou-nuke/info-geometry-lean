import InfoGeometry.Algebra.CubicJordanOs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CubicJordanOsDatum
import InfoGeometry.Algebra.CubicJordanFreudenthal
import InfoGeometry.Exceptional.Freudenthal
import Mathlib

open InfoGeometry.Algebra.CubicJordanOs
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Algebra.CubicJordanFreudenthal
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix

noncomputable section

/- The existing `AlbertMatrix` carrier uses an integer-valued split-octonion
   component, so it is not a real module.  Keep the concrete invariants at
   function level rather than introducing an unsupported `Module` instance. -/
def albertTraceBilin (X Y : AlbertMatrix) : ℝ := traceBilin X Y

noncomputable def albertNormCubic (X : AlbertMatrix) : ℝ := normCubic X

noncomputable def albertAdjointQuad (X : AlbertMatrix) : AlbertMatrix := adjointQuad X

noncomputable def albertNormTrilin (X Y Z : AlbertMatrix) : ℝ :=
  (1 / 3 : ℝ) *
    (traceBilin X (adjointQuad (addAlbert Y Z)) -
      traceBilin X (adjointQuad Y) - traceBilin X (adjointQuad Z))

theorem albert_trace_comm (x y : AlbertMatrix) :
    albertTraceBilin x y = albertTraceBilin y x := by
  exact trace_comm x y

theorem albert_normTrilin_swap₂₃ (x y z : AlbertMatrix) :
    albertNormTrilin x y z = albertNormTrilin x z y := by
  dsimp [albertNormTrilin]
  rw [addAlbert_comm y z]
  ring
