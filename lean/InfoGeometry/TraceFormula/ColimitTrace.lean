import InfoGeometry.Algebra.PrimonColimitAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The real linear colimit trace

This module exposes the normalized trace descent from the BitWord matrix
tower.  The stage maps remain RingHoms; the descended observable is a genuine
real linear map.  The construction and its scalar compatibility proofs live
in the algebra owner and are re-exported here as the trace-formula interface.
-/

noncomputable section

namespace InfoGeometry.TraceFormula.ColimitTrace

open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

abbrev normalizedTraceLin (n : ℕ) : MatrixStage n →ₗ[ℝ] ℝ :=
  normalizedTraceLinear n

theorem normalizedTraceLin_compatible (m n : ℕ) (h : m ≤ n) (M : MatrixStage m) :
    normalizedTraceLin n (bondMap matrixBond m n h M) =
      normalizedTraceLin m M :=
  normalizedTrace_compatible_bondMap m n h M

abbrev colimitTrace : PrimonUHFAlgebra →ₗ[ℝ] ℝ :=
  InfoGeometry.Algebra.PrimonColimitAlgebra.colimitTrace

abbrev tauInfinity : PrimonUHFAlgebra →ₗ[ℝ] ℝ :=
  InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity

@[simp] theorem colimitTrace_evaluate_ringhom (n : ℕ) (M : MatrixStage n) :
    colimitTrace (toColimit n M) = normalizedTrace n M :=
  InfoGeometry.Algebra.PrimonColimitAlgebra.colimitTrace_stage n M

theorem colimitTrace_one :
    colimitTrace (1 : PrimonUHFAlgebra) = 1 :=
  InfoGeometry.Algebra.PrimonColimitAlgebra.colimitTrace_one

@[simp] theorem tauInfinity_evaluate_ringhom (n : ℕ) (M : MatrixStage n) :
    tauInfinity (toColimit n M) = normalizedTrace n M :=
  InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity_stage n M

theorem tauInfinity_one :
    tauInfinity (1 : PrimonUHFAlgebra) = 1 :=
  InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity_one

end InfoGeometry.TraceFormula.ColimitTrace
