import InfoGeometry.Arithmetic.IndexTheorem
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Analysis.RotorCocycleBregmanBridge
import InfoGeometry.Geometry.SpectralDivisors
import DAG.ChiralDiracAnticommutation
import DAG.AffineProjectiveClosure

namespace InfoGeometry.Arithmetic.TopologicalIndexTheorem

open InfoGeometry.Arithmetic
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Geometry.SpectralDivisors
open InfoGeometry.Analysis.RotorCocycleBregmanBridge

/-- The arithmetic vacuum has trivial Liouville grading. -/
@[simp] theorem liouville_one :
    BostConnesSystem.liouville 1 = 1 :=
  IndexTheorem.liouville_one

/-- Multiplication by a prime flips the Liouville sign. -/
theorem liouville_prime_mul (p n : ℕ+) (hp : Nat.Prime p.val) :
    BostConnesSystem.liouville (p * n) = -BostConnesSystem.liouville n :=
  IndexTheorem.liouville_prime_mul p n hp

/-- The finite Dirac operator anticommutes with the finite chiral grading. -/
theorem dirac_anticommutes_gamma {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℝ)
    (B2 : Matrix (Fin n1) (Fin n2) ℝ) :
    DAG.ChiralDiracAnticommutation.chiralGamma *
        DAG.ChiralDiracAnticommutation.diracOp B1 B2 +
      DAG.ChiralDiracAnticommutation.diracOp B1 B2 *
        DAG.ChiralDiracAnticommutation.chiralGamma = 0 :=
  DAG.ChiralDiracAnticommutation.dirac_anticommutes_gamma B1 B2

/-- The rotor/Bregman packet has zero remainder at time `0`. -/
@[simp] theorem exponentialRemainder_zero {n : ℕ}
    (K : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n) :
    InfoGeometry.Analysis.BregmanAnalyticBound.exponentialRemainder K 0 = 0 :=
  InfoGeometry.Analysis.RotorCocycleBregmanBridge.exponentialRemainder_zero K

theorem finite_index_inputs {n0 n1 n2 n : ℕ}
    (p q : ℕ+) (hp : Nat.Prime p.val)
    (B1 : Matrix (Fin n0) (Fin n1) ℝ)
    (B2 : Matrix (Fin n1) (Fin n2) ℝ)
    (K : InfoGeometry.Analysis.BregmanAnalyticBound.MatrixEnd n) :
    BostConnesSystem.liouville 1 = 1 ∧
      BostConnesSystem.liouville (p * q) = -BostConnesSystem.liouville q ∧
      (DAG.ChiralDiracAnticommutation.chiralGamma *
          DAG.ChiralDiracAnticommutation.diracOp B1 B2 +
        DAG.ChiralDiracAnticommutation.diracOp B1 B2 *
          DAG.ChiralDiracAnticommutation.chiralGamma = 0) ∧
      (InfoGeometry.Analysis.BregmanAnalyticBound.exponentialRemainder K 0 = 0) := by
  constructor
  · exact liouville_one
  constructor
  · exact liouville_prime_mul p q hp
  constructor
  · exact dirac_anticommutes_gamma B1 B2
  · exact exponentialRemainder_zero K

theorem topological_index_eq_spectral_flow
    {Region Point Tangent Value Cycle : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    {W : WindingNumberDatum I N ω}
    (T : TopologicalIndexDatum I N ω W Cycle)
    (c : Cycle) :
    T.index c = T.spectralFlow c := by
  exact T.index_eq_spectralFlow c

end InfoGeometry.Arithmetic.TopologicalIndexTheorem
