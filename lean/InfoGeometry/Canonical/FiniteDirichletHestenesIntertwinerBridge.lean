import InfoGeometry.Canonical.HestenesLogScaleSamplingBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Dirichlet transport through a Hestenes log-shift intertwiner

This is the finite readout of the shift intertwining law.  Coefficients are
real so that the given real-linear encoding map can be used directly; no
complexification or infinite Dirichlet series is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteDirichletHestenesIntertwinerBridge

open InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge
open InfoGeometry.Canonical.HestenesLogScaleSamplingBridge
open InfoGeometry.Canonical.HestenesModularRealizationBridge
open scoped BigOperators

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]

def finiteLogShiftSum (N : ℕ) (f : TestFun) : TestFun :=
  ∑ n ∈ Finset.Icc 1 N, logShiftOp n f

def finiteWeightedLogShiftSum (N : ℕ) (a : ℕ → ℝ) (f : TestFun) : TestFun :=
  ∑ n ∈ Finset.Icc 1 N, a n • logShiftOp n f

theorem finiteLogShiftSum_eq_finiteDirichletShiftOp
    (N : ℕ) (f : TestFun) :
    finiteLogShiftSum N f = finiteDirichletShiftOp N f := by
  simp [finiteLogShiftSum, finiteDirichletShiftOp]

theorem encode_finiteLogShiftSum
    (H : HestenesModularDatum (M := M))
    (J : HestenesLogShiftIntertwinerDatum H)
    (N : ℕ) (f : TestFun) :
    J.encode (finiteLogShiftSum N f) =
      ∑ n ∈ Finset.Icc 1 N,
        H.Delta_real (Real.log (n : ℝ)) (J.encode f) := by
  unfold finiteLogShiftSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simpa [logShiftOp] using J.shift_intertwining (Real.log (n : ℝ)) f

theorem encode_finiteWeightedLogShiftSum
    (H : HestenesModularDatum (M := M))
    (J : HestenesLogShiftIntertwinerDatum H)
    (N : ℕ) (a : ℕ → ℝ) (f : TestFun) :
    J.encode (finiteWeightedLogShiftSum N a f) =
      ∑ n ∈ Finset.Icc 1 N,
        a n • H.Delta_real (Real.log (n : ℝ)) (J.encode f) := by
  unfold finiteWeightedLogShiftSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_smul]
  change a n • J.encode (shiftOp (Real.log (n : ℝ)) f) = _
  rw [J.shift_intertwining]

theorem encode_finiteDirichletShiftOp
    (H : HestenesModularDatum (M := M))
    (J : HestenesLogShiftIntertwinerDatum H)
    (N : ℕ) (f : TestFun) :
    J.encode (finiteDirichletShiftOp N f) =
      ∑ n ∈ Finset.Icc 1 N,
        H.Delta_real (Real.log (n : ℝ)) (J.encode f) := by
  rw [← finiteLogShiftSum_eq_finiteDirichletShiftOp]
  exact encode_finiteLogShiftSum H J N f

theorem encode_cantorDepthShift
    (H : HestenesModularDatum (M := M))
    (J : HestenesLogShiftIntertwinerDatum H)
    (k : ℕ) (f : TestFun) :
    J.encode (shiftOp (cantorLogTimeAtDepth k) f) =
      H.Delta_real ((k : ℝ) * Real.log 3) (J.encode f) := by
  simpa [cantorLogTimeAtDepth, logTimeAtDepth] using
    J.shift_intertwining (cantorLogTimeAtDepth k) f

/-- The generic finite Dirichlet operator in the Hestenes representation. -/
def hestenesFiniteDirichletOperator (H : HestenesModularDatum (M := M)) (a : ℕ → ℝ) (N : ℕ) : M →L[ℝ] M :=
  ∑ n ∈ Finset.Icc 1 N, a n • H.Delta_real (Real.log n)

/-- The intertwining theorem for finite Dirichlet operators (operator level). -/
theorem finiteDirichlet_hestenes_intertwining 
    (H : HestenesModularDatum (M := M)) (J : HestenesLogShiftIntertwinerDatum H)
    (a : ℕ → ℝ) (N : ℕ) (f : TestFun) :
    J.encode (finiteWeightedLogShiftSum N a f) = hestenesFiniteDirichletOperator H a N (J.encode f) := by
  unfold hestenesFiniteDirichletOperator
  rw [ContinuousLinearMap.sum_apply]
  have h := encode_finiteWeightedLogShiftSum H J N a f
  rw [h]
  apply Finset.sum_congr rfl
  intro x _
  rw [ContinuousLinearMap.smul_apply]


end InfoGeometry.Canonical.FiniteDirichletHestenesIntertwinerBridge
