import Mathlib

/-!
QMS isolated proof target for `InfoGeometry.Canonical.SouriauOperatorialLogPotential.traceClassClaim`.

Mathematical context:
- `Param` is a parameter space.
- `Op` is an operator carrier with scalar multiplication by real numbers.
- `E.untracedExponential β` is the unnormalized Gibbs/operatorial exponential.
- `E.traceReadout` is the scalar trace/readout functional.
- `E.partitionFunction β` is defined by the field theorem
  `partitionFunction_eq_trace β : Z β = traceReadout (untracedExponential β)`.
- `E.normalizedState β` is assumed to be the normalized Gibbs state
  `Z β⁻¹ • untracedExponential β`.
- the trace/readout is homogeneous for real scalar multiplication.
- `Z β ≠ 0`.

Pure proposition:
Under these premises, the trace/readout of the normalized state is exactly `1`.
This is finite algebra over `ℝ`; it is not a trace-class theorem, analytic convergence
result, or von Neumann algebra theorem.
-/

namespace InfoGeometry.QMS.SouriauOperatorialLogPotentialTraceClass

@[ext]
structure OperatorialExponentialFamily (Param Op : Type*) where
  K : Param → Op
  untracedExponential : Param → Op
  operatorialExponentialFamily : Param → Op
  operatorialExponentialFamily_eq : ∀ β, operatorialExponentialFamily β = untracedExponential β
  traceReadout : Op → ℝ
  partitionFunction : Param → ℝ
  partitionFunction_eq_trace : ∀ β, partitionFunction β = traceReadout (untracedExponential β)
  partitionPotential : Param → ℝ
  normalizedState : Param → Op
  partitionPotential_eq_log_trace : ∀ β, partitionPotential β = Real.log (traceReadout (untracedExponential β))

/--
If the normalized state is `Z⁻¹ • e^{-K}` and the trace/readout is homogeneous,
then its trace/readout is `1`, provided `Z ≠ 0` and `Z` is the trace/readout of
the unnormalized exponential.
-/
theorem traceReadout_normalizedState_eq_one
    {Param Op : Type*} [SMul ℝ Op]
    (E : OperatorialExponentialFamily Param Op) (β : Param)
    (h_norm : E.normalizedState β = (E.partitionFunction β)⁻¹ • E.untracedExponential β)
    (h_linear : ∀ c o, E.traceReadout (c • o) = c * E.traceReadout o)
    (h_pos : E.partitionFunction β ≠ 0) :
    E.traceReadout (E.normalizedState β) = 1 := by
  rw [h_norm]
  rw [h_linear]
  rw [← E.partitionFunction_eq_trace β]
  exact inv_mul_cancel₀ h_pos

end InfoGeometry.QMS.SouriauOperatorialLogPotentialTraceClass
