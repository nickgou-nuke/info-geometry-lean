import Mathlib.Algebra.Lie.TraceForm

/-!
# Trace-form scalar extension compatibility

The pinned Mathlib snapshot already supplies the Lie-module scalar-extension
instances, `LieModule.toEnd_baseChange`, and `LinearMap.trace_baseChange`.
This owner records their genuine trace-form consequence on pure tensors.
-/

open scoped TensorProduct

noncomputable section

namespace InfoGeometry.Lie.MathlibBackportTraceForm

variable {R A L M : Type*}
  [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [CommRing A] [Algebra R A]
  [Module.Free R M] [Module.Finite R M]

theorem traceForm_baseChange_tmul (x y : L) :
    (LieModule.traceForm A (A ⊗[R] L) (A ⊗[R] M))
      (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) =
      algebraMap R A ((LieModule.traceForm R L M) x y) := by
  change LinearMap.trace A (A ⊗[R] M)
      (((LieModule.toEnd A (A ⊗[R] L) (A ⊗[R] M)) (1 ⊗ₜ[R] x)) *
        ((LieModule.toEnd A (A ⊗[R] L) (A ⊗ₜ[R] M)) (1 ⊗ₜ[R] y))) = _
  rw [LieModule.toEnd_baseChange, LieModule.toEnd_baseChange]
  rw [← LinearMap.baseChange_mul]
  rw [LinearMap.trace_baseChange]
  rfl

end InfoGeometry.Lie.MathlibBackportTraceForm
