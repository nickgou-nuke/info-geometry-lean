import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Real.Basic

noncomputable section

namespace InfoGeometry.LinearAlgebra.TraceUpperTriangular

variable {M N : Type*}
variable [AddCommGroup M] [Module ℝ M]
variable [AddCommGroup N] [Module ℝ N]

def upperRight (b : N →ₗ[ℝ] M) : Module.End ℝ (M × N) :=
  (LinearMap.inl ℝ M N).comp
    (b.comp (LinearMap.snd ℝ M N))

@[simp]
theorem upperRight_apply (b : N →ₗ[ℝ] M) (x : M × N) :
    upperRight b x = (b x.2, 0) :=
  rfl

theorem trace_upperRight_zero
    [FiniteDimensional ℝ M]
    [FiniteDimensional ℝ N]
    (b : N →ₗ[ℝ] M) :
    LinearMap.trace ℝ (M × N) (upperRight b) = 0 := by
  let projection : (M × N) →ₗ[ℝ] M :=
    b.comp (LinearMap.snd ℝ M N)
  have hCycle :
      LinearMap.trace ℝ (M × N)
          ((LinearMap.inl ℝ M N).comp projection) =
        LinearMap.trace ℝ M
          (projection.comp (LinearMap.inl ℝ M N)) := by
    exact LinearMap.congr_fun
      (LinearMap.congr_fun
        (LinearMap.trace_comp_comm ℝ (M × N) M)
        (LinearMap.inl ℝ M N))
      projection
  have hZero :
      projection.comp (LinearMap.inl ℝ M N) = 0 := by
    ext x
    simp [projection, LinearMap.comp_apply]
  rw [upperRight, ← show projection =
      b.comp (LinearMap.snd ℝ M N) by rfl, hCycle, hZero]
  simp

def upperTriangular
    (a : Module.End ℝ M)
    (b : N →ₗ[ℝ] M)
    (d : Module.End ℝ N) :
    Module.End ℝ (M × N) :=
  a.prodMap d + upperRight b

@[simp]
theorem upperTriangular_apply
    (a : Module.End ℝ M)
    (b : N →ₗ[ℝ] M)
    (d : Module.End ℝ N)
    (x : M × N) :
    upperTriangular a b d x =
      (a x.1 + b x.2, d x.2) :=
  by
    simp [upperTriangular, upperRight, LinearMap.comp_apply]

theorem trace_upperTriangular
    [FiniteDimensional ℝ M]
    [FiniteDimensional ℝ N]
    (a : Module.End ℝ M)
    (b : N →ₗ[ℝ] M)
    (d : Module.End ℝ N) :
    LinearMap.trace ℝ (M × N) (upperTriangular a b d) =
      LinearMap.trace ℝ M a + LinearMap.trace ℝ N d := by
  rw [upperTriangular, map_add, LinearMap.trace_prodMap',
    trace_upperRight_zero, add_zero]

end InfoGeometry.LinearAlgebra.TraceUpperTriangular
