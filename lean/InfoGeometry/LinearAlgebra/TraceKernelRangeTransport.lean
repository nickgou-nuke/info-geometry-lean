import InfoGeometry.LinearAlgebra.TraceInvariantSubmodule
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.LinearAlgebra.TraceKernelRangeTransport

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]

theorem kernel_invariant
    (d : V →ₗ[ℝ] W)
    (f : Module.End ℝ V)
    (g : Module.End ℝ W)
    (hcomm : d.comp f = g.comp d) :
    LinearMap.ker d ≤ Submodule.comap f (LinearMap.ker d) := by
  intro x hx
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  have h := LinearMap.congr_fun hcomm x
  simpa [LinearMap.comp_apply, LinearMap.mem_ker.mp hx] using h

theorem range_invariant
    (d : V →ₗ[ℝ] W)
    (f : Module.End ℝ V)
    (g : Module.End ℝ W)
    (hcomm : d.comp f = g.comp d) :
    LinearMap.range d ≤ Submodule.comap g (LinearMap.range d) := by
  rintro _ ⟨x, rfl⟩
  rw [Submodule.mem_comap]
  refine ⟨f x, ?_⟩
  have h := LinearMap.congr_fun hcomm x
  simpa [LinearMap.comp_apply] using h

def kernelRestriction
    (d : V →ₗ[ℝ] W)
    (f : Module.End ℝ V)
    (g : Module.End ℝ W)
    (hcomm : d.comp f = g.comp d) :
    Module.End ℝ (LinearMap.ker d) :=
  f.restrict (kernel_invariant d f g hcomm)

def rangeRestriction
    (d : V →ₗ[ℝ] W)
    (f : Module.End ℝ V)
    (g : Module.End ℝ W)
    (hcomm : d.comp f = g.comp d) :
    Module.End ℝ (LinearMap.range d) :=
  g.restrict (range_invariant d f g hcomm)

def quotientByKernelMap
    (d : V →ₗ[ℝ] W)
    (f : Module.End ℝ V)
    (g : Module.End ℝ W)
    (hcomm : d.comp f = g.comp d) :
    Module.End ℝ (V ⧸ LinearMap.ker d) :=
  Submodule.mapQ (LinearMap.ker d) (LinearMap.ker d) f
    (kernel_invariant d f g hcomm)

theorem quotKerEquivRange_intertwines
    (d : V →ₗ[ℝ] W)
    (f : Module.End ℝ V)
    (g : Module.End ℝ W)
    (hcomm : d.comp f = g.comp d) :
    d.quotKerEquivRange.toLinearMap.comp
        (quotientByKernelMap d f g hcomm) =
      (rangeRestriction d f g hcomm).comp
        d.quotKerEquivRange.toLinearMap := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (LinearMap.ker d).mkQ_surjective q
  apply Subtype.ext
  change d (f x) = g (d x)
  simpa [LinearMap.comp_apply] using LinearMap.congr_fun hcomm x

theorem quotKerEquivRange_conj
    (d : V →ₗ[ℝ] W)
    (f : Module.End ℝ V)
    (g : Module.End ℝ W)
    (hcomm : d.comp f = g.comp d) :
    d.quotKerEquivRange.conj
        (quotientByKernelMap d f g hcomm) =
      rangeRestriction d f g hcomm := by
  apply LinearMap.ext
  intro y
  have h := LinearMap.congr_fun
    (quotKerEquivRange_intertwines d f g hcomm)
    (d.quotKerEquivRange.symm y)
  simpa [LinearMap.comp_apply] using h

theorem trace_quotientByKernel_eq_trace_rangeRestriction
    [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ W]
    (d : V →ₗ[ℝ] W)
    (f : Module.End ℝ V)
    (g : Module.End ℝ W)
    (hcomm : d.comp f = g.comp d) :
    LinearMap.trace ℝ (V ⧸ LinearMap.ker d)
        (quotientByKernelMap d f g hcomm) =
      LinearMap.trace ℝ (LinearMap.range d)
        (rangeRestriction d f g hcomm) := by
  rw [← quotKerEquivRange_conj d f g hcomm]
  exact (LinearMap.trace_conj'
    (quotientByKernelMap d f g hcomm)
    d.quotKerEquivRange).symm

end InfoGeometry.LinearAlgebra.TraceKernelRangeTransport
