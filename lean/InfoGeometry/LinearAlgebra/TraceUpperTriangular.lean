/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Trace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic

noncomputable section

namespace InfoGeometry.LinearAlgebra.TraceUpperTriangular

variable {K : Type*} [Field K]
variable {M N : Type*}
variable [AddCommGroup M] [Module K M]
variable [AddCommGroup N] [Module K N]

def upperRight (b : N →ₗ[K] M) : Module.End K (M × N) :=
  (LinearMap.inl K M N).comp
    (b.comp (LinearMap.snd K M N))

@[simp]
theorem upperRight_apply (b : N →ₗ[K] M) (x : M × N) :
    upperRight b x = (b x.2, 0) :=
  rfl

theorem trace_upperRight_zero
    [FiniteDimensional K M]
    [FiniteDimensional K N]
    (b : N →ₗ[K] M) :
    LinearMap.trace K (M × N) (upperRight b) = 0 := by
  let projection : (M × N) →ₗ[K] M :=
    b.comp (LinearMap.snd K M N)
  have hCycle :
      LinearMap.trace K (M × N)
          ((LinearMap.inl K M N).comp projection) =
        LinearMap.trace K M
          (projection.comp (LinearMap.inl K M N)) := by
    exact LinearMap.congr_fun
      (LinearMap.congr_fun
        (LinearMap.trace_comp_comm K (M × N) M)
        (LinearMap.inl K M N))
      projection
  have hZero :
      projection.comp (LinearMap.inl K M N) = 0 := by
    ext x
    simp [projection, LinearMap.comp_apply]
  rw [upperRight, ← show projection =
      b.comp (LinearMap.snd K M N) by rfl, hCycle, hZero]
  simp

def upperTriangular
    (a : Module.End K M)
    (b : N →ₗ[K] M)
    (d : Module.End K N) :
    Module.End K (M × N) :=
  a.prodMap d + upperRight b

@[simp]
theorem upperTriangular_apply
    (a : Module.End K M)
    (b : N →ₗ[K] M)
    (d : Module.End K N)
    (x : M × N) :
    upperTriangular a b d x =
      (a x.1 + b x.2, d x.2) :=
  by
    simp [upperTriangular, upperRight, LinearMap.comp_apply]

theorem trace_upperTriangular
    [FiniteDimensional K M]
    [FiniteDimensional K N]
    (a : Module.End K M)
    (b : N →ₗ[K] M)
    (d : Module.End K N) :
    LinearMap.trace K (M × N) (upperTriangular a b d) =
      LinearMap.trace K M a + LinearMap.trace K N d := by
  rw [upperTriangular, map_add, LinearMap.trace_prodMap',
    trace_upperRight_zero, add_zero]

end InfoGeometry.LinearAlgebra.TraceUpperTriangular
