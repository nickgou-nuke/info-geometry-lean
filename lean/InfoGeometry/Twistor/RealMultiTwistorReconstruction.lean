/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorIncidence
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Real multi-twistor reconstruction from a native spinor basis

A basis of primed spinors together with their unprimed partners determines a
unique real linear spacetime operator. Basis data provides independence and
spanning together; these facts are not separately postulated. Reconstruction
is covariant under a change of spinor basis and under the real twistor shear.
For a two-dimensional primed spinor module this is two-twistor reconstruction.
This does not impose a massive particle constraint or construct its reduction.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealMultiTwistorReconstruction

open RealTwistorIncidence

variable {ι S S' : Type*} [AddCommGroup S] [Module ℝ S]
  [AddCommGroup S'] [Module ℝ S']

/-- Extend the unprimed frame data by the universal property of a basis. -/
def reconstruct (b : Module.Basis ι ℝ S') (ω : ι → S) : S' →ₗ[ℝ] S :=
  b.constr ℝ ω

@[simp] theorem reconstruct_basis (b : Module.Basis ι ℝ S') (ω : ι → S) (i : ι) :
    reconstruct b ω (b i) = ω i := by
  simp [reconstruct]

/-- The reconstructed operator has the prescribed incident twistor frame. -/
theorem reconstruct_incidence (b : Module.Basis ι ℝ S') (ω : ι → S) (i : ι) :
    incidenceMap (reconstruct b ω) (b i) = (ω i, b i) := by
  simp

/-- A twistor frame with a primed-spinor basis determines exactly one operator. -/
theorem reconstruct_exists_unique (b : Module.Basis ι ℝ S') (ω : ι → S) :
    ∃! x : S' →ₗ[ℝ] S, ∀ i, incidenceMap x (b i) = (ω i, b i) := by
  refine ⟨reconstruct b ω, reconstruct_incidence b ω, ?_⟩
  intro x hx
  apply b.ext
  intro i
  rw [reconstruct_basis]
  exact congrArg Prod.fst (hx i)

/-- Resampling the reconstructed operator on any other basis reconstructs the
same operator. The second basis can have a different index type. -/
theorem reconstruct_frame_change {κ : Type*}
    (b : Module.Basis ι ℝ S') (c : Module.Basis κ ℝ S') (ω : ι → S) :
    reconstruct c (fun j => reconstruct b ω (c j)) = reconstruct b ω := by
  apply c.ext
  intro j
  simp

/-- Reconstruction and translating all unprimed frame entries commute. -/
theorem reconstruct_translation (b : Module.Basis ι ℝ S') (ω : ι → S)
    (d : S' →ₗ[ℝ] S) :
    reconstruct b (fun i => ω i + d (b i)) = reconstruct b ω + d := by
  apply b.ext
  intro i
  simp

/-- A change of basis in the target spinor module transports reconstruction
by composition. -/
theorem reconstruct_target_equiv {T : Type*} [AddCommGroup T] [Module ℝ T]
    (e : S ≃ₗ[ℝ] T) (b : Module.Basis ι ℝ S') (ω : ι → S) :
    reconstruct b (fun i => e (ω i)) = e.toLinearMap.comp (reconstruct b ω) := by
  apply b.ext
  intro i
  simp

end InfoGeometry.Twistor.RealMultiTwistorReconstruction
