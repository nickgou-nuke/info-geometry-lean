import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Canonical

open InfoGeometry.Krein
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Boundary fixed-point subspace of an operator `Δ`:
the kernel of `(Δ - 1)`, equivalently the locus where `Δ ψ = ψ`, i.e. the
inversion-stable horizon.
-/
def boundarySubspace (Δ : EndH) : Submodule ℝ H₂ :=
  (Δ - 1).ker

omit [CompleteSpace E] in
@[simp] theorem mem_boundarySubspace
    (Δ : EndH) (ψ : H₂) :
    ψ ∈ boundarySubspace (E := E) Δ ↔ Δ ψ = ψ := by
  change (Δ - 1) ψ = 0 ↔ Δ ψ = ψ
  constructor
  · intro h
    simpa [sub_eq_zero] using h
  · intro h
    simpa [sub_eq_zero] using h

/--
Boundary projector: the orthogonal projection onto the fixed-point subspace.
This is the operator-level projector onto the horizon locus.
-/
noncomputable def boundaryProjector (Δ : EndH)
    [(boundarySubspace (E := E) Δ).HasOrthogonalProjection] : EndH :=
  (boundarySubspace (E := E) Δ).subtypeL.comp
    (boundarySubspace (E := E) Δ).orthogonalProjection

omit [CompleteSpace E] in
theorem boundaryProjector_mem
    (Δ : EndH) [(boundarySubspace (E := E) Δ).HasOrthogonalProjection]
    (ψ : H₂) :
    boundaryProjector (E := E) Δ ψ ∈ boundarySubspace (E := E) Δ := by
  change
    (((boundarySubspace (E := E) Δ).orthogonalProjection ψ :
        boundarySubspace (E := E) Δ) : H₂) ∈ boundarySubspace (E := E) Δ
  exact ((boundarySubspace (E := E) Δ).orthogonalProjection ψ).2

omit [CompleteSpace E] in
theorem boundaryProjector_idempotent
    (Δ : EndH) [(boundarySubspace (E := E) Δ).HasOrthogonalProjection] :
    (boundaryProjector (E := E) Δ).comp (boundaryProjector (E := E) Δ)
      = boundaryProjector (E := E) Δ := by
  apply ContinuousLinearMap.ext
  intro ψ
  simpa [boundaryProjector, ContinuousLinearMap.comp_apply] using
    congrArg
      (fun v : boundarySubspace (E := E) Δ => (v : H₂))
      (Submodule.orthogonalProjection_mem_subspace_eq_self
        ((boundarySubspace (E := E) Δ).orthogonalProjection ψ))

omit [CompleteSpace E] in
theorem boundaryProjector_fixed_of_mem
    (Δ : EndH) [(boundarySubspace (E := E) Δ).HasOrthogonalProjection]
    {ψ : H₂} (hψ : ψ ∈ boundarySubspace (E := E) Δ) :
    boundaryProjector (E := E) Δ ψ = ψ := by
  simpa [boundaryProjector, ContinuousLinearMap.comp_apply] using
    congrArg
      (fun v : boundarySubspace (E := E) Δ => (v : H₂))
      (Submodule.orthogonalProjection_mem_subspace_eq_self ⟨ψ, hψ⟩)

end InfoGeometry.Canonical
