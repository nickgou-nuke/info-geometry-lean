import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Canonical

open InfoGeometry.Krein
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Boundary fixed-point subspace of a modular operator `Δ`:
the locus where `Δ ψ = ψ`, i.e. the inversion-stable horizon.
-/
def boundarySubspace (Δ : EndH) : Submodule ℝ H₂ :=
  LinearMap.eqLocus Δ.toLinearMap 1

@[simp] theorem mem_boundarySubspace
    (Δ : EndH) (ψ : H₂) :
    ψ ∈ boundarySubspace (E := E) Δ ↔ Δ ψ = ψ := by
  simpa [boundarySubspace] using
    (LinearMap.mem_eqLocus (x := ψ) (f := Δ.toLinearMap) (g := (1 : H₂ →ₗ[ℝ] H₂)))

/--
Boundary projector: the orthogonal projection onto the fixed-point subspace.
This is the operator-level projector onto the horizon locus.
-/
noncomputable def boundaryProjector (Δ : EndH)
    [(boundarySubspace (E := E) Δ).HasOrthogonalProjection] : EndH :=
  (boundarySubspace (E := E) Δ).subtypeL.comp
    (boundarySubspace (E := E) Δ).orthogonalProjection

end InfoGeometry.Canonical
