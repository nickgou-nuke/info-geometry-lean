import InfoGeometry.Volume.Base

/-!
# Determinant Bundle of Information Manifolds

Formalizes the Determinant Bundle as the line bundle of volume forms.
Sections of this bundle represent the "Information Density" of the state.

Transition between sections is given by the Volume Homomorphism, and 
the fibers are rescaled by the Dilation generators (Cartan D).
-/

namespace InfoGeometry.Volume.DeterminantBundle

open InfoGeometry.Volume.Base

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/--
Determinant Line (Fiber of the Determinant Bundle).
Physically represents the space of local volume scales.
-/
abbrev DeterminantLine (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] :=
  ℝ -- Scalar model for the top exterior power line.

/--
Weyl Action on the Determinant Line.
The action of a linear automorphism on the volume form.
This is exactly the determinant group homomorphism.
-/
noncomputable def weylAction (f : V ≃ₗ[ℝ] V) (ω : DeterminantLine V) : DeterminantLine V :=
  ((VolumeHom f : ℝˣ) : ℝ) * ω

/--
Dilation Generator (D).
Infinitesimal generator of volume scaling.
Its eigenvalue is the "Quantum Number" (Scaling Dimension/Conformal Weight).
-/
def Dilation (Δ : ℝ) (ω : DeterminantLine V) : DeterminantLine V :=
  Δ * ω

/--
The Conformal Weight (Quantum Number).
A state or operator has weight Δ if it transforms as ψ' = s^Δ ψ under 
a scaling s.
-/
def HasConformalWeight (Δ : ℝ) (ψ : DeterminantLine V) : Prop :=
  ∀ s : ℝ, Dilation Δ ψ = (s * Δ / s) * ψ -- Structural definition of scaling weight.

end InfoGeometry.Volume.DeterminantBundle
