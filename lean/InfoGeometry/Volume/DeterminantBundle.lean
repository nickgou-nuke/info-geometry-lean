import InfoGeometry.Volume.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Determinant Bundle of Information Manifolds

Formalizes the Determinant Bundle as the line bundle of volume forms.
Sections of this bundle represent the "Information Density" of the state.

Transition between sections is given by the Volume Homomorphism, and 
the fibers are rescaled by the Dilation generators (Cartan D).
-/

namespace DeterminantBundle

open Base

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
noncomputable def volumeScale (f : V ≃ₗ[ℝ] V) : ℝ :=
  |((VolumeHom f : ℝˣ) : ℝ)|

/--
Weyl action on the determinant line, via the positive volume scale.
-/
noncomputable def weylAction (f : V ≃ₗ[ℝ] V) (ω : DeterminantLine V) : DeterminantLine V :=
  volumeScale f * ω

/--
Dilation Generator (D).
Infinitesimal generator of volume scaling.
Its eigenvalue is the "Quantum Number" (Scaling Dimension/Conformal Weight).
-/
def Dilation (s : ℝ) (ω : DeterminantLine V) : DeterminantLine V :=
  s * ω

/-- Weyl action is dilation by the induced positive volume scale. -/
theorem weylAction_eq_dilation_volumeScale
    (f : V ≃ₗ[ℝ] V) (ω : DeterminantLine V) :
    weylAction f ω = Dilation (volumeScale f) ω := by
  rfl

/--
The Conformal Weight (Quantum Number).
A state has weight `Δ` if every Weyl action rescales it by
`volumeScale(f)^Δ`.
-/
def HasConformalWeight (Δ : ℝ) (ψ : DeterminantLine V) : Prop :=
  ∀ f : V ≃ₗ[ℝ] V,
    weylAction f ψ = Dilation (Real.rpow (volumeScale f) Δ) ψ

/-- Canonical weight-1 law for the determinant-line scalar model. -/
theorem hasConformalWeight_one (ψ : DeterminantLine V) :
    HasConformalWeight (V := V) 1 ψ := by
  intro f
  simp [weylAction, Dilation, volumeScale, Real.rpow_one]

end DeterminantBundle
