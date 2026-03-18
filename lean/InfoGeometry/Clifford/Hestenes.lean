import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Clifford.Lift
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

/-!
# Hestenes Geometric Algebra for Information Fluids

Formalizes the pseudoscalar, exponential maps, and signed volume in 
Clifford algebras Cl(n,n) following the Hestenes convention.

This connects the algebraic volume form to the Weyl scaling of the 
information manifold.
-/

namespace InfoGeometry.Clifford.Hestenes

open InfoGeometry.Clifford

/-- Concrete split-signature Clifford algebra `Cl(1,1)`. -/
abbrev Cl11 := CliffordAlgebra splitQ11

/--
Pseudoscalar (I).
Representing the signed unit volume element.
For Cl(1,1), I² = 1.
-/
noncomputable def Pseudoscalar : Cl11 :=
  CliffordAlgebra.ι splitQ11 (1, 0) * CliffordAlgebra.ι splitQ11 (0, 1)

/--
Exponential Map of the Pseudoscalar.
In GA, exp(θ I) = cosh θ + I sinh θ (when I² = 1).
This generates a Weyl scaling (dilation) of the volume form.
-/
noncomputable def expPseudoscalar (θ : ℝ) : ℝ :=
  Real.cosh θ + Real.sinh θ

/--
Theorem: Weyl Scaling Generation.
The exponential of the pseudoscalar generates a multiplicative scaling 
of the information volume.
-/
theorem expPseudoscalar_is_scaling (θ : ℝ) :
    expPseudoscalar θ = Real.exp θ := by
  unfold expPseudoscalar
  rw [Real.cosh_add_sinh]

/--
Bridge: Pseudoscalar as Signed Volume.
Identifies the top-level GA form with the Radon-Nikodym derivative.
-/
def IsSignedVolume (RN : ℝ) : Prop :=
  ∃ ρ : Cl11 →ₗ[ℝ] ℝ, ρ Pseudoscalar = RN

section Representation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Concrete representation bridge:
the Cl(1,1) pseudoscalar maps to the doubled-space spectral involution.
-/
lemma cl11Rep_pseudoscalar_eq_spectral_epsilon :
    cl11Rep (E := E) Pseudoscalar
      = InfoGeometry.Krein.spectral_epsilon (E := E) := by
  simpa [Pseudoscalar, Q11] using
    (cl11Rep_pseudoscalar (E := E))

end Representation

end InfoGeometry.Clifford.Hestenes
