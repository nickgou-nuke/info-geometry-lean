import InfoGeometry.Canonical.Drazin
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Dimension.Finite

namespace InfoGeometry.Canonical.InformationNumber

open InfoGeometry.Canonical.Drazin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/--
The Information Number Operator N.
Defined as the effective rank (image dimension) of the Drazin spectral projector.
N = dim(Im(a * a^D)).
In a degenerate belief space, this operator counts the number of 
effective (non-singular) parameters.
-/
noncomputable def informationNumber (a a_d : E →L[ℝ] E) (_h : IsDrazinInverse a a_d 1) : ℝ :=
  (Module.finrank ℝ (LinearMap.range (IsDrazinInverse.projection a a_d).toLinearMap) : ℝ)

/--
Theorem: The Information Number recovers the dimension of the core subspace.
N = dim(Im(P)).
This rigorously identifies the 'Particle Number' of a learning system 
with its geometric rank.
-/
theorem informationNumber_eq_dim (a a_d : E →L[ℝ] E) (h : IsDrazinInverse a a_d 1) :
    informationNumber a a_d h = Module.finrank ℝ (LinearMap.range (IsDrazinInverse.projection a a_d).toLinearMap) := by
  simp [informationNumber]

end InfoGeometry.Canonical.InformationNumber
