import InfoGeometry.Canonical.Promoted.Drazin
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Finite

namespace InfoGeometry.Research.InformationNumber

open InfoGeometry.Research.Drazin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/--
The Information Number Operator N.
Defined as the trace of the Drazin spectral projector.
N = Tr(a * a^D).
In a degenerate belief space, this operator counts the number of 
effective (non-singular) parameters.
-/
noncomputable def informationNumber (a a_d : E →L[ℝ] E) (_h : IsDrazinInverse a a_d 1) : ℝ :=
  let P := IsDrazinInverse.projection a a_d
  LinearMap.trace ℝ E P.toLinearMap

/--
Theorem: The Information Number recovers the dimension of the core subspace.
N = dim(Im(P)).
This rigorously identifies the 'Particle Number' of a learning system 
with its geometric rank.
-/
theorem informationNumber_eq_dim (a a_d : E →L[ℝ] E) (h : IsDrazinInverse a a_d 1) :
    informationNumber a a_d h = Module.finrank ℝ (LinearMap.range (IsDrazinInverse.projection a a_d).toLinearMap) := by
  let P : E →L[ℝ] E := IsDrazinInverse.projection a a_d
  have hPP : P * P = P := by
    simpa [P] using IsDrazinInverse.projection_is_idempotent (a := a) (b := a_d) (k := 1) h
  have hPP' : P.toLinearMap * P.toLinearMap = P.toLinearMap := by
    ext x
    simpa using congrArg (fun f => f x) hPP
  have hIdem : IsIdempotentElem P.toLinearMap := hPP'
  have hProj : LinearMap.IsProj (LinearMap.range P.toLinearMap) P.toLinearMap :=
    LinearMap.IsIdempotentElem.isProj_range (f := P.toLinearMap) hIdem
  have hTrace : LinearMap.trace ℝ E P.toLinearMap
      = (Module.finrank ℝ (LinearMap.range P.toLinearMap) : ℝ) := by
    simpa using (LinearMap.IsProj.trace (R := ℝ) (M := E)
      (p := LinearMap.range P.toLinearMap) (f := P.toLinearMap) hProj)
  simpa [informationNumber, P] using hTrace

end InfoGeometry.Research.InformationNumber
