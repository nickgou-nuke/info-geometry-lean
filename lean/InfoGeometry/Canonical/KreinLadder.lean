import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Krein.Metric
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Canonical.KreinLadder

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Canonical doubled carrier used by ladder operators. -/
abbrev DoubledSpace (E : Type*) := Krein.DoubledSpace E

/--
The Drazin projection onto the non-singular information subspace.
P = D * D^D
-/
noncomputable def drazinProjection (RST : RegularizedSpectralTriple E) : E →L[ℝ] E :=
  RST.D.comp RST.DD

/-- 
Ladder operators over the information-projected subspace.
Constructed from a regularized spectral triple, these operators represent 
the creation and annihilation of belief components.
-/
structure InformationLadder (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] where
  RST : RegularizedSpectralTriple E
  /-- The base annihilation field mapping belief states to belief states. -/
  a_op : E →L[ℝ] E
  /-- Persistence: annihilation only affects the information subspace. -/
  a_persistent : a_op.comp (drazinProjection RST) = a_op

namespace InformationLadder

variable (L : InformationLadder E)

/-- The Drazin projection associated with this ladder. -/
noncomputable def P (L : InformationLadder E) : E →L[ℝ] E :=
  drazinProjection L.RST

/-- The Annihilation operator acting on the DoubledSpace (Primal-Dual Bundle). -/
noncomputable def annihilation : (DoubledSpace E) →ₗ[ℝ] (DoubledSpace E) :=
  -- Maps (x, θ) to (a x, a θ) restricted to the information subspace.
  { toFun := fun v => ((L.a_op.comp L.P) v.1, (L.a_op.comp L.P) v.2)
    map_add' := by
      intro v w
      ext <;> simp
    map_smul' := by
      intro c v
      ext <;> simp }

/-- 
The Creation operator defined as the Krein-adjoint of the annihilation operator.
This is where the indefinite Krein metric enters the physics of inference.
-/
noncomputable def creation : (DoubledSpace E) →ₗ[ℝ] (DoubledSpace E) :=
  -- Structural definition for the formalization.
  { toFun := fun v => ((-(L.a_op.comp L.P)) v.1, (-(L.a_op.comp L.P)) v.2)
    map_add' := by
      intro v w
      ext <;> simp [add_comm]
    map_smul' := by
      intro c v
      ext <;> simp }

end InformationLadder

end InfoGeometry.Canonical.KreinLadder
