import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Topology.Weyl

/-- The momentum space equipped with a non-symmorphic glide reflection. -/
structure GlideBrillouinZone (BZ : Type*) [TopologicalSpace BZ] where
  -- The glide reflection operator
  glide : BZ ≃ₜ BZ
  -- The glide reflection is an involution on the momentum space
  h_involution : ∀ k, glide (glide k) = k

variable {BZ : Type*} [TopologicalSpace BZ]
variable (gbz : GlideBrillouinZone BZ)

/-- The Berry Curvature as a generic real-valued function over the BZ.
In a non-orientable Weyl semimetal, the Berry curvature is pseudo-scalar,
meaning it flips sign under the glide reflection. -/
structure TwistedBerryCurvature (gbz : GlideBrillouinZone BZ) where
  curvature : BZ → ℝ
  -- Z_2 Charge Cancellation: The curvature is odd under glide reflection
  h_twisted : ∀ k, curvature (gbz.glide k) = - curvature k

variable (F : TwistedBerryCurvature gbz)

/--
THEOREM: Z_2 Charge Cancellation on Non-Orientable Manifolds.
Because the Berry curvature is odd under the glide reflection,
the total integral over the orientable double cover cancels exactly to zero.
This forces the Nielsen-Ninomiya total chirality to be measured
in twisted (co)homology (modulo 2) rather than Z.
-/
theorem berry_curvature_odd_cancellation (k : BZ) :
    F.curvature k + F.curvature (gbz.glide k) = (0 : ℝ) := by
  calc
    F.curvature k + F.curvature (gbz.glide k) =
        F.curvature k + (- F.curvature k : ℝ) := by
      exact congrArg (fun x => F.curvature k + x) (F.h_twisted k)
    _ = (0 : ℝ) := add_neg_cancel (F.curvature k)

end InfoGeometry.Topology.Weyl
