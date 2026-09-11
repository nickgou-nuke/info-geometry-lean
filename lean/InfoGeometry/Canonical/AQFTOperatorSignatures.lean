import InfoGeometry.Canonical.SinkhornKMSCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# InfoGeometry.Canonical.AQFTOperatorSignatures

AQFT operator-algebra signature layer.
-/

namespace InfoGeometry.Canonical.AQFTOperatorInterface

open InfoGeometry.Canonical.KMSSinkhornBridge

section AbstractSignatures

variable (Obs : Type*)
variable [NonUnitalNormedRing Obs] [StarRing Obs]

/-- Abstract C*-ready AQFT operator-algebra signature. -/
abbrev IsCStarReady : Prop := CStarRing Obs

/--
Abstract complete-C*-ready AQFT signature used in this library:
this is only `CStarRing` plus completeness, not a von Neumann notion.
-/
abbrev IsCompleteCStarReady : Prop :=
  IsCStarReady Obs ∧ CompleteSpace Obs

end AbstractSignatures

section Realizations

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {Obs : Type*} [NonUnitalNormedRing Obs] [StarRing Obs]

/--
Explicit interpretation map from the concrete finite doubled-space operator model
into an abstract operator target.
No algebraic or star-preserving properties are imposed here.
-/
structure AQFTOperatorInterpretation
    (F : Type*) (Obs : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NonUnitalNormedRing Obs] [StarRing Obs] where
  interpret : AlgebraEnd F → Obs

end Realizations

end InfoGeometry.Canonical.AQFTOperatorInterface
