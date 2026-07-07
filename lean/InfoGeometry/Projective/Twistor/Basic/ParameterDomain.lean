import InfoGeometry.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace InfoGeometry.Information

/--
An open parameter domain in `ℝ^n`, represented as a set with an explicit `IsOpen` proof.
-/
structure OpenParameterDomain (n : ℕ) where
  carrier : Set (EuclideanSpace ℝ (Fin n))
  isOpen : IsOpen carrier

/-- Parameter points are subtype points of the open chart. -/
abbrev ParameterPoint (n : ℕ) (U : OpenParameterDomain n) : Type _ :=
  {θ : EuclideanSpace ℝ (Fin n) // θ ∈ U.carrier}

end InfoGeometry.Information
