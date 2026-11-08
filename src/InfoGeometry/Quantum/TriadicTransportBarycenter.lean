import InfoGeometry.Projective.Rays
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Quantum.TriadicTransport

open InfoGeometry.Krein
open InfoGeometry.Projective

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*}

local notation "H₂" => DoubledSpace E

/-- Abstract cost functional on triadic data and a candidate doubled-space state. -/
abbrev TriadicCost := (ι → ℝ) → (ι → H₂) → H₂ → ℝ

/-- A state is a surprisal barycenter when it minimizes the chosen triadic cost. -/
def IsSurprisalBarycenter (Cost : TriadicCost (E := E) (ι := ι))
    (w : ι → ℝ) (v : ι → H₂) (u : H₂) : Prop :=
  ∀ u', Cost w v u ≤ Cost w v u'

/-- Existence and projective uniqueness package for a barycenter of a chosen triadic cost. -/
structure HasUniqueSurprisalBarycenter
    (Cost : TriadicCost (E := E) (ι := ι))
    (w : ι → ℝ) (v : ι → H₂) where
  barycenter : H₂
  is_min : IsSurprisalBarycenter (E := E) (ι := ι) Cost w v barycenter
  unique : ∀ u, IsSurprisalBarycenter (E := E) (ι := ι) Cost w v u → same_ray (E := E) u barycenter
  nonzero : barycenter ≠ 0

end InfoGeometry.Quantum.TriadicTransport
