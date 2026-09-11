import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Projective.SplitOctonions
universe u

structure SplitAlbertPlaneDatum (R : Type u) [CommRing R] where
  A : Type u
  zero : A
  jordan : A → A → A
  trace : A → R
  rankOne : A → Prop
  jordan_comm : ∀ X Y, jordan X Y = jordan Y X

namespace SplitAlbertPlaneDatum

variable {R : Type u} [CommRing R]
variable (D : SplitAlbertPlaneDatum R)

/-- A projective point is a rank-one Jordan idempotent with trace one. -/
structure ProjectivePoint where
  P : D.A
  idempotent : D.jordan P P = P
  trace_one : D.trace P = 1
  rank_one : D.rankOne P

/-- A projective line is represented by the same rank-one idempotent data. -/
structure ProjectiveLine where
  L : D.A
  idempotent : D.jordan L L = L
  trace_one : D.trace L = 1
  rank_one : D.rankOne L

/-- Incidence is Jordan orthogonality. -/
def Incident (P : ProjectivePoint D) (L : ProjectiveLine D) : Prop :=
  D.jordan P.P L.L = D.zero

/-- Incidence is symmetric because the Jordan product is commutative. -/
theorem incident_symmetric
    (P : ProjectivePoint D) (L : ProjectiveLine D) :
    Incident D P L ↔ D.jordan L.L P.P = D.zero := by
  unfold Incident
  rw [D.jordan_comm]

end SplitAlbertPlaneDatum

end InfoGeometry.Projective.SplitOctonions
