import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TopologicalGradedRationalDifferential

namespace InfoGeometry.Canonical

variable {V : ℕ → Type*}
  [∀ p, NormedAddCommGroup (V p)]
  [∀ p, NormedSpace ℚ (V p)]
  [∀ p, FiniteDimensional ℚ (V p)]

/-!
  A sector is declared topological only together with the closedness proof.
  This avoids silently inferring closedness over incomplete coefficient fields.
-/

structure ClosedGradedSector where
  carrier : GradedSector V
  isClosed : ∀ p, IsClosed (carrier p : Set (V p))

def closedGradedSectorInf
    (S T : ClosedGradedSector (V := V)) : ClosedGradedSector (V := V) where
  carrier p := S.carrier p ⊓ T.carrier p
  isClosed p := by
    simpa using (S.isClosed p).inter (T.isClosed p)

def closedGradedSectorInf3
    (S T U : ClosedGradedSector (V := V)) : ClosedGradedSector (V := V) :=
  closedGradedSectorInf (closedGradedSectorInf S T) U

theorem closedGradedSectorInf_isClosed
    (S T : ClosedGradedSector (V := V)) (p : ℕ) :
    IsClosed ((closedGradedSectorInf S T).carrier p : Set (V p)) :=
  (closedGradedSectorInf S T).isClosed p

theorem closedGradedSectorInf3_isClosed
    (S T U : ClosedGradedSector (V := V)) (p : ℕ) :
    IsClosed ((closedGradedSectorInf3 S T U).carrier p : Set (V p)) :=
  (closedGradedSectorInf3 S T U).isClosed p

theorem differential_preserves_closedGradedSectorInf
    (D : GradedRationalDifferential V)
    (S T : ClosedGradedSector (V := V))
    (hS : DifferentialPreservesSector D S.carrier)
    (hT : DifferentialPreservesSector D T.carrier) :
    DifferentialPreservesSector D (closedGradedSectorInf S T).carrier := by
  intro p x hx
  exact ⟨hS p x hx.1, hT p x hx.2⟩

theorem continuous_differential_preserves_closedGradedSectorInf
    (D : GradedRationalDifferential V)
    (S T : ClosedGradedSector (V := V))
    (hS : DifferentialPreservesSector D S.carrier)
    (hT : DifferentialPreservesSector D T.carrier)
    (p : ℕ) {x : V p}
    (hx : x ∈ (closedGradedSectorInf S T).carrier p) :
    continuousGradedDifferential D p x ∈
      (closedGradedSectorInf S T).carrier (p + 1) := by
  simpa using differential_preserves_closedGradedSectorInf D S T hS hT p x hx

theorem differential_preserves_closedGradedSectorInf3
    (D : GradedRationalDifferential V)
    (S T U : ClosedGradedSector (V := V))
    (hS : DifferentialPreservesSector D S.carrier)
    (hT : DifferentialPreservesSector D T.carrier)
    (hU : DifferentialPreservesSector D U.carrier) :
    DifferentialPreservesSector D (closedGradedSectorInf3 S T U).carrier := by
  exact differential_preserves_closedGradedSectorInf D
    (closedGradedSectorInf S T) U
    (differential_preserves_closedGradedSectorInf D S T hS hT) hU

end InfoGeometry.Canonical
