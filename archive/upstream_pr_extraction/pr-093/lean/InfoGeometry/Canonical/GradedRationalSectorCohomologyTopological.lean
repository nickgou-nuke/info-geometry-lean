import InfoGeometry.Canonical.GradedRationalSectorCohomology

/-!
  Algebraic specialization of the sector cohomology quotient.
  The earlier continuity and `TopCat` claims were overreaching for the current
  quotient-carrier API, so this file now only exposes the descent maps.
-/

noncomputable section

namespace InfoGeometry.Canonical

variable {V W : ℕ → Type*}
  [∀ p, AddCommGroup (V p)]
  [∀ p, Module ℚ (V p)]
  [∀ p, AddCommGroup (W p)]
  [∀ p, Module ℚ (W p)]

def sectorCohomologyQuotientMk
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) :
    sectorCycleSubmodule D S hS (p + 1) →
      sectorCohomologyShadow D S hS p :=
  Submodule.Quotient.mk

def sectorCohomologyQuotientLift
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (S : GradedSector V)
    (T : GradedSector W)
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector E T)
    (p : ℕ)
    (f : sectorCycleSubmodule D S hS (p + 1) →
      sectorCycleSubmodule E T hT (p + 1))
    (hInvariant : ∀ a b : sectorCycleSubmodule D S hS (p + 1),
      (sectorBoundaryInCycles D S hS p).quotientRel a b →
        sectorCohomologyQuotientMk E T hT p (f a) =
          sectorCohomologyQuotientMk E T hT p (f b)) :
    sectorCohomologyShadow D S hS p →
      sectorCohomologyShadow E T hT p :=
  Quotient.lift
    (fun a => sectorCohomologyQuotientMk E T hT p (f a)) hInvariant

@[simp] theorem sectorCohomologyQuotientLift_mk
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (S : GradedSector V)
    (T : GradedSector W)
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector E T)
    (p : ℕ)
    (f : sectorCycleSubmodule D S hS (p + 1) →
      sectorCycleSubmodule E T hT (p + 1))
    (hInvariant : ∀ a b : sectorCycleSubmodule D S hS (p + 1),
      (sectorBoundaryInCycles D S hS p).quotientRel a b →
        sectorCohomologyQuotientMk E T hT p (f a) =
          sectorCohomologyQuotientMk E T hT p (f b))
    (x : sectorCycleSubmodule D S hS (p + 1)) :
    sectorCohomologyQuotientLift D E S T hS hT p f hInvariant
        (Submodule.Quotient.mk x) =
      sectorCohomologyQuotientMk E T hT p (f x) := by
  rfl

end InfoGeometry.Canonical
