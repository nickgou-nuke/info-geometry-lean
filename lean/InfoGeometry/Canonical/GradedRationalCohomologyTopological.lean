import Mathlib.Topology.Algebra.Module.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Constructions
import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.GradedRationalCohomologyShadow

/-!
  Native quotient topology for the graded cohomology shadows.  This layer
  does not choose representatives and does not assert finite-dimensionality;
  it only exposes the quotient projection and the universal continuous
  descent theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical

universe u

open CategoryTheory

variable {V W : ℕ → Type u}
  [∀ p, AddCommGroup (V p)]
  [∀ p, Module ℚ (V p)]
  [∀ p, AddCommGroup (W p)]
  [∀ p, Module ℚ (W p)]

/-! A cycle submodule inherits the ambient topology through its subtype
inclusion.  Keeping this instance explicit avoids asking Lean to guess the
topology on the source of the additive quotient. -/
instance gradedCycleSubmodule.instTopologicalSpace
    {p : ℕ} [TopologicalSpace (V p)]
    (D : GradedRationalDifferential V) :
    TopologicalSpace (gradedCycleSubmodule D p) :=
  TopologicalSpace.induced
    (Submodule.subtype (gradedCycleSubmodule D p)) inferInstance

/-! `Submodule.Quotient` is an additive quotient rather than the generic
`Quotient` type, so Mathlib does not install a topology automatically.  Give
it the final topology of the native quotient map; this is precisely the
topology for which quotient descent is universal. -/
instance gradedCohomologyShadow.instTopologicalSpace
    {p : ℕ} [TopologicalSpace (V (p + 1))]
    (D : GradedRationalDifferential V) :
    TopologicalSpace (gradedCohomologyShadow D p) :=
  TopologicalSpace.coinduced
    (Submodule.Quotient.mk :
      gradedCycleSubmodule D (p + 1) → gradedCohomologyShadow D p)
    inferInstance

def gradedCohomologyQuotientMk
    (D : GradedRationalDifferential V) (p : ℕ) :
    gradedCycleSubmodule D (p + 1) → gradedCohomologyShadow D p :=
  Submodule.Quotient.mk

theorem continuous_gradedCohomologyQuotientMk
    (D : GradedRationalDifferential V) (p : ℕ)
    [TopologicalSpace (V (p + 1))] :
    Continuous (gradedCohomologyQuotientMk D p) := by
  exact continuous_coinduced_rng

def gradedCohomologyTopCat
    (D : GradedRationalDifferential V) (p : ℕ)
    [TopologicalSpace (V (p + 1))] : TopCat :=
  TopCat.of (gradedCohomologyShadow D p)

def gradedCohomologyQuotientMkTopCat
    (D : GradedRationalDifferential V) (p : ℕ)
    [TopologicalSpace (V (p + 1))] :
    TopCat.of (gradedCycleSubmodule D (p + 1)) ⟶
      gradedCohomologyTopCat D p :=
  TopCat.ofHom
    { toFun := gradedCohomologyQuotientMk D p
      continuous_toFun := continuous_gradedCohomologyQuotientMk D p }

def gradedCohomologyQuotientLift
    (p : ℕ)
    [TopologicalSpace (V (p + 1))]
    [TopologicalSpace (W (p + 1))]
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (f : gradedCycleSubmodule D (p + 1) →
      gradedCycleSubmodule E (p + 1))
    (hInvariant : ∀ a b : gradedCycleSubmodule D (p + 1),
      (gradedBoundaryInCycles D p).quotientRel a b →
        gradedCohomologyQuotientMk E p (f a) =
          gradedCohomologyQuotientMk E p (f b)) :
    gradedCohomologyShadow D p → gradedCohomologyShadow E p :=
  Quotient.lift (fun a => gradedCohomologyQuotientMk E p (f a)) hInvariant

theorem continuous_gradedCohomologyQuotientLift
    (p : ℕ)
    [TopologicalSpace (V (p + 1))]
    [TopologicalSpace (W (p + 1))]
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (f : gradedCycleSubmodule D (p + 1) →
      gradedCycleSubmodule E (p + 1))
    (hf : Continuous f)
    (hInvariant : ∀ a b : gradedCycleSubmodule D (p + 1),
      (gradedBoundaryInCycles D p).quotientRel a b →
        gradedCohomologyQuotientMk E p (f a) =
          gradedCohomologyQuotientMk E p (f b)) :
    Continuous (gradedCohomologyQuotientLift p D E f hInvariant) := by
  apply Continuous.quotient_lift
  exact (continuous_gradedCohomologyQuotientMk E p).comp hf

def gradedCohomologyQuotientLiftTopCat
    (p : ℕ)
    [TopologicalSpace (V (p + 1))]
    [TopologicalSpace (W (p + 1))]
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (f : gradedCycleSubmodule D (p + 1) →
      gradedCycleSubmodule E (p + 1))
    (hf : Continuous f)
    (hInvariant : ∀ a b : gradedCycleSubmodule D (p + 1),
      (gradedBoundaryInCycles D p).quotientRel a b →
        gradedCohomologyQuotientMk E p (f a) =
          gradedCohomologyQuotientMk E p (f b)) :
    gradedCohomologyTopCat (V := V) D p ⟶
      gradedCohomologyTopCat (V := W) E p :=
  TopCat.ofHom
    { toFun := gradedCohomologyQuotientLift p D E f hInvariant
      continuous_toFun :=
        continuous_gradedCohomologyQuotientLift p D E f hf hInvariant }

@[simp] theorem gradedCohomologyQuotientLift_mk
    (p : ℕ)
    [TopologicalSpace (V (p + 1))]
    [TopologicalSpace (W (p + 1))]
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (f : gradedCycleSubmodule D (p + 1) →
      gradedCycleSubmodule E (p + 1))
    (hInvariant : ∀ a b : gradedCycleSubmodule D (p + 1),
      (gradedBoundaryInCycles D p).quotientRel a b →
        gradedCohomologyQuotientMk E p (f a) =
          gradedCohomologyQuotientMk E p (f b))
    (x : gradedCycleSubmodule D (p + 1)) :
    gradedCohomologyQuotientLift p D E f hInvariant
        (Submodule.Quotient.mk x) =
      gradedCohomologyQuotientMk E p (f x) := by
  rfl

end InfoGeometry.Canonical
