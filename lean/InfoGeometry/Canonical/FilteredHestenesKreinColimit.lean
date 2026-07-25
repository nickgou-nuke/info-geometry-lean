import InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
import InfoGeometry.Canonical.HestenesAnalyticity

/-!
# Filtered Hestenes--Krein colimit

Concrete doubled-space realization of filtered inductive phase analyticity.
Every bonding map and cone map is required to commute with the Hestenes clock
axis.  The resulting Cauchy analyticity is then constructed from the native
continuous-linear derivative theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredHestenesKreinColimit

open InfoGeometry.Krein
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity

/-- A sequential system of real Hilbert carriers whose doubled spaces form a
compatible Hestenes--Krein cone. -/
structure HestenesKreinCone where
  Base : ℕ → Type
  baseNormedAddCommGroup : ∀ n, NormedAddCommGroup (Base n)
  baseInnerProductSpace : ∀ n, InnerProductSpace ℝ (Base n)
  baseCompleteSpace : ∀ n, CompleteSpace (Base n)
  LimitBase : Type
  limitNormedAddCommGroup : NormedAddCommGroup LimitBase
  limitInnerProductSpace : InnerProductSpace ℝ LimitBase
  limitCompleteSpace : CompleteSpace LimitBase
  bond : ∀ n, DoubledSpace (Base n) →L[ℝ] DoubledSpace (Base (n + 1))
  bond_hestenes :
    ∀ n, IsHestenesHolomorphicDifferential (E := Base n) (F := Base (n + 1)) (bond n)
  ι : ∀ n, DoubledSpace (Base n) →L[ℝ] DoubledSpace LimitBase
  ι_hestenes :
    ∀ n, IsHestenesHolomorphicDifferential (E := Base n) (F := LimitBase) (ι n)
  ι_bond : ∀ n, (ι (n + 1)).comp (bond n) = ι n

attribute [instance] HestenesKreinCone.baseNormedAddCommGroup
attribute [instance] HestenesKreinCone.baseInnerProductSpace
attribute [instance] HestenesKreinCone.baseCompleteSpace
attribute [instance] HestenesKreinCone.limitNormedAddCommGroup
attribute [instance] HestenesKreinCone.limitInnerProductSpace
attribute [instance] HestenesKreinCone.limitCompleteSpace

namespace HestenesKreinCone

variable (C : HestenesKreinCone)

/-- The Hestenes clock-axis commutation law is exactly phase-linearity for the
canonical doubled-space phase structures. -/
theorem bond_phaseLinear (n : ℕ) :
    (clockPhaseStructure (C.Base n)).IsPhaseLinearMap
      (C.bond n) (clockPhaseStructure (C.Base (n + 1))) :=
  C.bond_hestenes n

/-- Cone maps preserve the Hestenes clock axis. -/
theorem ι_phaseLinear (n : ℕ) :
    (clockPhaseStructure (C.Base n)).IsPhaseLinearMap
      (C.ι n) (clockPhaseStructure C.LimitBase) :=
  C.ι_hestenes n

/-- Forgetting the Hilbert presentation yields the generic filtered phase
cone, with the Hestenes clock axis as its phase structure. -/
def toFilteredPhaseCone : FilteredPhaseCone where
  Stage := fun n => DoubledSpace (C.Base n)
  stageNormedAddCommGroup := fun n => inferInstance
  stageNormedSpace := fun n => inferInstance
  phase := fun n => clockPhaseStructure (C.Base n)
  bond := C.bond
  bond_phase := C.bond_hestenes
  Limit := DoubledSpace C.LimitBase
  limitNormedAddCommGroup := inferInstance
  limitNormedSpace := inferInstance
  limitPhase := clockPhaseStructure C.LimitBase
  ι := C.ι
  ι_phase := C.ι_hestenes
  ι_bond := C.ι_bond

/-- Every finite Hestenes--Krein bonding map is Cauchy-analytic, without a
power-series or scalar-complex analyticity hypothesis. -/
def bondCauchyAnalyticAt (n : ℕ) (x : DoubledSpace (C.Base n)) :
    CauchyAnalyticAt
      (clockPhaseStructure (C.Base n))
      (clockPhaseStructure (C.Base (n + 1)))
      (fun y => C.bond n y) x :=
  (C.toFilteredPhaseCone).bondCauchyAnalyticAt n x

@[simp] theorem bondCauchyAnalyticAt_deriv
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    (C.bondCauchyAnalyticAt n x).deriv = C.bond n :=
  rfl

/-- Every canonical map from a finite doubled stage into the doubled colimit
carrier is Cauchy-analytic. -/
def ιCauchyAnalyticAt (n : ℕ) (x : DoubledSpace (C.Base n)) :
    CauchyAnalyticAt
      (clockPhaseStructure (C.Base n))
      (clockPhaseStructure C.LimitBase)
      (fun y => C.ι n y) x :=
  (C.toFilteredPhaseCone).includeCauchyAnalyticAt n x

@[simp] theorem ιCauchyAnalyticAt_deriv
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    (C.ιCauchyAnalyticAt n x).deriv = C.ι n :=
  rfl

/-- The derivative computed after one filtered stage transition equals the
canonical derivative from the original stage. -/
theorem transported_deriv_eq_ι
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    ((C.toFilteredPhaseCone).includeAfterBondCauchyAnalyticAt n x).deriv =
      C.ι n :=
  (C.toFilteredPhaseCone).includeAfterBond_deriv_eq_include n x

/-- Hestenes Cauchy--Riemann compatibility survives one filtered transition. -/
theorem filtered_clockAxis_compatibility
    (n : ℕ) (x v : DoubledSpace (C.Base n)) :
    ((C.toFilteredPhaseCone).includeAfterBondCauchyAnalyticAt n x).deriv
        (clockAxis (E := C.Base n) v) =
      clockAxis (E := C.LimitBase) (C.ι n v) :=
  (C.toFilteredPhaseCone).filtered_cauchyRiemann_compatibility n x v

/-- Compatible stage representatives have equal images in the doubled colimit
carrier. -/
theorem ι_bond_apply (n : ℕ) (x : DoubledSpace (C.Base n)) :
    C.ι (n + 1) (C.bond n x) = C.ι n x :=
  (C.toFilteredPhaseCone).include_bond_apply n x

end HestenesKreinCone

end InfoGeometry.Canonical.FilteredHestenesKreinColimit
