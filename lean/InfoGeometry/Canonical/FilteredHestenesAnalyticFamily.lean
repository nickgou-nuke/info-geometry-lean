import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

noncomputable section

namespace InfoGeometry.Canonical.FilteredHestenesAnalyticFamily

open InfoGeometry.Krein
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity

/-- A nonlinear observable family on a filtered Hestenes--Krein tower.

The family is pointwise Cauchy-analytic at every finite stage.  Values and
derivatives intertwine the bonding maps, which is the exact data needed for a
stage-independent colimit readout. -/
structure AnalyticFamily (C : HestenesKreinCone) where
  map : ∀ n, DoubledSpace (C.Base n) → DoubledSpace (C.Base n)
  analytic :
    ∀ n x,
      CauchyAnalyticAt
        (clockPhaseStructure (C.Base n))
        (clockPhaseStructure (C.Base n))
        (map n) x
  map_bond :
    ∀ n x, C.bond n (map n x) = map (n + 1) (C.bond n x)
  deriv_bond :
    ∀ n x,
      ((analytic (n + 1) (C.bond n x)).deriv).comp (C.bond n) =
        (C.bond n).comp ((analytic n x).deriv)

namespace AnalyticFamily

variable {C : HestenesKreinCone} (F : AnalyticFamily C)

/-- Read a finite-stage observable in the doubled filtered-colimit carrier. -/
def colimitReadout (n : ℕ) :
    DoubledSpace (C.Base n) → DoubledSpace C.LimitBase :=
  fun x => C.ι n (F.map n x)

/-- The colimit readout of a finite-stage Hestenes-analytic observable is
Cauchy-analytic. -/
def colimitReadoutCauchyAnalyticAt
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    CauchyAnalyticAt
      (clockPhaseStructure (C.Base n))
      (clockPhaseStructure C.LimitBase)
      (F.colimitReadout n) x :=
  { deriv := (C.ι n).comp ((F.analytic n x).deriv)
    has_fderiv_at := by
      simpa [colimitReadout] using
        (C.ι n).hasFDerivAt.comp x (F.analytic n x).has_fderiv_at
    phase_linear_deriv :=
      PhaseStructure.comp_phaseLinear
        (clockPhaseStructure (C.Base n))
        (clockPhaseStructure (C.Base n))
        (clockPhaseStructure C.LimitBase)
        (F.analytic n x).phase_linear_deriv
        (C.ι_hestenes n) }

/-- The derivative of the colimit readout is the canonical cone map composed
with the finite-stage derivative. -/
@[simp] theorem colimitReadout_deriv
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    (F.colimitReadoutCauchyAnalyticAt n x).deriv =
      (C.ι n).comp ((F.analytic n x).deriv) := by
  rfl

/-- Advancing both the state and observable by one filtered stage does not
change the colimit value. -/
theorem colimitReadout_bond
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    F.colimitReadout (n + 1) (C.bond n x) =
      F.colimitReadout n x := by
  unfold colimitReadout
  rw [← F.map_bond n x]
  exact C.ι_bond_apply n (F.map n x)

/-! Compatibility with an arbitrary finite composite of bonding maps. -/
theorem colimitReadout_bondIterate
    (n : ℕ) : ∀ m : ℕ, ∀ x : DoubledSpace (C.Base n),
      F.colimitReadout (n + m)
          (C.toFilteredPhaseCone.bondIterate n m x) =
        F.colimitReadout n x
  | 0, x => by simp [FilteredPhaseCone.bondIterate, colimitReadout]
  | m + 1, x => by
      simpa [FilteredPhaseCone.bondIterate, Nat.add_assoc] using
        (F.colimitReadout_bond (n + m)
          (C.toFilteredPhaseCone.bondIterate n m x)).trans
          (colimitReadout_bondIterate n m x)

/-- The derivative obtained after advancing one stage and differentiating
along the bonding map equals the derivative of the original colimit readout. -/
theorem colimitReadout_deriv_bond
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    ((C.ι (n + 1)).comp
      ((F.analytic (n + 1) (C.bond n x)).deriv)).comp (C.bond n) =
        (C.ι n).comp ((F.analytic n x).deriv) := by
  calc
    ((C.ι (n + 1)).comp
        ((F.analytic (n + 1) (C.bond n x)).deriv)).comp (C.bond n)
        =
      (C.ι (n + 1)).comp
        (((F.analytic (n + 1) (C.bond n x)).deriv).comp (C.bond n)) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ =
      (C.ι (n + 1)).comp
        ((C.bond n).comp ((F.analytic n x).deriv)) := by
          rw [F.deriv_bond n x]
    _ =
      ((C.ι (n + 1)).comp (C.bond n)).comp
        ((F.analytic n x).deriv) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (C.ι n).comp ((F.analytic n x).deriv) := by
          rw [C.ι_bond n]

/-! Derivative compatibility for an arbitrary finite composite. -/
theorem colimitReadout_deriv_bondIterate
    (n : ℕ) : ∀ m : ℕ, ∀ x : DoubledSpace (C.Base n),
      ((C.ι (n + m)).comp
        ((F.analytic (n + m)
          (C.toFilteredPhaseCone.bondIterate n m x)).deriv)).comp
        (C.toFilteredPhaseCone.bondIterate n m) =
      (C.ι n).comp ((F.analytic n x).deriv)
  | 0, x => by simp [FilteredPhaseCone.bondIterate]
  | m + 1, x => by
      have hstep := F.colimitReadout_deriv_bond
        (n + m) (C.toFilteredPhaseCone.bondIterate n m x)
      have hprev := colimitReadout_deriv_bondIterate n m x
      have hcomp := congrArg
        (fun L => L.comp (C.toFilteredPhaseCone.bondIterate n m)) hstep
      simpa [FilteredPhaseCone.bondIterate, Nat.add_assoc,
        ContinuousLinearMap.comp_assoc] using hcomp.trans hprev

/-- The colimit-readout derivative obeys the Hestenes clock-axis
Cauchy--Riemann law. -/
theorem colimitReadout_clockAxis
    (n : ℕ) (x v : DoubledSpace (C.Base n)) :
    (F.colimitReadoutCauchyAnalyticAt n x).deriv
        (clockAxis (E := C.Base n) v) =
      clockAxis (E := C.LimitBase)
        ((F.colimitReadoutCauchyAnalyticAt n x).deriv v) :=
  (F.colimitReadoutCauchyAnalyticAt n x).cauchyRiemann_apply v

/-- The stage-independent value law and derivative law form the filtered
Hestenes analyticity packet for one transition. -/
theorem filtered_value_and_derivative_compatibility
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    F.colimitReadout (n + 1) (C.bond n x) = F.colimitReadout n x ∧
      ((C.ι (n + 1)).comp
        ((F.analytic (n + 1) (C.bond n x)).deriv)).comp (C.bond n) =
          (C.ι n).comp ((F.analytic n x).deriv) :=
  ⟨F.colimitReadout_bond n x, F.colimitReadout_deriv_bond n x⟩

end AnalyticFamily

end InfoGeometry.Canonical.FilteredHestenesAnalyticFamily

end noncomputable section
