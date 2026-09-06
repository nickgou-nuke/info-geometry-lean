import InfoGeometry.Geometry.BilingualAnalyticity

/-!
# Filtered inductive Hestenes analyticity

This file gives the theorem-safe analytic structure carried by a filtered
inductive system of real normed phase spaces.  The relevant notion is not
power-series analyticity on an algebraic direct limit.  It is the finite-stage
Fréchet differentiability and phase-linearity that is transported by every
bonding map and every compatible map into a normed colimit carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity

open InfoGeometry.Geometry.BilingualAnalyticity

universe u

/-- A sequential filtered system of normed real phase spaces together with a
compatible cone into a normed phase-space carrier. -/
structure FilteredPhaseCone where
  Stage : ℕ → Type u
  stageNormedAddCommGroup : ∀ n, NormedAddCommGroup (Stage n)
  stageNormedSpace : ∀ n, NormedSpace ℝ (Stage n)
  phase : ∀ n, PhaseStructure (Stage n)
  bond : ∀ n, Stage n →L[ℝ] Stage (n + 1)
  bond_phase : ∀ n, (bond n).comp (phase n).K = (phase (n + 1)).K.comp (bond n)
  Limit : Type u
  limitNormedAddCommGroup : NormedAddCommGroup Limit
  limitNormedSpace : NormedSpace ℝ Limit
  limitPhase : PhaseStructure Limit
  ι : ∀ n, Stage n →L[ℝ] Limit
  ι_phase : ∀ n, (ι n).comp (phase n).K = limitPhase.K.comp (ι n)
  ι_bond : ∀ n, (ι (n + 1)).comp (bond n) = ι n

attribute [instance] FilteredPhaseCone.stageNormedAddCommGroup
attribute [instance] FilteredPhaseCone.stageNormedSpace
attribute [instance] FilteredPhaseCone.limitNormedAddCommGroup
attribute [instance] FilteredPhaseCone.limitNormedSpace

namespace FilteredPhaseCone

variable (C : FilteredPhaseCone)

/-- Every bonding map is phase-linear. -/
theorem bond_isPhaseLinearMap (n : ℕ) :
    (C.phase n).IsPhaseLinearMap (C.bond n) (C.phase (n + 1)) :=
  C.bond_phase n

/-- Every canonical stage map into the cone carrier is phase-linear. -/
theorem include_isPhaseLinearMap (n : ℕ) :
    (C.phase n).IsPhaseLinearMap (C.ι n) C.limitPhase :=
  C.ι_phase n

/-- A bonding map is Cauchy-analytic at every point, with derivative equal to
the bonding map itself. -/
def bondCauchyAnalyticAt (n : ℕ) (x : C.Stage n) :
    CauchyAnalyticAt (C.phase n) (C.phase (n + 1))
      (fun y => C.bond n y) x :=
  CauchyAnalyticAt.ofContinuousLinearMap
    (C.phase n) (C.phase (n + 1)) (C.bond n) (C.bond_phase n) x

@[simp] theorem bondCauchyAnalyticAt_deriv (n : ℕ) (x : C.Stage n) :
    (C.bondCauchyAnalyticAt n x).deriv = C.bond n :=
  rfl

/-- A canonical stage map into the normed cone carrier is Cauchy-analytic at
every point, with derivative equal to the canonical map itself. -/
def includeCauchyAnalyticAt (n : ℕ) (x : C.Stage n) :
    CauchyAnalyticAt (C.phase n) C.limitPhase
      (fun y => C.ι n y) x :=
  CauchyAnalyticAt.ofContinuousLinearMap
    (C.phase n) C.limitPhase (C.ι n) (C.ι_phase n) x

@[simp] theorem includeCauchyAnalyticAt_deriv (n : ℕ) (x : C.Stage n) :
    (C.includeCauchyAnalyticAt n x).deriv = C.ι n :=
  rfl

/-- The composite of one bonding map with the next stage's canonical map is
Cauchy-analytic by the phase-form chain rule. -/
def includeAfterBondCauchyAnalyticAt (n : ℕ) (x : C.Stage n) :
    CauchyAnalyticAt (C.phase n) C.limitPhase
      (fun y => C.ι (n + 1) (C.bond n y)) x :=
  CauchyAnalyticAt.comp
    (C.bondCauchyAnalyticAt n x)
    (C.includeCauchyAnalyticAt (n + 1) (C.bond n x))

/-- The derivative transported through one filtered bonding step is exactly
the original canonical stage map. -/
theorem includeAfterBond_deriv_eq_include (n : ℕ) (x : C.Stage n) :
    (C.includeAfterBondCauchyAnalyticAt n x).deriv = C.ι n := by
  change (C.ι (n + 1)).comp (C.bond n) = C.ι n
  exact C.ι_bond n

/-- Pointwise compatibility of the filtered cone. -/
theorem include_bond_apply (n : ℕ) (x : C.Stage n) :
    C.ι (n + 1) (C.bond n x) = C.ι n x := by
  have h := congrArg (fun L : C.Stage n →L[ℝ] C.Limit => L x) (C.ι_bond n)
  simpa [ContinuousLinearMap.comp_apply] using h

/-- The Cauchy-Riemann law for a stage representative is independent of
whether it is read directly or after one filtered bonding step. -/
theorem filtered_cauchyRiemann_compatibility
    (n : ℕ) (x v : C.Stage n) :
    (C.includeAfterBondCauchyAnalyticAt n x).deriv ((C.phase n).K v) =
      C.limitPhase.K ((C.ι n) v) := by
  rw [C.includeAfterBond_deriv_eq_include n x]
  exact (C.includeCauchyAnalyticAt n x).cauchyRiemann_apply v

/-- A phase-linear finite-stage observable remains phase-linear after
composition with the canonical map into the filtered cone carrier. -/
theorem include_comp_phaseLinear
    {n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (KY : PhaseStructure Y) (L : Y →L[ℝ] C.Stage n)
    (hL : KY.IsPhaseLinearMap L (C.phase n)) :
    KY.IsPhaseLinearMap ((C.ι n).comp L) C.limitPhase :=
  PhaseStructure.comp_phaseLinear KY (C.phase n) C.limitPhase
    hL (C.include_isPhaseLinearMap n)

end FilteredPhaseCone

end InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
