import InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity

namespace InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity.FilteredPhaseCone

variable (C : FilteredPhaseCone)

/-- Composite bonding map from stage `n` to stage `n + m`. -/
def bondIterate (C : FilteredPhaseCone) (n : ℕ) :
    ∀ m : ℕ, C.Stage n →L[ℝ] C.Stage (n + m)
  | 0 => ContinuousLinearMap.id ℝ (C.Stage n)
  | m + 1 => (C.bond (n + m)).comp (bondIterate C n m)

@[simp] theorem bondIterate_zero (n : ℕ) :
    C.bondIterate n 0 = ContinuousLinearMap.id ℝ (C.Stage n) :=
  rfl

@[simp] theorem bondIterate_succ (n m : ℕ) :
    C.bondIterate n (m + 1) =
      (C.bond (n + m)).comp (C.bondIterate n m) :=
  rfl

/-- Iterated bonding maps preserve the filtered phase structure. -/
theorem bondIterate_phaseLinear (n : ℕ) :
    ∀ m : ℕ,
      (C.phase n).IsPhaseLinearMap
        (C.bondIterate n m) (C.phase (n + m))
  | 0 => by
      simpa using PhaseStructure.id_phaseLinear (C.phase n)
  | m + 1 => by
      simpa using
        PhaseStructure.comp_phaseLinear
          (C.phase n) (C.phase (n + m)) (C.phase (n + (m + 1)))
          (bondIterate_phaseLinear n m)
          (by
            simpa [Nat.add_assoc] using C.bond_isPhaseLinearMap (n + m))

/-- The canonical cone map after any finite number of transitions equals the
canonical map from the original stage. -/
theorem ι_comp_bondIterate (n : ℕ) :
    ∀ m : ℕ, (C.ι (n + m)).comp (C.bondIterate n m) = C.ι n
  | 0 => by
      simp
  | m + 1 => by
      change
        (C.ι ((n + m) + 1)).comp
          ((C.bond (n + m)).comp (C.bondIterate n m)) = C.ι n
      rw [← ContinuousLinearMap.comp_assoc]
      rw [C.ι_bond (n + m)]
      exact ι_comp_bondIterate n m

/-- Pointwise form of arbitrary-length cone compatibility. -/
theorem ι_bondIterate_apply
    (n m : ℕ) (x : C.Stage n) :
    C.ι (n + m) (C.bondIterate n m x) = C.ι n x := by
  have h := congrArg
    (fun L : C.Stage n →L[ℝ] C.Limit => L x)
    (ι_comp_bondIterate C n m)
  simpa [ContinuousLinearMap.comp_apply] using h

/-- Every iterated filtered transition is Cauchy-analytic. -/
def bondIterateCauchyAnalyticAt
    (n m : ℕ) (x : C.Stage n) :
    CauchyAnalyticAt
      (C.phase n) (C.phase (n + m))
      (fun y => C.bondIterate n m y) x :=
  CauchyAnalyticAt.ofContinuousLinearMap
    (C.phase n) (C.phase (n + m))
    (C.bondIterate n m)
    (bondIterate_phaseLinear C n m)
    x

@[simp] theorem bondIterateCauchyAnalyticAt_deriv
    (n m : ℕ) (x : C.Stage n) :
    (C.bondIterateCauchyAnalyticAt n m x).deriv =
      C.bondIterate n m :=
  rfl

/-- Reading an iterated representative in the colimit carrier is
Cauchy-analytic with derivative equal to the original canonical stage map. -/
def iteratedReadoutCauchyAnalyticAt
    (n m : ℕ) (x : C.Stage n) :
    CauchyAnalyticAt
      (C.phase n) C.limitPhase
      (fun y => C.ι (n + m) (C.bondIterate n m y)) x :=
  CauchyAnalyticAt.comp
    (C.bondIterateCauchyAnalyticAt n m x)
    (C.includeCauchyAnalyticAt (n + m) (C.bondIterate n m x))

/-- The derivative of the arbitrary-stage colimit readout is independent of
the chosen later representative. -/
theorem iteratedReadout_deriv_eq_ι
    (n m : ℕ) (x : C.Stage n) :
    (C.iteratedReadoutCauchyAnalyticAt n m x).deriv = C.ι n := by
  change (C.ι (n + m)).comp (C.bondIterate n m) = C.ι n
  exact ι_comp_bondIterate C n m

/-- Arbitrary-length filtered transport preserves the Cauchy--Riemann law in
the colimit phase space. -/
theorem iteratedReadout_cauchyRiemann
    (n m : ℕ) (x v : C.Stage n) :
    (C.iteratedReadoutCauchyAnalyticAt n m x).deriv ((C.phase n).K v) =
      C.limitPhase.K (C.ι n v) := by
  rw [C.iteratedReadout_deriv_eq_ι n m x]
  exact (C.includeCauchyAnalyticAt n x).cauchyRiemann_apply v

end InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity.FilteredPhaseCone
