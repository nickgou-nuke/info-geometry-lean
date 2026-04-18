import InfoGeometry.LLM.TrialityMoE
import InfoGeometry.Canonical.WindingOrbitClosure
import InfoGeometry.Canonical.SinkhornFoundation

/-!
# Sinkhorn Defect Flow Owner Surface

Owner-level defect flow surface for Sinkhorn-side router updates.
Primary defect is the relative-volume (Radon-Nikodym barrier) trajectory; the
odd-sector norm channel is kept as a derived router readout.
This module intentionally avoids interpretation language and exposes only
operator inequalities on the defect budget.
-/

namespace InfoGeometry.LLM.SinkhornDefectFlow

open InfoGeometry.LLM.TrialityMoE

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Odd-sector defect functional attached to a bounded router residual. -/
noncomputable def δ_odd (B : RouterDefectBoundBridge (E := E)) : ℝ :=
  ‖B.routerResidual‖

/-- Equilibrium condition: odd-sector defect functional vanishes. -/
def IsRouterEquilibrium (B : RouterDefectBoundBridge (E := E)) : Prop :=
  δ_odd B = 0

theorem δ_odd_nonneg (B : RouterDefectBoundBridge (E := E)) :
    0 ≤ δ_odd B := by
  unfold δ_odd
  exact norm_nonneg B.routerResidual

theorem δ_odd_le_ZD (B : RouterDefectBoundBridge (E := E)) :
    δ_odd B ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD B.CIK‖ := by
  simpa [δ_odd] using B.residual_norm_le_ZD

/-- `δ_odd = 0` is exactly residual equilibrium. -/
theorem δ_odd_eq_zero_iff_equilibrium (B : RouterDefectBoundBridge (E := E)) :
    δ_odd B = 0 ↔ IsRouterEquilibrium B := by
  rfl

theorem equilibrium_of_δ_odd_eq_zero
    (B : RouterDefectBoundBridge (E := E))
    (hδ : δ_odd B = 0) :
    IsRouterEquilibrium B := hδ

/-- The sourced-generator deviation is exactly `δ_odd`. -/
theorem sourcedGenerator_deviation_eq_δ_odd
    (B : RouterDefectBoundBridge (E := E)) :
    ‖B.sourcedGenerator - B.flow.K0‖ = δ_odd B := by
  unfold InfoGeometry.LLM.TrialityMoE.RouterDefectBoundBridge.sourcedGenerator δ_odd
  simp [sub_eq_add_neg, add_assoc]

/--
One-step Sinkhorn update wrapper carrying monotone defect reduction as an owner
obligation.
-/
structure SinkhornDefectStep (B : RouterDefectBoundBridge (E := E)) where
  next : RouterDefectBoundBridge (E := E)
  δ_odd_next_le_δ_odd : δ_odd next ≤ δ_odd B

theorem δ_odd_next_le_δ_odd
    {B : RouterDefectBoundBridge (E := E)}
    (step : SinkhornDefectStep B) :
    δ_odd step.next ≤ δ_odd B :=
  step.δ_odd_next_le_δ_odd

theorem sourcedGenerator_deviation_next_le
    {B : RouterDefectBoundBridge (E := E)}
    (step : SinkhornDefectStep B) :
    ‖step.next.sourcedGenerator - step.next.flow.K0‖ ≤ ‖B.sourcedGenerator - B.flow.K0‖ := by
  rw [sourcedGenerator_deviation_eq_δ_odd step.next,
    sourcedGenerator_deviation_eq_δ_odd B]
  exact step.δ_odd_next_le_δ_odd

/--
Owner bridge from LLM residual budget to the non-equilibrium clock-defect lane.
-/
structure RouterClockDefectBridge where
  bound : RouterDefectBoundBridge (E := E)
  hMod : EndH
  residual_eq_clockDefect :
    bound.routerResidual =
      InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) hMod

/--
On the clock-defect bridge, odd-sector defect is exactly the non-equilibrium
clock-defect norm.
-/
theorem δ_odd_eq_clockDefect_norm
    (B : RouterClockDefectBridge (E := E)) :
    δ_odd B.bound =
      ‖InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) B.hMod‖ := by
  simp [δ_odd, B.residual_eq_clockDefect]

/--
Detailed equilibrium (`scalePart = 0`) forces vanishing odd-sector defect on
the clock-defect bridge.
-/
theorem δ_odd_eq_zero_of_detailedEquilibrium
    (B : RouterClockDefectBridge (E := E))
    (hEq : InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) B.hMod) :
    δ_odd B.bound = 0 := by
  rw [δ_odd_eq_clockDefect_norm (E := E) B]
  have hZero :
      InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) B.hMod = 0 :=
    InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect_eq_zero_of_detailedEquilibrium
      (H := E) B.hMod hEq
  rw [hZero]
  exact ContinuousLinearMap.opNorm_zero

/--
Detailed equilibrium implies router-equilibrium on the clock-defect bridge.
-/
theorem router_equilibrium_of_detailedEquilibrium
    (B : RouterClockDefectBridge (E := E))
    (hEq : InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) B.hMod) :
    IsRouterEquilibrium B.bound := by
  exact equilibrium_of_δ_odd_eq_zero (E := E) B.bound
    (δ_odd_eq_zero_of_detailedEquilibrium (E := E) B hEq)

/--
Positive odd-sector defect implies noncommuting scale lane on the same
clock-defect bridge.
-/
theorem noncommutingScaleLane_of_δ_odd_pos
    (B : RouterClockDefectBridge (E := E))
    (hδ : 0 < δ_odd B.bound) :
    InfoGeometry.Canonical.WindingOrbitClosure.IsNoncommutingScaleLane (H := E) B.hMod := by
  unfold InfoGeometry.Canonical.WindingOrbitClosure.IsNoncommutingScaleLane
  intro hZero
  have hδZero : δ_odd B.bound = 0 := by
    rw [δ_odd_eq_clockDefect_norm (E := E) B]
    rw [hZero]
    exact ContinuousLinearMap.opNorm_zero
  exact (ne_of_gt hδ) hδZero

/--
Positive odd-sector defect excludes detailed equilibrium on the same
clock-defect bridge.
-/
theorem not_detailedEquilibrium_of_δ_odd_pos
    (B : RouterClockDefectBridge (E := E))
    (hδ : 0 < δ_odd B.bound) :
    ¬ InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) B.hMod := by
  exact InfoGeometry.Canonical.WindingOrbitClosure.not_detailedEquilibrium_of_noncommutingScaleLane
    (H := E) B.hMod
    (noncommutingScaleLane_of_δ_odd_pos (E := E) B hδ)

/--
Executable Sinkhorn defect-reduction update operator.
-/
structure SinkhornDefectUpdate where
  map : RouterDefectBoundBridge (E := E) → RouterDefectBoundBridge (E := E)
  δ_odd_map_le : ∀ B : RouterDefectBoundBridge (E := E), δ_odd (map B) ≤ δ_odd B

/--
`n`-step iteration of a Sinkhorn defect-reduction update.
-/
def iterate
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    RouterDefectBoundBridge (E := E) :=
  Nat.rec B0 (fun _ B => U.map B) n

@[simp] theorem iterate_zero
    (U : SinkhornDefectUpdate (E := E))
    (B0 : RouterDefectBoundBridge (E := E)) :
    iterate (E := E) U 0 B0 = B0 := rfl

@[simp] theorem iterate_succ
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    iterate (E := E) U (n + 1) B0 = U.map (iterate (E := E) U n B0) := by
  rfl

/--
One-step monotone defect reduction along the executable iterator.
-/
theorem δ_odd_iterate_succ_le_iterate
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    δ_odd (iterate (E := E) U (n + 1) B0) ≤ δ_odd (iterate (E := E) U n B0) := by
  simpa [iterate_succ] using U.δ_odd_map_le (iterate (E := E) U n B0)

/--
Defect budget is globally bounded by the initial state along the executable
Sinkhorn iterator.
-/
theorem δ_odd_iterate_le_initial
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    δ_odd (iterate (E := E) U n B0) ≤ δ_odd B0 := by
  induction n with
  | zero =>
      simp [iterate_zero]
  | succ n ih =>
      exact le_trans (δ_odd_iterate_succ_le_iterate (E := E) U n B0) ih

/--
One-step sourced-generator deviation monotonicity along the executable iterator.
-/
theorem sourcedGenerator_deviation_iterate_succ_le_iterate
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    ‖(iterate (E := E) U (n + 1) B0).sourcedGenerator - (iterate (E := E) U (n + 1) B0).flow.K0‖
      ≤
    ‖(iterate (E := E) U n B0).sourcedGenerator - (iterate (E := E) U n B0).flow.K0‖ := by
  rw [sourcedGenerator_deviation_eq_δ_odd (E := E) (iterate (E := E) U (n + 1) B0),
    sourcedGenerator_deviation_eq_δ_odd (E := E) (iterate (E := E) U n B0)]
  exact δ_odd_iterate_succ_le_iterate (E := E) U n B0

/--
Global sourced-generator deviation bound by the initial state.
-/
theorem sourcedGenerator_deviation_iterate_le_initial
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    ‖(iterate (E := E) U n B0).sourcedGenerator - (iterate (E := E) U n B0).flow.K0‖
      ≤
    ‖B0.sourcedGenerator - B0.flow.K0‖ := by
  rw [sourcedGenerator_deviation_eq_δ_odd (E := E) (iterate (E := E) U n B0),
    sourcedGenerator_deviation_eq_δ_odd (E := E) B0]
  exact δ_odd_iterate_le_initial (E := E) U n B0

section VolumeAnomaly

open InfoGeometry.Canonical.MoE

/--
Primary relative-volume defect functional on a Sinkhorn trajectory:
the phase-aligned Radon-Nikodym barrier before step `k`.
-/
noncomputable def δ_relVol
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) : ℝ :=
  trajectoryRNBarrier n T k

/--
Backward-compatible name for `δ_relVol`.
-/
noncomputable def δ_volume
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) : ℝ :=
  δ_relVol n T k

@[simp] theorem δ_volume_eq_δ_relVol
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    δ_volume n T k = δ_relVol n T k := rfl

theorem δ_relVol_nonneg
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    0 ≤ δ_relVol n T k := by
  unfold δ_relVol trajectoryRNBarrier
  exact phaseRNBarrierBefore_nonneg (n := n) (phaseAt k) (T.state k)

theorem δ_volume_nonneg
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    0 ≤ δ_volume n T k := by
  simpa [δ_volume_eq_δ_relVol] using δ_relVol_nonneg (n := n) T k

theorem δ_relVol_next_le
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    trajectoryRNBarrierNext n T k ≤ δ_relVol n T k := by
  simpa [δ_relVol] using trajectoryRNBarrier_monotone (n := n) T k

theorem δ_volume_next_le
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    trajectoryRNBarrierNext n T k ≤ δ_volume n T k := by
  simpa [δ_volume_eq_δ_relVol] using δ_relVol_next_le (n := n) T k

/--
Bridge from Sinkhorn relative-volume anomaly to the router odd-defect lane.
This is the owner surface for volume-driven defect reduction.
-/
structure SinkhornVolumeAnomalyBridge (n : Nat) where
  T : SinkhornTrajectory n
  state : Nat → RouterDefectBoundBridge (E := E)
  next_le_volumeNext :
    ∀ k : Nat, δ_odd (state (k + 1)) ≤ trajectoryRNBarrierNext n T k
  volume_le_now :
    ∀ k : Nat, trajectoryRNBarrier n T k ≤ δ_odd (state k)

/--
Primary-name alias: relative-defect bridge driven by trajectory RN barriers.
-/
abbrev SinkhornRelativeDefectBridge (n : Nat) :=
  SinkhornVolumeAnomalyBridge (E := E) n

/--
Volume anomaly monotonicity forces one-step odd-defect monotonicity.
-/
theorem δ_odd_next_le_of_relativeDefectBridge
    {n : Nat}
    (B : SinkhornRelativeDefectBridge (E := E) n)
    (k : Nat) :
    δ_odd (B.state (k + 1)) ≤ δ_odd (B.state k) := by
  exact le_trans (B.next_le_volumeNext k)
    (le_trans (trajectoryRNBarrier_monotone (n := n) B.T k) (B.volume_le_now k))

/--
Backward-compatible theorem name for relative-defect one-step reduction.
-/
theorem δ_odd_next_le_of_volumeAnomalyBridge
    {n : Nat}
    (B : SinkhornVolumeAnomalyBridge (E := E) n)
    (k : Nat) :
    δ_odd (B.state (k + 1)) ≤ δ_odd (B.state k) :=
  δ_odd_next_le_of_relativeDefectBridge (E := E) B k

end VolumeAnomaly

end InfoGeometry.LLM.SinkhornDefectFlow
