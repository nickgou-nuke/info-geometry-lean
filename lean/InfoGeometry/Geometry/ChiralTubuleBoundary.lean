/-
InfoGeometry/Geometry/ChiralTubuleBoundary.lean

Bregman Hessian degeneracy and chiral tubule transition boundary.

This file defines the formal boundary where a regular Bregman/Legendre geometry
loses Hessian invertibility and a chiral phase separation witness appears.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.Geometry.ChiralTubuleBoundary

/-! ## 1. Bregman Hessian and dual-flat geometry -/

/--
Bregman Hessian data.

`isInvertibleAt U` is the regularity predicate for the Legendre/Fisher Hessian.
The concrete Hessian operator is stored abstractly.
-/
structure BregmanHessianDatum
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] where
  hessian : Op → Op →L[ℝ] Op
  isInvertibleAt : Op → Prop

/--
The topological snap boundary is the locus where the Hessian ceases to be
invertible.
-/
def IsTopologicalSnapBoundary
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (H : BregmanHessianDatum Op)
    (U : Op) : Prop :=
  ¬ H.isInvertibleAt U

/--
Dual-flat operator geometry.

`nablaExp` and `nablaMix` represent the exponential and mixture connections.
Their difference is the Amari-Chentsov shear/torsion readout.
-/
structure DualFlatOperatorGeometry
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] where
  nablaExp : Op → Op →L[ℝ] Op
  nablaMix : Op → Op →L[ℝ] Op

  levi_civita_balance_law : Prop
  levi_civita_balance_certificate : levi_civita_balance_law

/-- Amari-Chentsov shear operator. -/
def torsionShear
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (G : DualFlatOperatorGeometry Op)
    (U : Op) : Op →L[ℝ] Op :=
  G.nablaExp U - G.nablaMix U

/-- Real-valued shear magnitude. -/
def shearMagnitude
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (G : DualFlatOperatorGeometry Op)
    (U : Op) : ℝ :=
  ‖torsionShear G U‖

/--
Threshold version of extreme shear.

This replaces literal infinity claims in a real-valued normed setting.
-/
def IsExtremeShear
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (G : DualFlatOperatorGeometry Op)
    (threshold : ℝ)
    (U : Op) : Prop :=
  threshold ≤ shearMagnitude G U

/-! ## 2. Chiral tubule crystallization -/

/--
A chiral tubule crystallization witness.

At a snap boundary, the previously connected regular phase is represented by
two disjoint chiral support regions.
-/
structure ChiralTubuleCrystallization
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (H : BregmanHessianDatum Op) where
  boundaryState : Op
  is_snap :
    IsTopologicalSnapBoundary H boundaryState

  phaseR : Set Op
  phaseL : Set Op

  phase_disjoint :
    Disjoint phaseR phaseL

  exponential_connection_trapped_in_R_law : Prop
  exponential_connection_trapped_in_R_certificate :
    exponential_connection_trapped_in_R_law

  mixture_connection_trapped_in_L_law : Prop
  mixture_connection_trapped_in_L_certificate :
    mixture_connection_trapped_in_L_law

  PT_inversion_boundary_calibration_law : Prop
  PT_inversion_boundary_calibration_certificate :
    PT_inversion_boundary_calibration_law

namespace ChiralTubuleCrystallization

variable
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {H : BregmanHessianDatum Op}

/-- The two chiral phases are disjoint. -/
theorem disjoint_phases
    (C : ChiralTubuleCrystallization Op H) :
    Disjoint C.phaseR C.phaseL :=
  C.phase_disjoint

end ChiralTubuleCrystallization

/-! ## 3. Transition law -/

/--
Transition law saying that extreme shear forces a snap/crystallization.

This is a physical/geometric bridge witness, not a theorem derivable from the
abstract Hessian data alone.
-/
structure ChiralTubuleTransitionLaw
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (H : BregmanHessianDatum Op)
    (G : DualFlatOperatorGeometry Op) where
  threshold : ℝ
  threshold_nonneg : 0 ≤ threshold

  extreme_shear_forces_crystallization :
    ∀ U : Op,
      IsExtremeShear G threshold U →
        ∃ C : ChiralTubuleCrystallization Op H,
          C.boundaryState = U

namespace ChiralTubuleTransitionLaw

variable
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    {H : BregmanHessianDatum Op}
    {G : DualFlatOperatorGeometry Op}

/--
Extreme Bregman shear yields a chiral tubule crystallization once the transition
law is supplied.
-/
theorem extreme_flux_implies_crystallization
    (L : ChiralTubuleTransitionLaw Op H G)
    (U : Op)
    (hU : IsExtremeShear G L.threshold U) :
    ∃ C : ChiralTubuleCrystallization Op H,
      C.boundaryState = U :=
  L.extreme_shear_forces_crystallization U hU

end ChiralTubuleTransitionLaw

/-! ## 4. Owner target -/

/--
Owner target for the chiral tubule boundary.

It is intentionally witness-gated by a transition law.
-/
def ChiralTubuleBoundaryOwnerTarget : Prop :=
  ∀ (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op],
  ∀ H : BregmanHessianDatum Op,
  ∀ G : DualFlatOperatorGeometry Op,
  ∀ L : ChiralTubuleTransitionLaw Op H G,
  ∀ U : Op,
    IsExtremeShear G L.threshold U →
      ∃ C : ChiralTubuleCrystallization Op H,
        C.boundaryState = U

/-- The owner target follows directly from the supplied transition law. -/
theorem chiralTubuleBoundaryOwnerTarget :
    ChiralTubuleBoundaryOwnerTarget := by
  intro Op _ _ H G L U hU
  exact L.extreme_flux_implies_crystallization U hU

end InfoGeometry.Geometry.ChiralTubuleBoundary
