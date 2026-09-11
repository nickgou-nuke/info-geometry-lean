import InfoGeometry.Canonical.ConnesArakiCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ModularWeldBridge
import InfoGeometry.Canonical.TomitaTakesaki

/-!
# InfoGeometry.Canonical.ConnesArakiTomita

Tomita-specialized Connes-Araki endpoints over the generic core carrier.

This lane is owner-facing and diagnostic-oriented: it reuses the generic
Connes-Araki core plus the Tomita flow-unit cocycle witness, while keeping the
finite diagonal branch as a readout/diagnostic projection.

The finite diagonal outputs are explicit shadow diagnostics induced by chosen
coordinate frames; they are not treated as primitive noncommutative content.

In particular, diagonal identities in this file are projection-only witnesses and
must be consumed as readout channels, never as owner-level noncommutative
evidence.
-/

namespace InfoGeometry.Canonical.ConnesArakiFramework

open InfoGeometry.Volume.ConnesCocycle
open InfoGeometry.Canonical.BekensteinBound
open InfoGeometry.Canonical.MongeAmpereCramerRao
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularOperator

variable {n : Nat}
variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section TomitaSpecialization

variable {u : ℝ → AlgebraEnd H}
variable {T : SinkhornTrajectory n}

/--
Tomita-specialized Connes-Araki package using the canonical modular-sign flow.
-/
abbrev TomitaConnesArakiData
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n) :=
  ConnesArakiData (H := H)
    (σ := TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
    u T

/-- Tomita-specialized Connes-Araki package on the canonical unit cocycle lane. -/
abbrev TomitaUnitConnesArakiData
    (T : SinkhornTrajectory n) :=
  TomitaConnesArakiData (H := H)
    (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
      (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    T

/--
Canonical constructor on the Tomita unit-cocycle lane, implemented as the
specialization of the generic `ConnesArakiData.ofUnitCocycle`.

`tomitaUnitConnesArakiDataOfCasini'` keeps the dependency on the core lane
constructor explicit.
-/
noncomputable def tomitaUnitConnesArakiDataOfCasini'
    (T : SinkhornTrajectory n)
    (relEnt : ArakiRelativeEntropyProfile)
    (hCasini : CasiniIncrementBridge
      (n := n) (H := H)
      (TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
      (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
      T
      relEnt) :
    TomitaUnitConnesArakiData (H := H) T :=
  ConnesArakiData.ofUnitCocycle
    (H := H)
    (σ := TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
    (T := T)
    relEnt
    hCasini

/--
Backward-compatible constructor name.
-/
noncomputable def tomitaUnitConnesArakiDataOfCasini
    (T : SinkhornTrajectory n)
    (relEnt : ArakiRelativeEntropyProfile)
    (hCasini : CasiniIncrementBridge
      (n := n) (H := H)
      (TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
      (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
      T
      relEnt) :
    TomitaUnitConnesArakiData (H := H) T :=
  tomitaUnitConnesArakiDataOfCasini'
    (H := H) (T := T) relEnt hCasini

/-- Diagnostic bridge into the finite diagonal lane:
this statement is a shadow/readout alias, not an owner identity, for Tomita endpoints. -/
theorem tomitaFiniteDiagonalLane_shadow_alias
    (q q0 : PositiveRay (Fin n)) [Nonempty (Fin n)] :
    InfoGeometry.Canonical.RelativeModularOperator.relativeModularOperator
        (n := n) q q0 =
      NormedSpace.exp
        (InfoGeometry.Canonical.ModularWeldBridge.relativeLogDensityOperator
          (n := n) q q0) := by
  simpa using
    (InfoGeometry.Canonical.ModularWeldBridge.finiteDiagonalShadowLane (n := n) q q0)

/-- Diagnostic marker that the finite diagonal readout remains a projection channel. -/
theorem tomitaFiniteDiagonalLane_shadow_marker
    (q q0 : PositiveRay (Fin n)) [Nonempty (Fin n)] :
    InfoGeometry.Canonical.RelativeModularOperator.relativeModularOperator
        (n := n) q q0 =
      NormedSpace.exp
        (InfoGeometry.Canonical.ModularWeldBridge.relativeLogDensityOperator
          (n := n) q q0) := by
  simpa using tomitaFiniteDiagonalLane_shadow_alias (n := n) (q := q) (q0 := q0)

/-- Diagnostic ownership boundary:
this is an explicit finite-frame projection alias for Tomita endpoints. -/
theorem tomitaFiniteDiagonalLane_shadow_projection_only
    (q q0 : PositiveRay (Fin n)) [Nonempty (Fin n)] :
    InfoGeometry.Canonical.RelativeModularOperator.relativeModularOperator
        (n := n) q q0 =
      NormedSpace.exp
        (InfoGeometry.Canonical.ModularWeldBridge.relativeLogDensityOperator
          (n := n) q q0) := by
  simpa using tomitaFiniteDiagonalLane_shadow_marker (n := n) (q := q) (q0 := q0)

/-- Projection-only naming for downstream operators: finite diagonal remains readout. -/
theorem tomitaFiniteDiagonalLane_shadow_projection_channel
    (q q0 : PositiveRay (Fin n)) [Nonempty (Fin n)] :
    InfoGeometry.Canonical.RelativeModularOperator.relativeModularOperator
        (n := n) q q0 =
      NormedSpace.exp
        (InfoGeometry.Canonical.ModularWeldBridge.relativeLogDensityOperator
          (n := n) q q0) := by
  simpa using tomitaFiniteDiagonalLane_shadow_projection_only
    (n := n) (q := q) (q0 := q0)

/-! ### Tomita unit-cocycle API surface

These lemmas expose the welded Tomita flow-unit cocycle directly through the
Connes-Araki Tomita specialization.  They are theorem-only extensions:
no new carrier fields, no new assumptions on `TomitaUnitConnesArakiData`.

Conceptually, these are observer/readout lemmas: flow-unit evaluations are fixed to
the operator unit and are used as thin diagnostics on top of the underlying
non-commutative operator lane.
-/

/-- The Tomita modular-sign flow fixes the algebra unit. -/
@[simp] theorem tomita_modularSignAdditiveModularFlow_map_one
    (t : ℝ) :
    TomitaTakesaki.modularSignAdditiveModularFlow
        (E := H) t (1 : AlgebraEnd H) = 1 := by
  simpa [InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle]
    using
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_eq_one
        (H := H) (σ := TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) t)

/-- The Tomita flow-unit cocycle is pointwise the operator unit. -/
@[simp] theorem tomitaUnitConnesAraki_flowUnitCocycle_apply
    (t : ℝ) :
    InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) t
      =
    (1 : AlgebraEnd H) := by
  simpa [InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle]
    using
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_eq_one
        (H := H) (σ := TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) t)

/-- Time-zero normalization of the Tomita unit cocycle on the Connes-Araki lane. -/
@[simp] theorem tomitaUnitConnesAraki_flowUnitCocycle_zero
    :
  InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) 0
      =
    (1 : AlgebraEnd H) := by
  simp

/-- Tomita unit-cocycle at fixed time is operator unit. -/
@[simp] theorem tomitaUnitConnesAraki_flowUnitCocycle_one
    (t : ℝ) :
    InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) t
      =
    (1 : AlgebraEnd H) := by
  simpa using (tomitaUnitConnesAraki_flowUnitCocycle_apply (H := H) t)

/-- Thin alias in Connes-Araki naming: Tomita flow-unit cocycle is identically unit. -/
@[simp] theorem tomitaUnit_connesAraki_flowUnitCocycle_eq_one
    (t : ℝ) :
    InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
      (H := H)
      (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) t
      =
    (1 : AlgebraEnd H) := by
  simpa using (tomitaUnitConnesAraki_flowUnitCocycle_apply (H := H) t)

/-- Diagnostic alias: Tomita flow-unit cocycle is the shadow unit across Connes-Araki lanes. -/
@[simp] theorem tomitaUnitConnesAraki_flowUnitCocycle_shadow_eq_one
    (t : ℝ) :
    InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
      (H := H)
      (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) t
      =
    (1 : AlgebraEnd H) := by
  simpa using (tomitaUnitConnesAraki_flowUnitCocycle_apply (H := H) t)

/-- Diagnostic readout alias: the shadow unit cocycle is the unit for each time slice. -/
theorem tomitaUnitConnesAraki_flowUnitCocycle_shadow_readout_eq_one
    (t : ℝ) :
    InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
      (H := H)
      (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) t
      =
    (1 : AlgebraEnd H) := by
  simpa using (tomitaUnitConnesAraki_flowUnitCocycle_shadow_eq_one (H := H) t)

/-- Canonical Connes-cocycle witness for the Tomita flow-unit lane. -/
theorem tomitaUnitConnesAraki_flowUnitCocycle_cocycle :
    IsConnesCocycle
      (TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H))) := by
  simpa using
    (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_isConnesCocycle
      (H := H) (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))

/-- Thin owner-facing alias: Tomita flow-unit cocycle is an operator-valued Connes cocycle. -/
theorem tomitaUnit_connesAraki_flowUnitCocycle_isConnesCocycle :
    IsConnesCocycle
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow
        (E := H))
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow
          (E := H))) := by
  simpa using
    (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_isConnesCocycle
      (H := H) (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))

/-- Tomita-unit cocycle satisfies the Connes cocycle equation pointwise. -/
theorem tomitaUnitConnesAraki_flowUnitCocycle_eq
    (s t : ℝ) :
    InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) (s + t)
      =
    InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) s *
    TomitaTakesaki.modularSignAdditiveModularFlow (E := H)
      s
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) t) := by
  exact
    (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_cocycle
      (H := H)
      (σ := TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) s t)

/-- Diagnostic alias of the pointwise Connes-cocycle equation for shadow-transport. -/
theorem tomitaUnitConnesAraki_flowUnitCocycle_shadow_eq
    (s t : ℝ) :
    InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) (s + t)
      =
    InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) s *
    TomitaTakesaki.modularSignAdditiveModularFlow (E := H)
      s
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) t) := by
  exact
    (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_cocycle
      (H := H)
      (σ := TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) s t)

/-- Shadow readout alias of the Connes-cocycle transport identity. -/
theorem tomitaUnitConnesAraki_flowUnitCocycle_shadow_transport_eq
    (s t : ℝ) :
    InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) (s + t)
      =
    InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) s *
    TomitaTakesaki.modularSignAdditiveModularFlow (E := H)
      s
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) t) := by
  exact
    (tomitaUnitConnesAraki_flowUnitCocycle_shadow_eq
      (H := H) (s := s) (t := t))

/-- Diagnostic ownership alias: Tomita flow-unit shadow cocycle is a Connes-cocycle. -/
theorem tomitaUnitConnesAraki_flowUnitCocycle_shadow_isConnesCocycle :
    IsConnesCocycle
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow
        (E := H))
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
        (H := H)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow
          (E := H))) := by
  simpa using
    (tomitaUnitConnesAraki_flowUnitCocycle_cocycle
      (H := H))

/--
For any Tomita unit-cocycle Connes-Araki package, scalar descent of the
operator unit cocycle is the scalar unit.

This holds for arbitrary `D.bridge`: we only use multiplicativity of
`D.bridge.toScalar`.
-/
@[simp] theorem tomitaUnitConnesArakiData_scalarCocycle_eq_one
    (D : TomitaUnitConnesArakiData (H := H) T)
    (t : ℝ) :
    scalarCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (H := H)
          (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        D.bridge t
      =
    (1 : ℝˣ) := by
  rw [scalarCocycle, tomitaUnitConnesAraki_flowUnitCocycle_apply (H := H) t]
  simp

/--
The logarithmic scalar cocycle potential vanishes identically on the Tomita
unit-cocycle lane.
-/
theorem tomitaUnitConnesArakiData_cocycleLogPotential_eq_zero
    (D : TomitaUnitConnesArakiData (H := H) T)
    (t : ℝ) :
    cocycleLogPotential
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (H := H)
            (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        D.bridge t
      =
    0 := by
  unfold cocycleLogPotential
  rw [tomitaUnitConnesArakiData_scalarCocycle_eq_one (H := H) (T := T) D t]
  simp

/-- Unit descent on the Tomita lane is simultaneously multiplicative and null-log. -/
theorem tomitaUnitConnesArakiData_unitLane_vanishes
    (D : TomitaUnitConnesArakiData (H := H) T)
    (t : ℝ) :
    scalarCocycle
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (H := H)
          (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        D.bridge t =
      (1 : ℝˣ) ∧
    cocycleLogPotential
        (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (H := H)
            (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        D.bridge t =
      0 := by
  constructor
  · exact tomitaUnitConnesArakiData_scalarCocycle_eq_one (H := H) (T := T) D t
  · exact tomitaUnitConnesArakiData_cocycleLogPotential_eq_zero (H := H) (T := T) D t

/-- Constructor-specific bridge computation: the canonical Tomita constructor uses
the canonical unit scalar bridge definitionally. -/
theorem tomitaUnitConnesArakiDataOfCasini_bridge
    (T : SinkhornTrajectory n)
    (relEnt : ArakiRelativeEntropyProfile)
    (hCasini :
      CasiniIncrementBridge
        (n := n) (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (H := H)
          (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
          (H := H)
          (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        T
        relEnt) :
    (tomitaUnitConnesArakiDataOfCasini
        (H := H) (T := T) relEnt hCasini).bridge
      =
    InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
      (H := H)
      (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)) := rfl

/-- Constructor-specific relative-entropy field computation. -/
@[simp] theorem tomitaUnitConnesArakiDataOfCasini_relEnt
    (T : SinkhornTrajectory n)
    (relEnt : ArakiRelativeEntropyProfile)
    (hCasini :
      CasiniIncrementBridge
        (n := n) (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (H := H)
          (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
          (H := H)
          (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        T
        relEnt) :
    (tomitaUnitConnesArakiDataOfCasini
        (H := H) (T := T) relEnt hCasini).relEnt
      =
    relEnt := rfl

/-- Constructor-specific Casini bridge field computation. -/
theorem tomitaUnitConnesArakiDataOfCasini_casini
    (T : SinkhornTrajectory n)
    (relEnt : ArakiRelativeEntropyProfile)
    (hCasini :
      CasiniIncrementBridge
        (n := n) (H := H)
        (TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
        (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
          (H := H)
          (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
          (H := H)
          (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
        T
        relEnt) :
    (tomitaUnitConnesArakiDataOfCasini
        (H := H) (T := T) relEnt hCasini).casini
      =
    hCasini := rfl

/--
Tomita-specialized canonical squeezing endpoint:
ambient and restricted Araki-drop presentations both flow through the same
restricted-drop interface.
-/
theorem abs_squeezingLogShear_le_of_abs_time_le_tomitaArakiRelativeEntropyDrop
    (D : TomitaConnesArakiData (H := H) u T)
    {relEntRestricted : ArakiRelativeEntropyProfile}
    (hRestrDrop :
      ArakiRelativeEntropyRestrictionDropMonotone D.relEnt relEntRestricted)
    (k : Nat)
    (t : ℝ)
    (hTime : |t| ≤ |arakiRelativeEntropyDrop relEntRestricted k|) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n T k := by
  exact abs_squeezingLogShear_le_of_abs_time_le_arakiRelativeEntropyDrop
    (H := H)
    (σ := TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
    (u := u) (T := T) D hRestrDrop k t hTime

/--
Carrier-completing endpoint: Tomita-specialized Connes-Araki data gives the
trajectorywise Bekenstein bound, while a thermal KMS-like hypothesis for the
modular-sign generator is re-expressed directly in the Tomita modular-flow
language used by the Connes-Araki carrier.
-/
theorem topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData
    (D : TomitaConnesArakiData (H := H) u T)
    (ω : AlgebraEnd H →L[ℝ] ℝ)
    (β : ℝ)
    (hKMS :
      InfoGeometry.Krein.satisfies_kms_like
        (E := H)
        (TomitaTakesaki.modularSignEpsilon (E := H))
        ω β) :
    TopologicalBekensteinBound n T
      ∧ ∀ A B : AlgebraEnd H,
          ω
              (A *
                TomitaTakesaki.modularSignAdditiveModularFlow
                  (E := H) β B)
            = ω (B * A) := by
  refine ⟨topologicalBekensteinBound_of_tomitaConnesCocycle_casiniIncrement
    (n := n) (H := H) (u := u) (T := T)
    (hCocycle := D.cocycle) (hBridge := D.bridge)
    (relEnt := D.relEnt) (hCasini := D.casini), ?_⟩
  exact TomitaTakesaki.modularSignAdditiveModularFlow_kms_of_satisfies_kms_like
    (E := H) (ω := ω) (β := β) hKMS

/--
Owner-name form of the Tomita-specialized Bekenstein/KMS endpoint: the KMS
assumption is stated directly on the root modular-sign operator `spectral_epsilon`.
-/
theorem topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData_root
    (D : TomitaConnesArakiData (H := H) u T)
    (ω : AlgebraEnd H →L[ℝ] ℝ)
    (β : ℝ)
    (hKMS :
      InfoGeometry.Krein.satisfies_kms_like
        (E := H)
        (InfoGeometry.Krein.spectral_epsilon (E := H))
        ω β) :
    TopologicalBekensteinBound n T
      ∧ ∀ A B : AlgebraEnd H,
          ω
              (A *
                TomitaTakesaki.modularSignAdditiveModularFlow
                  (E := H) β B)
            = ω (B * A) := by
  simpa [TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    (topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData
      (H := H) (u := u) (T := T) D ω β hKMS)

/--
Unit-cocycle specialization of the Tomita endpoint:
the cocycle lane is fixed to the welded flow-unit cocycle witness.
-/
theorem topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaUnitConnesArakiData
    (D : TomitaUnitConnesArakiData (H := H) T)
    (ω : AlgebraEnd H →L[ℝ] ℝ)
    (β : ℝ)
    (hKMS :
      InfoGeometry.Krein.satisfies_kms_like
        (E := H)
        (TomitaTakesaki.modularSignEpsilon (E := H))
        ω β) :
    TopologicalBekensteinBound n T
      ∧ ∀ A B : AlgebraEnd H,
          ω
              (A *
                TomitaTakesaki.modularSignAdditiveModularFlow
                  (E := H) β B)
            = ω (B * A) := by
  exact topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData
    (H := H)
    (u := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle
      (TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
    (T := T)
    D
    ω
    β
    hKMS

end TomitaSpecialization

end InfoGeometry.Canonical.ConnesArakiFramework
