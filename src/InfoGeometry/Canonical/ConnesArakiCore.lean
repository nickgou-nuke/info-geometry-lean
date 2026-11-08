import InfoGeometry.Canonical.BekensteinBound
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.MongeAmpereCramerRao
import InfoGeometry.Volume.ConnesCocycle

/-!
# InfoGeometry.Canonical.ConnesArakiCore

Core Connes-Araki carrier and restriction-aware squeezing estimates in the
finite Sinkhorn scaffold.
-/

namespace InfoGeometry.Canonical.ConnesArakiFramework

open InfoGeometry.Volume.ConnesCocycle
open InfoGeometry.Canonical.BekensteinBound
open InfoGeometry.Canonical.MongeAmpereCramerRao
open InfoGeometry.Canonical.MoE

variable {n : Nat}
variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Araki-style relative-entropy profile on discrete Sinkhorn steps. -/
abbrev ArakiRelativeEntropyProfile := RelativeEntropyProfile

/-- One-step Araki relative-entropy drop at step `k`. -/
def arakiRelativeEntropyDrop
    (relEnt : ArakiRelativeEntropyProfile) (k : Nat) : ℝ :=
  relEnt k - relEnt (k + 1)

/--
Packaged Connes-Araki data:
Connes cocycle, scalar bridge, and Casini-style identification of cocycle
increments with relative-entropy drops.
-/
structure ConnesArakiData
  (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (T : SinkhornTrajectory n) where
  bridge : ScalarCocycleBridge (H := H) σ
  cocycle : IsConnesCocycle σ u
  relEnt : ArakiRelativeEntropyProfile
  casini : CasiniIncrementBridge (n := n) (H := H) σ u bridge T relEnt

namespace ConnesArakiData

variable {σ : AdditiveModularFlow (H := H)}
variable {T : SinkhornTrajectory n}

/--
Canonical constructor using the flow-derived unit cocycle and unit scalar bridge.

This removes a free cocycle witness in the common "existential packaging" use
case: only the Casini bridge on the fixed flow-native cocycle lane is required.
-/
noncomputable def ofUnitCocycle
    (relEnt : ArakiRelativeEntropyProfile)
    (hCasini : CasiniIncrementBridge
      (n := n) (H := H)
      σ
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle σ)
      (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge σ)
      T
      relEnt) :
    ConnesArakiData (H := H) (σ := σ)
      (u := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle σ) T where
  bridge := InfoGeometry.Volume.ConnesCocycle.unitScalarBridge σ
  cocycle := InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_isConnesCocycle σ
  relEnt := relEnt
  casini := hCasini

end ConnesArakiData

section Core

variable {σ : AdditiveModularFlow (H := H)}
variable {u : ℝ → AlgebraEnd H}
variable {T : SinkhornTrajectory n}

/-- Each Araki relative-entropy drop is controlled by the trajectory RN barrier. -/
private lemma abs_arakiRelativeEntropyDrop_le_trajectoryRNBarrier
  (D : ConnesArakiData (H := H) σ u T) :
    ∀ k : Nat,
      |arakiRelativeEntropyDrop D.relEnt k| ≤ trajectoryRNBarrier n T k := by
  intro k
  have hEq :
      arakiRelativeEntropyDrop D.relEnt k
        = phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
    simpa [arakiRelativeEntropyDrop] using D.casini.2.1 k
  rw [hEq]
  exact abs_trajectoryRNGenerator_le_trajectoryRNBarrier (n := n) T k

/--
Quantitative restriction interface:
the restricted Araki relative entropy is pointwise bounded by the ambient one,
and one-step drops are controlled in absolute value.
-/
def ArakiRelativeEntropyRestrictionDropMonotone
    (relEnt : ArakiRelativeEntropyProfile)
    (relEntRestricted : ArakiRelativeEntropyProfile) : Prop :=
  ∀ k : Nat,
    |arakiRelativeEntropyDrop relEntRestricted k|
      ≤ |arakiRelativeEntropyDrop relEnt k|

/--
Restricted-drop RN-barrier control:
if restriction drops are dominated by ambient drops, they inherit the same
trajectory RN barrier bound.
-/
private theorem abs_arakiRelativeEntropyDrop_restricted_le_trajectoryRNBarrier
    (D : ConnesArakiData (H := H) σ u T)
    {relEntRestricted : ArakiRelativeEntropyProfile}
    (hRestrDrop :
      ArakiRelativeEntropyRestrictionDropMonotone D.relEnt relEntRestricted) :
    ∀ k : Nat,
      |arakiRelativeEntropyDrop relEntRestricted k| ≤ trajectoryRNBarrier n T k := by
  intro k
  exact le_trans (hRestrDrop k)
    (abs_arakiRelativeEntropyDrop_le_trajectoryRNBarrier
      (H := H) (σ := σ) (u := u) (T := T) D k)

/--
Canonical entropy-drop-to-squeezing theorem:
ambient and restricted Araki-drop presentations both flow through the same
restriction-aware interface.
-/
theorem abs_squeezingLogShear_le_of_abs_time_le_arakiRelativeEntropyDrop
  (D : ConnesArakiData (H := H) σ u T)
    {relEntRestricted : ArakiRelativeEntropyProfile}
    (hRestrDrop :
      ArakiRelativeEntropyRestrictionDropMonotone D.relEnt relEntRestricted)
    (k : Nat)
    (t : ℝ)
    (hTime : |t| ≤ |arakiRelativeEntropyDrop relEntRestricted k|) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n T k := by
  have hShearToDrop :
      |squeezingLogShear t| ≤ 4 * |arakiRelativeEntropyDrop relEntRestricted k| :=
    abs_squeezingLogShear_le_of_abs_time_le_barrier (t := t)
      (b := |arakiRelativeEntropyDrop relEntRestricted k|) hTime
  have hDropToBarrier :
      |arakiRelativeEntropyDrop relEntRestricted k| ≤ trajectoryRNBarrier n T k :=
    abs_arakiRelativeEntropyDrop_restricted_le_trajectoryRNBarrier
      (H := H) (σ := σ) (u := u) (T := T) D hRestrDrop k
  have hScale :
      4 * |arakiRelativeEntropyDrop relEntRestricted k| ≤ 4 * trajectoryRNBarrier n T k := by
    nlinarith [hDropToBarrier]
  exact le_trans hShearToDrop hScale

end Core

end InfoGeometry.Canonical.ConnesArakiFramework
