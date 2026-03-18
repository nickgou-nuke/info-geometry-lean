import InfoGeometry.Canonical.BekensteinBound
import InfoGeometry.Canonical.MongeAmpereCramerRao
import InfoGeometry.Canonical.TomitaTakesaki

/-!
# InfoGeometry.Canonical.ConnesArakiFramework

Unified Connes-Araki framework in the finite Sinkhorn scaffold:
- Connes cocycle and scalar bridge data,
- Araki-style relative-entropy drops,
- RN-barrier / topological Bekenstein control,
- squeezing-flow bounds driven by entropy-drop budgets.
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

section Core

variable {σ : AdditiveModularFlow (H := H)}
variable {u : ℝ → AlgebraEnd H}
variable {T : SinkhornTrajectory n}

/-- Relative-entropy drops are nonnegative under the Casini monotonicity clause. -/
private lemma arakiRelativeEntropyDrop_nonneg
  (D : ConnesArakiData (H := H) σ u T) :
    ∀ k : Nat, 0 ≤ arakiRelativeEntropyDrop D.relEnt k := by
  intro k
  simpa [arakiRelativeEntropyDrop] using
    relEnt_drop_nonneg_of_casiniIncrementBridge
      (n := n) (H := H) (σ := σ) (u := u)
      (hBridge := D.bridge) (T := T) (relEnt := D.relEnt) D.casini k

/-- Each Araki relative-entropy drop is controlled by the trajectory RN barrier. -/
private lemma abs_arakiRelativeEntropyDrop_le_trajectoryRNBarrier
  (D : ConnesArakiData (H := H) σ u T) :
    ∀ k : Nat,
      |arakiRelativeEntropyDrop D.relEnt k| ≤ trajectoryRNBarrier n T k := by
  intro k
  have hEq :
      arakiRelativeEntropyDrop D.relEnt k
        = phaseRNGeneratorBefore n (phaseAt k) (T.state k) := by
    simpa [arakiRelativeEntropyDrop] using D.casini.relEnt_drop_eq_phaseRN k
  rw [hEq]
  exact abs_trajectoryRNGenerator_le_trajectoryRNBarrier (n := n) T k

/--
Entropy-drop-to-squeezing theorem:
if flow time is budgeted by an Araki relative-entropy drop at step `k`, then
logarithmic squeezing shear is bounded by the RN barrier at that step.
-/
theorem abs_squeezingLogShear_le_of_abs_time_le_arakiRelativeEntropyDrop
  (D : ConnesArakiData (H := H) σ u T)
    (k : Nat)
    (t : ℝ)
    (hTime : |t| ≤ arakiRelativeEntropyDrop D.relEnt k) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n T k := by
  have hDropNonneg : 0 ≤ arakiRelativeEntropyDrop D.relEnt k :=
    arakiRelativeEntropyDrop_nonneg (H := H) (σ := σ) (u := u) (T := T) D k
  have hTimeAbs : |t| ≤ |arakiRelativeEntropyDrop D.relEnt k| := by
    simpa [abs_of_nonneg hDropNonneg] using hTime
  have hShearToDrop :
      |squeezingLogShear t| ≤ 4 * |arakiRelativeEntropyDrop D.relEnt k| :=
    abs_squeezingLogShear_le_of_abs_time_le_barrier (t := t)
      (b := |arakiRelativeEntropyDrop D.relEnt k|) hTimeAbs
  have hDropToBarrier :
      |arakiRelativeEntropyDrop D.relEnt k| ≤ trajectoryRNBarrier n T k :=
    abs_arakiRelativeEntropyDrop_le_trajectoryRNBarrier
      (H := H) (σ := σ) (u := u) (T := T) D k
  have hScale :
      4 * |arakiRelativeEntropyDrop D.relEnt k| ≤ 4 * trajectoryRNBarrier n T k := by
    nlinarith [hDropToBarrier]
  exact le_trans hShearToDrop hScale

/--
Monotonicity interface under subalgebra restriction:
the restricted Araki relative entropy is pointwise bounded by the ambient one.
-/
structure ArakiRelativeEntropyRestrictionMonotone
    (relEnt : ArakiRelativeEntropyProfile)
    (relEntRestricted : ArakiRelativeEntropyProfile) : Prop where
  pointwise_le : ∀ k : Nat, relEntRestricted k ≤ relEnt k

/--
Quantitative restriction interface:
in addition to pointwise monotonicity, one-step drops are controlled in
absolute value.
-/
structure ArakiRelativeEntropyRestrictionDropMonotone
    (relEnt : ArakiRelativeEntropyProfile)
    (relEntRestricted : ArakiRelativeEntropyProfile) : Prop where
  pointwise : ArakiRelativeEntropyRestrictionMonotone relEnt relEntRestricted
  drop_abs_le :
    ∀ k : Nat,
      |arakiRelativeEntropyDrop relEntRestricted k|
        ≤ |arakiRelativeEntropyDrop relEnt k|

/--
Restricted-drop RN-barrier control:
if restriction drops are dominated by ambient drops, they inherit the same
trajectory RN barrier bound.
-/
theorem abs_arakiRelativeEntropyDrop_restricted_le_trajectoryRNBarrier
    (D : ConnesArakiData (H := H) σ u T)
    {relEntRestricted : ArakiRelativeEntropyProfile}
    (hRestrDrop :
      ArakiRelativeEntropyRestrictionDropMonotone D.relEnt relEntRestricted) :
    ∀ k : Nat,
      |arakiRelativeEntropyDrop relEntRestricted k| ≤ trajectoryRNBarrier n T k := by
  intro k
  exact le_trans (hRestrDrop.drop_abs_le k)
    (abs_arakiRelativeEntropyDrop_le_trajectoryRNBarrier
      (H := H) (σ := σ) (u := u) (T := T) D k)

/--
Restricted-drop squeezing bound:
time budgets controlled by restricted Araki drops imply the same RN-barrier
squeezing bound, providing a monotonicity interface toward QNEC/Bekenstein
applications.
-/
theorem abs_squeezingLogShear_le_of_abs_time_le_restrictedArakiRelativeEntropyDrop
    (D : ConnesArakiData (H := H) σ u T)
    {relEntRestricted : ArakiRelativeEntropyProfile}
    (hRestrDrop :
      ArakiRelativeEntropyRestrictionDropMonotone D.relEnt relEntRestricted)
    (k : Nat)
    (t : ℝ)
    (hTime : |t| ≤ |arakiRelativeEntropyDrop relEntRestricted k|) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n T k := by
  have hShearToRestrictedDrop :
      |squeezingLogShear t| ≤ 4 * |arakiRelativeEntropyDrop relEntRestricted k| :=
    abs_squeezingLogShear_le_of_abs_time_le_barrier
      (t := t) (b := |arakiRelativeEntropyDrop relEntRestricted k|) hTime
  have hRestrictedDropToBarrier :
      |arakiRelativeEntropyDrop relEntRestricted k| ≤ trajectoryRNBarrier n T k :=
    abs_arakiRelativeEntropyDrop_restricted_le_trajectoryRNBarrier
      (H := H) (σ := σ) (u := u) (T := T) D hRestrDrop k
  have hScale :
      4 * |arakiRelativeEntropyDrop relEntRestricted k| ≤ 4 * trajectoryRNBarrier n T k := by
    nlinarith [hRestrictedDropToBarrier]
  exact le_trans hShearToRestrictedDrop hScale

end Core

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
    (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
    u T

/--
Tomita-specialized entropy-drop-to-squeezing theorem.
-/
theorem abs_squeezingLogShear_le_of_abs_time_le_tomitaArakiRelativeEntropyDrop
    (D : TomitaConnesArakiData (H := H) u T)
    (k : Nat)
    (t : ℝ)
    (hTime : |t| ≤ arakiRelativeEntropyDrop D.relEnt k) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n T k := by
  exact abs_squeezingLogShear_le_of_abs_time_le_arakiRelativeEntropyDrop
    (H := H)
    (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
    (u := u) (T := T) D k t hTime

/--
Tomita-specialized Bekenstein-bound corollary extracted from Connes-Araki data.
-/
theorem topologicalBekensteinBound_of_tomitaConnesArakiData
    (D : TomitaConnesArakiData (H := H) u T) :
    TopologicalBekensteinBound n T := by
  exact topologicalBekensteinBound_of_tomitaConnesCocycle_casiniIncrement
    (n := n) (H := H) (u := u) (T := T)
    (hCocycle := D.cocycle) (hBridge := D.bridge)
    (relEnt := D.relEnt) (hCasini := D.casini)

/--
Tomita-specialized restricted-drop squeezing bound.
-/
theorem abs_squeezingLogShear_le_of_abs_time_le_tomitaRestrictedArakiRelativeEntropyDrop
    (D : TomitaConnesArakiData (H := H) u T)
    {relEntRestricted : ArakiRelativeEntropyProfile}
    (hRestrDrop :
      ArakiRelativeEntropyRestrictionDropMonotone D.relEnt relEntRestricted)
    (k : Nat)
    (t : ℝ)
    (hTime : |t| ≤ |arakiRelativeEntropyDrop relEntRestricted k|) :
    |squeezingLogShear t| ≤ 4 * trajectoryRNBarrier n T k := by
  exact abs_squeezingLogShear_le_of_abs_time_le_restrictedArakiRelativeEntropyDrop
    (H := H)
    (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
    (u := u) (T := T) D hRestrDrop k t hTime

end TomitaSpecialization

end InfoGeometry.Canonical.ConnesArakiFramework
