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
Quantitative restriction interface:
the restricted Araki relative entropy is pointwise bounded by the ambient one,
and one-step drops are controlled in absolute value.
-/
structure ArakiRelativeEntropyRestrictionDropMonotone
    (relEnt : ArakiRelativeEntropyProfile)
    (relEntRestricted : ArakiRelativeEntropyProfile) : Prop where
  pointwise_le : ∀ k : Nat, relEntRestricted k ≤ relEnt k
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
    (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
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
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon (E := H))
        ω β) :
    TopologicalBekensteinBound n T
      ∧ ∀ A B : AlgebraEnd H,
          ω
              (A *
                InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow
                  (E := H) β B)
            = ω (B * A) := by
  refine ⟨topologicalBekensteinBound_of_tomitaConnesCocycle_casiniIncrement
    (n := n) (H := H) (u := u) (T := T)
    (hCocycle := D.cocycle) (hBridge := D.bridge)
    (relEnt := D.relEnt) (hCasini := D.casini), ?_⟩
  exact InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow_kms_of_satisfies_kms_like
    (E := H) (ω := ω) (β := β) hKMS


end TomitaSpecialization

end InfoGeometry.Canonical.ConnesArakiFramework
