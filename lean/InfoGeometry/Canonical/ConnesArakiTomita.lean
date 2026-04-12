import InfoGeometry.Canonical.ConnesArakiCore
import InfoGeometry.Canonical.TomitaTakesaki

/-!
# InfoGeometry.Canonical.ConnesArakiTomita

Tomita-specialized Connes-Araki endpoints over the generic core carrier.
-/

namespace InfoGeometry.Canonical.ConnesArakiFramework

open InfoGeometry.Volume.ConnesCocycle
open InfoGeometry.Canonical.BekensteinBound
open InfoGeometry.Canonical.MongeAmpereCramerRao
open InfoGeometry.Canonical.MoE

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
    (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
    u T

/-- Tomita-specialized Connes-Araki package on the canonical unit cocycle lane. -/
abbrev TomitaUnitConnesArakiData
    (T : SinkhornTrajectory n) :=
  TomitaConnesArakiData (H := H) (InfoGeometry.Volume.ConnesCocycle.unitCocycle) T

/--
Canonical constructor on the Tomita unit-cocycle lane.

This keeps `u` non-free for consumers that only need a concrete cocycle
instantiation and a Casini bridge witness.
-/
noncomputable def tomitaUnitConnesArakiDataOfCasini
    (T : SinkhornTrajectory n)
    (relEnt : ArakiRelativeEntropyProfile)
    (hCasini : CasiniIncrementBridge
      (n := n) (H := H)
      (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
      (InfoGeometry.Volume.ConnesCocycle.unitCocycle)
      (InfoGeometry.Volume.ConnesCocycle.unitScalarBridge
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H)))
      T
      relEnt) :
    TomitaUnitConnesArakiData (H := H) T :=
  ConnesArakiData.ofUnitCocycle
    (H := H)
    (σ := InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow (E := H))
    (T := T)
    relEnt
    hCasini

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
                InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow
                  (E := H) β B)
            = ω (B * A) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    (topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData
      (H := H) (u := u) (T := T) D ω β hKMS)

end TomitaSpecialization

end InfoGeometry.Canonical.ConnesArakiFramework
