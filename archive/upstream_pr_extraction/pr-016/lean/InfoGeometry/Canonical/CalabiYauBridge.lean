import InfoGeometry.Canonical.CalabiYauMetricRicci
import InfoGeometry.Canonical.CalabiYauRNMongeAmpere
import InfoGeometry.Canonical.CalabiYauWBridge

namespace InfoGeometry

namespace Canonical.CalabiYauBridge

open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.MoE

section CanopyAssembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/--
Canopy assembly package for the entropic-to-geometric Calabi-Yau bridge.
This package is the integration surface of the metric RN bridge and the
RN-entropy Monge-Ampere source branch.
-/
structure EntropicMetricCanopyPackage
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (R : RicciTensor E)
    (x : E)
    (M : SinkhornMatrix n) : Prop where
  entropy_source : RNEntropySourcesMongeAmpere n Kgeo M
  unit_relative_volume : relativeVolumeChangeRN n M = 1
  metric_bridge : MetricRNRicciBridge R Kgeo x

/--
First canopy closure: package data yields the unit-relative-volume state on the
geometric branch.
-/
theorem canopy_unitRelativeVolumeState
    {n : Nat}
    {Kgeo : KaehlerInformationGeometry E}
    {R : RicciTensor E}
    {x : E}
    {M : SinkhornMatrix n}
    (P : EntropicMetricCanopyPackage n Kgeo R x M) :
    UnitRelativeVolumeState Kgeo := by
  exact unitRelativeVolumeState_of_rnEntropySource_of_unitRelativeVolume
    (n := n) (Kgeo := Kgeo) (M := M) P.entropy_source P.unit_relative_volume

/--
Main canopy closure: RN entropy source + unit-volume closure + metric bridge
produce Ricci-flatness and vacuum Einstein closure on the `scalar = 2Λ` branch.
-/
theorem canopy_isRicciFlat_and_vacuumEinstein
    {n : Nat}
    {Kgeo : KaehlerInformationGeometry E}
    {R : RicciTensor E}
    {x : E}
    (Λ : ℝ)
    {M : SinkhornMatrix n}
    (P : EntropicMetricCanopyPackage n Kgeo R x M) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact isRicciFlat_and_vacuumEinsteinEquation_of_rnEntropySource_of_unitRelativeVolume
    (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
    (M := M) P.entropy_source P.unit_relative_volume P.metric_bridge

/--
Trunk-to-canopy closure packet for the Calabi-Yau lane:
the entropic package simultaneously yields unit-relative-volume, Ricci-flatness,
and vacuum-Einstein closure.
-/
theorem calabiYau_trunk_to_canopy_closure
    {n : Nat}
    {Kgeo : KaehlerInformationGeometry E}
    {R : RicciTensor E}
    {x : E}
    (Λ : ℝ)
    {M : SinkhornMatrix n}
    (P : EntropicMetricCanopyPackage n Kgeo R x M) :
    UnitRelativeVolumeState Kgeo ∧
      IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  refine ⟨?_, ?_⟩
  · exact canopy_unitRelativeVolumeState (E := E) (n := n) (Kgeo := Kgeo) (R := R) (x := x) (M := M) P
  · exact canopy_isRicciFlat_and_vacuumEinstein
      (E := E) (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ) (M := M) P

/--
Root-factorization packet: one canopy package witnesses the complete geometric
closure tuple on the Calabi-Yau branch.
-/
theorem calabiYau_root_factorization
    {n : Nat}
    {Kgeo : KaehlerInformationGeometry E}
    {R : RicciTensor E}
    {x : E}
    (Λ : ℝ)
    {M : SinkhornMatrix n}
    (P : EntropicMetricCanopyPackage n Kgeo R x M) :
    ∃ _ : UnitRelativeVolumeState Kgeo,
      IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  refine ⟨canopy_unitRelativeVolumeState (E := E) (n := n) (Kgeo := Kgeo) (R := R) (x := x) (M := M) P, ?_⟩
  simpa using canopy_isRicciFlat_and_vacuumEinstein
    (E := E) (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ) (M := M) P

end CanopyAssembly

end Canonical.CalabiYauBridge

end InfoGeometry
