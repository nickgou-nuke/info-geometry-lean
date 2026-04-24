import InfoGeometry.Canonical.CalabiYauMetricRicci
import InfoGeometry.Canonical.MongeAmpereCramerRao

namespace InfoGeometry.Canonical.CalabiYauBridge

open InfoGeometry.Convex
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.MongeAmpereCramerRao
open InfoGeometry.Canonical.PerelmanW
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.SpectralInference

section MongeAmpereRicci

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Entropy-sourced Monge-Ampere hypothesis:
the Monge-Ampere density is the RN-induced relative-volume factor
`exp(-K_RN)` associated to a Sinkhorn matrix state.
-/
def RNEntropySourcesMongeAmpere
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n) : Prop :=
  SatisfiesMongeAmpere Kgeo.H (fun _ => relativeVolumeChangeRN n M)

omit [FiniteDimensional ℝ E] in
/--
Unit relative-volume closure extracted from RN-sourced Monge-Ampere density.
-/
theorem unitRelativeVolumeState_of_rnEntropySource_of_unitRelativeVolume
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1) :
    UnitRelativeVolumeState Kgeo := by
  intro x
  simpa [RNEntropySourcesMongeAmpere, hUnit] using hSource x

omit [FiniteDimensional ℝ E] in
/--
RN entropy sourcing plus unit relative-volume closure yields the incompressible
Monge-Ampere regime used by the Cramer-Rao bridge.
-/
theorem incompressibleMongeAmpere_of_rnEntropySource_of_unitRelativeVolume
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1) :
    IncompressibleMongeAmpere Kgeo.H := by
  exact unitRelativeVolumeState_of_rnEntropySource_of_unitRelativeVolume
    (n := n) (Kgeo := Kgeo) (M := M) hSource hUnit

omit [FiniteDimensional ℝ E] in
/--
Direct Cramer-Rao determinant closure from the RN entropy source and unit
relative-volume hypothesis.
-/
theorem absDet_cramerRaoMetric_eq_one_of_rnEntropySource_of_unitRelativeVolume
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1)
    (x : E)
    (hdet : LinearMap.det (cramerRaoMetricOp Kgeo.H x).toLinearMap ≠ 0) :
    |LinearMap.det (cramerRaoMetricOp Kgeo.H x).toLinearMap| = 1 := by
  exact MongeAmpereCramerRao.absDet_cramerRaoMetric_eq_one_of_incompressible
    (H := Kgeo.H)
    (hIncomp :=
      incompressibleMongeAmpere_of_rnEntropySource_of_unitRelativeVolume
        (n := n) (Kgeo := Kgeo) (M := M) hSource hUnit)
    (x := x)
    hdet

omit [FiniteDimensional ℝ E] in
/--
Potential-form Cramer-Rao closure from the RN entropy source and unit
relative-volume hypothesis.
-/
theorem cramerRaoMetricVolumePotential_eq_zero_of_rnEntropySource_of_unitRelativeVolume
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1)
    (x : E) :
    cramerRaoMetricVolumePotential Kgeo.H x = 0 := by
  exact MongeAmpereCramerRao.cramerRaoMetricVolumePotential_eq_zero_of_incompressible
    (H := Kgeo.H)
    (hIncomp :=
      incompressibleMongeAmpere_of_rnEntropySource_of_unitRelativeVolume
        (n := n) (Kgeo := Kgeo) (M := M) hSource hUnit)
    (x := x)

omit [FiniteDimensional ℝ E] in
/--
Direct logarithmic Cramer-Rao closure from the RN entropy source and unit
relative-volume hypothesis.
-/
theorem logAbsDet_cramerRaoMetric_eq_zero_of_rnEntropySource_of_unitRelativeVolume
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1)
    (x : E) :
    Real.log (|LinearMap.det (cramerRaoMetricOp Kgeo.H x).toLinearMap|) = 0 := by
  have hPotentialZero : cramerRaoMetricVolumePotential Kgeo.H x = 0 :=
    cramerRaoMetricVolumePotential_eq_zero_of_rnEntropySource_of_unitRelativeVolume
      (n := n) (Kgeo := Kgeo) (M := M) hSource hUnit x
  have hNegLogZero : -Real.log (|LinearMap.det (cramerRaoMetricOp Kgeo.H x).toLinearMap|) = 0 := by
    simpa [cramerRaoMetricVolumePotential, cramerRaoMetricVolumeShadow,
      MongeAmpereCramerRao.cramerRaoMetricOperatorOwner, cramerRaoMetricOp] using hPotentialZero
  linarith

omit [FiniteDimensional ℝ E] in
/--
RN entropy sourcing plus unit relative-volume closure yields the vacuum Einstein
equation on the `c = 0` branch (`scalar = 2Λ`) once a metric RN bridge is fixed.
-/
theorem vacuumEinsteinEquation_of_rnEntropySource_of_unitRelativeVolume
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (R : RicciTensor E)
    (x : E)
    (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  have hUnitState : UnitRelativeVolumeState Kgeo :=
    unitRelativeVolumeState_of_rnEntropySource_of_unitRelativeVolume
      (n := n) (Kgeo := Kgeo) (M := M) hSource hUnit
  exact vacuumEinsteinEquation_of_unitRelativeVolume
    (R := R) (K := Kgeo) (x := x) (Λ := Λ) hUnitState hBridge

omit [FiniteDimensional ℝ E] in
/--
RN entropy sourcing plus unit relative-volume closure yields both Ricci-flatness
and the vacuum Einstein equation once a metric RN bridge is fixed.
-/
theorem isRicciFlat_and_vacuumEinsteinEquation_of_rnEntropySource_of_unitRelativeVolume
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (R : RicciTensor E)
    (x : E)
    (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  have hUnitState : UnitRelativeVolumeState Kgeo :=
    unitRelativeVolumeState_of_rnEntropySource_of_unitRelativeVolume
      (n := n) (Kgeo := Kgeo) (M := M) hSource hUnit
  refine ⟨?_, ?_⟩
  · exact isRicciFlat_of_unitRelativeVolume
      (R := R) (K := Kgeo) (x := x) hUnitState hBridge
  · exact vacuumEinsteinEquation_of_rnEntropySource_of_unitRelativeVolume
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
      (M := M) hSource hUnit hBridge

omit [FiniteDimensional ℝ E] in
/--
Constant-density witness extracted from RN-entropy Monge-Ampere sourcing.
-/
private theorem hasConstantMongeAmpereDensity_of_rnEntropySource
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M) :
    HasConstantMongeAmpereDensity Kgeo.H := by
  exact ⟨relativeVolumeChangeRN n M, hSource⟩

omit [FiniteDimensional ℝ E] in
/--
RN entropy sourcing can be read in potential form: the Monge-Ampere density is
the exponential of the negative RN/Kähler potential.
-/
theorem rnEntropySourcesMongeAmperePotential
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M) :
    SatisfiesMongeAmperePotential Kgeo.H (fun _ => -kahlerPotentialRN n M) := by
  intro x
  rw [hSource x, relativeVolumeChangeRN]

omit [FiniteDimensional ℝ E] in
/--
Pointwise log form of RN entropy sourcing: the logarithmic Monge-Ampere density
is exactly the negative RN/Kähler potential.
-/
theorem log_mongeAmpereDensity_eq_neg_kahlerPotentialRN_of_rnEntropySource
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (x : E) :
    Real.log (mongeAmpereDensity Kgeo.H x) = -kahlerPotentialRN n M := by
  rw [hSource x, relativeVolumeChangeRN]
  simp

omit [FiniteDimensional ℝ E] in
/--
Equivalent pointwise form: the RN/Kähler potential is minus the logarithmic
Monge-Ampere density under RN entropy sourcing.
-/
private theorem kahlerPotentialRN_eq_neg_log_mongeAmpereDensity_of_rnEntropySource
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (x : E) :
    kahlerPotentialRN n M = -Real.log (mongeAmpereDensity Kgeo.H x) := by
  calc
    kahlerPotentialRN n M = -(-kahlerPotentialRN n M) := by ring
    _ = -Real.log (mongeAmpereDensity Kgeo.H x) := by
      rw [log_mongeAmpereDensity_eq_neg_kahlerPotentialRN_of_rnEntropySource
        (n := n) (Kgeo := Kgeo) (M := M) hSource x]

omit [FiniteDimensional ℝ E] in
/--
If the Kähler logarithmic potential `logF` matches the negative RN/Kähler
potential, then RN entropy sourcing upgrades directly to a `logF`-driven
Monge-Ampere potential witness.
-/
theorem rnEntropySourcesMongeAmperePotential_of_logF_eq_neg_kahlerPotentialRN
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hLogF : ∀ x : E, Kgeo.logF x = -kahlerPotentialRN n M) :
    SatisfiesMongeAmperePotential Kgeo.H Kgeo.logF := by
  intro x
  calc
    mongeAmpereDensity Kgeo.H x = Real.exp (-kahlerPotentialRN n M) := by
      exact rnEntropySourcesMongeAmperePotential
        (n := n) (Kgeo := Kgeo) (M := M) hSource x
    _ = Real.exp (Kgeo.logF x) := by
      rw [hLogF x]

omit [FiniteDimensional ℝ E] in
/--
Pointwise logarithmic Monge-Ampere closure along the same bridge: when `logF`
coincides with the negative RN/Kähler potential, the logarithmic Monge-Ampere
density is exactly `logF`.
-/
private theorem log_mongeAmpereDensity_eq_logF_of_rnEntropySource_of_logF_eq_neg_kahlerPotentialRN
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hLogF : ∀ x : E, Kgeo.logF x = -kahlerPotentialRN n M)
    (x : E) :
    Real.log (mongeAmpereDensity Kgeo.H x) = Kgeo.logF x := by
  calc
    Real.log (mongeAmpereDensity Kgeo.H x) = -kahlerPotentialRN n M := by
      exact log_mongeAmpereDensity_eq_neg_kahlerPotentialRN_of_rnEntropySource
        (n := n) (Kgeo := Kgeo) (M := M) hSource x
    _ = Kgeo.logF x := by
      symm
      exact hLogF x

end MongeAmpereRicci

end InfoGeometry.Canonical.CalabiYauBridge
