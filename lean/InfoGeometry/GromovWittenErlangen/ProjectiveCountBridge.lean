import InfoGeometry.Arithmetic.PrimitiveProjectiveRays
import InfoGeometry.GromovWittenErlangen.LieOrbitCurve

/-!
# InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge

Projective-count substrate for the GW/Erlangen localization lane.

This module formalizes the lowest layer of the architecture:

* L0: raw unnormalized count profile;
* L1: positive projective ray / scale-invariant normalized shape;
* L2: GW localization graph shadow.

No Drazin inverse, Moore-Penrose inverse, Frobenius theorem, virtual
localization theorem, or Atiyah-Singer theorem is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge

open InfoGeometry.Arithmetic.PrimitiveProjectiveRays

/--
Projective count substrate for a GW localization packet.

The raw data is an unnormalized count profile.  The projective geometry is the
positive ray of that profile.  A model supplies the law connecting localization
vertices/edges to the count profile.
-/
structure GWProjectiveCountState
    (G T Target Coeff : Type*) where
  /-- Finite GW/Erlangen localization packet. -/
  localization :
    InfoGeometry.GromovWittenErlangen.VirtualLocalizationOrbitPacket
      G T Target Coeff

  /-- Raw unnormalized count profile. -/
  counts :
    CountProfile

  /-- Finite support of active count atoms. -/
  support :
    Finset ℕ

  /-- Vertex-to-arithmetic atom code. -/
  vertexCode :
    localization.graph.Vertex → ℕ

  /-- Edge-to-arithmetic atom code. -/
  edgeCode :
    localization.graph.Edge → ℕ

  /-- Scalar readout of localization coefficients. -/
  coeffReadout :
    Coeff → ℝ

  /--
  Model-supplied law saying the localization graph is represented by this
  count profile.
  -/
  countShadowLaw :
    Prop

  /-- Certificate for the count-shadow law. -/
  countShadow_valid :
    countShadowLaw

namespace GWProjectiveCountState

variable {G T Target Coeff : Type*}
variable (C : GWProjectiveCountState G T Target Coeff)

/-- The supplied GW-to-count shadow law is available. -/
theorem countShadow_holds :
    C.countShadowLaw :=
  C.countShadow_valid

/-- Finite partition/gauge readout of the projective count state. -/
def finitePartition (β : ℝ) : ℝ :=
  finiteArithmeticPartition C.counts C.support β

/-- Gauge-normalized finite shape of the projective count state. -/
def normalizedShape (β : ℝ) : CountProfile :=
  finiteArithmeticNormalizedRay C.counts C.support β

/-- Positive rescaling gives the same projective count ray. -/
theorem samePositiveRay_of_positive_scale
    (c : ℝ) (hc : 0 < c) :
    SamePositiveRay C.counts (fun n => c * C.counts n) :=
  ⟨c, hc, rfl⟩

/--
The normalized shape is invariant under nonzero global rescaling of the raw
count profile.
-/
theorem normalizedShape_scale_counts
    (β c : ℝ) (hc : c ≠ 0) :
    finiteArithmeticNormalizedRay (fun n => c * C.counts n) C.support β =
      C.normalizedShape β := by
  simpa [normalizedShape] using
    finiteArithmeticNormalizedRay_scale_counts C.counts C.support β c hc

/-- Pointwise form of scale invariance. -/
theorem normalizedShape_scale_counts_apply
    (β c : ℝ) (hc : c ≠ 0) (n : ℕ) :
    finiteArithmeticNormalizedRay (fun k => c * C.counts k) C.support β n =
      C.normalizedShape β n := by
  simpa using congrFun (C.normalizedShape_scale_counts β c hc) n

/--
If two count profiles lie on the same positive ray, their normalized shapes
agree.
-/
theorem normalizedShape_eq_of_samePositiveRay
    {counts₂ : CountProfile}
    (hray : SamePositiveRay C.counts counts₂)
    (β : ℝ)
    (hZ : finiteArithmeticPartition C.counts C.support β ≠ 0)
    (n : ℕ) :
    finiteArithmeticNormalizedRay counts₂ C.support β n =
      C.normalizedShape β n := by
  simpa [normalizedShape] using
    finiteArithmeticNormalizedRay_eq_of_samePositiveRay
      (counts₁ := C.counts)
      (counts₂ := counts₂)
      (support := C.support)
      (s := β)
      hray hZ n

/--
When the partition is nonzero, the normalized count state has total mass one on
the chosen support.
-/
theorem normalizedShape_sum_eq_one
    (β : ℝ)
    (hZ : finiteArithmeticPartition C.counts C.support β ≠ 0) :
    Finset.sum C.support (fun n => C.normalizedShape β n) = 1 := by
  simpa [normalizedShape] using
    finiteArithmeticNormalizedRay_sum_eq_one C.counts C.support β hZ

end GWProjectiveCountState

/--
Late-bound volume/entropy gauge for a projective count state.

This is intentionally separate from `GWProjectiveCountState`: projective count
geometry exists before a partition, Weyl, Drazin, or thermodynamic gauge is
chosen.
-/
structure ProjectiveCountVolumeGauge
    {G T Target Coeff : Type*}
    (C : GWProjectiveCountState G T Target Coeff) where
  /-- Gauge-fixed volume/readout. -/
  volume : ℝ

  /-- Positivity of the gauge-fixed volume. -/
  volume_pos : 0 < volume

  /-- Boltzmann/unit-normalization scalar. -/
  kB : ℝ

  /-- Positivity of the entropy normalization. -/
  kB_pos : 0 < kB

  /-- Entropy readout after choosing the gauge. -/
  entropy : ℝ

  /-- Entropy is the logarithm of the selected gauge volume. -/
  entropy_eq_kB_log_volume :
    entropy = kB * Real.log volume

  /-- Model-specific volume gauge law. -/
  volumeGaugeLaw : Prop

  /-- Certificate for the volume gauge law. -/
  volumeGauge_valid : volumeGaugeLaw

namespace ProjectiveCountVolumeGauge

variable {G T Target Coeff : Type*}
variable {C : GWProjectiveCountState G T Target Coeff}
variable (Γ : ProjectiveCountVolumeGauge C)

/-- The supplied volume gauge law is available. -/
theorem volumeGauge_holds :
    Γ.volumeGaugeLaw :=
  Γ.volumeGauge_valid

/-- Entropy is nonnegative when the selected gauge volume is at least one. -/
theorem entropy_nonneg_of_one_le_volume
    (hvol : 1 ≤ Γ.volume) :
    0 ≤ Γ.entropy := by
  rw [Γ.entropy_eq_kB_log_volume]
  exact mul_nonneg Γ.kB_pos.le (Real.log_nonneg hvol)

/-- Entropy is positive when the selected gauge volume is strictly bigger than one. -/
theorem entropy_pos_of_one_lt_volume
    (hvol : 1 < Γ.volume) :
    0 < Γ.entropy := by
  rw [Γ.entropy_eq_kB_log_volume]
  exact mul_pos Γ.kB_pos (Real.log_pos hvol)

end ProjectiveCountVolumeGauge

/--
Projective-count bridge without gauge fixing.

This is the L0/L1/L2 owner surface: localization data has a count-shadow law,
and the finite normalized shape is scale-invariant by construction.
-/
structure GWProjectiveCountBridge
    (G T Target Coeff : Type*) where
  countState :
    GWProjectiveCountState G T Target Coeff

namespace GWProjectiveCountBridge

variable {G T Target Coeff : Type*}
variable (B : GWProjectiveCountBridge G T Target Coeff)

/-- The localization-to-count law is available. -/
theorem countShadow_holds :
    B.countState.countShadowLaw :=
  B.countState.countShadow_valid

/-- Scale invariance of the projective normalized shape. -/
theorem normalizedShape_scale_counts
    (β c : ℝ) (hc : c ≠ 0) :
    finiteArithmeticNormalizedRay
        (fun n => c * B.countState.counts n)
        B.countState.support β =
      B.countState.normalizedShape β :=
  B.countState.normalizedShape_scale_counts β c hc

end GWProjectiveCountBridge

/--
Gauge-fixed projective-count bridge.

This is the first point at which thermodynamic language is allowed.
-/
structure GaugeFixedGWProjectiveCountBridge
    (G T Target Coeff : Type*) where
  projective :
    GWProjectiveCountBridge G T Target Coeff

  gauge :
    ProjectiveCountVolumeGauge projective.countState

namespace GaugeFixedGWProjectiveCountBridge

variable {G T Target Coeff : Type*}
variable (B : GaugeFixedGWProjectiveCountBridge G T Target Coeff)

/-- The localization-to-count law is available. -/
theorem countShadow_holds :
    B.projective.countState.countShadowLaw :=
  B.projective.countShadow_holds

/-- The volume-gauge law is available. -/
theorem volumeGauge_holds :
    B.gauge.volumeGaugeLaw :=
  B.gauge.volumeGauge_valid

/-- Entropy is nonnegative when the selected gauge volume is at least one. -/
theorem entropy_nonneg_of_one_le_volume
    (hvol : 1 ≤ B.gauge.volume) :
    0 ≤ B.gauge.entropy :=
  B.gauge.entropy_nonneg_of_one_le_volume hvol

end GaugeFixedGWProjectiveCountBridge

end InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge
