import InfoGeometry.Canonical.FilteredHestenesAnalyticFamily
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

noncomputable section

open InfoGeometry.Krein
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredHestenesAnalyticFamily
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity

namespace InfoGeometry.Canonical.FilteredHestenesAnalyticFamily.AnalyticFamily

variable {C : HestenesKreinCone} (F : AnalyticFamily C)

/-- A finite-stage zero mode has zero canonical observable readout. -/
theorem colimitReadout_eq_zero_of_map_eq_zero
    {n : ℕ} {x : DoubledSpace (C.Base n)}
    (hx : F.map n x = 0) :
    F.colimitReadout n x = 0 := by
  simp [colimitReadout, hx]

/-- Under injectivity of the canonical cone map, a nonzero finite-stage zero
mode remains nonzero in the filtered carrier while its observable readout
vanishes. -/
theorem zeroMode_survives_colimit
    {n : ℕ} {x : DoubledSpace (C.Base n)}
    (hι : Function.Injective (C.ι n))
    (hx_ne : x ≠ 0)
    (hx_zero : F.map n x = 0) :
    C.ι n x ≠ 0 ∧ F.colimitReadout n x = 0 := by
  constructor
  · intro hzero
    apply hx_ne
    apply hι
    simpa using hzero
  · exact F.colimitReadout_eq_zero_of_map_eq_zero hx_zero

/-- A compatible global operator induced on the filtered carrier annihilates
the image of every finite-stage zero mode. -/
theorem globalOperator_zero_of_stage_zero
    (Tlimit : DoubledSpace C.LimitBase → DoubledSpace C.LimitBase)
    (hT : ∀ n x, Tlimit (C.ι n x) = C.ι n (F.map n x))
    {n : ℕ} {x : DoubledSpace (C.Base n)}
    (hx_zero : F.map n x = 0) :
    Tlimit (C.ι n x) = 0 := by
  rw [hT n x, hx_zero]
  exact map_zero (C.ι n)

/-- Injectivity plus global intertwining transports a nontrivial stage kernel
element to a nontrivial kernel element of the descended global operator. -/
theorem globalKernel_survival
    (Tlimit : DoubledSpace C.LimitBase → DoubledSpace C.LimitBase)
    (hT : ∀ n x, Tlimit (C.ι n x) = C.ι n (F.map n x))
    {n : ℕ} {x : DoubledSpace (C.Base n)}
    (hι : Function.Injective (C.ι n))
    (hx_ne : x ≠ 0)
    (hx_zero : F.map n x = 0) :
    C.ι n x ≠ 0 ∧ Tlimit (C.ι n x) = 0 :=
  ⟨(F.zeroMode_survives_colimit hι hx_ne hx_zero).1,
    F.globalOperator_zero_of_stage_zero Tlimit hT hx_zero⟩

/-- After any finite number of bonding steps, the representative of a
nontrivial stage zero mode has the same nonzero colimit image. -/
theorem iterated_zeroMode_image_ne_zero
    {n m : ℕ} {x : DoubledSpace (C.Base n)}
    (hι : Function.Injective (C.ι n))
    (hx_ne : x ≠ 0) :
    C.ι (n + m)
      ((C.toFilteredPhaseCone).bondIterate n m x) ≠ 0 := by
  have hcompat :
      C.ι (n + m) ((C.toFilteredPhaseCone).bondIterate n m x) = C.ι n x := by
    simpa [HestenesKreinCone.toFilteredPhaseCone] using
      (C.toFilteredPhaseCone).ι_bondIterate_apply n m x
  rw [hcompat]
  intro hzero
  apply hx_ne
  apply hι
  simpa using hzero

/-- Kernel survival is independent of the chosen later-stage representative. -/
theorem iterated_globalKernel_survival
    (Tlimit : DoubledSpace C.LimitBase → DoubledSpace C.LimitBase)
    (hT : ∀ n x, Tlimit (C.ι n x) = C.ι n (F.map n x))
    {n m : ℕ} {x : DoubledSpace (C.Base n)}
    (hι : Function.Injective (C.ι n))
    (hx_ne : x ≠ 0)
    (hx_zero : F.map n x = 0) :
    C.ι (n + m)
        ((C.toFilteredPhaseCone).bondIterate n m x) ≠ 0 ∧
      Tlimit (C.ι (n + m)
        ((C.toFilteredPhaseCone).bondIterate n m x)) = 0 := by
  constructor
  · exact iterated_zeroMode_image_ne_zero (C := C) hι hx_ne
  · have hcompat :
        C.ι (n + m) ((C.toFilteredPhaseCone).bondIterate n m x) = C.ι n x := by
      simpa [HestenesKreinCone.toFilteredPhaseCone] using
        (C.toFilteredPhaseCone).ι_bondIterate_apply n m x
    rw [hcompat]
    exact F.globalOperator_zero_of_stage_zero Tlimit hT hx_zero

end InfoGeometry.Canonical.FilteredHestenesAnalyticFamily.AnalyticFamily
