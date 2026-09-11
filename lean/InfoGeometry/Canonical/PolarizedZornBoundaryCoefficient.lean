import InfoGeometry.Streaming.TwoBoundaryDyadCompression
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# What a product of boundary coefficients actually computes

The product `<post|v> f(pre)` is the numerator of the rank-one probe
`v tensor f`. Its normalization is the independently supplied total overlap,
not that product itself. The existing weak functional and normalized dyad
are reused unchanged; no trace/determinant encoding is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.PolarizedZornBoundaryCoefficient

open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
open InfoGeometry.Streaming.TwoBoundaryDyadCompression

variable {ι : Type*} [Fintype ι]

/-- The attachment's product is an actual rank-one matrix coefficient. -/
theorem rankOne_numerator (p : RegularBoundaryPair ι)
    (v : State ι) (f : Module.Dual ℂ (State ι)) :
    numerator p (f.smulRight v) = pairing p.post v * f p.pre := by
  change pairing p.post (f p.pre • v) = _
  rw [pairing_smul_right]
  ring

/-- The denominator is the original overlap, independently of the inserted probe. -/
theorem rankOne_weakValue (p : RegularBoundaryPair ι)
    (v : State ι) (f : Module.Dual ℂ (State ι)) :
    weakValue p (f.smulRight v) = (pairing p.post v * f p.pre) / overlap p := by
  rw [weakValue, rankOne_numerator]

/-- The exact source-derived bridge to the established compression theorem. -/
theorem rankOne_boundary_compression (p : RegularBoundaryPair ι)
    (v : State ι) (f : Module.Dual ℂ (State ι)) :
    boundaryDyad p * f.smulRight v * boundaryDyad p =
      ((pairing p.post v * f p.pre) / overlap p) • boundaryDyad p := by
  rw [boundaryDyad_compression, rankOne_weakValue]

/-- Changing the probe changes the weak value even though boundary data,
and therefore any fixed boundary trace or determinant, stay unchanged. -/
theorem same_boundary_distinct_probe_readouts (p : RegularBoundaryPair ι) :
    weakValue p (0 : Operator ι) = 0 ∧ weakValue p (1 : Operator ι) = 1 ∧
      weakValue p (0 : Operator ι) ≠ weakValue p (1 : Operator ι) := by
  simp

/-- A constant function of boundary-only invariants cannot represent the
entire probe-dependent weak functional. -/
theorem no_boundary_only_weakValue (p : RegularBoundaryPair ι) :
    ¬ ∃ c : ℂ, ∀ A : Operator ι, weakValue p A = c := by
  rintro ⟨c, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  rw [weakValue_zero] at h0
  rw [weakValue_one] at h1
  exact zero_ne_one (h0.trans h1.symm)

end InfoGeometry.Canonical.PolarizedZornBoundaryCoefficient
