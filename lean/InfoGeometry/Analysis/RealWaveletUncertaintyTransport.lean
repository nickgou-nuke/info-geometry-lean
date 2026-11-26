/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.RealSchwartzUncertainty

/-!
# Real uncertainty transport through a scalar tight analysis map

An analysis map with a scalar tight-frame identity and derivative
intertwining transports the real Schwartz position/derivative uncertainty
principle. The hypotheses describe the analysis map, rather than storing an
uncertainty inequality or a precomputed moment pairing.

The result applies to analysis maps whose coefficient profiles are Schwartz
functions of one translation coordinate, with values in a real Hilbert space.
It does not construct the full Clifford continuous wavelet transform on
`SIM(n)` or assert that an arbitrary admissible wavelet has such profiles.
Those analytic identifications require separate regularity, measure, and
admissibility proofs.
-/

noncomputable section

namespace InfoGeometry.Analysis.RealWaveletUncertaintyTransport

open MeasureTheory

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- A real scalar tight analysis map which intertwines differentiation obeys
the directional moment uncertainty inequality. Position is centered at any
real `a`; no normalization of the input is needed.

The derivatives act on Schwartz space, so the theorem makes no boundedness
claim about differentiation or position multiplication on `L2`. -/
theorem scalar_tight_derivative_uncertainty
    (W : SchwartzMap ℝ H →ₗ[ℝ] SchwartzMap ℝ G)
    (C : ℝ) (hC : 0 < C)
    (htight : ∀ f, ‖(W f).toLp 2 volume‖ ^ 2 = C * ‖f.toLp 2 volume‖ ^ 2)
    (hderiv : ∀ f, SchwartzMap.derivCLM ℝ G (W f) =
      W (SchwartzMap.derivCLM ℝ H f))
    (f : SchwartzMap ℝ H) (a : ℝ) :
    C * ‖f.toLp 2 volume‖ ^ 4 ≤
      4 * ‖(SchwartzMap.smulLeftCLM G (fun b : ℝ => b - a) (W f)).toLp 2 volume‖ ^ 2 *
        ‖(SchwartzMap.derivCLM ℝ H f).toLp 2 volume‖ ^ 2 := by
  have h := RealSchwartzUncertainty.norm_four_le_four_mul_position_sq_mul_deriv_sq (W f) a
  have hfour : ‖(W f).toLp 2 volume‖ ^ 4 =
      (C * ‖f.toLp 2 volume‖ ^ 2) ^ 2 := by
    calc
      ‖(W f).toLp 2 volume‖ ^ 4 = (‖(W f).toLp 2 volume‖ ^ 2) ^ 2 := by ring
      _ = _ := by rw [htight f]
  rw [hfour, hderiv f, htight (SchwartzMap.derivCLM ℝ H f)] at h
  refine le_of_mul_le_mul_left (a := C) ?_ hC
  calc
    C * (C * ‖f.toLp 2 volume‖ ^ 4) =
        (C * ‖f.toLp 2 volume‖ ^ 2) ^ 2 := by ring
    _ ≤ 4 *
        ‖(SchwartzMap.smulLeftCLM G (fun b : ℝ => b - a) (W f)).toLp 2 volume‖ ^ 2 *
          (C * ‖(SchwartzMap.derivCLM ℝ H f).toLp 2 volume‖ ^ 2) := h
    _ = C * (4 *
        ‖(SchwartzMap.smulLeftCLM G (fun b : ℝ => b - a) (W f)).toLp 2 volume‖ ^ 2 *
          ‖(SchwartzMap.derivCLM ℝ H f).toLp 2 volume‖ ^ 2) := by ring

/-- Centered real uncertainty transport. In addition to differentiation,
`W` intertwines the actual pointwise phase lifts on source and coefficient
spaces. Only the coefficient phase needs an explicit skewness hypothesis.
The input phase is constrained by this intertwining and scalar tightness.

The shift parameter `b` is an arbitrary real number. No identification with
a Fourier frequency distribution is asserted by this theorem. -/
theorem scalar_tight_shifted_derivative_uncertainty
    (W : SchwartzMap ℝ H →ₗ[ℝ] SchwartzMap ℝ G)
    (C : ℝ) (hC : 0 < C)
    (htight : ∀ f, ‖(W f).toLp 2 volume‖ ^ 2 = C * ‖f.toLp 2 volume‖ ^ 2)
    (hderiv : ∀ f, SchwartzMap.derivCLM ℝ G (W f) =
      W (SchwartzMap.derivCLM ℝ H f))
    (KH : H →L[ℝ] H) (KG : G →L[ℝ] G)
    (hKG : ∀ u v, inner ℝ (KG u) v = -inner ℝ u (KG v))
    (hphase : ∀ f, SchwartzMap.postcompCLM KG (W f) =
      W (SchwartzMap.postcompCLM KH f))
    (f : SchwartzMap ℝ H) (a b : ℝ) :
    C * ‖f.toLp 2 volume‖ ^ 4 ≤
      4 * ‖(SchwartzMap.smulLeftCLM G (fun x : ℝ => x - a) (W f)).toLp 2 volume‖ ^ 2 *
        ‖(SchwartzMap.derivCLM ℝ H f -
          b • SchwartzMap.postcompCLM KH f).toLp 2 volume‖ ^ 2 := by
  have h := RealSchwartzUncertainty.norm_four_le_four_mul_position_sq_mul_shifted_deriv_sq
    (W f) a b KG hKG
  have hshift :
      SchwartzMap.derivCLM ℝ G (W f) - b • SchwartzMap.postcompCLM KG (W f) =
        W (SchwartzMap.derivCLM ℝ H f - b • SchwartzMap.postcompCLM KH f) := by
    rw [hderiv f, hphase f, map_sub, map_smul]
  have hfour : ‖(W f).toLp 2 volume‖ ^ 4 =
      (C * ‖f.toLp 2 volume‖ ^ 2) ^ 2 := by
    calc
      ‖(W f).toLp 2 volume‖ ^ 4 = (‖(W f).toLp 2 volume‖ ^ 2) ^ 2 := by ring
      _ = _ := by rw [htight f]
  rw [hfour, hshift,
    htight (SchwartzMap.derivCLM ℝ H f - b • SchwartzMap.postcompCLM KH f)] at h
  refine le_of_mul_le_mul_left (a := C) ?_ hC
  calc
    C * (C * ‖f.toLp 2 volume‖ ^ 4) =
        (C * ‖f.toLp 2 volume‖ ^ 2) ^ 2 := by ring
    _ ≤ 4 *
        ‖(SchwartzMap.smulLeftCLM G (fun x : ℝ => x - a) (W f)).toLp 2 volume‖ ^ 2 *
          (C * ‖(SchwartzMap.derivCLM ℝ H f -
            b • SchwartzMap.postcompCLM KH f).toLp 2 volume‖ ^ 2) := h
    _ = C * (4 *
        ‖(SchwartzMap.smulLeftCLM G (fun x : ℝ => x - a) (W f)).toLp 2 volume‖ ^ 2 *
          ‖(SchwartzMap.derivCLM ℝ H f -
            b • SchwartzMap.postcompCLM KH f).toLp 2 volume‖ ^ 2) := by ring

-- The identity analysis map with frame constant one satisfies the uncentered
-- transport hypotheses and recovers the source Schwartz uncertainty theorem.
example (f : SchwartzMap ℝ H) (a : ℝ) :
    ‖f.toLp 2 volume‖ ^ 4 ≤
      4 * ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ ^ 2 *
        ‖(SchwartzMap.derivCLM ℝ H f).toLp 2 volume‖ ^ 2 := by
  simpa only [LinearMap.id_apply, one_mul] using
    scalar_tight_derivative_uncertainty
      (LinearMap.id : SchwartzMap ℝ H →ₗ[ℝ] SchwartzMap ℝ H)
      1 zero_lt_one (by intro g; simp) (by intro g; rfl) f a

end InfoGeometry.Analysis.RealWaveletUncertaintyTransport
