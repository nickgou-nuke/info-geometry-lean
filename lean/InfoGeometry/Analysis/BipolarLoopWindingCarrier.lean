import InfoGeometry.Analysis.BipolarLoopExpLift
import InfoGeometry.Analysis.BipolarLoopCrossRatioLift
import InfoGeometry.Analysis.BipolarWindingPeriodLattice

/-!
# Integer endpoint readout for logarithmic loop lifts

The exponential covering supplies an integer deck translation for every loop in
`ℂˣ`.  This file makes that integer a canonical native readout by choice, and
proves its endpoint and period laws.  It does not identify arbitrary loops in
the twice-punctured plane with `ℤ × ℤ`; that requires the separate winding
classification frontier.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarLoopWindingCarrier

open Complex Topology
open InfoGeometry.Analysis.BipolarAdmissibleLoops
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLoopExpLift
open InfoGeometry.Analysis.BipolarLoopCrossRatioLift
open InfoGeometry.Analysis.BipolarNativeExpCoveringBridge
open InfoGeometry.Analysis.BipolarWindingPeriodLattice

abbrev NonzeroComplex := {z : ℂ // z ≠ 0}
abbrev Period := 2 * (Real.pi : ℂ) * Complex.I

/-- The deck integer selected by the native exponential lift of a loop. -/
noncomputable def liftEndpointInteger
    {x : NonzeroComplex} (γ : Path x x) (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) : ℤ :=
  Classical.choose (exp_lift_loop_endpoint_period γ W hW)

/-- The selected integer is the endpoint translation of the actual lift. -/
theorem liftEndpointInteger_spec
    {x : NonzeroComplex} (γ : Path x x) (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    (Complex.isCoveringMap_exp.liftPath γ W (γ.source.trans hW)) 1 =
      W + (liftEndpointInteger γ W hW : ℂ) * Period := by
  exact Classical.choose_spec (exp_lift_loop_endpoint_period γ W hW)

/-- The endpoint readout is unique: a fixed logarithm fibre has one integer
deck translation. -/
theorem liftEndpointInteger_unique
    {x : NonzeroComplex} (γ : Path x x) (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex))
    {m n : ℤ}
    (hm : (Complex.isCoveringMap_exp.liftPath γ W (γ.source.trans hW)) 1 =
      W + (m : ℂ) * Period)
    (hn : (Complex.isCoveringMap_exp.liftPath γ W (γ.source.trans hW)) 1 =
      W + (n : ℂ) * Period) :
    m = n := by
  have hmn : (m : ℂ) * Period = (n : ℂ) * Period := by
    calc
      (m : ℂ) * Period =
          ((Complex.isCoveringMap_exp.liftPath γ W (γ.source.trans hW)) 1 - W) := by
            rw [hm]
            ring
      _ = (n : ℂ) * Period := by
            rw [hn]
            ring
  have hperiod : Period ≠ 0 := by
    exact Complex.two_pi_I_ne_zero
  have hcast : (m : ℂ) = (n : ℂ) := by
    exact (mul_right_cancel₀ hperiod hmn)
  exact_mod_cast hcast

/-- The chosen endpoint translation is the unique deck integer for the lift. -/
theorem liftEndpointInteger_eq_of_endpoint
    {x : NonzeroComplex} (γ : Path x x) (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex))
    {n : ℤ}
    (hn : (Complex.isCoveringMap_exp.liftPath γ W (γ.source.trans hW)) 1 =
      W + (n : ℂ) * Period) :
    liftEndpointInteger γ W hW = n := by
  apply liftEndpointInteger_unique γ W hW
    (liftEndpointInteger_spec γ W hW) hn

/-- The corresponding period is the endpoint displacement of the lift. -/
theorem liftEndpointPeriod_eq_sub
    {x : NonzeroComplex} (γ : Path x x) (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    (liftEndpointInteger γ W hW : ℂ) * Period =
      (Complex.isCoveringMap_exp.liftPath γ W (γ.source.trans hW)) 1 - W := by
  rw [liftEndpointInteger_spec γ W hW]
  ring

/-- A native integer deck readout is additive after passing to its period. -/
theorem liftEndpointPeriod_mem_nativeDeck
    {x : NonzeroComplex} (γ : Path x x) (W : ℂ)
    (hW : x = (⟨Complex.exp W, Complex.exp_ne_zero W⟩ : NonzeroComplex)) :
    (liftEndpointInteger γ W hW : ℂ) * Period ∈
      AddSubgroup.zmultiples Period := by
  apply AddSubgroup.mem_zmultiples_iff.mpr
  exact ⟨liftEndpointInteger γ W hW, by rw [zsmul_eq_mul]⟩

/-! ### Canonical bipolar pair readout

The two entries below are obtained from the actual lifts of the two
nonvanishing coordinates `s / (1 - s)` and `s - 1`.  This is a covering-space
readout, not a definition of winding by the contour integral and not yet a
classification of all loop classes in the twice-punctured plane.
-/

private theorem crossRatioPath_basepoint_exp_log (γ : AdmissibleLoop) :
    bipolarCrossRatioMap (basePoint γ) =
      (⟨Complex.exp (bipolarLog γ.base), Complex.exp_ne_zero _⟩ : NonzeroComplex) := by
  apply Subtype.ext
  change crossRatio01 γ.base = Complex.exp (bipolarLog γ.base)
  exact (exp_bipolarLog (basePoint γ).property).symm

private theorem crossRatioPath_source_eq_exp_log (γ : AdmissibleLoop) :
    crossRatioPath γ 0 =
      (⟨Complex.exp (bipolarLog γ.base), Complex.exp_ne_zero _⟩ : NonzeroComplex) := by
  exact (crossRatioPath γ).source.trans (crossRatioPath_basepoint_exp_log γ)

/-! ### Named native logarithmic lifts

These are the actual continuous path lifts supplied by Mathlib's exponential
covering.  Naming them gives downstream analytic owners one canonical carrier
for the two logarithmic coordinates; no logarithm branch or contour integral is
chosen by definition. -/

noncomputable def nativeCrossRatioLift (γ : AdmissibleLoop) :
    C(↑unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftPath (crossRatioPath γ)
    (bipolarLog γ.base) (crossRatioPath_source_eq_exp_log γ)

noncomputable def nativeShiftedLift (γ : AdmissibleLoop) :
    C(↑unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftPath (shiftedPath γ)
    (Complex.log (γ.base - 1)) (shiftedPath_source_eq_exp_log γ)

theorem nativeCrossRatioLift_lifts (γ : AdmissibleLoop) :
    (fun t => Complex.exp (nativeCrossRatioLift γ t)) =
      (fun t => (crossRatioPath γ t : ℂ)) := by
  funext t
  have h := congrFun (Complex.isCoveringMap_exp.liftPath_lifts
    (crossRatioPath γ) (bipolarLog γ.base)
    (crossRatioPath_source_eq_exp_log γ)) t
  exact congrArg Subtype.val h

theorem nativeShiftedLift_lifts (γ : AdmissibleLoop) :
    (fun t => Complex.exp (nativeShiftedLift γ t)) =
      (fun t => (shiftedPath γ t : ℂ)) := by
  funext t
  have h := congrFun (Complex.isCoveringMap_exp.liftPath_lifts
    (shiftedPath γ) (Complex.log (γ.base - 1))
    (shiftedPath_source_eq_exp_log γ)) t
  exact congrArg Subtype.val h

@[simp] theorem nativeCrossRatioLift_zero (γ : AdmissibleLoop) :
    nativeCrossRatioLift γ 0 = bipolarLog γ.base := by
  exact Complex.isCoveringMap_exp.liftPath_zero (crossRatioPath γ)
    (bipolarLog γ.base) (crossRatioPath_source_eq_exp_log γ)

@[simp] theorem nativeShiftedLift_zero (γ : AdmissibleLoop) :
    nativeShiftedLift γ 0 = Complex.log (γ.base - 1) := by
  exact Complex.isCoveringMap_exp.liftPath_zero (shiftedPath γ)
    (Complex.log (γ.base - 1)) (shiftedPath_source_eq_exp_log γ)

theorem nativeCrossRatioLift_endpoint_period (γ : AdmissibleLoop) :
    ∃ n : ℤ,
      nativeCrossRatioLift γ 1 =
        bipolarLog γ.base + n * Period := by
  exact exp_lift_loop_endpoint_period (crossRatioPath γ)
    (bipolarLog γ.base) (crossRatioPath_basepoint_exp_log γ)

theorem nativeShiftedLift_endpoint_period (γ : AdmissibleLoop) :
    ∃ n : ℤ,
      nativeShiftedLift γ 1 =
        Complex.log (γ.base - 1) + n * Period := by
  exact exp_lift_loop_endpoint_period (shiftedPath γ)
    (Complex.log (γ.base - 1)) (shiftedBasePoint_eq_exp_log γ)

noncomputable def bipolarLiftEndpointPair (γ : AdmissibleLoop) : WindingPair :=
  (liftEndpointInteger (crossRatioPath γ) (bipolarLog γ.base)
      (crossRatioPath_basepoint_exp_log γ),
    liftEndpointInteger (shiftedPath γ) (Complex.log (γ.base - 1))
      (shiftedBasePoint_eq_exp_log γ))

theorem bipolarLiftEndpointPair_crossRatio_spec (γ : AdmissibleLoop) :
    (Complex.isCoveringMap_exp.liftPath (crossRatioPath γ)
      (bipolarLog γ.base) (crossRatioPath_source_eq_exp_log γ)) 1 =
        bipolarLog γ.base +
          (bipolarLiftEndpointPair γ).1 * Period := by
  exact liftEndpointInteger_spec (crossRatioPath γ) (bipolarLog γ.base)
    (crossRatioPath_basepoint_exp_log γ)

theorem bipolarLiftEndpointPair_shifted_spec (γ : AdmissibleLoop) :
    (Complex.isCoveringMap_exp.liftPath (shiftedPath γ)
      (Complex.log (γ.base - 1)) (shiftedPath_source_eq_exp_log γ)) 1 =
        Complex.log (γ.base - 1) +
          (bipolarLiftEndpointPair γ).2 * Period := by
  exact liftEndpointInteger_spec (shiftedPath γ) (Complex.log (γ.base - 1))
    (shiftedBasePoint_eq_exp_log γ)

theorem bipolarLiftEndpointPair_period_spec (γ : AdmissibleLoop) :
    ((bipolarLiftEndpointPair γ).1 : ℂ) * Period =
    (Complex.isCoveringMap_exp.liftPath (crossRatioPath γ)
          (bipolarLog γ.base) (crossRatioPath_source_eq_exp_log γ)) 1 -
          bipolarLog γ.base ∧
    ((bipolarLiftEndpointPair γ).2 : ℂ) * Period =
    (Complex.isCoveringMap_exp.liftPath (shiftedPath γ)
          (Complex.log (γ.base - 1)) (shiftedPath_source_eq_exp_log γ)) 1 -
          Complex.log (γ.base - 1) := by
  constructor
  · exact liftEndpointPeriod_eq_sub (crossRatioPath γ) (bipolarLog γ.base)
      (crossRatioPath_basepoint_exp_log γ)
  · exact liftEndpointPeriod_eq_sub (shiftedPath γ) (Complex.log (γ.base - 1))
      (shiftedBasePoint_eq_exp_log γ)

theorem bipolarLiftEndpointPair_period_mem_nativeDeck (γ : AdmissibleLoop) :
    ((bipolarLiftEndpointPair γ).1 : ℂ) * Period ∈
        AddSubgroup.zmultiples Period ∧
    ((bipolarLiftEndpointPair γ).2 : ℂ) * Period ∈
        AddSubgroup.zmultiples Period := by
  constructor
  · exact liftEndpointPeriod_mem_nativeDeck (crossRatioPath γ)
      (bipolarLog γ.base) (crossRatioPath_basepoint_exp_log γ)
  · exact liftEndpointPeriod_mem_nativeDeck (shiftedPath γ)
      (Complex.log (γ.base - 1)) (shiftedBasePoint_eq_exp_log γ)

end InfoGeometry.Analysis.BipolarLoopWindingCarrier
