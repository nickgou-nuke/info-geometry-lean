import InfoGeometry.Lie.CanonicalZornG2AppendixDGenerators
import InfoGeometry.Lie.SplitOctonionStandardDerivation

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2AppendixDSourceBridge

open InfoGeometry.Lie.CanonicalZornG2AppendixDGenerators
open InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionStandardDerivation

attribute [simp] epsilonAction_appendixD_expansion_public
attribute [simp] InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita.leviCivita3

abbrev Vector := AppendixDVector
abbrev Paper :=
  InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.PaperZorn

def paperTraceZero (X : Paper) : Prop := X.a + X.b = 0

theorem paperTraceZero_iff_canonicalTraceZero (X : Paper) :
    paperTraceZero X ↔
      realZornTrace (paperCanonicalLinearEquiv X) = 0 := by
  rfl

def traceZeroSubmodule : Submodule ℝ Paper where
  carrier := {X | paperTraceZero X}
  zero_mem' := by
    change (0 : ℝ) + 0 = 0
    ring
  add_mem' := by
    intro X Y hX hY
    change (X + Y).a + (X + Y).b = 0
    change X.a + X.b = 0 at hX
    change Y.a + Y.b = 0 at hY
    change X.a + Y.a + (X.b + Y.b) = 0
    linarith
  smul_mem' := by
    intro c X hX
    change (c • X).a + (c • X).b = 0
    change X.a + X.b = 0 at hX
    change c * X.a + c * X.b = 0
    calc
      c * X.a + c * X.b = c * (X.a + X.b) := (mul_add c X.a X.b).symm
      _ = 0 := by simp [hX]

abbrev TraceZeroPaper := traceZeroSubmodule

/-! The source carrier is the trace-zero Zorn hyperplane with coordinates
`(t,y,z) ↦ [[t,y],[z,-t]]`.  The map is kept linear and coordinate-free at
the API boundary; only the four native Zorn fields are exposed in its proof.
-/
noncomputable def vectorToPaper : Vector →ₗ[ℝ] Paper where
  toFun v := { a := v.1, b := -v.1, v := v.2.1, w := v.2.2 }
  map_add' v w := by
    cases v with
    | mk t yz =>
      cases yz with
      | mk y z =>
        cases w with
        | mk t' yz' =>
          cases yz' with
          | mk y' z' =>
            apply InfoGeometry.Algebra.ZornMatrix.ext
            · rfl
            · ext i; fin_cases i <;> rfl
            · ext i; fin_cases i <;> rfl
            · change -((t + t')) = -t + -t'
              ring
  map_smul' c v := by
    cases v with
    | mk t yz =>
      cases yz with
      | mk y z =>
        apply InfoGeometry.Algebra.ZornMatrix.ext
        · rfl
        · ext i; fin_cases i <;> rfl
        · ext i; fin_cases i <;> rfl
        · change -(c * t) = c * -t
          ring

attribute [simp] vectorToPaper

/-! The Appendix-D source basis and the canonical Zorn basis differ by the
orientation of the third axial pair.  This is a linear calibration, not a
new carrier: it sends the third `y` and `z` coordinates to their negatives. -/

noncomputable def appendixDOrientationCalibration : Vector ≃ₗ[ℝ] Vector where
  toFun v := (v.1,
    (fun i => if i = 2 then -v.2.1 i else v.2.1 i),
    (fun i => if i = 2 then -v.2.2 i else v.2.2 i))
  invFun v := (v.1,
    (fun i => if i = 2 then -v.2.1 i else v.2.1 i),
    (fun i => if i = 2 then -v.2.2 i else v.2.2 i))
  left_inv v := by
    cases v with
    | mk t yz =>
      cases yz with
      | mk y z =>
        apply Prod.ext
        · rfl
        · apply Prod.ext <;> funext i <;>
            by_cases h : i = 2 <;> simp [h]
  right_inv v := by
    cases v with
    | mk t yz =>
      cases yz with
      | mk y z =>
        apply Prod.ext
        · rfl
        · apply Prod.ext <;> funext i <;>
            by_cases h : i = 2 <;> simp [h]
  map_add' v w := by
    cases v with
    | mk t yz =>
      cases yz with
      | mk y z =>
        cases w with
        | mk t' yz' =>
          cases yz' with
          | mk y' z' =>
            apply Prod.ext
            · rfl
            · apply Prod.ext <;> funext i <;>
                by_cases h : i = 2 <;> simp [h, Pi.add_apply] <;> ring
  map_smul' c v := by
    cases v with
    | mk t yz =>
      cases yz with
      | mk y z =>
        apply Prod.ext
        · rfl
        · apply Prod.ext <;> funext i <;>
            by_cases h : i = 2 <;> simp [h, Pi.smul_apply]

@[simp] theorem appendixDOrientationCalibration_v (v : Vector) (i : Fin 3) :
    (appendixDOrientationCalibration v).2.1 i =
      if i = 2 then -v.2.1 i else v.2.1 i := rfl

@[simp] theorem appendixDOrientationCalibration_a (v : Vector) :
    (appendixDOrientationCalibration v).1 = v.1 := rfl

@[simp] theorem appendixDOrientationCalibration_w (v : Vector) (i : Fin 3) :
    (appendixDOrientationCalibration v).2.2 i =
      if i = 2 then -v.2.2 i else v.2.2 i := rfl

noncomputable def appendixDCalibratedVectorToPaper : Vector →ₗ[ℝ] Paper :=
  vectorToPaper.comp appendixDOrientationCalibration.toLinearMap

@[simp] theorem appendixDCalibratedVectorToPaper_apply (v : Vector) :
    appendixDCalibratedVectorToPaper v =
      vectorToPaper (appendixDOrientationCalibration v) := rfl

@[simp] theorem appendixDCalibratedVectorToPaper_a (v : Vector) :
    (appendixDCalibratedVectorToPaper v).a = v.1 := rfl

@[simp] theorem appendixDCalibratedVectorToPaper_b (v : Vector) :
    (appendixDCalibratedVectorToPaper v).b = -v.1 := rfl

@[simp] theorem appendixDCalibratedVectorToPaper_v (v : Vector) (i : Fin 3) :
    (appendixDCalibratedVectorToPaper v).v i =
      if i = 2 then -v.2.1 i else v.2.1 i := rfl

@[simp] theorem appendixDCalibratedVectorToPaper_w (v : Vector) (i : Fin 3) :
    (appendixDCalibratedVectorToPaper v).w i =
      if i = 2 then -v.2.2 i else v.2.2 i := rfl

theorem appendixDCalibratedVectorToPaper_source_a
    (S : Vector →ₗ[ℝ] Vector) (v : Vector) :
    (appendixDCalibratedVectorToPaper (S v)).a = (S v).1 := rfl

theorem appendixDCalibratedVectorToPaper_source_b
    (S : Vector →ₗ[ℝ] Vector) (v : Vector) :
    (appendixDCalibratedVectorToPaper (S v)).b = -(S v).1 := rfl

theorem appendixDCalibratedVectorToPaper_source_v
    (S : Vector →ₗ[ℝ] Vector) (v : Vector) (i : Fin 3) :
    (appendixDCalibratedVectorToPaper (S v)).v i =
      if i = 2 then -(S v).2.1 i else (S v).2.1 i := rfl

theorem appendixDCalibratedVectorToPaper_source_w
    (S : Vector →ₗ[ℝ] Vector) (v : Vector) (i : Fin 3) :
    (appendixDCalibratedVectorToPaper (S v)).w i =
      if i = 2 then -(S v).2.2 i else (S v).2.2 i := rfl

noncomputable def paperToVector : Paper →ₗ[ℝ] Vector where
  toFun X := ((X.a - X.b) / 2, X.v, X.w)
  map_add' X Y := by
    cases X with
    | mk a v w b =>
      cases Y with
      | mk a' v' w' b' =>
        apply Prod.ext
        · change ((a + a') - (b + b')) / 2 =
            (a - b) / 2 + (a' - b') / 2
          ring
        · apply Prod.ext
          · ext i; fin_cases i <;> rfl
          · ext i; fin_cases i <;> rfl
  map_smul' c X := by
    cases X with
    | mk a v w b =>
      apply Prod.ext
      · change (c * a - c * b) / 2 = c * ((a - b) / 2)
        ring
      · apply Prod.ext
        · ext i; fin_cases i <;> rfl
        · ext i; fin_cases i <;> rfl

theorem vectorToPaper_trace_zero (v : Vector) :
    paperTraceZero (vectorToPaper v) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      change t + -t = 0
      ring

@[simp] theorem paperToVector_vectorToPaper (v : Vector) :
    paperToVector (vectorToPaper v) = v := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply Prod.ext
      · change (t - -t) / 2 = t
        ring
      · apply Prod.ext <;> rfl

theorem vectorToPaper_paperToVector_of_trace_zero
    (X : Paper) (hX : paperTraceZero X) :
    vectorToPaper (paperToVector X) = X := by
  cases X with
  | mk a v w b =>
    change a + b = 0 at hX
    apply InfoGeometry.Algebra.ZornMatrix.ext
    · change (a - b) / 2 = a
      linarith
    · rfl
    · rfl
    · change -((a - b) / 2) = b
      linarith

def appendixDParameterXn0Zero : Params := parameterUnit 0 1

theorem appendixDXn0_zero_eq_parameterAction_calibrated (v : Vector) :
    appendixDCalibratedVectorToPaper (appendixDXn0 0 v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction appendixDParameterXn0Zero
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv
                (appendixDCalibratedVectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      all_goals try simp only [appendixDCalibratedVectorToPaper_source_a,
        appendixDCalibratedVectorToPaper_source_b,
        appendixDCalibratedVectorToPaper_source_v,
        appendixDCalibratedVectorToPaper_source_w]
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration,
          vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
          appendixDParameterXn0Zero, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration,
            vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
            appendixDParameterXn0Zero, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;> norm_num at * <;>
          ring
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration,
            vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
            appendixDParameterXn0Zero, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;> norm_num at * <;>
          ring
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration,
          vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
          appendixDParameterXn0Zero, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]

def appendixDParameterX0nZero : Params := parameterUnit 10 (-1)

theorem appendixDX0n_zero_eq_parameterAction_calibrated (v : Vector) :
    appendixDCalibratedVectorToPaper (appendixDX0n 0 v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction appendixDParameterX0nZero
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv
                (appendixDCalibratedVectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
          appendixDParameterX0nZero, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
            appendixDParameterX0nZero, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;>
          ring
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
            appendixDParameterX0nZero, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;>
          ring
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
          appendixDParameterX0nZero, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]

def appendixDParameterXn0One : Params := parameterUnit 3 1

theorem appendixDXn0_one_eq_parameterAction_calibrated (v : Vector) :
    appendixDCalibratedVectorToPaper (appendixDXn0 1 v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction appendixDParameterXn0One
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv
                (appendixDCalibratedVectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
          appendixDParameterXn0One, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
            appendixDParameterXn0One, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;>
          ring
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
            appendixDParameterXn0One, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;>
          ring
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
          appendixDParameterXn0One, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]

def appendixDParameterXn0Two : Params := parameterUnit 8 (-1)

theorem appendixDXn0_two_eq_parameterAction_calibrated (v : Vector) :
    appendixDCalibratedVectorToPaper (appendixDXn0 2 v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction appendixDParameterXn0Two
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv
                (appendixDCalibratedVectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
          appendixDParameterXn0Two, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
            appendixDParameterXn0Two, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;>
          ring
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
            appendixDParameterXn0Two, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;>
          ring
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDXn0_a, appendixDXn0_y, appendixDXn0_z,
          appendixDParameterXn0Two, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]

def appendixDParameterX0nOne : Params := parameterUnit 9 1

theorem appendixDX0n_one_eq_parameterAction_calibrated (v : Vector) :
    appendixDCalibratedVectorToPaper (appendixDX0n 1 v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction appendixDParameterX0nOne
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv
                (appendixDCalibratedVectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
          appendixDParameterX0nOne, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
            appendixDParameterX0nOne, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;>
          ring
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
            appendixDParameterX0nOne, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;>
          ring
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
          appendixDParameterX0nOne, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]

def appendixDParameterX0nTwo : Params := parameterUnit 4 1

theorem appendixDX0n_two_eq_parameterAction_calibrated (v : Vector) :
    appendixDCalibratedVectorToPaper (appendixDX0n 2 v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction appendixDParameterX0nTwo
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv
                (appendixDCalibratedVectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
          appendixDParameterX0nTwo, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
            appendixDParameterX0nTwo, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;>
          ring
      · funext i
        fin_cases i <;>
          simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
            appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
            appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
            appendixDParameterX0nTwo, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
            Fin.sum_univ_three] <;>
          ring
      · simp [appendixDCalibratedVectorToPaper_apply, appendixDOrientationCalibration, vectorToPaper, appendixDCalibratedVectorToPaper_a, appendixDCalibratedVectorToPaper_b,
          appendixDCalibratedVectorToPaper_v, appendixDCalibratedVectorToPaper_w,
          appendixDX0n_a, appendixDX0n_y, appendixDX0n_z,
          appendixDParameterX0nTwo, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv,
          Fin.sum_univ_three]

def appendixDCalibratedParameterXnm (n m : Fin 3) : Params :=
  match n, m with
  | 0, 1 => parameterUnit 1 (-1)
  | 0, 2 => parameterUnit 2 1
  | 1, 0 => parameterUnit 5 (-1)
  | 1, 2 => parameterUnit 7 1
  | 2, 0 => parameterUnit 11 1
  | 2, 1 => parameterUnit 12 1
  | _, _ => 0

theorem appendixDXnm_calibrated_eq_parameterAction
    (n m : Fin 3) (h : n ≠ m) (v : Vector) :
    appendixDCalibratedVectorToPaper (appendixDXnm n m h v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction (appendixDCalibratedParameterXnm n m)
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv
                (appendixDCalibratedVectorToPaper v))))) := by
  fin_cases n <;> fin_cases m
  all_goals
    try { exact (h rfl).elim }
  all_goals
    cases v with
    | mk t yz =>
      cases yz with
      | mk y z =>
        apply InfoGeometry.Algebra.ZornMatrix.ext
        · simp [appendixDCalibratedVectorToPaper,
            appendixDXnm, appendixDXnm_a, appendixDXnm_y, appendixDXnm_z,
            appendixDCalibratedParameterXnm, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, Fin.sum_univ_three]
          <;> ring
        · funext i
          fin_cases i <;>
            simp [appendixDCalibratedVectorToPaper,
              appendixDXnm, appendixDXnm_a, appendixDXnm_y, appendixDXnm_z,
              appendixDCalibratedParameterXnm, parameterAction, parameterUnit,
              canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
              Fin.sum_univ_three] <;> ring
        · funext i
          fin_cases i <;>
            simp [appendixDCalibratedVectorToPaper,
              appendixDXnm, appendixDXnm_a, appendixDXnm_y, appendixDXnm_z,
              appendixDCalibratedParameterXnm, parameterAction, parameterUnit,
              canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
              Fin.sum_univ_three] <;> ring
        · simp [appendixDCalibratedVectorToPaper,
            appendixDXnm, appendixDXnm_a, appendixDXnm_y, appendixDXnm_z,
            appendixDCalibratedParameterXnm, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, Fin.sum_univ_three]
          <;> ring

def appendixDCalibratedParameterXn0 (n : Fin 3) : Params :=
  match n with
  | 0 => appendixDParameterXn0Zero
  | 1 => appendixDParameterXn0One
  | 2 => appendixDParameterXn0Two

theorem appendixDXn0_calibrated_eq_parameterAction
    (n : Fin 3) (v : Vector) :
    appendixDCalibratedVectorToPaper (appendixDXn0 n v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction (appendixDCalibratedParameterXn0 n)
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv
                (appendixDCalibratedVectorToPaper v))))) := by
  fin_cases n
  · simpa [appendixDCalibratedParameterXn0] using
      appendixDXn0_zero_eq_parameterAction_calibrated v
  · simpa [appendixDCalibratedParameterXn0] using
      appendixDXn0_one_eq_parameterAction_calibrated v
  · simpa [appendixDCalibratedParameterXn0] using
      appendixDXn0_two_eq_parameterAction_calibrated v

def appendixDCalibratedParameterX0n (n : Fin 3) : Params :=
  match n with
  | 0 => appendixDParameterX0nZero
  | 1 => appendixDParameterX0nOne
  | 2 => appendixDParameterX0nTwo

theorem appendixDX0n_calibrated_eq_parameterAction
    (n : Fin 3) (v : Vector) :
    appendixDCalibratedVectorToPaper (appendixDX0n n v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction (appendixDCalibratedParameterX0n n)
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv
                (appendixDCalibratedVectorToPaper v))))) := by
  fin_cases n
  · simpa [appendixDCalibratedParameterX0n] using
      appendixDX0n_zero_eq_parameterAction_calibrated v
  · simpa [appendixDCalibratedParameterX0n] using
      appendixDX0n_one_eq_parameterAction_calibrated v
  · simpa [appendixDCalibratedParameterX0n] using
      appendixDX0n_two_eq_parameterAction_calibrated v

def appendixDCalibratedParameterXnn (n : Fin 3) : Params :=
  match n with
  | 0 => (1 / 3 : ℝ) • (parameterUnit 6 + parameterUnit 13)
  | 1 => (-2 / 3 : ℝ) • parameterUnit 6 + (1 / 3 : ℝ) • parameterUnit 13
  | 2 => (1 / 3 : ℝ) • parameterUnit 6 - (2 / 3 : ℝ) • parameterUnit 13

theorem appendixDXnn_calibrated_eq_parameterAction
    (n : Fin 3) (v : Vector) :
    appendixDCalibratedVectorToPaper (appendixDXnn n v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction (appendixDCalibratedParameterXnn n)
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv
                (appendixDCalibratedVectorToPaper v))))) := by
  fin_cases n
  all_goals
    cases v with
    | mk t yz =>
      cases yz with
      | mk y z =>
        apply InfoGeometry.Algebra.ZornMatrix.ext
        · simp [appendixDCalibratedVectorToPaper,
            appendixDXnn, appendixDXnn_a, appendixDXnn_y, appendixDXnn_z,
            appendixDCalibratedParameterXnn, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, Fin.sum_univ_three]
          <;> ring
        · funext i
          fin_cases i <;>
            simp [appendixDCalibratedVectorToPaper,
              appendixDXnn, appendixDXnn_a, appendixDXnn_y, appendixDXnn_z,
              appendixDCalibratedParameterXnn, parameterAction, parameterUnit,
              canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
              Fin.sum_univ_three] <;> ring
        · funext i
          fin_cases i <;>
            simp [appendixDCalibratedVectorToPaper,
              appendixDXnn, appendixDXnn_a, appendixDXnn_y, appendixDXnn_z,
              appendixDCalibratedParameterXnn, parameterAction, parameterUnit,
              canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper,
              Fin.sum_univ_three] <;> ring
        · simp [appendixDCalibratedVectorToPaper,
            appendixDXnn, appendixDXnn_a, appendixDXnn_y, appendixDXnn_z,
            appendixDCalibratedParameterXnn, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, Fin.sum_univ_three]
          <;> ring

theorem appendixDCalibratedVectorToPaper_appendixDXnn_diagonal_relation
    (v : Vector) :
    appendixDCalibratedVectorToPaper
        ((appendixDXnn 0 + appendixDXnn 1 + appendixDXnn 2) v) = 0 := by
  rw [appendixDXnn_diagonal_relation]
  apply InfoGeometry.Algebra.ZornMatrix.ext
  · simp [InfoGeometry.Algebra.ZornMatrix.zero]
  · funext i
    dsimp [InfoGeometry.Algebra.ZornMatrix.zero]
    fin_cases i <;> simp
  · funext i
    dsimp [InfoGeometry.Algebra.ZornMatrix.zero]
    fin_cases i <;> simp
  · simp [InfoGeometry.Algebra.ZornMatrix.zero]

def appendixDParameterXnnZero : Params :=
  (1 / 3 : ℝ) • (parameterUnit 6 + parameterUnit 13)

theorem appendixDXnn_zero_eq_parameterAction (v : Vector) :
    vectorToPaper (appendixDXnn 0 v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction appendixDParameterXnnZero
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv (vectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · change (appendixDXnn 0 (t, y, z)).1 = _
        rw [appendixDXnn_a]
        simp [appendixDParameterXnnZero, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv]
      · funext i
        change (appendixDXnn 0 (t, y, z)).2.1 i = _
        rw [appendixDXnn_y]
        fin_cases i <;>
          simp [appendixDParameterXnnZero, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · funext i
        change (appendixDXnn 0 (t, y, z)).2.2 i = _
        rw [appendixDXnn_z]
        fin_cases i <;>
          simp [appendixDParameterXnnZero, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · change -(appendixDXnn 0 (t, y, z)).1 = _
        rw [appendixDXnn_a]
        simp [appendixDParameterXnnZero, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv]

def appendixDParameterXnnOne : Params :=
  (-2 / 3 : ℝ) • parameterUnit 6 + (1 / 3 : ℝ) • parameterUnit 13

theorem appendixDXnn_one_eq_parameterAction (v : Vector) :
    vectorToPaper (appendixDXnn 1 v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction appendixDParameterXnnOne
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv (vectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · change (appendixDXnn 1 (t, y, z)).1 = _
        rw [appendixDXnn_a]
        simp [appendixDParameterXnnOne, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv]
      · funext i
        change (appendixDXnn 1 (t, y, z)).2.1 i = _
        rw [appendixDXnn_y]
        fin_cases i <;>
          simp [appendixDParameterXnnOne, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · funext i
        change (appendixDXnn 1 (t, y, z)).2.2 i = _
        rw [appendixDXnn_z]
        fin_cases i <;>
          simp [appendixDParameterXnnOne, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · change -(appendixDXnn 1 (t, y, z)).1 = _
        rw [appendixDXnn_a]
        simp [appendixDParameterXnnOne, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv]

def appendixDParameterXnnTwo : Params :=
  (1 / 3 : ℝ) • parameterUnit 6 - (2 / 3 : ℝ) • parameterUnit 13

theorem appendixDXnn_two_eq_parameterAction (v : Vector) :
    vectorToPaper (appendixDXnn 2 v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction appendixDParameterXnnTwo
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv (vectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · change (appendixDXnn 2 (t, y, z)).1 = _
        rw [appendixDXnn_a]
        simp [appendixDParameterXnnTwo, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv]
      · funext i
        change (appendixDXnn 2 (t, y, z)).2.1 i = _
        rw [appendixDXnn_y]
        fin_cases i <;>
          simp [appendixDParameterXnnTwo, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · funext i
        change (appendixDXnn 2 (t, y, z)).2.2 i = _
        rw [appendixDXnn_z]
        fin_cases i <;>
          simp [appendixDParameterXnnTwo, parameterAction, parameterUnit,
            canonicalVectorEquiv, paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · change -(appendixDXnn 2 (t, y, z)).1 = _
        rw [appendixDXnn_a]
        simp [appendixDParameterXnnTwo, parameterAction, parameterUnit,
          canonicalVectorEquiv, paperCanonicalLinearEquiv]

theorem appendixDXnm_zero_one_eq_parameterAction (v : Vector) :
    vectorToPaper (appendixDXnm 0 1 (by decide) v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction (parameterUnit 1 (-1))
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv (vectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · change (appendixDXnm 0 1 (by decide) (t, y, z)).1 = _
        rw [appendixDXnm_a]
        simp [parameterAction, parameterUnit, canonicalVectorEquiv,
          paperCanonicalLinearEquiv]

      · funext i
        change (appendixDXnm 0 1 (by decide) (t, y, z)).2.1 i = _
        rw [appendixDXnm_y]
        fin_cases i <;>
          simp [parameterAction, parameterUnit, canonicalVectorEquiv,
            paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · funext i
        change (appendixDXnm 0 1 (by decide) (t, y, z)).2.2 i = _
        rw [appendixDXnm_z]
        fin_cases i <;>
          simp [parameterAction, parameterUnit, canonicalVectorEquiv,
            paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · change -(appendixDXnm 0 1 (by decide) (t, y, z)).1 = _
        rw [appendixDXnm_a]
        simp [parameterAction, parameterUnit, canonicalVectorEquiv,
          paperCanonicalLinearEquiv]

theorem appendixDXnm_zero_two_eq_parameterAction (v : Vector) :
    vectorToPaper (appendixDXnm 0 2 (by decide) v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction (parameterUnit 2 (-1))
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv (vectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · change (appendixDXnm 0 2 (by decide) (t, y, z)).1 = _
        rw [appendixDXnm_a]
        simp [parameterAction, parameterUnit, canonicalVectorEquiv,
          paperCanonicalLinearEquiv]
      · funext i
        change (appendixDXnm 0 2 (by decide) (t, y, z)).2.1 i = _
        rw [appendixDXnm_y]
        fin_cases i <;>
          simp [parameterAction, parameterUnit, canonicalVectorEquiv,
            paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · funext i
        change (appendixDXnm 0 2 (by decide) (t, y, z)).2.2 i = _
        rw [appendixDXnm_z]
        fin_cases i <;>
          simp [parameterAction, parameterUnit, canonicalVectorEquiv,
            paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · change -(appendixDXnm 0 2 (by decide) (t, y, z)).1 = _
        rw [appendixDXnm_a]
        simp [parameterAction, parameterUnit, canonicalVectorEquiv,
          paperCanonicalLinearEquiv]

theorem appendixDXnm_one_zero_eq_parameterAction (v : Vector) :
    vectorToPaper (appendixDXnm 1 0 (by decide) v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction (parameterUnit 5 (-1))
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv (vectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · change (appendixDXnm 1 0 (by decide) (t, y, z)).1 = _
        rw [appendixDXnm_a]
        simp [parameterAction, parameterUnit, canonicalVectorEquiv,
          paperCanonicalLinearEquiv]
      · funext i
        change (appendixDXnm 1 0 (by decide) (t, y, z)).2.1 i = _
        rw [appendixDXnm_y]
        fin_cases i <;>
          simp [parameterAction, parameterUnit, canonicalVectorEquiv,
            paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · funext i
        change (appendixDXnm 1 0 (by decide) (t, y, z)).2.2 i = _
        rw [appendixDXnm_z]
        fin_cases i <;>
          simp [parameterAction, parameterUnit, canonicalVectorEquiv,
            paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · change -(appendixDXnm 1 0 (by decide) (t, y, z)).1 = _
        rw [appendixDXnm_a]
        simp [parameterAction, parameterUnit, canonicalVectorEquiv,
          paperCanonicalLinearEquiv]

theorem appendixDXnm_one_two_eq_parameterAction (v : Vector) :
    vectorToPaper (appendixDXnm 1 2 (by decide) v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction (parameterUnit 7 (-1))
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv (vectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · change (appendixDXnm 1 2 (by decide) (t, y, z)).1 = _
        rw [appendixDXnm_a]
        simp [parameterAction, parameterUnit, canonicalVectorEquiv,
          paperCanonicalLinearEquiv]
      · funext i
        change (appendixDXnm 1 2 (by decide) (t, y, z)).2.1 i = _
        rw [appendixDXnm_y]
        fin_cases i <;>
          simp [parameterAction, parameterUnit, canonicalVectorEquiv,
            paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · funext i
        change (appendixDXnm 1 2 (by decide) (t, y, z)).2.2 i = _
        rw [appendixDXnm_z]
        fin_cases i <;>
          simp [parameterAction, parameterUnit, canonicalVectorEquiv,
            paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · change -(appendixDXnm 1 2 (by decide) (t, y, z)).1 = _
        rw [appendixDXnm_a]
        simp [parameterAction, parameterUnit, canonicalVectorEquiv,
          paperCanonicalLinearEquiv]

theorem appendixDXnm_two_zero_eq_parameterAction (v : Vector) :
    vectorToPaper (appendixDXnm 2 0 (by decide) v) =
      paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction (parameterUnit 11 (-1))
            (canonicalVectorEquiv
              (paperCanonicalLinearEquiv (vectorToPaper v))))) := by
  cases v with
  | mk t yz =>
    cases yz with
    | mk y z =>
      apply InfoGeometry.Algebra.ZornMatrix.ext
      · change (appendixDXnm 2 0 (by decide) (t, y, z)).1 = _
        rw [appendixDXnm_a]
        simp [parameterAction, parameterUnit, canonicalVectorEquiv,
          paperCanonicalLinearEquiv]
      · funext i
        change (appendixDXnm 2 0 (by decide) (t, y, z)).2.1 i = _
        rw [appendixDXnm_y]
        fin_cases i <;>
          simp [parameterAction, parameterUnit, canonicalVectorEquiv,
            paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · funext i
        change (appendixDXnm 2 0 (by decide) (t, y, z)).2.2 i = _
        rw [appendixDXnm_z]
        fin_cases i <;>
          simp [parameterAction, parameterUnit, canonicalVectorEquiv,
            paperCanonicalLinearEquiv, vectorToPaper]
        all_goals ring
      · change -(appendixDXnm 2 0 (by decide) (t, y, z)).1 = _
        rw [appendixDXnm_a]
        simp [parameterAction, parameterUnit, canonicalVectorEquiv,
          paperCanonicalLinearEquiv]

theorem vectorToPaper_injective : Function.Injective vectorToPaper := by
  intro v w h
  apply (paperToVector_vectorToPaper v).symm.trans
  rw [h]
  exact paperToVector_vectorToPaper w

theorem vectorToPaper_mem_iff (X : Paper) :
    (∃ v : Vector, vectorToPaper v = X) ↔ paperTraceZero X := by
  constructor
  · rintro ⟨v, rfl⟩
    exact vectorToPaper_trace_zero v
  · intro hX
    exact ⟨paperToVector X, vectorToPaper_paperToVector_of_trace_zero X hX⟩

noncomputable def vectorToTraceZero : Vector ≃ₗ[ℝ] TraceZeroPaper where
  toFun v := ⟨vectorToPaper v, vectorToPaper_trace_zero v⟩
  invFun X := paperToVector X
  left_inv v := paperToVector_vectorToPaper v
  right_inv X := by
    apply Subtype.ext
    exact vectorToPaper_paperToVector_of_trace_zero X.1 X.2
  map_add' v w := by
    apply Subtype.ext
    exact vectorToPaper.map_add v w
  map_smul' c v := by
    apply Subtype.ext
    exact vectorToPaper.map_smul c v

/-- The literal Appendix-D source carrier has the expected seven dimensions. -/
theorem appendixDVector_finrank :
    Module.finrank ℝ Vector = 7 := by
  simp [Vector, AppendixDVector, Module.finrank_prod,
    Module.finrank_pi_fintype]

theorem traceZeroPaper_finrank :
    Module.finrank ℝ TraceZeroPaper = 7 := by
  rw [← vectorToTraceZero.finrank_eq]
  exact appendixDVector_finrank

def transportSourceOperator (S : Module.End ℝ Vector) :
    Module.End ℝ TraceZeroPaper :=
  vectorToTraceZero.toLinearMap.comp
    (S.comp vectorToTraceZero.symm.toLinearMap)

@[simp] theorem transportSourceOperator_apply
    (S : Module.End ℝ Vector) (X : TraceZeroPaper) :
    transportSourceOperator S X =
      vectorToTraceZero (S (vectorToTraceZero.symm X)) :=
  rfl

theorem transportSourceOperator_add (S T : Module.End ℝ Vector) :
    transportSourceOperator (S + T) =
      transportSourceOperator S + transportSourceOperator T := by
  apply LinearMap.ext
  intro X
  apply vectorToTraceZero.symm.injective
  simp [transportSourceOperator, LinearMap.add_apply]

theorem transportSourceOperator_smul (c : ℝ) (S : Module.End ℝ Vector) :
    transportSourceOperator (c • S) = c • transportSourceOperator S := by
  apply LinearMap.ext
  intro X
  apply vectorToTraceZero.symm.injective
  simp [transportSourceOperator, LinearMap.smul_apply]

theorem transportSourceOperator_zero :
    transportSourceOperator (0 : Module.End ℝ Vector) = 0 := by
  apply LinearMap.ext
  intro X
  apply vectorToTraceZero.symm.injective
  simp [transportSourceOperator]

theorem transportSourceOperator_lie (S T : Module.End ℝ Vector) :
    transportSourceOperator ⁅S, T⁆ =
      ⁅transportSourceOperator S, transportSourceOperator T⁆ := by
  apply LinearMap.ext
  intro X
  apply vectorToTraceZero.symm.injective
  simp [transportSourceOperator, LieRing.of_associative_ring_bracket,
    LinearMap.comp_apply]

noncomputable def appendixDXnnTraceZero (n : Fin 3) :
    Module.End ℝ TraceZeroPaper :=
  transportSourceOperator (appendixDXnn n)

noncomputable def appendixDXnmTraceZero (n m : Fin 3) (h : n ≠ m) :
    Module.End ℝ TraceZeroPaper :=
  transportSourceOperator (appendixDXnm n m h)

noncomputable def appendixDXn0TraceZero (n : Fin 3) :
    Module.End ℝ TraceZeroPaper :=
  transportSourceOperator (appendixDXn0 n)

noncomputable def appendixDX0nTraceZero (n : Fin 3) :
    Module.End ℝ TraceZeroPaper :=
  transportSourceOperator (appendixDX0n n)

theorem appendixDXnnTraceZero_diagonal_relation :
    appendixDXnnTraceZero 0 + appendixDXnnTraceZero 1 +
        appendixDXnnTraceZero 2 = 0 := by
  simp only [appendixDXnnTraceZero]
  rw [← transportSourceOperator_add, ← transportSourceOperator_add]
  change transportSourceOperator
    (appendixDXnn 0 + appendixDXnn 1 + appendixDXnn 2) = 0
  rw [appendixDXnn_diagonal_relation, transportSourceOperator_zero]

/-! The calibrated Appendix-D parameter table spans all fourteen canonical
coordinates.  The two Cartan coordinates are recovered from the first two
diagonal combinations; all remaining coordinates occur as scaled table
entries. -/

noncomputable def appendixDCalibratedParameterFamily : Fin 15 → Params
  | 0 => appendixDCalibratedParameterXnn 0
  | 1 => appendixDCalibratedParameterXnn 1
  | 2 => appendixDCalibratedParameterXnn 2
  | 3 => appendixDCalibratedParameterXn0 0
  | 4 => appendixDCalibratedParameterXn0 1
  | 5 => appendixDCalibratedParameterXn0 2
  | 6 => appendixDCalibratedParameterX0n 0
  | 7 => appendixDCalibratedParameterX0n 1
  | 8 => appendixDCalibratedParameterX0n 2
  | 9 => appendixDCalibratedParameterXnm 0 1
  | 10 => appendixDCalibratedParameterXnm 0 2
  | 11 => appendixDCalibratedParameterXnm 1 0
  | 12 => appendixDCalibratedParameterXnm 1 2
  | 13 => appendixDCalibratedParameterXnm 2 0
  | 14 => appendixDCalibratedParameterXnm 2 1

theorem appendixD_parameterUnit_mem_span (j : Fin 14) :
    parameterUnit j ∈
      Submodule.span ℝ (Set.range appendixDCalibratedParameterFamily) := by
  let S : Submodule ℝ Params :=
    Submodule.span ℝ (Set.range appendixDCalibratedParameterFamily)
  have hmem (i : Fin 15) : appendixDCalibratedParameterFamily i ∈ S :=
    Submodule.subset_span ⟨i, rfl⟩
  have scaled_mem (j : Fin 14) (r : ℝ) (hr : r ≠ 0)
      (hm : parameterUnit j r ∈ S) : parameterUnit j ∈ S := by
    have hs := S.smul_mem r⁻¹ hm
    have heq : r⁻¹ • parameterUnit j r = parameterUnit j := by
      ext i
      simp only [parameterUnit, Pi.smul_apply, smul_eq_mul]
      split_ifs with h
      · exact inv_mul_cancel₀ hr
      · ring
    exact heq ▸ hs
  change parameterUnit j ∈ S
  have h0 := hmem 0
  have h1 := hmem 1
  have h3 := hmem 3
  have h4 := hmem 4
  have h5 := hmem 5
  have h6 := hmem 6
  have h7 := hmem 7
  have h8 := hmem 8
  have h9 := hmem 9
  have h10 := hmem 10
  have h11 := hmem 11
  have h12 := hmem 12
  have h13 := hmem 13
  have h14 := hmem 14
  change (1 / 3 : ℝ) • (parameterUnit 6 + parameterUnit 13) ∈ S at h0
  change (-2 / 3 : ℝ) • parameterUnit 6 +
    (1 / 3 : ℝ) • parameterUnit 13 ∈ S at h1
  have h3' : parameterUnit 0 1 ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterXn0,
      appendixDParameterXn0Zero] using h3
  have h4' : parameterUnit 3 1 ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterXn0,
      appendixDParameterXn0One] using h4
  have h5' : parameterUnit 8 (-1) ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterXn0,
      appendixDParameterXn0Two] using h5
  have h6' : parameterUnit 10 (-1) ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterX0n,
      appendixDParameterX0nZero] using h6
  have h7' : parameterUnit 9 1 ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterX0n,
      appendixDParameterX0nOne] using h7
  have h8' : parameterUnit 4 1 ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterX0n,
      appendixDParameterX0nTwo] using h8
  have h9' : parameterUnit 1 (-1) ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterXnm] using h9
  have h10' : parameterUnit 2 1 ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterXnm] using h10
  have h11' : parameterUnit 5 (-1) ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterXnm] using h11
  have h12' : parameterUnit 7 1 ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterXnm] using h12
  have h13' : parameterUnit 11 1 ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterXnm] using h13
  have h14' : parameterUnit 12 1 ∈ S := by
    simpa [appendixDCalibratedParameterFamily, appendixDCalibratedParameterXnm] using h14
  fin_cases j
  · exact scaled_mem 0 1 (by norm_num) h3'
  · exact scaled_mem 1 (-1) (by norm_num) h9'
  · exact scaled_mem 2 1 (by norm_num) h10'
  · exact scaled_mem 3 1 (by norm_num) h4'
  · exact scaled_mem 4 1 (by norm_num) h8'
  · exact scaled_mem 5 (-1) (by norm_num) h11'
  · have hx := S.sub_mem h0 h1
    convert hx using 1 <;> funext i <;> fin_cases i <;>
      simp [parameterUnit] <;> ring
  · exact scaled_mem 7 1 (by norm_num) h12'
  · exact scaled_mem 8 (-1) (by norm_num) h5'
  · exact scaled_mem 9 1 (by norm_num) h7'
  · exact scaled_mem 10 (-1) (by norm_num) h6'
  · exact scaled_mem 11 1 (by norm_num) h13'
  · exact scaled_mem 12 1 (by norm_num) h14'
  · have hx := S.add_mem (S.smul_mem 2 h0) h1
    convert hx using 1 <;> funext i <;> fin_cases i <;>
      simp [parameterUnit] <;> ring

theorem appendixD_calibrated_parameter_span_top :
    Submodule.span ℝ (Set.range appendixDCalibratedParameterFamily) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro p
  have hp : p = ∑ i : Fin 14, p i • parameterUnit i := by
    funext j
    simp [parameterUnit]
  rw [hp]
  exact Submodule.sum_mem _ (fun i _ =>
      (Submodule.span ℝ (Set.range appendixDCalibratedParameterFamily)).smul_mem _
      (appendixD_parameterUnit_mem_span i))

/-! The calibrated Appendix-D table is transported to the existing native
paper-side derivation Lie algebra. -/

noncomputable def appendixDCalibratedPaperDerivationFamily : Fin 15 →
    InfoGeometry.Lie.CanonicalZornG2AppendixDGenerators.PaperDer :=
  fun i =>
    InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge.paperDerivationLieEquiv
      (canonicalParameterLinearEquiv (appendixDCalibratedParameterFamily i))

theorem appendixD_calibrated_paperDerivation_span_top :
    Submodule.span ℝ (Set.range appendixDCalibratedPaperDerivationFamily) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro X
  let S : Submodule ℝ
      InfoGeometry.Lie.CanonicalZornG2AppendixDGenerators.PaperDer :=
    Submodule.span ℝ (Set.range appendixDCalibratedPaperDerivationFamily)
  let L : Params →ₗ[ℝ]
      InfoGeometry.Lie.CanonicalZornG2AppendixDGenerators.PaperDer :=
    InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge.paperDerivationLieEquiv.toLinearMap.comp
      canonicalParameterLinearEquiv.toLinearMap
  let p : Params :=
    canonicalParameterLinearEquiv.symm
      (InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge.paperDerivationLieEquiv.symm X)
  have hp : p ∈ Submodule.span ℝ (Set.range appendixDCalibratedParameterFamily) := by
    rw [appendixD_calibrated_parameter_span_top]
    exact Submodule.mem_top
  have hLp : L p ∈ S := by
    refine Submodule.span_induction (p := fun x _ => L x ∈ S) ?_ ?_ ?_ ?_ hp
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · simpa [L] using S.zero_mem
    · intro x y hx hy hx' hy'
      simpa [L] using S.add_mem hx' hy'
    · intro a x hx hx'
      simpa [L] using S.smul_mem a hx'
  simpa [S, L, p, appendixDCalibratedPaperDerivationFamily] using hLp

end InfoGeometry.Lie.CanonicalZornG2AppendixDSourceBridge
