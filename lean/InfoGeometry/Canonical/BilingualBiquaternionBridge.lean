import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BilingualRealHestenesDictionary
import InfoGeometry.Clifford.Biquaternion
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Canonical.BilingualBiquaternionBridge

open InfoGeometry.Canonical.BilingualRealHestenesDictionary
open InfoGeometry.Clifford
open InfoGeometry.Krein

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The STANDARD Biquaternion (ℍ ⊗ ℂ).
Here we represent it as a pair of real quaternionic-like operators (A, B)
which would classically be written as A + iB.
-/
structure StandardBiquaternion (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  realPart : DoubledSpace E →L[ℝ] DoubledSpace E
  imagPart : DoubledSpace E →L[ℝ] DoubledSpace E
  realPart_phaseLinear :
    InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := E) realPart
  imagPart_phaseLinear :
    InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := E) imagPart

theorem phaseLinear_clockAxis_comp_of_phaseLinear
    (B : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hB : InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := E) B) :
    InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear
      (E := E) ((clockAxis (E := E)).comp B) := by
  unfold InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear at hB ⊢
  apply ContinuousLinearMap.ext
  intro x
  have hK2 :
      (clockAxis (E := E)) ((clockAxis (E := E)) (B x)) = -B x := by
    exact congrArg (fun T : DoubledSpace E →L[ℝ] DoubledSpace E => T (B x))
      (clockAxis_sq (E := E))
  have hBcomm :
      B ((clockAxis (E := E)) x) = (clockAxis (E := E)) (B x) := by
    exact congrArg (fun T : DoubledSpace E →L[ℝ] DoubledSpace E => T x) hB
  calc
    (clockAxis (E := E)) (B ((clockAxis (E := E)) x))
        = (clockAxis (E := E)) ((clockAxis (E := E)) (B x)) := by rw [hBcomm]
    _ = -B x := hK2
    _ = (clockAxis (E := E)) ((clockAxis (E := E)) (B x)) := hK2.symm

omit [CompleteSpace E] in
theorem phaseLinear_add
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := E) A)
    (hB : InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := E) B) :
    InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := E) (A + B) := by
  unfold InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear at hA hB ⊢
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hA, hB]

/--
The Bilingual Bridge.
We explicitly use the `BilingualRealHestenesDictionary` to map the scalar `i`
of the standard biquaternion into the repo-native `clockAxis`.
-/
noncomputable def bilingualSoldering (q : StandardBiquaternion E) : Biquaternion E :=
  let A := q.realPart
  let B := q.imagPart
  let op := A + (clockAxis (E := E)).comp B
  { op := op
  , is_k_linear := by
      exact phaseLinear_add (E := E) A ((clockAxis (E := E)).comp B)
        q.realPart_phaseLinear
        (phaseLinear_clockAxis_comp_of_phaseLinear (E := E) B q.imagPart_phaseLinear)
  , is_biquaternionic := by use A, B
  }

end InfoGeometry.Canonical.BilingualBiquaternionBridge
