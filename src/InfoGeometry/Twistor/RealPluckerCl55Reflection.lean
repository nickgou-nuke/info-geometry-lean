/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorBlockInversion
import InfoGeometry.Canonical.Cl55InfinityWittBoundary
import InfoGeometry.Clifford.Cl55WittOrthogonalReflections

/-!
# A native real Plücker/Clifford reflection intertwiner

The literal real Klein coordinates embed injectively into the existing
`V55` carrier, preserving its quadratic form and its Clifford anticommutator.
The exterior-square action of the real twistor block rotation intertwines
with the partial negative-sheet reflection in modes `0` and `4`.

This partial reflection exchanges the native infinity/origin pair. It is
different from the global particle/hole reflection. A concrete fixed-vector
obstruction proves that the latter cannot intertwine this real split-Klein
action through a quadratic-preserving map, for either overall form sign.
No complexification or Lorentzian real-slice identification is used.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealPluckerCl55Reflection

open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open InfoGeometry.Twistor.RealTwistorBlockInversion
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.PACSplit55Cl55CoordinateBridge
open InfoGeometry.Canonical.Cl55InfinityWittBoundary
open ProjectiveAffineConformalClosure55

/-- An explicit real split `(3,3)` subspace, with endpoints on native mode `4`. -/
def pluckerToPAC55 (P : Plucker6 ℝ) : PACSplit55 where
  x0 := (P.p03 + P.p12) / 2
  x1 := (P.p02 - P.p13) / 2
  x2 := 0
  x3 := 0
  y0 := (P.p12 - P.p03) / 2
  y1 := (P.p02 + P.p13) / 2
  y2 := 0
  y3 := 0
  u := (P.p01 + P.p23) / 2
  v := (P.p23 - P.p01) / 2

def pluckerToV55 (P : Plucker6 ℝ) : V55 :=
  pacSplit55ToV55 (pluckerToPAC55 P)

/-- Recover all six original coordinates from the actual native carrier. -/
def v55PluckerReadback (v : V55) : Plucker6 ℝ where
  p01 := v.1 4 - v.2 4
  p02 := v.1 1 + v.2 1
  p03 := v.1 0 - v.2 0
  p12 := v.1 0 + v.2 0
  p13 := v.2 1 - v.1 1
  p23 := v.1 4 + v.2 4

@[simp] theorem v55PluckerReadback_embedding (P : Plucker6 ℝ) :
    v55PluckerReadback (pluckerToV55 P) = P := by
  apply Plucker6.ext <;>
    dsimp [v55PluckerReadback, pluckerToV55, pluckerToPAC55, pacSplit55ToV55] <;>
    ring

theorem pluckerToV55_injective : Function.Injective pluckerToV55 :=
  Function.LeftInverse.injective v55PluckerReadback_embedding

/-- Native Clifford inclusion retains all six real Plücker coordinates. -/
theorem native_generator_injective :
    Function.Injective (fun P : Plucker6 ℝ => ι55 (pluckerToV55 P)) :=
  ι55_injective.comp pluckerToV55_injective

theorem pluckerToV55_add (P Q : Plucker6 ℝ) :
    pluckerToV55 (Plucker6.add P Q) = pluckerToV55 P + pluckerToV55 Q := by
  ext i <;> fin_cases i <;>
    simp [pluckerToV55, pluckerToPAC55, pacSplit55ToV55, Plucker6.add] <;>
    ring

theorem pluckerToV55_scale (c : ℝ) (P : Plucker6 ℝ) :
    pluckerToV55 (Plucker6.scale c P) = c • pluckerToV55 P := by
  ext i <;> fin_cases i <;>
    simp [pluckerToV55, pluckerToPAC55, pacSplit55ToV55, Plucker6.scale] <;>
    ring

/-- The real Klein form is preserved with its literal `(3,3)` sign convention. -/
theorem nativeQ55_pluckerToV55 (P : Plucker6 ℝ) :
    InfoGeometry.Clifford.Clifford55.Q55 (pluckerToV55 P) = kleinQ P := by
  unfold pluckerToV55
  rw [nativeQ55_pacSplit55ToV55]
  simp only [ProjectiveAffineConformalClosure55.Q55, pluckerToPAC55, kleinQ]
  ring

theorem nativePolar_pluckerToV55 (P Q : Plucker6 ℝ) :
    QuadraticMap.polar InfoGeometry.Clifford.Clifford55.Q55
        (pluckerToV55 P) (pluckerToV55 Q) = kleinPolar P Q := by
  rw [QuadraticMap.polar, ← pluckerToV55_add,
    nativeQ55_pluckerToV55, nativeQ55_pluckerToV55, nativeQ55_pluckerToV55]
  exact (kleinPolar_eq_kleinQ_add_sub P Q).symm

/-- The scalar readout follows from the canonical noncommutative Clifford relation. -/
theorem native_anticommutator_eq_kleinPolar (P Q : Plucker6 ℝ) :
    ι55 (pluckerToV55 P) * ι55 (pluckerToV55 Q) +
        ι55 (pluckerToV55 Q) * ι55 (pluckerToV55 P) =
      algebraMap ℝ Cl55 (kleinPolar P Q) := by
  rw [CliffordAlgebra.ι_mul_ι_add_swap, nativePolar_pluckerToV55]

theorem native_generator_sq (P : Plucker6 ℝ) :
    ι55 (pluckerToV55 P) * ι55 (pluckerToV55 P) =
      algebraMap ℝ Cl55 (kleinQ P) := by
  rw [CliffordAlgebra.ι_sq_scalar, nativeQ55_pluckerToV55]

theorem native_klein_generator_sq_zero (P : Plucker6 ℝ) (hP : kleinQ P = 0) :
    ι55 (pluckerToV55 P) * ι55 (pluckerToV55 P) = 0 := by
  rw [native_generator_sq, hP, map_zero]

/-- Only the two negative modes changed by the real exterior-square action. -/
def partialReflection (v : V55) : V55 :=
  negativeReflection 0 (negativeReflection 4 v)

def partialReflectionAlg : Cl55 ≃ₐ[ℝ] Cl55 :=
  (negativeReflectionAlg 4).trans (negativeReflectionAlg 0)

theorem partialReflection_preserves_Q55 (v : V55) :
    InfoGeometry.Clifford.Clifford55.Q55 (partialReflection v) =
      InfoGeometry.Clifford.Clifford55.Q55 v := by
  rw [partialReflection, negativeReflection_preserves_Q55,
    negativeReflection_preserves_Q55]

@[simp] theorem partialReflection_involutive (v : V55) :
    partialReflection (partialReflection v) = v := by
  unfold partialReflection
  rw [negativeReflection_commute 4 0 (negativeReflection 4 v),
    negativeReflection_involutive, negativeReflection_involutive]

theorem partialReflectionAlg_apply_ι (v : V55) :
    partialReflectionAlg (ι55 v) = ι55 (partialReflection v) := by
  change negativeReflectionAlg 0 (negativeReflectionAlg 4 (ι55 v)) = _
  rw [negativeReflectionAlg_apply_ι, negativeReflectionAlg_apply_ι]
  rfl

/-- The coordinate action is the actual restriction of the native orthogonal action. -/
theorem partialReflection_pluckerToV55 (P : Plucker6 ℝ) :
    partialReflection (pluckerToV55 P) = pluckerToV55 (pluckerRotation P) := by
  ext i <;> fin_cases i <;>
    simp [partialReflection, negativeReflection, pluckerRotation,
      pluckerToV55, pluckerToPAC55, pacSplit55ToV55] <;> ring

/-- The signed real intertwiner lands in the existing native Clifford algebra. -/
theorem native_reflection_intertwiner (P : Plucker6 ℝ) :
    partialReflectionAlg (ι55 (pluckerToV55 P)) =
      ι55 (pluckerToV55 (pluckerRotation P)) := by
  rw [partialReflectionAlg_apply_ι, partialReflection_pluckerToV55]

theorem native_image_infinity :
    pluckerToV55 ⟨1, 0, 0, 0, 0, 0⟩ = infinityVector55 := by
  ext i <;> fin_cases i <;>
    norm_num [pluckerToV55, pluckerToPAC55, pacSplit55ToV55,
      infinityVector55, n_bar_vec, nbar_pair, e_pos, f_neg]

theorem native_image_origin :
    pluckerToV55 ⟨0, 0, 0, 0, 0, 1⟩ = originVector55 := by
  ext i <;> fin_cases i <;>
    norm_num [pluckerToV55, pluckerToPAC55, pacSplit55ToV55,
      originVector55, n_vec, n_pair, e_pos, f_neg]

theorem partialReflection_infinity :
    partialReflection infinityVector55 = originVector55 := by
  rw [← native_image_infinity, partialReflection_pluckerToV55]
  exact native_image_origin

theorem partialReflection_origin :
    partialReflection originVector55 = infinityVector55 := by
  rw [← native_image_origin, partialReflection_pluckerToV55]
  exact native_image_infinity

theorem partialReflectionAlg_infinity :
    partialReflectionAlg infinityClifford55 = originClifford55 := by
  rw [infinityClifford55, partialReflectionAlg_apply_ι, partialReflection_infinity]
  rfl

theorem partialReflectionAlg_origin :
    partialReflectionAlg originClifford55 = infinityClifford55 := by
  rw [originClifford55, partialReflectionAlg_apply_ι, partialReflection_origin]
  rfl

theorem plucker_affineGauge (P : Plucker6 ℝ) :
    affineGaugeCoord (pluckerToPAC55 P) = P.p23 := by
  dsimp [affineGaugeCoord, pluckerToPAC55]
  ring

theorem plucker_complementaryGauge (P : Plucker6 ℝ) :
    complementaryGaugeCoord (pluckerToPAC55 P) = P.p01 := by
  dsimp [complementaryGaugeCoord, pluckerToPAC55]
  ring

theorem native_infinity_reads_p23 (P : Plucker6 ℝ) :
    infinityClifford55 * ι55 (pluckerToV55 P) +
        ι55 (pluckerToV55 P) * infinityClifford55 =
      algebraMap ℝ Cl55 P.p23 := by
  simpa only [infinityClifford55, pluckerToV55, plucker_affineGauge] using
    infinity_reads_affineGauge (pluckerToPAC55 P)

theorem native_origin_reads_p01 (P : Plucker6 ℝ) :
    originClifford55 * ι55 (pluckerToV55 P) +
        ι55 (pluckerToV55 P) * originClifford55 =
      algebraMap ℝ Cl55 P.p01 := by
  simpa only [originClifford55, pluckerToV55, plucker_complementaryGauge] using
    origin_reads_complementaryGauge (pluckerToPAC55 P)

/-! The global particle/hole action is a different orthogonal transformation. -/

theorem partialReflection_ne_globalSheetReflection :
    partialReflection ≠ globalSheetReflection := by
  intro h
  have hcoord := congrArg (fun f : V55 → V55 => (f (f_neg 1)).2 1) h
  norm_num [partialReflection, negativeReflection, globalSheetReflection, f_neg] at hcoord

/-- A global-reflection fixed vector has no negative-sheet component. -/
theorem globalSheetReflection_fixed_Q55_nonneg (v : V55)
    (hv : globalSheetReflection v = v) :
    0 ≤ InfoGeometry.Clifford.Clifford55.Q55 v := by
  have hneg : v.2 = 0 := by
    funext i
    have hi := congrArg (fun w : V55 => w.2 i) hv
    change -v.2 i = v.2 i at hi
    change v.2 i = 0
    linarith
  have hpos : 0 ≤ ∑ i : Fin 5, v.1 i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (v.1 i))
  simpa [InfoGeometry.Clifford.Clifford55.Q55_apply, hneg] using hpos

/-- A fixed negative-norm Klein vector obstructs the proposed global identification. -/
theorem no_global_reflection_intertwiner :
    ¬ ∃ E : Plucker6 ℝ → V55,
      (∀ P, InfoGeometry.Clifford.Clifford55.Q55 (E P) = kleinQ P) ∧
        (∀ P, globalSheetReflection (E P) = E (pluckerRotation P)) := by
  rintro ⟨E, hQ, hF⟩
  let P : Plucker6 ℝ := ⟨0, 1, 0, 0, 1, 0⟩
  have hT : pluckerRotation P = P := rfl
  have hfixed : globalSheetReflection (E P) = E P :=
    (hF P).trans (congrArg E hT)
  have hn := globalSheetReflection_fixed_Q55_nonneg (E P) hfixed
  rw [hQ] at hn
  norm_num [P, kleinQ] at hn

/-- Changing only the overall quadratic sign does not repair that identification. -/
theorem no_global_reflection_intertwiner_neg_form :
    ¬ ∃ E : Plucker6 ℝ → V55,
      (∀ P, InfoGeometry.Clifford.Clifford55.Q55 (E P) = -kleinQ P) ∧
        (∀ P, globalSheetReflection (E P) = E (pluckerRotation P)) := by
  rintro ⟨E, hQ, hF⟩
  let P : Plucker6 ℝ := ⟨1, 0, 0, 0, 0, 1⟩
  have hT : pluckerRotation P = P := rfl
  have hfixed : globalSheetReflection (E P) = E P :=
    (hF P).trans (congrArg E hT)
  have hn := globalSheetReflection_fixed_Q55_nonneg (E P) hfixed
  rw [hQ] at hn
  norm_num [P, kleinQ] at hn

end InfoGeometry.Twistor.RealPluckerCl55Reflection
