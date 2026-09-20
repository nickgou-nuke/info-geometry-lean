import InfoGeometry.Topology.MobiusProjectiveAction
import InfoGeometry.Topology.ThermodynamicSL2MobiusFlow

noncomputable section

namespace InfoGeometry.Topology.ThermodynamicProjectiveFlow

open MobiusProjectiveAction ThermodynamicSL2MobiusFlow
open ThermodynamicSL2Variation

def flowRepresentative (variation : ThermodynamicSL2Variation) (time : ℂ) :
    MobiusTransform where
  a := variation.matrixFlow time 0 0
  b := variation.matrixFlow time 0 1
  c := variation.matrixFlow time 1 0
  d := variation.matrixFlow time 1 1
  det_ne_zero := by
    have determinant := variation.matrixFlow_det time
    rw [Matrix.det_fin_two] at determinant
    rw [determinant]
    exact one_ne_zero

theorem flowRepresentative_zero (variation : ThermodynamicSL2Variation) :
    flowRepresentative variation 0 = default := by
  unfold flowRepresentative
  simp only [matrixFlow_zero]
  rfl

theorem flowRepresentative_add (variation : ThermodynamicSL2Variation)
    (firstTime secondTime : ℂ) :
    flowRepresentative variation (firstTime + secondTime) =
      InfoGeometry.comp (flowRepresentative variation firstTime)
        (flowRepresentative variation secondTime) := by
  unfold flowRepresentative InfoGeometry.comp
  congr 1 <;> simp only [matrixFlow_add, Matrix.mul_apply, Fin.sum_univ_two]

def projectiveFlow (variation : ThermodynamicSL2Variation) (time : ℂ) : PGL2C :=
  Quotient.mk' (flowRepresentative variation time)

@[simp] theorem projectiveFlow_zero (variation : ThermodynamicSL2Variation) :
    projectiveFlow variation 0 = 1 := by
  unfold projectiveFlow
  rw [flowRepresentative_zero]
  rfl

theorem projectiveFlow_add (variation : ThermodynamicSL2Variation)
    (firstTime secondTime : ℂ) :
    projectiveFlow variation (firstTime + secondTime) =
      projectiveFlow variation firstTime * projectiveFlow variation secondTime := by
  change Quotient.mk' (flowRepresentative variation (firstTime + secondTime)) =
    Quotient.mk' (InfoGeometry.comp (flowRepresentative variation firstTime)
      (flowRepresentative variation secondTime))
  rw [flowRepresentative_add]

def globalOrbit (variation : ThermodynamicSL2Variation) (time : ℂ)
    (point : RiemannSphere) : RiemannSphere :=
  projectiveFlow variation time • point

@[simp] theorem globalOrbit_zero (variation : ThermodynamicSL2Variation)
    (point : RiemannSphere) : globalOrbit variation 0 point = point := by
  simp [globalOrbit]

theorem globalOrbit_add (variation : ThermodynamicSL2Variation)
    (firstTime secondTime : ℂ) (point : RiemannSphere) :
    globalOrbit variation (firstTime + secondTime) point =
      globalOrbit variation firstTime (globalOrbit variation secondTime point) := by
  simp only [globalOrbit, projectiveFlow_add, mul_smul]

theorem globalOrbit_neg (variation : ThermodynamicSL2Variation)
    (time : ℂ) (point : RiemannSphere) :
    globalOrbit variation (-time) (globalOrbit variation time point) = point := by
  rw [← globalOrbit_add]
  simp

theorem globalOrbit_some_of_den_ne_zero (variation : ThermodynamicSL2Variation)
    (time point : ℂ) (denominator_ne : variation.finiteOrbitDenominator time point ≠ 0) :
    globalOrbit variation time (some point) = some (variation.finiteOrbit time point) := by
  change (flowRepresentative variation time).eval (some point) = _
  have denominator_ne' :
      variation.matrixFlow time 1 0 * point + variation.matrixFlow time 1 1 ≠ 0 :=
    denominator_ne
  simp [MobiusTransform.eval, flowRepresentative, finiteOrbit,
    InfoGeometry.Clifford.DiscreteMoebiusGroup.moebiusAction, denominator_ne']

theorem globalOrbit_some_of_den_zero (variation : ThermodynamicSL2Variation)
    (time point : ℂ) (denominator_zero : variation.finiteOrbitDenominator time point = 0) :
    globalOrbit variation time (some point) = none := by
  change (flowRepresentative variation time).eval (some point) = none
  have denominator_zero' :
      variation.matrixFlow time 1 0 * point + variation.matrixFlow time 1 1 = 0 :=
    denominator_zero
  simp [MobiusTransform.eval, flowRepresentative, denominator_zero']

theorem globalOrbit_toRiemannSphere (variation : ThermodynamicSL2Variation)
    (time : ℂ) (point : CP1) :
    globalOrbit variation time point.toRiemannSphere =
      ((flowRepresentative variation time).actCP1 point).toRiemannSphere := by
  exact mk_smul_toRiemannSphere (flowRepresentative variation time) point

theorem globalOrbit_affine_ode (variation : ThermodynamicSL2Variation)
    (time point : ℂ) (denominator_ne : variation.finiteOrbitDenominator time point ≠ 0) :
    globalOrbit variation time (some point) = some (variation.finiteOrbit time point) ∧
      HasDerivAt (fun parameter => variation.finiteOrbit parameter point)
        (variation.vectorField (variation.finiteOrbit time point)) time := by
  exact ⟨globalOrbit_some_of_den_ne_zero variation time point denominator_ne,
    variation.hasDerivAt_finiteOrbit_eq_vectorField time point denominator_ne⟩

end InfoGeometry.Topology.ThermodynamicProjectiveFlow
