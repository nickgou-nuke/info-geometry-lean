import InfoGeometry.Canonical.ZornMaxwellDifferentialBridge
import InfoGeometry.Canonical.ZornMaxwellSourceReadout

/-!
# Finite gauge invariance of the Zorn potential readout

The transform is the finite-calculus analogue of
`phi ↦ phi + ∂ₜg`, `A ↦ A - grad g`.  The result is only a field-readout
invariance theorem; no continuum gauge group or bundle is introduced here.
-/

namespace InfoGeometry.Canonical.ZornMaxwellGaugeBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Canonical.ZornFiniteVectorCalculus
open InfoGeometry.Canonical.ZornPotentialDifferentialReadout
open InfoGeometry.Canonical.ZornMaxwellDifferentialBridge
open InfoGeometry.Canonical.ZornMaxwellComponentReadout
open InfoGeometry.Canonical.ZornMaxwellSourceReadout

local notation "Vec3" => ZornVec3 ℝ

def gaugeScalar (D : DifferentialCarrier (R := ℝ)) (scalar g : ℝ) : ℝ :=
  scalar + D.timeDerivative g

def gaugeVector (D : DifferentialCarrier (R := ℝ)) (vector : Vec3) (g : ℝ) : Vec3 :=
  fun i => vector i - D.spatialDerivative i g

theorem gauge_electric_invariant
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) (g : ℝ) :
    electricReadout (potentialData D (gaugeScalar D scalar g)
      (gaugeVector D vector g)) =
      electricReadout (potentialData D scalar vector) := by
  have hsub (x y : ℝ) :
      D.timeDerivative (x - y) =
        D.timeDerivative x - D.timeDerivative y := by
    rw [sub_eq_add_neg, D.time_add, hneg y, sub_eq_add_neg]
  funext i
  simp [gaugeScalar, gaugeVector, potentialData, electricReadout,
    gradient, hcomm, hsub, D.time_add, D.spatial_add]

theorem gauge_magnetic_invariant
    (D : DifferentialCarrier (R := ℝ))
    (scalar : ℝ) (vector : Vec3) (g : ℝ) :
    magneticReadout (potentialData D (gaugeScalar D scalar g)
      (gaugeVector D vector g)) =
      magneticReadout (potentialData D scalar vector) := by
  have hsub (i : Fin 3) (x y : ℝ) :
      D.spatialDerivative i (x - y) =
        D.spatialDerivative i x - D.spatialDerivative i y := by
    rw [sub_eq_add_neg, D.spatial_add, D.spatial_neg, sub_eq_add_neg]
  funext i
  fin_cases i
  · simp [gaugeVector, potentialData, magneticReadout, curl, hsub]
    rw [D.spatial_commute 1 2 g]
    ring
  · simp [gaugeVector, potentialData, magneticReadout, curl, hsub]
    rw [D.spatial_commute 2 0 g]
    ring
  · simp [gaugeVector, potentialData, magneticReadout, curl, hsub]
    rw [D.spatial_commute 0 1 g]
    ring

theorem gauge_lorenzResidual_shift
    (D : DifferentialCarrier (R := ℝ))
    (scalar : ℝ) (vector : Vec3) (g : ℝ) :
    lorenzResidual (potentialData D (gaugeScalar D scalar g)
      (gaugeVector D vector g)) =
      lorenzResidual (potentialData D scalar vector) +
        D.timeDerivative (D.timeDerivative g) +
          divergence D (gradient D g) := by
  have hsub (i : Fin 3) (x y : ℝ) :
      D.spatialDerivative i (x - y) =
        D.spatialDerivative i x - D.spatialDerivative i y := by
    rw [sub_eq_add_neg, D.spatial_add, D.spatial_neg, sub_eq_add_neg]
  simp [lorenzResidual, gaugeScalar, gaugeVector, potentialData,
    divergence, Fin.sum_univ_three, gradient, D.time_add, hsub]
  ring

theorem gauge_field_readout_invariant
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) (g : ℝ) :
    (electricReadout (potentialData D (gaugeScalar D scalar g)
        (gaugeVector D vector g)) =
      electricReadout (potentialData D scalar vector)) ∧
    (magneticReadout (potentialData D (gaugeScalar D scalar g)
        (gaugeVector D vector g)) =
      magneticReadout (potentialData D scalar vector)) := by
  exact ⟨gauge_electric_invariant D hneg hcomm scalar vector g,
    gauge_magnetic_invariant D scalar vector g⟩

theorem gauge_inducedComponents_invariant
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) (g : ℝ) :
    inducedComponents D (gaugeScalar D scalar g) (gaugeVector D vector g) =
      inducedComponents D scalar vector := by
  have hE := gauge_electric_invariant D hneg hcomm scalar vector g
  have hB := gauge_magnetic_invariant D scalar vector g
  simp only [inducedComponents]
  rw [hE, hB]

theorem gauge_derivativeReadout_invariant
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) (g : ℝ) :
    derivativeReadout (inducedComponents D (gaugeScalar D scalar g)
      (gaugeVector D vector g)) =
      derivativeReadout (inducedComponents D scalar vector) := by
  exact congrArg derivativeReadout
    (gauge_inducedComponents_invariant D hneg hcomm scalar vector g)

theorem gauge_sourceMaxwellLaws_invariant
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) (g : ℝ) (S : MaxwellSource) :
    sourceMaxwellLaws (inducedComponents D (gaugeScalar D scalar g)
      (gaugeVector D vector g)) S ↔
      sourceMaxwellLaws (inducedComponents D scalar vector) S := by
  rw [gauge_inducedComponents_invariant D hneg hcomm scalar vector g]

end InfoGeometry.Canonical.ZornMaxwellGaugeBridge
