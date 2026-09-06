import InfoGeometry.Canonical.ZornMaxwellDifferentialBridge
import InfoGeometry.Canonical.ZornMaxwellSourceReadout

/-!
# Differential bridge with external Maxwell sources

This owner keeps the source `(rho, current)` external.  Gauss and Ampere are
assumptions about the chosen fields and source, while divergence--curl and
Faraday remain consequences of the finite differential carrier.
-/

namespace InfoGeometry.Canonical.ZornMaxwellSourceDifferentialBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Canonical.ZornFiniteVectorCalculus
open InfoGeometry.Canonical.ZornPotentialDifferentialReadout
open InfoGeometry.Canonical.ZornMaxwellComponentReadout
open InfoGeometry.Canonical.ZornMaxwellDifferentialBridge
open InfoGeometry.Canonical.ZornMaxwellSourceReadout

local notation "Vec3" => ZornVec3 ℝ

def externalGaussAmpere
    (D : DifferentialCarrier (R := ℝ))
    (scalar : ℝ) (vector : Vec3) (S : MaxwellSource) : Prop :=
  divergence D (electricReadout (potentialData D scalar vector)) = S.rho ∧
    ∀ i,
      curl D (magneticReadout (potentialData D scalar vector)) i -
        D.timeDerivative (electricReadout (potentialData D scalar vector) i) =
      S.current i

theorem time_divergence_commute
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (v : Vec3) :
    D.timeDerivative (divergence D v) =
      divergence D (fun i => D.timeDerivative (v i)) := by
  have hsub (x y : ℝ) :
      D.timeDerivative (x - y) =
        D.timeDerivative x - D.timeDerivative y := by
    rw [sub_eq_add_neg, D.time_add, hneg y, sub_eq_add_neg]
  simp only [divergence, Fin.sum_univ_three]
  rw [D.time_add, D.time_add]
  simp [hcomm]

theorem externalSource_conservation
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) (S : MaxwellSource)
    (hsource : externalGaussAmpere D scalar vector S) :
    D.timeDerivative S.rho + divergence D S.current = 0 := by
  rcases hsource with ⟨hρ, hj⟩
  have hcommDiv := time_divergence_commute D hneg hcomm
    (electricReadout (potentialData D scalar vector))
  have hcurl := divergence_curl D
    (magneticReadout (potentialData D scalar vector))
  rw [← hρ]
  rw [hcommDiv]
  have h0 := hj 0
  have h1 := hj 1
  have h2 := hj 2
  have hS : S.current = fun i =>
      curl D (magneticReadout (potentialData D scalar vector)) i -
        D.timeDerivative (electricReadout (potentialData D scalar vector) i) := by
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
  rw [hS]
  have hspatialSub (i : Fin 3) (x y : ℝ) :
      D.spatialDerivative i (x - y) =
        D.spatialDerivative i x - D.spatialDerivative i y := by
    rw [sub_eq_add_neg, D.spatial_add, D.spatial_neg, sub_eq_add_neg]
  have hdivSub :
      divergence D (fun i =>
        curl D (magneticReadout (potentialData D scalar vector)) i -
          D.timeDerivative (electricReadout (potentialData D scalar vector) i)) =
        divergence D (curl D (magneticReadout (potentialData D scalar vector))) -
          divergence D (fun i =>
            D.timeDerivative (electricReadout (potentialData D scalar vector) i)) := by
    simp only [divergence, Fin.sum_univ_three, hspatialSub]
    ring
  rw [hdivSub, hcurl]
  ring

theorem inducedComponents_sourceMaxwellLaws
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) (S : MaxwellSource)
    (hsource : externalGaussAmpere D scalar vector S) :
    sourceMaxwellLaws (inducedComponents D scalar vector) S := by
  rcases hsource with ⟨hρ, hj⟩
  refine ⟨hρ, inducedComponents_divB_zero D scalar vector, ?_, ?_⟩
  · exact inducedComponents_faraday_zero D hneg hcomm scalar vector
  · intro i
    exact hj i

theorem inducedComponents_derivativeReadout_eq_sourceReadout
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) (S : MaxwellSource)
    (hsource : externalGaussAmpere D scalar vector S) :
    derivativeReadout (inducedComponents D scalar vector) = sourceReadout S := by
  apply (derivativeReadout_eq_sourceReadout_iff
    (inducedComponents D scalar vector) S).2
  exact inducedComponents_sourceMaxwellLaws D hneg hcomm scalar vector S hsource

theorem inducedComponents_sourceMaxwellLaws_iff_externalGaussAmpere
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) (S : MaxwellSource) :
    sourceMaxwellLaws (inducedComponents D scalar vector) S ↔
      externalGaussAmpere D scalar vector S := by
  constructor
  · rintro ⟨hρ, _, _, hj⟩
    refine ⟨hρ, ?_⟩
    intro i
    simpa [inducedComponents, ampereResidual] using hj i
  · intro hsource
    exact inducedComponents_sourceMaxwellLaws D hneg hcomm scalar vector S hsource

theorem inducedComponents_derivativeReadout_eq_sourceReadout_iff_externalGaussAmpere
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) (S : MaxwellSource) :
    derivativeReadout (inducedComponents D scalar vector) = sourceReadout S ↔
      externalGaussAmpere D scalar vector S := by
  rw [derivativeReadout_eq_sourceReadout_iff]
  exact inducedComponents_sourceMaxwellLaws_iff_externalGaussAmpere
    D hneg hcomm scalar vector S

end InfoGeometry.Canonical.ZornMaxwellSourceDifferentialBridge
