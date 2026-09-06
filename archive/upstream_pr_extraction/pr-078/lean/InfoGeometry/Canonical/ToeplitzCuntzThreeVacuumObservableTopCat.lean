import InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge
import InfoGeometry.Canonical.ToeplitzCuntzThreeBraidCubicTopologicalBridge

/-!
# Topological vacuum readout for the Toeplitz--Cuntz braid action

The defect projection is a noncommutative observable on the original carrier.
This file proves that the two Artin braid generators preserve its left
readout.  The result is a finite topological observable theorem; it does not
replace the noncommutative carrier by a quotient or a diagonal model.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumObservableTopCat

open CategoryTheory
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeBraidCubicTopologicalBridge
open ToeplitzCuntzThreeGenerators

variable {R : Type*} [Ring R] [StarRing R]
variable [TopologicalSpace R] [ContinuousMul R]
variable (g : ToeplitzCuntzThreeGenerators R)

theorem defectProjection_mul_braidGenerator1 :
    g.P0 * braidGenerator1 g = g.P0 := by
  have hp0_12 : g.P0 * (g.V1 * star g.V2) = 0 := by
    have h1 : g.V1 * star g.V2 = g.P1 * (g.V1 * star g.V2) := by
      dsimp [P1]
      have h : g.V1 * star g.V1 * (g.V1 * star g.V2) =
          g.V1 * (star g.V1 * g.V1) * star g.V2 := by
        noncomm_ring
      rw [h, g.V1_isometry, mul_one]
    rw [h1, ← mul_assoc, p0_p1_ortho g, zero_mul]
  have hp0_21 : g.P0 * (g.V2 * star g.V1) = 0 := by
    have h1 : g.V2 * star g.V1 = g.P2 * (g.V2 * star g.V1) := by
      dsimp [P2]
      have h : g.V2 * star g.V2 * (g.V2 * star g.V1) =
          g.V2 * (star g.V2 * g.V2) * star g.V1 := by
        noncomm_ring
      rw [h, g.V2_isometry, mul_one]
    rw [h1, ← mul_assoc, p0_p2_ortho g, zero_mul]
  have hp0_3 : g.P0 * g.P3 = 0 := p0_p3_ortho g
  have hp0 : g.P0 * g.P0 = g.P0 := defectProjection_sq g
  dsimp [braidGenerator1]
  calc
    g.P0 * (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3 + g.P0) =
        g.P0 * (g.V1 * star g.V2) +
          g.P0 * (g.V2 * star g.V1) + g.P0 * g.P3 + g.P0 * g.P0 := by
      noncomm_ring
    _ = g.P0 := by rw [hp0_12, hp0_21, hp0_3, hp0]; abel

theorem defectProjection_mul_braidGenerator2 :
    g.P0 * braidGenerator2 g = g.P0 := by
  have hp0_23 : g.P0 * (g.V2 * star g.V3) = 0 := by
    have h1 : g.V2 * star g.V3 = g.P2 * (g.V2 * star g.V3) := by
      dsimp [P2]
      have h : g.V2 * star g.V2 * (g.V2 * star g.V3) =
          g.V2 * (star g.V2 * g.V2) * star g.V3 := by
        noncomm_ring
      rw [h, g.V2_isometry, mul_one]
    rw [h1, ← mul_assoc, p0_p2_ortho g, zero_mul]
  have hp0_32 : g.P0 * (g.V3 * star g.V2) = 0 := by
    have h1 : g.V3 * star g.V2 = g.P3 * (g.V3 * star g.V2) := by
      dsimp [P3]
      have h : g.V3 * star g.V3 * (g.V3 * star g.V2) =
          g.V3 * (star g.V3 * g.V3) * star g.V2 := by
        noncomm_ring
      rw [h, g.V3_isometry, mul_one]
    rw [h1, ← mul_assoc, p0_p3_ortho g, zero_mul]
  have hp0_1 : g.P0 * g.P1 = 0 := p0_p1_ortho g
  have hp0 : g.P0 * g.P0 = g.P0 := defectProjection_sq g
  dsimp [braidGenerator2]
  calc
    g.P0 * (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1 + g.P0) =
        g.P0 * (g.V2 * star g.V3) +
          g.P0 * (g.V3 * star g.V2) + g.P0 * g.P1 + g.P0 * g.P0 := by
      noncomm_ring
    _ = g.P0 := by rw [hp0_23, hp0_32, hp0_1, hp0]; abel

theorem braidGenerator1_preserves_defectReadout :
    braidGenerator1LeftTopCatHom g ≫ defectProjectionTopCatHom g =
      defectProjectionTopCatHom g := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change g.P0 * (braidGenerator1 g * x) = g.P0 * x
  rw [← mul_assoc, defectProjection_mul_braidGenerator1]

theorem braidGenerator2_preserves_defectReadout :
    braidGenerator2LeftTopCatHom g ≫ defectProjectionTopCatHom g =
      defectProjectionTopCatHom g := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change g.P0 * (braidGenerator2 g * x) = g.P0 * x
  rw [← mul_assoc, defectProjection_mul_braidGenerator2]

end InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumObservableTopCat
