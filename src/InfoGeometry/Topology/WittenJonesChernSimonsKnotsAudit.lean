/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Topology.WittenJonesChernSimonsKnots

/-!
# Audit Module for Section 148: Witten-Jones Polynomials and Chern-Simons Knots
Target: `InfoGeometry/Topology/WittenJonesChernSimonsKnotsAudit.lean`

Provides concrete integer (`ℤ`) evaluations and checks by `decide`.
-/

namespace InfoGeometry.Topology.WittenJonesKnotsAudit

open InfoGeometry.Topology.WittenJonesKnots

/-- Concrete integer verification of `A * A_inv = 1` for `canonicalChernSimonsPhaseInt = ⟨-1, -1⟩`. -/
theorem audit_canonical_phase_invertible_int :
    canonicalChernSimonsPhaseInt.A * canonicalChernSimonsPhaseInt.A_inv = 1 := by decide

/-- Concrete integer evaluation of `unknotVacuumLoop` for `⟨-1, -1⟩`. -/
theorem audit_unknot_vacuum_loop_int :
    unknotVacuumLoop canonicalChernSimonsPhaseInt = -2 := by decide

/-- Concrete integer evaluation of `octonion_skein_trace_eq_phase_sum` for `⟨3, 2⟩`. -/
theorem audit_octonion_skein_trace_int :
    SplitOctonion.trace
      (octonionSkeinBraiding (⟨3, 2⟩ : ChernSimonsPhase ℤ) canonicalColorVec3Int ⟨0, 1, -1⟩) = 5 := by
  decide

/-- Concrete integer verification of `octonion_skein_difference_eq_framing_anomaly` for `⟨3, 1⟩`. -/
theorem audit_octonion_skein_difference_int :
    SplitOctonion.sub
      (octonionSkeinBraiding (⟨3, 1⟩ : ChernSimonsPhase ℤ) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩)
      (octonionSkeinInverse (⟨3, 1⟩ : ChernSimonsPhase ℤ) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩) =
    SplitOctonion.scale (2 : ℤ)
      (SplitOctonion.add SplitOctonion.paraSymplecticK0
        (SplitOctonion.sub (SplitOctonion.quark ⟨1, 0, 0⟩) (SplitOctonion.antiquark ⟨0, 1, 0⟩))) := by
  decide

/-- Concrete integer non-commutativity of split-octonion multiplication. -/
theorem audit_split_octonion_noncommutative_int :
    SplitOctonion.mul octonionBasisU1Int octonionBasisU2Int ≠
      SplitOctonion.mul octonionBasisU2Int octonionBasisU1Int := by decide

/-- Concrete integer verification of the Temperley-Lieb quadratic and cubic relations for `d = -2`. -/
theorem audit_tlGen_relations_int :
    Mat3.mul (tlGenE1 (-2 : ℤ)) (tlGenE1 (-2 : ℤ)) = Mat3.smul (-2 : ℤ) (tlGenE1 (-2 : ℤ)) ∧
    Mat3.mul (tlGenE2 (-2 : ℤ)) (tlGenE2 (-2 : ℤ)) = Mat3.smul (-2 : ℤ) (tlGenE2 (-2 : ℤ)) ∧
    Mat3.mul (Mat3.mul (tlGenE1 (-2 : ℤ)) (tlGenE2 (-2 : ℤ))) (tlGenE1 (-2 : ℤ)) = tlGenE1 (-2 : ℤ) ∧
    Mat3.mul (Mat3.mul (tlGenE2 (-2 : ℤ)) (tlGenE1 (-2 : ℤ))) (tlGenE2 (-2 : ℤ)) = tlGenE2 (-2 : ℤ) := by
  decide

/-- Concrete integer verification of Kauffman braid inversion and Yang-Baxter equation on `canonicalChernSimonsPhaseInt`. -/
theorem audit_kauffman_braid_yang_baxter_int :
    Mat3.mul (kauffmanBraidR1 canonicalChernSimonsPhaseInt) (kauffmanBraidR1Inv canonicalChernSimonsPhaseInt) =
      Mat3.one ∧
    Mat3.mul
      (Mat3.mul (kauffmanBraidR1 canonicalChernSimonsPhaseInt) (kauffmanBraidR2 canonicalChernSimonsPhaseInt))
      (kauffmanBraidR1 canonicalChernSimonsPhaseInt) =
    Mat3.mul
      (Mat3.mul (kauffmanBraidR2 canonicalChernSimonsPhaseInt) (kauffmanBraidR1 canonicalChernSimonsPhaseInt))
      (kauffmanBraidR2 canonicalChernSimonsPhaseInt) := by
  decide

end InfoGeometry.Topology.WittenJonesKnotsAudit
