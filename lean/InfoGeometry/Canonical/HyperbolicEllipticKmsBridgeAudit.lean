/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HyperbolicEllipticKmsBridge
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact rational noncommutative witnesses for the hyperbolic--elliptic--KMS bridge. -/

namespace InfoGeometry.Canonical.HyperbolicEllipticKmsBridgeAudit

open Matrix InfoGeometry.Core.DualSeedPeirce InfoGeometry.Core.PeirceRotor
open InfoGeometry.Core.HyperbolicPeirceRotor
open InfoGeometry.Canonical.HyperbolicEllipticKmsBridge
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

abbrev Mat2Q := Matrix (Fin 2) (Fin 2) ℚ

def seedDQ : Mat2Q := !![0, 1; 0, 0]
def seedBQ : Mat2Q := !![0, 0; 1, 0]

theorem mat2Q_isDualSeedPair : IsDualSeedPair seedDQ seedBQ := by
  constructor <;> (ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [seedDQ, seedBQ, Matrix.mul_apply, Fin.sum_univ_two])

/-- Concrete rational witness at `(c, s) = (3/5, 4/5)` (`c^2 + s^2 = 1`) and
`(u, v) = (5/3, 4/3)` (`u^2 - v^2 = 1`) certifying opposite-sign chordal squares,
KMS diagonal decoherence, and the two-state transition sandwich. -/
theorem mat2Q_elliptic_hyperbolic_kms_witness :
    seedDQ * seedBQ ≠ seedBQ * seedDQ ∧
    IsIdempotentElem (movingPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ) ∧
    IsIdempotentElem (hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ) ∧
    (movingPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) *
      (movingPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) =
        ((16 / 25 : ℚ) • carrierSupport seedDQ seedBQ) ∧
    (hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) *
      (hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) =
        -((16 / 9 : ℚ) • carrierSupport seedDQ seedBQ) ∧
    diagonalDecoherence seedDQ seedBQ
      (movingPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ) =
        kmsModularWeight (4 / 5 : ℚ) (3 / 5 : ℚ) seedDQ seedBQ ∧
    polePlus seedDQ seedBQ * transitionVelocity seedDQ seedBQ *
      movingPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ =
        (16 / 25 : ℚ) • seedDQ - (12 / 25 : ℚ) • polePlus seedDQ seedBQ := by
  have hpair := mat2Q_isDualSeedPair
  have hcs : (3 / 5 : ℚ) * (3 / 5 : ℚ) + (4 / 5 : ℚ) * (4 / 5 : ℚ) = 1 := by norm_num
  have huv : (5 / 3 : ℚ) * (5 / 3 : ℚ) - (4 / 3 : ℚ) * (4 / 3 : ℚ) = 1 := by norm_num
  have hmaster := elliptic_hyperbolic_kms_master_synthesis hpair hcs huv
  have h45 : (4 / 5 : ℚ) * (4 / 5 : ℚ) = 16 / 25 := by norm_num
  have h43 : (4 / 3 : ℚ) * (4 / 3 : ℚ) = 16 / 9 := by norm_num
  have h3545 : (3 / 5 : ℚ) * (4 / 5 : ℚ) = 12 / 25 := by norm_num
  have hne : seedDQ * seedBQ ≠ seedBQ * seedDQ := by
    intro h
    have h00 := congr_fun (congr_fun h 0) 0
    revert h00
    norm_num [seedDQ, seedBQ, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hne, hmaster.1, hmaster.2.1, ?_, ?_, hmaster.2.2.2.2, ?_⟩
  · simpa [h45] using hmaster.2.2.1
  · simpa [h43] using hmaster.2.2.2.1
  · simpa [h45, h3545] using two_state_velocity_sandwich hpair (3 / 5 : ℚ) (4 / 5 : ℚ)

#check nilpotent_commuting_inverse_forces_zero
#check carrierSupport_commuting_group_inverse
#check bipartite_directed_edge_transport
#check no_hyperbolic_boost_iff_seeds_vanish
#check hyperbolicRotorUnit
#check hyperbolic_projector_relations
#check hyperbolic_chordal_square
#check two_state_velocity_sandwich
#check diagonalDecoherence_movingPolePlus_eq_kms
#check elliptic_hyperbolic_kms_master_synthesis
#check mat2Q_elliptic_hyperbolic_kms_witness

end InfoGeometry.Canonical.HyperbolicEllipticKmsBridgeAudit
