/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.HistoricalDictionaryAndTomitaFrontiersPoset

/-!
# Peirce Spine Historical Frontiers: Derived Operator Identities

## BUCKET 1 — Kernel-verified identities
Finite adjoint iteration and Foldy–Wouthuysen polynomial identities are proved below.

## BUCKET 2 — Conditional consequences
The involution conclusions use the stated idempotence hypothesis on the owner projectors.

## BUCKET 3 — Open interpretation
No analytic exponential flow or continuum dynamics is established by these finite identities.

The eighth-order frontier, historical dictionary, and decadic/Unruh identities are already
proved in `HistoricalDictionaryAndTomitaFrontiersPoset`. This file adds two consequences not
packaged there: finite iteration of the grade-`+1` adjoint action and the square of the
linearly dressed Foldy–Wouthuysen operators after using the owner's idempotence result.
No analytic exponential action is inferred from the finite iteration theorem.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceSpineHistoricalFrontiers

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.WheelerSingleCommutatorHistoricalPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.IKKTLaxHolographicDarkCondensatePoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.HistoricalDictionaryAndTomitaFrontiersPoset

universe u
variable {B : Type u} [Ring B]

/-- Iterated inner derivation, with iteration order explicit. -/
def adjointIter (H Z : B) : ℕ → B
  | 0 => Z
  | n + 1 => comm H (adjointIter H Z n)

/-- The expanding three-horizon current is fixed by every finite iterate of the
modular adjoint action. This follows from its grade `+1` eigenrelation. -/
theorem three_horizon_expanding_wave_adjoint_iterates
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := 1 - P1 - P2
    let H := P1 - P2
    let Np1 := P1 * X * P0 + P0 * X * P2
    ∀ n : ℕ, adjointIter H Np1 n = Np1 := by
  intro P0 H Np1 n
  have hbase := SouriauMetriplecticParabolicPoset.node7_log_radial_modular_time_and_five_graded_weyl_invariance
    P1 P2 X Y h1 h2 h12 h21
  dsimp only at hbase
  rcases hbase with ⟨_, _, _, _, hweight, _, _, _, _, _, _, _⟩
  have hweight' : comm H Np1 = Np1 := by simpa [H, Np1, P0] using hweight
  induction n with
  | zero => rfl
  | succ n ih =>
      change comm H (adjointIter H Np1 n) = Np1
      rw [ih]
      exact hweight'

/-- Linear Foldy–Wouthuysen deformations of the Peirce reflection. -/
def S_FW_lin_pos (P X : B) : B := S_P P + 2 • J_1 P X
/-- Negative linear Foldy–Wouthuysen deformation of the Peirce reflection. -/
def S_FW_lin_neg (P X : B) : B := S_P P - 2 • J_1 P X

/-- The linear deformations have the metric defect `1 - 4V`; the cubic owner
projections yield exact involutions because the corresponding operators are idempotent. -/
theorem linear_and_degree3_foldy_wouthuysen_involutions
    (P X : B) (hP : P * P = P) :
    S_FW_lin_pos P X * S_FW_lin_pos P X = 1 - 4 • V_1 P X ∧
    S_FW_lin_neg P X * S_FW_lin_neg P X = 1 - 4 • V_1 P X ∧
    S_FW_plus P X * S_FW_plus P X = 1 ∧
    S_FW_minus P X * S_FW_minus P X = 1 := by
  have h68 := archetypes_FP6_to_FP8_kahler_sakharov_1_1_2_and_foldy_wouthuysen P X 0 hP
  have hPp : P_FW_plus P X * P_FW_plus P X = P_FW_plus P X := h68.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hPm : P_FW_minus P X * P_FW_minus P X = P_FW_minus P X := h68.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSp : S_FW_plus P X * S_FW_plus P X = 1 := by
    dsimp only [S_FW_plus]
    calc (P_FW_plus P X + P_FW_plus P X - 1) * (P_FW_plus P X + P_FW_plus P X - 1)
      _ = 4 • (P_FW_plus P X * P_FW_plus P X - P_FW_plus P X) + 1 := by noncomm_ring
      _ = 1 := by rw [hPp, sub_self, smul_zero, zero_add]
  have hSm : S_FW_minus P X * S_FW_minus P X = 1 := by
    dsimp only [S_FW_minus]
    calc (P_FW_minus P X + P_FW_minus P X - 1) * (P_FW_minus P X + P_FW_minus P X - 1)
      _ = 4 • (P_FW_minus P X * P_FW_minus P X - P_FW_minus P X) + 1 := by noncomm_ring
      _ = 1 := by rw [hPm, sub_self, smul_zero, zero_add]
  refine ⟨?_, ?_, hSp, hSm⟩ <;>
  · dsimp only [S_FW_lin_pos, S_FW_lin_neg]
    rw [J_1_eq P X, V_1_eq hP X]
    dsimp only [S_P, J_mc, V_met, Q_pos, Q_neg, N_plus, N_minus]
    amari_peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceSpineHistoricalFrontiers
