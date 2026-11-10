/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Canonical.BitWordComplexStandardColimitEquivalence
import InfoGeometry.Canonical.BoundaryBondSquare

/-!
BUCKET 1: The even matrix stages and their transition into the existing UHF colimit.
BUCKET 2: Trace compatibility at each finite stage and its induced colimit functional.
BUCKET 3: The precise scope: a complex matrix-stage colimit, without an unstated
identification with an abstract Clifford algebra or a completed CAR C*-algebra.

# Even Clifford-sized stages in the complex matrix UHF colimit

The stage indexed by `N` has matrix size `2^(2*N)`.  It is the even-index
subsequence of the already constructed complex dyadic matrix tower.  Its
transition is the actual iterated matrix embedding, and its target is the
existing algebraic direct limit.  The normalized trace descends to that
colimit by the compatible trace construction owned by `BoundaryBondSquare`.

This file proves these stage and colimit facts.  It does not identify these
matrix stages with an abstract Clifford algebra, nor identify the algebraic
colimit with an analytic CAR completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.CliffordInfiniteCARColimit

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.BitWordComplexStandardColimitEquivalence
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
open InfoGeometry.Canonical.BoundaryBondSquare
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The even-index matrix stage of the complex dyadic tower. -/
abbrev CliffordStage (N : ℕ) : Type := MatrixStage (2 * N)

/-- The normalized trace on the even stage. -/
def cliffordTraceState (N : ℕ) (A : CliffordStage N) : ℂ :=
  matrixTraceState (2 * N) A

/-- The algebraic direct limit of the full complex dyadic matrix tower.
The even-index stages map into this same unbounded carrier. -/
abbrev CliffordColimit : Type := StandardColimit

/-- The canonical map from the even stage into the full matrix colimit. -/
def cliffordStageInjection (N : ℕ) : CliffordStage N →+* CliffordColimit :=
  standardToColimit (2 * N)

/-- The even-stage transition, obtained by advancing two dyadic matrix steps. -/
def cliffordBond (N : ℕ) : CliffordStage N →⋆ₐ[ℂ] CliffordStage (N + 1) :=
  concreteMap (show 2 * N ≤ 2 * (N + 1) by omega)

/-- The star-algebra transition and the ring-hom iteration used by the direct
limit are the same stage map. -/
theorem concreteMap_eq_bondMap {m n : ℕ} (h : m ≤ n) (A : MatrixStage m) :
    concreteMap h A = bondMap standardBond m n h A := by
  induction h with
  | refl =>
      simp [concreteMap, bondMap_refl]
  | @step n h ih =>
      change map concreteData (Nat.le.step h) A =
        bondMap standardBond m (n + 1) (Nat.le.step h) A
      rw [map_succ concreteData h, bondMap_succ standardBond m n h]
      change concreteStep n (concreteMap h A) =
        concreteStep n (bondMap standardBond m n h A)
      rw [ih]

/-- The stage maps respect the even-subsequence transition in the colimit. -/
theorem cliffordStageInjection_transition (N : ℕ) (A : CliffordStage N) :
    cliffordStageInjection (N + 1) (cliffordBond N A) = cliffordStageInjection N A := by
  change directLimitOf standardBond (2 * (N + 1)) (cliffordBond N A) =
    directLimitOf standardBond (2 * N) A
  have hmap : cliffordBond N A = bondMap standardBond (2 * N) (2 * (N + 1))
      (show 2 * N ≤ 2 * (N + 1) by omega) A := concreteMap_eq_bondMap
    (show 2 * N ≤ 2 * (N + 1) by omega) A
  rw [hmap]
  exact directLimitOf_bondMap standardBond (2 * N) (2 * (N + 1))
    (show 2 * N ≤ 2 * (N + 1) by omega) A

/-- Every even matrix cutoff embeds faithfully into the algebraic colimit. -/
theorem cliffordStageInjection_injective (N : ℕ) :
    Function.Injective (cliffordStageInjection N) := by
  exact directLimitOf_injective standardBond
    (fun n => by simpa [standardBond] using concreteStep_injective n) (2 * N)

/-- Normalized trace at the unit of every even matrix stage. -/
theorem cliffordTraceState_one (N : ℕ) : cliffordTraceState N 1 = 1 := by
  rw [cliffordTraceState, matrixTraceState_apply, Matrix.trace_one]
  have h_pos : (2 ^ (2 * N) : ℂ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero (2 * N) (by norm_num)
  have h_card : (↑(Fintype.card (Fin (2 ^ (2 * N))) : ℕ) : ℂ) =
      (2 ^ (2 * N) : ℂ) := by
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [h_card]
  exact one_div_mul_cancel h_pos

/-- The normalized trace is preserved by the actual even-stage transition. -/
theorem cliffordBond_trace (N : ℕ) (A : CliffordStage N) :
    cliffordTraceState (N + 1) (cliffordBond N A) = cliffordTraceState N A := by
  exact concreteMap_trace (show 2 * N ≤ 2 * (N + 1) by omega) A

/-- The two-step matrix-size factorization induces an equivalence of the
finite index sets used by the even-stage matrix algebra. -/
theorem clifford_dim_factorization (N : ℕ) :
    Nonempty (Fin (2 ^ (2 * N)) × Fin 4 ≃ Fin (2 ^ (2 * (N + 1)))) := by
  have hdim : (2 ^ (2 * N)) * 4 = 2 ^ (2 * (N + 1)) := by
    have h : 2 * (N + 1) = 2 * N + 2 := by omega
    rw [h, pow_add]
    norm_num
  exact ⟨finProdFinEquiv.trans (finCongr hdim)⟩

/-- The normalized trace on the matrix colimit, transported across the already
proved equivalence with the BitWord-indexed colimit. -/
def cliffordTraceColimit : CliffordColimit → ℂ :=
  fun x => normalizedTraceColimit (fromStandardColimit x)

/-- The normalized trace readout on the algebraic colimit agrees with every
finite even-stage trace. This is the colimit-level trace compatibility law. -/
theorem clifford_trace_compatibility (N : ℕ) (A : CliffordStage N) :
    cliffordTraceColimit (cliffordStageInjection N A) = cliffordTraceState N A := by
  change normalizedTraceColimit
      (ComplexMatrixStage.toColimit (2 * N) ((stageStarAlgEquiv (2 * N)).symm A)) =
    matrixTraceState (2 * N) A
  rw [normalizedTraceColimit_stage]
  rw [stageStarAlgEquiv_normalizedTrace (2 * N) ((stageStarAlgEquiv (2 * N)).symm A)]
  simp

/-- The trace of the colimit unit is normalized. -/
theorem cliffordTraceColimit_one : cliffordTraceColimit (1 : CliffordColimit) = 1 := by
  change normalizedTraceColimit (fromStandardColimit (1 : StandardColimit)) = 1
  rw [map_one]
  exact normalizedTraceColimit_one

end InfoGeometry.Canonical.CliffordInfiniteCARColimit
