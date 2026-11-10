/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option linter.style.haveILetI false

/-!
# Dimension growth in the native split-Clifford algebraic colimit

The finite `Cl(n,n)` stages are grade cutoffs. Their operator values embed into
the algebraic direct limit `SplitCliffordInfinity`; this file proves that no
single finite-dimensional real vector space can contain that limit faithfully.
No completion or finite-dimensional model of the limit is introduced.

## BUCKET 1: Proved
The native stage dimension growth and non-finite-dimensionality of the
algebraic direct limit.

## BUCKET 2: Conditional
No conditional results are declared in this owner.

## BUCKET 3: Open boundary
No norm, topology, or analytic completion of the direct limit is constructed.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordColimitDimension

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.SplitCliffordNativeTensorFinrank
open InfoGeometry.Clifford.Clifford55

/-- The native split-Clifford stage dimension grows by a factor of four from
the first `Cl(1,1)` head onward. -/
theorem splitClNNAlg_finrank_succStage (n : ℕ) :
    Module.finrank ℝ (SplitClNNAlg (n + 1)) = 4 ^ (n + 1) := by
  induction n with
  | zero =>
      simpa using splitClNNAlg_finrank_one
  | succ n ih =>
      rw [splitClNNAlg_finrank_succ (n + 1), ih, pow_succ]
      ring

/-- The native split-Clifford algebraic direct limit is not finite-dimensional.

The contradiction uses the stage at cutoff `d + 1`, where `d` would be the
dimension of the limit: that stage injects into the limit but has dimension
`4^(d+1) > d`. This is an algebraic colimit statement, not a claim about a
topological completion. -/
theorem splitCliffordInfinity_not_finiteDimensional :
    ¬ FiniteDimensional ℝ SplitCliffordInfinity := by
  intro hfinite
  haveI : FiniteDimensional ℝ SplitCliffordInfinity := hfinite
  let d := Module.finrank ℝ SplitCliffordInfinity
  let stageMap := DirectLimit.Module.of ℝ ℕ SplitClNNAlg
    (fun m n h => splitCliffordMap m n h) (d + 1)
  have hstage_injective : Function.Injective stageMap := by
    change Function.Injective
      (DirectLimit.Ring.of SplitClNNAlg
        (fun m n h => (splitCliffordMap m n h).toRingHom) (d + 1))
    exact splitCliffordInfinity_stage_injective (d + 1)
  have hbound : 4 ^ (d + 1) ≤ d := by
    rw [← splitClNNAlg_finrank_succStage d]
    exact LinearMap.finrank_le_finrank_of_injective hstage_injective
  have hlt : d < 4 ^ (d + 1) := by
    calc
      d < d + 1 := Nat.lt_succ_self d
      _ < 4 ^ (d + 1) := Nat.lt_pow_self (by decide : 1 < 4)
  exact (Nat.not_lt_of_ge hbound) hlt

end InfoGeometry.Canonical.SplitCliffordColimitDimension
