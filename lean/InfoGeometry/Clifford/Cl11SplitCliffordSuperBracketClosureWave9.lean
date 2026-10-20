/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.Clifford.CliffordBott

/-!
# Superbracket transport through the split Clifford tower

The split `Cl(n,n)` tower and its direct limit are distinct from the matrix
`Cl(1,1)` tensor tower.  This module records the missing compatibility for the
canonical `splitCliffordStep`, its iterated maps, and the canonical direct-limit
stage maps.  No new carrier or bracket is introduced.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.CliffordBott

open InfoGeometry.Algebra.SupergradedBracket
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower

/-- The canonical split `Cl(n,n) → Cl(n+1,n+1)` map preserves each
parity-controlled associative superbracket. -/
theorem splitCliffordStep_superBracket
    (px py : Bool) (n : ℕ) (A B : SplitClNNAlg n) :
    splitCliffordStep n (superBracket px py A B) =
      superBracket px py (splitCliffordStep n A) (splitCliffordStep n B) := by
  exact map_superBracket (splitCliffordStep n).toRingHom px py A B

/-- Every iterated split-tower transition preserves the same
parity-controlled superbracket. -/
theorem splitCliffordMap_superBracket
    (px py : Bool) (m n : ℕ) (h : m ≤ n) (A B : SplitClNNAlg m) :
    splitCliffordMap m n h (superBracket px py A B) =
      superBracket px py
        (splitCliffordMap m n h A) (splitCliffordMap m n h B) := by
  exact map_superBracket (splitCliffordMap m n h).toRingHom px py A B

/-- The canonical direct-limit image of a finite split Clifford stage
preserves the superbracket. -/
theorem ofStage_superBracket
    (px py : Bool) (n : ℕ) (A B : SplitClNNAlg n) :
    ofStage n (superBracket px py A B) =
      superBracket px py (ofStage n A) (ofStage n B) := by
  exact map_superBracket (ofStage n) px py A B

/-- The odd--odd generator bracket in every finite split Clifford stage
remains the quadratic polar form after passage to the direct limit. -/
theorem ofStage_generator_oddOdd_polar
    (n : ℕ) (x y : SplitSpace n) :
    superBracket true true
        (ofStage n (CliffordAlgebra.ι (Qsplit n) x))
        (ofStage n (CliffordAlgebra.ι (Qsplit n) y)) =
      ofStage n
        (algebraMap ℝ (CliffordAlgebra (Qsplit n))
          (QuadraticMap.polar (Qsplit n) x y)) := by
  rw [← ofStage_superBracket]
  rw [superBracket_odd_odd]
  exact congrArg (ofStage n) (CliffordAlgebra.ι_mul_ι_add_swap (Q := Qsplit n) x y)

end InfoGeometry.Clifford.CliffordBott
