/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.HodgeTheorems
import Mathlib.Tactic

/-! Euler characteristic of a finite 2-complex needs the second Betti term. -/
namespace DAG.EulerNeedsBettiTwo

/-- Two copies of the canonical triangle face have the same boundary. -/
def doubledTriangle : DAG.TwoComplex Nat :=
  { DAG.canonicalTriangleComplex with
    faces := #[DAG.canonicalTriangleComplex.faces[0]!,
               DAG.canonicalTriangleComplex.faces[0]!] }

/-- The second Betti number of a finite 2-complex, computed as the dimension
of the 2-chain space minus the rank of its boundary map. -/
def betti2 (tc : DAG.TwoComplex Nat) : Nat :=
  tc.faces.size + tc.digons.size - DAG.gaussianRank (DAG.boundary2 tc)

/-- Duplicate 2-cells contribute a nontrivial second homology class, so the
truncated identity `χ = β₀ - β₁` fails on this complex. -/
theorem doubled_triangle_invariants :
    DAG.eulerCharacteristic doubledTriangle = 2 ∧
      DAG.betti0 doubledTriangle = 1 ∧
      DAG.betti1 doubledTriangle = 0 ∧
      betti2 doubledTriangle = 1 := by
  native_decide

/-- The alternating Betti sum includes `β₂` and recovers Euler characteristic
for this explicit finite complex. -/
theorem euler_is_alternating_betti_sum :
    Int.ofNat (DAG.betti0 doubledTriangle) -
        Int.ofNat (DAG.betti1 doubledTriangle).toNat +
          Int.ofNat (betti2 doubledTriangle) =
      DAG.eulerCharacteristic doubledTriangle := by
  native_decide

end DAG.EulerNeedsBettiTwo
