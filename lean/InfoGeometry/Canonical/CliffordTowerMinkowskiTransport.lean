/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl44MinkowskiSubspace
import InfoGeometry.Canonical.SplitCliffordDirectLimit

/-! # Lorentz-signature vectors along the native graded Clifford tower

The stage-four vector is carried by the existing injective Clifford maps;
its quadratic relation persists at every finite later stage.
-/

noncomputable section

namespace InfoGeometry.Canonical.CliffordTowerMinkowskiTransport

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl44MinkowskiSubspace
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-- The actual iterated native Clifford bonding maps are injective. -/
theorem splitCliffordMap_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective (splitCliffordMap m n h) := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [splitCliffordMap_refl]
    intro a b hab
    exact hab
  | succ n hn ih =>
    rw [splitCliffordMap_succ m n hn]
    exact (splitCliffordStep_injective n).comp ih

/-- The native Lorentz vector embedded into any subsequent finite stage. -/
def towerMinkowskiVector (n : ℕ) (h : 4 ≤ n) (t x y z : ℝ) : SplitClNNAlg n :=
  splitCliffordMap 4 n h (CliffordAlgebra.ι (Qsplit 4) (minkowskiVector t x y z))

/-- The Minkowski quadratic relation survives every native graded bonding map. -/
theorem towerMinkowskiVector_square (n : ℕ) (h : 4 ≤ n) (t x y z : ℝ) :
    towerMinkowskiVector n h t x y z * towerMinkowskiVector n h t x y z =
      algebraMap ℝ (SplitClNNAlg n) (t * t - x * x - y * y - z * z) := by
  unfold towerMinkowskiVector
  rw [← map_mul, minkowskiVector_clifford_square, AlgHom.commutes]

/-- The full polarized Lorentz Clifford relation is stable along the
native graded tower. -/
theorem towerMinkowskiVector_anticommutator (n : ℕ) (h : 4 ≤ n)
    (t x y z s a b c : ℝ) :
    towerMinkowskiVector n h t x y z * towerMinkowskiVector n h s a b c +
      towerMinkowskiVector n h s a b c * towerMinkowskiVector n h t x y z =
      algebraMap ℝ (SplitClNNAlg n) (2 * (t * s - x * a - y * b - z * c)) := by
  unfold towerMinkowskiVector
  simpa only [map_add, map_mul, AlgHom.commutes] using
    congrArg (splitCliffordMap 4 n h)
      (minkowskiVector_clifford_anticommutator t x y z s a b c)

end InfoGeometry.Canonical.CliffordTowerMinkowskiTransport

end
