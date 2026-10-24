/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GrowingOnsiteMatrixHamiltonian

/-! All-index commutator compatibility for the actual finite onsite recursion.
This extends the proved successor relation along the native matrix tower.
No GNS or completed-family claim is made here. -/
noncomputable section

namespace InfoGeometry.Canonical.GrowingOnsiteMatrixHamiltonian

open CuntzMatrixTowerInstantiation CuntzMatrixTraceTower

/-- Every native transition intertwines the growing onsite commutators. -/
theorem onsite_commutator_concreteMap (w : ℕ → ℝ) {i j : ℕ}
    (hij : i ≤ j) (A : MatrixStage i) :
    onsiteHamiltonian w j * concreteMap hij A -
        concreteMap hij A * onsiteHamiltonian w j =
      concreteMap hij (onsiteHamiltonian w i * A - A * onsiteHamiltonian w i) := by
  induction hij with
  | refl => simp
  | @step j hij ih =>
      have hstep : concreteMap (Nat.le.step hij) =
          (concreteStep j).comp (concreteMap hij) :=
        map_succ concreteData hij
      rw [hstep]
      change onsiteHamiltonian w (j + 1) * concreteStep j (concreteMap hij A) -
          concreteStep j (concreteMap hij A) * onsiteHamiltonian w (j + 1) =
        concreteStep j (concreteMap hij
          (onsiteHamiltonian w i * A - A * onsiteHamiltonian w i))
      rw [onsite_commutator_successor, ih]

end InfoGeometry.Canonical.GrowingOnsiteMatrixHamiltonian
