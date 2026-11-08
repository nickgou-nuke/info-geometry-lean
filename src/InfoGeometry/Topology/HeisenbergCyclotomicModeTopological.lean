/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergCyclotomicModeBridge

/-!
# Topological Readout for the Heisenberg Cyclotomic Mode Bridge

This module packages the `ℤ → ZMod 3` cyclotomic degree map `heisenbergModeDegree`
as a topological map between discrete spaces and proves its evaluation, negation,
continuity, and local constancy laws.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergCyclotomicModeBridge`: `heisenbergModeDegree`,
    `heisenbergModeDegree_neg`.
- BUCKET 2 (Deconfabulation):
  * All evaluation and topological theorems are proved via explicit unfolding and
    discrete-topology lemmas.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `topologicalHeisenbergModeDegree`: topological mode-degree readout `ℤ → ZMod 3`.
  * `topologicalHeisenbergModeDegree_eq`, `topologicalHeisenbergModeDegree_neg`.
  * `continuous_topologicalHeisenbergModeDegree`,
    `isLocallyConstant_topologicalHeisenbergModeDegree`.
-/

namespace InfoGeometry.Topology.HeisenbergCyclotomicModeTopological

open InfoGeometry.Canonical

noncomputable section

/-- The cyclotomic degree of a Heisenberg mode, viewed as a topological map `ℤ → ZMod 3`. -/
def topologicalHeisenbergModeDegree (k : ℤ) : ZMod 3 :=
  heisenbergModeDegree k

/-- Explicit evaluation of `topologicalHeisenbergModeDegree k`. -/
@[simp] theorem topologicalHeisenbergModeDegree_eq (k : ℤ) :
    topologicalHeisenbergModeDegree k = heisenbergModeDegree k := by
  unfold topologicalHeisenbergModeDegree
  exact Eq.refl _

/-- Negating the integer mode negates its topological cyclotomic degree in `ZMod 3`. -/
@[simp] theorem topologicalHeisenbergModeDegree_neg (k : ℤ) :
    topologicalHeisenbergModeDegree (-k) = -topologicalHeisenbergModeDegree k := by
  unfold topologicalHeisenbergModeDegree
  exact heisenbergModeDegree_neg k

/-- The cyclotomic degree readout is continuous on the discrete integer mode domain. -/
theorem continuous_topologicalHeisenbergModeDegree :
    Continuous topologicalHeisenbergModeDegree := by
  unfold topologicalHeisenbergModeDegree
  exact continuous_of_discreteTopology

/-- The cyclotomic degree readout is locally constant on the discrete integer mode domain. -/
theorem isLocallyConstant_topologicalHeisenbergModeDegree :
    IsLocallyConstant topologicalHeisenbergModeDegree := by
  unfold topologicalHeisenbergModeDegree
  exact IsLocallyConstant.of_discrete

end
end InfoGeometry.Topology.HeisenbergCyclotomicModeTopological
