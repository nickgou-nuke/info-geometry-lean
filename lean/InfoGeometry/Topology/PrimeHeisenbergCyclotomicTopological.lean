/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergCyclotomicModeBridge
import InfoGeometry.Canonical.PrimeHeisenbergOscillators

/-!
# Topological Prime-Mode / Cyclotomic Readout

This module defines the `ZMod 3` cyclotomic degree readout `primeModeCyclotomicDegree`
and paired annihilation/creation readout `primeModeCyclotomicPair` on natural-number
prime oscillator indices, and proves creation degree inversion, annihilation/creation
resonance neutrality, continuity, and local constancy.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergCyclotomicModeBridge`:
    `heisenbergModeDegree`, `heisenbergModeDegree_neg`,
    `heisenberg_resonance_has_zero_cyclotomic_degree`.
  * `InfoGeometry.Canonical.PrimeHeisenbergOscillators`:
    `primeAnnihilation`, `primeCreation`.
- BUCKET 2 (Deconfabulation):
  * All arithmetic degree and topological continuity laws are proved constructively.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `primeModeCyclotomicDegree`, `primeModeCyclotomicPair`.
  * `primeModeCyclotomicDegree_eq`, `primeCreationCyclotomicDegree`,
    `primeMode_resonance_cyclotomic_degree_zero`.
  * `continuous_primeModeCyclotomicDegree`,
    `isLocallyConstant_primeModeCyclotomicDegree`,
    `continuous_primeModeCyclotomicPair`,
    `isLocallyConstant_primeModeCyclotomicPair`.
-/

namespace InfoGeometry.Topology.PrimeHeisenbergCyclotomicTopological

open InfoGeometry.Canonical
open InfoGeometry.Canonical.PrimeHeisenbergOscillators

noncomputable section

/-- Cyclotomic degree in `ZMod 3` of the positive oscillator mode `J_p`. -/
def primeModeCyclotomicDegree (p : ℕ) : ZMod 3 :=
  heisenbergModeDegree (p : ℤ)

/-- Explicit evaluation of `primeModeCyclotomicDegree p`. -/
@[simp] theorem primeModeCyclotomicDegree_eq (p : ℕ) :
    primeModeCyclotomicDegree p = heisenbergModeDegree (p : ℤ) := by
  unfold primeModeCyclotomicDegree
  exact Eq.refl _

/-- The creation mode `-(p : ℤ)` has the opposite cyclotomic degree of `primeModeCyclotomicDegree p`. -/
@[simp] theorem primeCreationCyclotomicDegree (p : ℕ) :
    heisenbergModeDegree (-(p : ℤ)) =
      -primeModeCyclotomicDegree p := by
  unfold primeModeCyclotomicDegree
  exact heisenbergModeDegree_neg (p : ℤ)

/-- The annihilation/creation pair `(p, -p)` has total cyclotomic degree zero. -/
theorem primeMode_resonance_cyclotomic_degree_zero (p : ℕ) :
    primeModeCyclotomicDegree p +
        heisenbergModeDegree (-(p : ℤ)) = 0 := by
  change heisenbergModeDegree (p : ℤ) +
      heisenbergModeDegree (-(p : ℤ)) = 0
  exact heisenberg_resonance_has_zero_cyclotomic_degree
    (p : ℤ) (-(p : ℤ)) (add_neg_cancel (p : ℤ))

/-- The prime degree readout is continuous for the discrete natural-number topology. -/
theorem continuous_primeModeCyclotomicDegree :
    Continuous primeModeCyclotomicDegree := by
  unfold primeModeCyclotomicDegree
  exact continuous_of_discreteTopology

/-- The prime degree readout is locally constant for the discrete natural-number topology. -/
theorem isLocallyConstant_primeModeCyclotomicDegree :
    IsLocallyConstant primeModeCyclotomicDegree := by
  unfold primeModeCyclotomicDegree
  exact IsLocallyConstant.of_discrete

/-- Paired annihilation/creation cyclotomic degree readout `ℕ → ZMod 3 × ZMod 3`. -/
def primeModeCyclotomicPair (p : ℕ) : ZMod 3 × ZMod 3 :=
  (primeModeCyclotomicDegree p, heisenbergModeDegree (-(p : ℤ)))

/-- Continuity of the paired annihilation/creation cyclotomic degree readout. -/
theorem continuous_primeModeCyclotomicPair :
    Continuous primeModeCyclotomicPair := by
  unfold primeModeCyclotomicPair
  exact continuous_of_discreteTopology

/-- Local constancy of the paired annihilation/creation cyclotomic degree readout. -/
theorem isLocallyConstant_primeModeCyclotomicPair :
    IsLocallyConstant primeModeCyclotomicPair := by
  unfold primeModeCyclotomicPair
  exact IsLocallyConstant.of_discrete

end
end InfoGeometry.Topology.PrimeHeisenbergCyclotomicTopological
