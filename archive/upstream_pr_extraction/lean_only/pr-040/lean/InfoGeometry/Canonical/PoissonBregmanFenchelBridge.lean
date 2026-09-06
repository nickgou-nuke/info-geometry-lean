/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.Canonical.FenchelExpLogScalar
import InfoGeometry.Inference.PoissonBregman
import InfoGeometry.Inference.RegularizedPoissonDeviance

/-!
# Poisson counts as exp/log dual Bregman energy

For strictly positive observed counts and positive model means, the scalar
Poisson Bregman energy used by the inference layer is exactly the dual
Bregman divergence of `y * log y - y`.  The inference definition retains an
explicit zero-count branch; this bridge deliberately states the interior
identity and does not erase that boundary convention.
-/

namespace InfoGeometry.Inference

open InfoGeometry.Canonical.FenchelExpLogScalar
open FiniteGibbs

noncomputable section

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]

/--
The Poisson Bregman energy is the exp/log dual Bregman divergence on the
strictly positive count/mean domain.
-/
theorem poissonBregman_eq_bregmanDual
    {y lam : ℝ} (hy : 0 < y) (hlam : 0 < lam) :
    poissonBregman y lam = bregmanDual y lam := by
  unfold poissonBregman
  rw [if_neg (ne_of_gt hy)]
  symm
  exact bregmanDual_eq_kl_form y lam hy hlam

/--
The same identity extends to the zero-count boundary.  In particular, the
Mathlib convention `Real.log 0 = 0` makes the dual expression at `y = 0`
reduce to `lam`, matching the explicit inference-layer branch.
-/
theorem poissonBregman_eq_bregmanDual_of_nonneg
    {y lam : ℝ} (hy : 0 ≤ y) (hlam : 0 < lam) :
    poissonBregman y lam = bregmanDual y lam := by
  by_cases hy0 : y = 0
  · subst y
    unfold poissonBregman bregmanDual fStar gradDual
    simp
    ring
  · exact poissonBregman_eq_bregmanDual (lt_of_le_of_ne hy (Ne.symm hy0)) hlam

/--
The regularized Poisson deviance is twice the same dual Bregman energy.
-/
theorem poissonDeviance_eq_two_bregmanDual
    {y lam : ℝ} (hy : 0 ≤ y) (hlam : 0 < lam) :
    poissonDeviance y lam = 2 * bregmanDual y lam := by
  unfold poissonDeviance
  rw [poissonBregman_eq_bregmanDual_of_nonneg hy hlam]

/--
The regularized Poisson Gibbs factor written directly in exp/log dual
Bregman coordinates.  This is the bridge consumed by partition-function and
robust-weight constructions; no change is made to the zero-count semantics.
-/
theorem regularizedPoissonWeight_eq_bregmanDual_factor
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) (i : Data)
    (hobserved : 0 ≤ M.observed i) (hmean : 0 < M.mean i θ) :
    regularizedPoissonWeight M θ ε i =
      Real.exp (-(2 * bregmanDual (M.observed i) (M.mean i θ)) / ε) /
        partitionFunction M.devianceGibbsModel θ ε := by
  rw [regularizedPoissonWeight_eq_deviance_factor]
  rw [poissonDeviance_eq_two_bregmanDual hobserved hmean]

end

end InfoGeometry.Inference
