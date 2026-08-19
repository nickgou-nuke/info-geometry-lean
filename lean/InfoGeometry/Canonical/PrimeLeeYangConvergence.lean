import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.PrimeHurwitzLimit
import InfoGeometry.Canonical.PrimePartitionPolynomials

/-!
# InfoGeometry.Canonical.PrimeLeeYangConvergence

Convergence theorems for the prime Lee--Yang program.

This file owns the exact analytic target needed by `PrimeHurwitzLimit`:
* finite Lee--Yang approximants `A : LeeYangApproximants`;
* a limiting Cayley pullback of completed `xi`;
* zero-freeness on the inner and outer components of the Lee--Yang circle complement;
* the zero predicate comparison between completed `xi` and the limiting Cayley readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangConvergence

open InfoGeometry.Canonical.PrimeHurwitzLimit
open InfoGeometry.Canonical.PrimePartitionPolynomials

variable {Ξ : CompletedXiZeroPredicate}
variable {A : LeeYangApproximants}

/--
Zero-free complement transfer induced by the convergence hypotheses.
-/
@[rep_depth operator]
def zeroFreeTransfer
    (limitF : ℂ → ℂ)
    (inner_zero_free : ∀ z : ℂ, InUnitDisk z → limitF z ≠ 0)
    (outer_zero_free : ∀ z : ℂ, OutsideUnitDisk z → limitF z ≠ 0) :
    ZeroFreeDomainTransfer where
  limitF := limitF
  inner_zero_free := inner_zero_free
  outer_zero_free := outer_zero_free

/-- The convergence hypotheses map completed-`xi` zeros to the Lee--Yang circle. -/
@[rep_depth operator]
theorem xiZeros_map_to_unit_circle
    (limitF : ℂ → ℂ)
    (locallyUniformRenormalizedLimit : LocallyUniformLimit A.renormZ limitF)
    (nontrivial_in : ∃ z : ℂ, InUnitDisk z ∧ limitF z ≠ 0)
    (nontrivial_out : ∃ z : ℂ, OutsideUnitDisk z ∧ limitF z ≠ 0)
    (inner_zero_free : ∀ z : ℂ, InUnitDisk z → limitF z ≠ 0)
    (outer_zero_free : ∀ z : ℂ, OutsideUnitDisk z → limitF z ≠ 0)
    (xi_zero_iff_limit_zero : ∀ s : ℂ, s ≠ 1 → (Ξ.XiZero s ↔ limitF (cayley s) = 0))
    (s : ℂ)
    (hs_ne_one : s ≠ 1)
    (hs : Ξ.XiZero s) :
    OnUnitCircle (cayley s) := by
  let H : CorrectHurwitzZeroTransferWitness Ξ A :=
    { limitF := limitF
      locallyUniformRenormalizedLimit := locallyUniformRenormalizedLimit
      nontrivial_in := nontrivial_in
      nontrivial_out := nontrivial_out
      noSpuriousZeros := fun z hz =>
        ZeroFreeDomainTransfer.zero_on_unit_of_inner_outer_zero_free
          (zeroFreeTransfer limitF inner_zero_free outer_zero_free) hz
      transfer := zeroFreeTransfer limitF inner_zero_free outer_zero_free
      transfer_limitF := rfl
      xi_zero_iff_limit_zero := xi_zero_iff_limit_zero }
  exact corrected_hurwitz_xiZeros_map_to_unit_circle H s hs_ne_one hs

/--
Conditional RH theorem from prime Lee--Yang convergence hypotheses.
-/
@[rep_depth operator]
theorem limitF_zero_on_unitCircle
    (limitF : ℂ → ℂ)
    (inner_zero_free : ∀ z : ℂ, InUnitDisk z → limitF z ≠ 0)
    (outer_zero_free : ∀ z : ℂ, OutsideUnitDisk z → limitF z ≠ 0)
    {z : ℂ}
    (hz : limitF z = 0) :
    OnUnitCircle z :=
  ZeroFreeDomainTransfer.zero_on_unit_of_inner_outer_zero_free
    (zeroFreeTransfer limitF inner_zero_free outer_zero_free) hz

/-- Conditional RH theorem from prime Lee--Yang convergence hypotheses. -/
@[rep_depth operator]
theorem RH_of_convergence
    (limitF : ℂ → ℂ)
    (locallyUniformRenormalizedLimit : LocallyUniformLimit A.renormZ limitF)
    (nontrivial_in : ∃ z : ℂ, InUnitDisk z ∧ limitF z ≠ 0)
    (nontrivial_out : ∃ z : ℂ, OutsideUnitDisk z ∧ limitF z ≠ 0)
    (inner_zero_free : ∀ z : ℂ, InUnitDisk z → limitF z ≠ 0)
    (outer_zero_free : ∀ z : ℂ, OutsideUnitDisk z → limitF z ≠ 0)
    (xi_zero_iff_limit_zero : ∀ s : ℂ, s ≠ 1 → (Ξ.XiZero s ↔ limitF (cayley s) = 0))
    (C : (∀ s : ℂ, s ≠ 1 → cayleyInv (cayley s) = s) ∧
      (∀ s : ℂ, s ≠ 1 → OnCriticalLine s → OnUnitCircle (cayley s)) ∧
        (∀ s : ℂ, s ≠ 1 → OnUnitCircle (cayley s) → OnCriticalLine s) ∧
          (∀ s : ℂ, s ≠ 0 → s ≠ 1 → cayley (1 - s) = (cayley s)⁻¹)) :
    RiemannHypothesis Ξ := by
  let H : CorrectHurwitzZeroTransferWitness Ξ A :=
    { limitF := limitF
      locallyUniformRenormalizedLimit := locallyUniformRenormalizedLimit
      nontrivial_in := nontrivial_in
      nontrivial_out := nontrivial_out
      noSpuriousZeros := fun z hz =>
        ZeroFreeDomainTransfer.zero_on_unit_of_inner_outer_zero_free
          (zeroFreeTransfer limitF inner_zero_free outer_zero_free) hz
      transfer := zeroFreeTransfer limitF inner_zero_free outer_zero_free
      transfer_limitF := rfl
      xi_zero_iff_limit_zero := xi_zero_iff_limit_zero }
  exact RH_from_Correct_Hurwitz_LeeYang Ξ C _ H

end InfoGeometry.Canonical.PrimeLeeYangConvergence
