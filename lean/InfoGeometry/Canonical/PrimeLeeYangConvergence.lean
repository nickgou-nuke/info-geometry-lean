import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Canonical.PrimeHurwitzLimit
import InfoGeometry.Canonical.PrimePartitionPolynomials

/-!
# InfoGeometry.Canonical.PrimeLeeYangConvergence

witness-gated (Native Closure Mandated: Closure Debt) convergence socket for the prime Lee--Yang program.

This file owns the exact analytic target needed by `PrimeHurwitzLimit`:

* finite Lee--Yang approximants `A : LeeYangApproximants`;
* nonvanishing renormalization already stored in `A`;
* locally uniform convergence of `A.renormZ`;
* a limiting Cayley pullback of completed `xi`;
* zero-freeness on the inner and outer components of the Lee--Yang circle
  complement;
* nontriviality of the limiting readout on both components;
* the zero predicate comparison between completed `xi` and the limiting
  Cayley readout.

It does not prove the convergence theorem, does not prove Hurwitz's theorem,
and does not prove RH.  It assembles the supplied analytic witnesses into the
corrected Hurwitz bridge.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangConvergence

open InfoGeometry.Canonical.PrimeHurwitzLimit
open InfoGeometry.Canonical.PrimePartitionPolynomials

/--
Coupling-limit identity socket for finite prime Lee--Yang approximants.

The intended mathematical content is:

`R_N(z) * Z_N(z) → ξ(z / (1 + z))`

locally uniformly on the Cayley chart, with the two zero-free complement
domains transferred by Hurwitz.  Every analytic part is stored as data.
-/
@[socket_debt_tag, rep_depth operator]
structure PrimeLeeYangConvergenceSocket
    (Ξ : CompletedXiZeroPredicate)
    (A : LeeYangApproximants) where
  /-- Limiting readout of the renormalized finite approximants. -/
  limitF :
    ℂ → ℂ

  /-- Intended Cayley pullback of completed `xi`. -/
  xiCayleyPullback :
    ℂ → ℂ

  /-- Locally uniform convergence of `A.renormZ` to `limitF`. -/
  locallyUniformRenormalizedLimit :
    LocallyUniformLimit A.renormZ limitF

  /-- Identification of the abstract limit with the completed-`xi` Cayley pullback. -/
  limit_eq_xiCayleyPullback_law : Prop
  limit_eq_xiCayleyPullback_certificate :
    limit_eq_xiCayleyPullback_law

  /-- The limit is not identically zero on the inner component. -/
  nontrivial_in :
    ∃ z : ℂ, InUnitDisk z ∧ limitF z ≠ 0

  /-- The limit is not identically zero on the outer component. -/
  nontrivial_out :
    ∃ z : ℂ, OutsideUnitDisk z ∧ limitF z ≠ 0

  /-- Hurwitz-transferred zero-freeness inside the Lee--Yang circle. -/
  inner_zero_free :
    ∀ z : ℂ, InUnitDisk z → limitF z ≠ 0

  /-- Hurwitz-transferred zero-freeness outside the Lee--Yang circle. -/
  outer_zero_free :
    ∀ z : ℂ, OutsideUnitDisk z → limitF z ≠ 0

  /-- No finite renormalization or limiting artifact contributes spurious zeros. -/
  noSpuriousZeros : Prop
  noSpuriousZeros_certificate :
    noSpuriousZeros

  /--
  Comparison between completed-`xi` zeros and zeros of the limiting Cayley
  readout.
  -/
  xi_zero_iff_limit_zero :
    ∀ s : ℂ, s ≠ 1 → (Ξ.XiZero s ↔ limitF (cayley s) = 0)

namespace PrimeLeeYangConvergenceSocket

variable {Ξ : CompletedXiZeroPredicate}
variable {A : LeeYangApproximants}
variable (S : PrimeLeeYangConvergenceSocket Ξ A)

/-- Re-export of the supplied completed-`xi` Cayley-pullback identity law. -/
@[rep_depth operator]
theorem limit_eq_xiCayleyPullback :
    S.limit_eq_xiCayleyPullback_law :=
  S.limit_eq_xiCayleyPullback_certificate

/-- Re-export of the supplied no-spurious-zeros law. -/
@[rep_depth operator]
theorem noSpuriousZeros_law :
    S.noSpuriousZeros :=
  S.noSpuriousZeros_certificate

/-- Zero-free complement transfer induced by the convergence socket. -/
@[rep_depth operator]
def zeroFreeTransfer :
    ZeroFreeDomainTransfer where
  limitF := S.limitF
  inner_zero_free := S.inner_zero_free
  outer_zero_free := S.outer_zero_free

/--
Build the corrected Hurwitz witness consumed by `PrimeHurwitzLimit`.
-/
@[rep_depth operator]
def toCorrectHurwitzZeroTransferWitness :
    CorrectHurwitzZeroTransferWitness Ξ A where
  limitF := S.limitF
  locallyUniformRenormalizedLimit := S.locallyUniformRenormalizedLimit
  nontrivial_in := S.nontrivial_in
  nontrivial_out := S.nontrivial_out
  noSpuriousZeros := S.noSpuriousZeros
  transfer := S.zeroFreeTransfer
  transfer_limitF := rfl
  xi_zero_iff_limit_zero := S.xi_zero_iff_limit_zero

/-- The convergence socket maps completed-`xi` zeros to the Lee--Yang circle. -/
@[rep_depth operator]
theorem xiZeros_map_to_unit_circle
    (S : PrimeLeeYangConvergenceSocket Ξ A)
    (s : ℂ)
    (hs_ne_one : s ≠ 1)
    (hs : Ξ.XiZero s) :
    OnUnitCircle (cayley s) :=
  corrected_hurwitz_xiZeros_map_to_unit_circle
    (toCorrectHurwitzZeroTransferWitness S) s hs_ne_one hs

/--
Conditional RH theorem from a prime Lee--Yang convergence socket.

This is a theorem-safe reduction: all hard convergence, nontriviality, and
zero-transfer inputs are supplied by `S`.
-/
@[rep_depth operator]
theorem limitF_zero_on_unitCircle
    (S : PrimeLeeYangConvergenceSocket Ξ A)
    {z : ℂ}
    (hz : S.limitF z = 0) :
    OnUnitCircle z :=
  ZeroFreeDomainTransfer.zero_on_unit_of_inner_outer_zero_free
    S.zeroFreeTransfer hz

/-- Conditional RH theorem from a prime Lee--Yang convergence socket. -/
@[rep_depth operator]
theorem RH_of_convergence_socket
    (S : PrimeLeeYangConvergenceSocket Ξ A)
    (C : CayleyCriticalWitness) :
    RiemannHypothesis Ξ :=
  RH_from_Correct_Hurwitz_LeeYang
    Ξ C _ (toCorrectHurwitzZeroTransferWitness S)

end PrimeLeeYangConvergenceSocket

end InfoGeometry.Canonical.PrimeLeeYangConvergence
