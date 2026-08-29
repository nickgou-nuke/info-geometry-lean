import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit
import InfoGeometry.Canonical.PrimeHurwitzLimit
import InfoGeometry.Canonical.PrimeLeeYangConvergence
import InfoGeometry.Canonical.PrimeLeeYangHopfieldLimitBridge
import InfoGeometry.Analysis.LeeYangRootLimit

/-!
# InfoGeometry.Canonical.PrimeLeeYangToHurwitz

Relay layer from the prime convergence interface to the Hurwitz zero-transfer
interface.

This file does not prove any prime-to-`xi` convergence statement and does not
prove RH. It isolates the transfer step that comes after the analytic
convergence property. The Clifford-wavelet layer is imported only as the
candidate source of that convergence property.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangToHurwitz

open InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit
open InfoGeometry.Canonical.PrimeHurwitzLimit
open InfoGeometry.Canonical.PrimeHurwitzLimit.CayleyCriticalWitness
open InfoGeometry.Canonical.PrimeLeeYangConvergence
open InfoGeometry.Canonical.PrimeLeeYangHopfieldLimitBridge
open InfoGeometry.Analysis.LeeYangRootLimit

variable {Ξ : CompletedXiZeroPredicate}
variable {A : LeeYangApproximants}



/--
Completed-`xi` zeros map to the Lee--Yang circle when they are limits of
actual roots of the finite renormalized approximants.

Unlike the former relay theorem, this statement consumes no property packet and
does not store the desired zero-location conclusion as data.
-/
@[rep_depth operator]
theorem xiZeros_map_to_unit_circle
    (A : LeeYangApproximants)
    (root : ℂ → ℕ → ℂ)
    (hroot :
      ∀ s, Ξ.XiZero s → ∀ n, A.renormZ n (root s n) = 0)
    (hlim :
      ∀ s, Ξ.XiZero s →
        Filter.Tendsto (root s) Filter.atTop (nhds (cayley s)))
    (s : ℂ)
    (hs : Ξ.XiZero s) :
    OnUnitCircle (cayley s) :=
  zeroPredicate_maps_to_unitCircle_of_root_limit
    Ξ.XiZero A root hroot hlim s hs

/--
Concrete convergence witness from prime Lee--Yang approximants to the
Hurwitz limit.

This packages the root-limit data needed to transfer completed-`xi` zeros
to the Lee--Yang unit circle.  Combined with a Hurwitz convergence packet,
it yields the full Lee--Yang/Hurwitz bridge.
-/
@[rep_depth operator]
structure PrimeLeeYangToHurwitzWitness
    (Ξ : CompletedXiZeroPredicate)
    (A : LeeYangApproximants) where
  /-- The limiting Cayley readout of completed `xi`. -/
  limitF : ℂ → ℂ
  /-- A selection of roots for each completed-`xi` zero. -/
  root : ℂ → ℕ → ℂ
  /-- Each selected point is an actual zero of the renormalized approximant. -/
  hroot :
    ∀ s, Ξ.XiZero s → ∀ n, A.renormZ n (root s n) = 0
  /-- The selected roots converge to the Cayley image of the zero. -/
  hlim :
    ∀ s, Ξ.XiZero s →
      Filter.Tendsto (root s) Filter.atTop (nhds (cayley s))

/-- The witness implies the basic zero-location transfer. -/
@[rep_depth operator]
theorem xiZeros_map_to_unit_circle_of_witness
    {Ξ : CompletedXiZeroPredicate}
    {A : LeeYangApproximants}
    (W : PrimeLeeYangToHurwitzWitness Ξ A)
    (s : ℂ)
    (hs : Ξ.XiZero s) :
    OnUnitCircle (cayley s) :=
  xiZeros_map_to_unit_circle A W.root W.hroot W.hlim s hs

/-- The witness implies critical-line localization for completed-`xi` zeros. -/
@[rep_depth operator]
theorem xiZeros_map_to_critical_line_of_witness
    {Ξ : CompletedXiZeroPredicate}
    {A : LeeYangApproximants}
    (W : PrimeLeeYangToHurwitzWitness Ξ A)
    (s : ℂ)
    (hs : Ξ.XiZero s)
    (hs_ne : s ≠ 1) :
    OnCriticalLine s := by
  have hcircle : OnUnitCircle (cayley s) :=
    xiZeros_map_to_unit_circle_of_witness W s hs
  exact cayley_critical_of_unit s hs_ne hcircle

/-- Conditional RH theorem from the prime Lee--Yang witness. -/
@[rep_depth operator]
theorem RH_of_primeLeeYangToHurwitz_witness
    (Ξ : CompletedXiZeroPredicate)
    (A : LeeYangApproximants)
    (W : PrimeLeeYangToHurwitzWitness Ξ A) :
    RiemannHypothesis Ξ := by
  intro s hs
  have hs_ne : s ≠ 1 := Ξ.zero_ne_one s hs
  exact xiZeros_map_to_critical_line_of_witness W s hs hs_ne

end InfoGeometry.Canonical.PrimeLeeYangToHurwitz

