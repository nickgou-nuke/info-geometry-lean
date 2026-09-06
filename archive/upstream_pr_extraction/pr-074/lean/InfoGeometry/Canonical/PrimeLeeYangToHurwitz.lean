import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit
import InfoGeometry.Canonical.PrimeHurwitzLimit
import InfoGeometry.Canonical.PrimeLeeYangConvergence
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
open InfoGeometry.Canonical.PrimeLeeYangConvergence
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

end InfoGeometry.Canonical.PrimeLeeYangToHurwitz
