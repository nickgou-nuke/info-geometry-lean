import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.External.Virasoro.CentralChargeCalc
import Mathlib.Tactic

/-!
# SUSY central-charge bookkeeping

This file records the channel-counting layer for the SUSY/current bridge.

It does not prove a super-Virasoro relation, a BPS bound, a Lichnerowicz
formula, or a topological action theorem.  Those require additional operator
relations.  The purpose here is only to expose the `c = 4`, `c = 8`, and
`c = 12` bookkeeping in a kernel-checked form, while importing the already
implemented supercharge, current-to-Sugawara, and central-charge calculation
surfaces.

We store `2c` as an integer to avoid rational arithmetic:

* one real chiral Majorana contributes `2c = 1`;
* one bosonic current/free boson contributes `2c = 2`;
* one `N = 1` boson-Majorana multiplet contributes `2c = 3`.
-/

namespace InfoGeometry.Canonical.SUSYCentralChargeBridge

/-- Twice the central charge of `n` real chiral Majorana channels. -/
def twiceCentralMajorana (n : Nat) : Int :=
  Int.ofNat n

/-- Twice the central charge of `n` bosonic current/free-boson channels. -/
def twiceCentralBoson (n : Nat) : Int :=
  2 * Int.ofNat n

/-- Twice the central charge of `n` free `N = 1` boson-Majorana multiplets. -/
def twiceCentralN1Multiplet (n : Nat) : Int :=
  twiceCentralMajorana n + twiceCentralBoson n

/-- `8` Majoranas have `c = 4`, stored as `2c = 8`. -/
theorem c4_is_eight_majoranas :
    twiceCentralMajorana 8 = 8 := by
  norm_num [twiceCentralMajorana]

/-- `8` bosonic currents/free bosons have `c = 8`, stored as `2c = 16`. -/
theorem c8_is_eight_bosons :
    twiceCentralBoson 8 = 16 := by
  norm_num [twiceCentralBoson]

/-- `8` free `N = 1` multiplets have total `c = 12`, stored as `2c = 24`. -/
theorem eight_N1_multiplets_have_c12 :
    twiceCentralN1Multiplet 8 = 24 := by
  norm_num [twiceCentralN1Multiplet, twiceCentralMajorana, twiceCentralBoson]

/-- General channel count: `n` free `N = 1` multiplets contribute `2c = 3n`. -/
theorem twiceCentralN1Multiplet_eq_three_mul (n : Nat) :
    twiceCentralN1Multiplet n = 3 * Int.ofNat n := by
  simp [twiceCentralN1Multiplet, twiceCentralMajorana, twiceCentralBoson]
  ring

end InfoGeometry.Canonical.SUSYCentralChargeBridge
