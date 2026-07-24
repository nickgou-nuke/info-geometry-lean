import Mathlib
import InfoGeometry.Arithmetic.PrimeMajoranaCAR

noncomputable section

namespace InfoGeometry.Arithmetic.SplitMajoranaPrimeGas

open scoped BigOperators

/--
Finite split-Majorana/CAR datum indexed by prime labels.

This is the finite algebraic cutoff only. The field-theoretic OPE and the
analytic zeta layer are separate owner surfaces.
-/
structure SplitPrimeCAR
    (PrimeLabel A : Type*) [DecidableEq PrimeLabel] [Ring A] where
  eps : PrimeLabel → A
  iota : PrimeLabel → A
  eps_sq : ∀ p, eps p * eps p = 0
  iota_sq : ∀ p, iota p * iota p = 0
  iota_eps_add_eps_iota : ∀ p, iota p * eps p + eps p * iota p = 1

namespace SplitPrimeCAR

variable {PrimeLabel A : Type*}
variable [DecidableEq PrimeLabel] [Ring A]
variable (C : SplitPrimeCAR PrimeLabel A)

/-- Positive split-Majorana component. -/
def c (p : PrimeLabel) : A :=
  C.eps p + C.iota p

/-- Negative split-Majorana component. -/
def d (p : PrimeLabel) : A :=
  C.eps p - C.iota p

/-- Local occupation number. -/
def N (p : PrimeLabel) : A :=
  C.eps p * C.iota p

/-- Local Möbius / parity operator. -/
def Pi (p : PrimeLabel) : A :=
  C.c p * C.d p

/-- Convert the finite split-CAR datum to the already-native local CAR pair. -/
def toExteriorCARPair (p : PrimeLabel) :
    InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair A :=
  { eps := C.eps p
    iota := C.iota p
    eps_sq_zero := C.eps_sq p
    iota_sq_zero := C.iota_sq p
    iota_eps_add_eps_iota := C.iota_eps_add_eps_iota p }

/-- `c² = 1` in the finite split-Majorana cutoff. -/
theorem c_sq_eq_one (p : PrimeLabel) :
    C.c p * C.c p = 1 := by
  have h := (SplitPrimeCAR.toExteriorCARPair C p).cMajorana_sq
  simpa [c, InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.cMajorana,
    toExteriorCARPair] using h

/-- `d² = -1` in the finite split-Majorana cutoff. -/
theorem d_sq_eq_neg_one (p : PrimeLabel) :
    C.d p * C.d p = -1 := by
  have h := (SplitPrimeCAR.toExteriorCARPair C p).dMajorana_sq
  simpa [d, InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.dMajorana,
    toExteriorCARPair] using h

/-- The local parity operator is `Π_p = 1 - 2N_p`. -/
theorem Pi_eq_one_sub_two_N (p : PrimeLabel) :
    C.Pi p = 1 - (2 : A) * C.N p := by
  have h := (SplitPrimeCAR.toExteriorCARPair C p).parityOp_eq_one_sub_two_numberOp
  simpa [Pi, N, c, d,
    InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.parityOp,
    InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.numberOp,
    toExteriorCARPair] using h

end SplitPrimeCAR

end InfoGeometry.Arithmetic.SplitMajoranaPrimeGas
