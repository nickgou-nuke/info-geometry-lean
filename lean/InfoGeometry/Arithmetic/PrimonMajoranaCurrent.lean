import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeMajoranaCAR
import InfoGeometry.Arithmetic.PrimeMajoranaOPE
import InfoGeometry.Arithmetic.PrimeWeylGaugeCantorFockBridge

/-!
# InfoGeometry.Arithmetic.PrimonMajoranaCurrent

Owner-side finite primon current corridor.

This file stays in the arithmetic owner lane. It does not introduce a new
synthesis wrapper. Instead it records the concrete local current action already
visible in the split-Majorana CAR model:

* `c = ε + ι`;
* `d = ε - ι`;
* `j = c d = 1 - 2N`.

The theorems proved here are same-mode local current-action identities derived
from the explicit CAR owner. They do not assert a Laurent-series/OPE backend,
prime-mode commutation between distinct labels, or the full symbolic current
transport required by `Canonical/PrimeVirasoroSugawara.lean`.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonMajoranaCurrent

open InfoGeometry.Arithmetic.PrimeMajoranaCAR
open InfoGeometry.Arithmetic.PrimeMajoranaOPE

namespace PrimeMajoranaCAR.ExteriorCARPair

variable {Op : Type*} [Ring Op]
variable (P : PrimeMajoranaCAR.ExteriorCARPair Op)

/-- Right action of the local Möbius current on `c` sends `c` to `d`. -/
theorem cMajorana_mul_parityOp :
    P.cMajorana * P.parityOp = P.dMajorana := by
  calc
    P.cMajorana * P.parityOp
        = P.cMajorana * (P.cMajorana * P.dMajorana) := by
            rfl
    _ = (P.cMajorana * P.cMajorana) * P.dMajorana := by
            noncomm_ring
    _ = P.dMajorana := by
            rw [P.cMajorana_sq]
            simp

/-- Right action of the local Möbius current on `d` sends `d` to `c`. -/
theorem dMajorana_mul_parityOp :
    P.dMajorana * P.parityOp = P.cMajorana := by
  calc
    P.dMajorana * P.parityOp
        = P.dMajorana * (P.cMajorana * P.dMajorana) := by
            rfl
    _ = (P.dMajorana * P.cMajorana) * P.dMajorana := by
            rw [mul_assoc]
    _ = (-P.parityOp) * P.dMajorana := by
            rw [P.dMajorana_mul_cMajorana_eq_neg]
    _ = (-(P.cMajorana * P.dMajorana)) * P.dMajorana := by
            rfl
    _ = -(P.cMajorana * (P.dMajorana * P.dMajorana)) := by
            noncomm_ring
    _ = P.cMajorana := by
            rw [P.dMajorana_sq]
            simp

/-- Left action of the local Möbius current on `c` sends `c` to `-d`. -/
theorem parityOp_mul_cMajorana :
    P.parityOp * P.cMajorana = -P.dMajorana := by
  calc
    P.parityOp * P.cMajorana
        = (P.cMajorana * P.dMajorana) * P.cMajorana := by
            rfl
    _ = P.cMajorana * (P.dMajorana * P.cMajorana) := by
            rw [mul_assoc]
    _ = P.cMajorana * (-P.parityOp) := by
            rw [P.dMajorana_mul_cMajorana_eq_neg]
    _ = -(P.cMajorana * P.parityOp) := by
            noncomm_ring
    _ = -P.dMajorana := by
            rw [cMajorana_mul_parityOp]

/-- Left action of the local Möbius current on `d` sends `d` to `-c`. -/
theorem parityOp_mul_dMajorana :
    P.parityOp * P.dMajorana = -P.cMajorana := by
  calc
    P.parityOp * P.dMajorana
        = (P.cMajorana * P.dMajorana) * P.dMajorana := by
            rfl
    _ = P.cMajorana * (P.dMajorana * P.dMajorana) := by
            rw [mul_assoc]
    _ = P.cMajorana * (-1) := by
            rw [P.dMajorana_sq]
    _ = -P.cMajorana := by
            noncomm_ring

end PrimeMajoranaCAR.ExteriorCARPair

/-- Prime-indexed family of local split-Majorana CAR owners. -/
structure PrimeLocalCARFamily (PrimeLabel Op : Type*) [Ring Op] where
  pair : PrimeLabel → PrimeMajoranaCAR.ExteriorCARPair Op

namespace PrimeLocalCARFamily

variable {PrimeLabel Op : Type*} [Ring Op]

/-- Prime-indexed `c`-field from the local CAR owner. -/
def cField (F : PrimeLocalCARFamily PrimeLabel Op) : PrimeLabel → Op :=
  fun p => (F.pair p).cMajorana

/-- Prime-indexed `d`-field from the local CAR owner. -/
def dField (F : PrimeLocalCARFamily PrimeLabel Op) : PrimeLabel → Op :=
  fun p => (F.pair p).dMajorana

/-- Prime-indexed local Möbius current `j_p = c_p d_p = 1 - 2N_p`. -/
def current (F : PrimeLocalCARFamily PrimeLabel Op) : PrimeLabel → Op :=
  fun p => (F.pair p).parityOp

/-- The explicit local current sends `c_p` to `d_p` on the same prime mode. -/
theorem sameModeCurrentC (F : PrimeLocalCARFamily PrimeLabel Op) :
    ∀ p, cField F p * current F p = dField F p := by
  intro p
  exact PrimeMajoranaCAR.ExteriorCARPair.cMajorana_mul_parityOp (F.pair p)

/-- The explicit local current sends `d_p` to `c_p` on the same prime mode. -/
theorem sameModeCurrentD (F : PrimeLocalCARFamily PrimeLabel Op) :
    ∀ p, dField F p * current F p = cField F p := by
  intro p
  exact PrimeMajoranaCAR.ExteriorCARPair.dMajorana_mul_parityOp (F.pair p)

/--
Transport the concrete same-mode current action to the symbolic arithmetic
current socket.

Boundary: this only packages same-mode local action laws. Distinct-prime OPE
relations and Laurent/VOA semantics remain open owner debt.
-/
def toMobiusCurrentOPE
    (F : PrimeLocalCARFamily PrimeLabel Op) :
    MobiusCurrentOPE PrimeLabel Op where
  cField := cField F
  dField := dField F
  current := current F
  CurrentActsOnC := fun _p j c d => c * j = d
  CurrentActsOnD := fun _p j c d => d * j = c
  current_c := by
    intro p
    exact sameModeCurrentC F p
  current_d := by
    intro p
    exact sameModeCurrentD F p

theorem toMobiusCurrentOPE_current_c
    (F : PrimeLocalCARFamily PrimeLabel Op)
    (p : PrimeLabel) :
    (cField F p) * (current F p) = dField F p :=
  (toMobiusCurrentOPE F).current_c p

theorem toMobiusCurrentOPE_current_d
    (F : PrimeLocalCARFamily PrimeLabel Op)
    (p : PrimeLabel) :
    (dField F p) * (current F p) = cField F p :=
  (toMobiusCurrentOPE F).current_d p

end PrimeLocalCARFamily

namespace PrimeWeylGaugeCantorFockBridge.WeylGaugeTiltSwitchNormalization

open InfoGeometry.Arithmetic.PrimeWeylGaugeCantorFockBridge

variable {Idx Raw Op : Type*} [Ring Op]
variable (N : WeylGaugeTiltSwitchNormalization Idx Raw Op)

theorem sameModeCurrentC :
    ∀ p, N.c p * (N.c p * N.d p) = N.d p := by
  intro p
  calc
    N.c p * (N.c p * N.d p)
        = (N.c p * N.c p) * N.d p := by noncomm_ring
    _ = N.d p := by rw [N.c_sq p]; simp

theorem sameModeCurrentD :
    ∀ p, N.d p * (N.c p * N.d p) = N.c p := by
  intro p
  calc
    N.d p * (N.c p * N.d p)
        = (N.d p * N.c p) * N.d p := by rw [mul_assoc]
    _ = (-(N.c p * N.d p)) * N.d p := by
        have h := N.c_d_anticomm_same p
        have hdcp : N.d p * N.c p = -(N.c p * N.d p) :=
          eq_neg_of_add_eq_zero_right h
        rw [hdcp]
    _ = -(N.c p * (N.d p * N.d p)) := by noncomm_ring
    _ = N.c p := by rw [N.d_sq p]; simp

theorem offDiagCurrentC :
    ∀ p q, p ≠ q → (N.c p * N.d p) * N.c q = N.c q * (N.c p * N.d p) := by
  intro p q hpq
  exact N.localParity_commutes_c_offdiag p q hpq

theorem offDiagCurrentD :
    ∀ p q, p ≠ q → (N.c p * N.d p) * N.d q = N.d q * (N.c p * N.d p) := by
  intro p q hpq
  exact N.localParity_commutes_d_offdiag p q hpq

/--
Concrete transport of the normalized Weyl-gauge owner current into the symbolic
current socket.

The current laws are packaged as conjunctions of same-mode action and
off-diagonal commutation. Laurent/OPE singular-part semantics still remain open.
-/
def toMobiusCurrentOPE :
    MobiusCurrentOPE Idx Op where
  cField := N.c
  dField := N.d
  current := fun p => N.c p * N.d p
  CurrentActsOnC := fun _p j c d => c * j = d
  CurrentActsOnD := fun _p j c d => d * j = c
  current_c := by
    intro p
    exact sameModeCurrentC N p
  current_d := by
    intro p
    exact sameModeCurrentD N p

theorem toMobiusCurrentOPE_current_c :
    ∀ p, N.c p * (N.c p * N.d p) = N.d p :=
  (toMobiusCurrentOPE N).current_c

theorem toMobiusCurrentOPE_current_d :
    ∀ p, N.d p * (N.c p * N.d p) = N.c p :=
  (toMobiusCurrentOPE N).current_d

end PrimeWeylGaugeCantorFockBridge.WeylGaugeTiltSwitchNormalization

end InfoGeometry.Arithmetic.PrimonMajoranaCurrent
