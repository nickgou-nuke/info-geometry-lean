import Mathlib
import InfoGeometry.Arithmetic.PrimeMajoranaCAR
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

/-- Same-mode local current-on-`c` action law. -/
def sameModeCurrentCLaw (F : PrimeLocalCARFamily PrimeLabel Op) : Prop :=
  ∀ p, cField F p * current F p = dField F p

/-- Same-mode local current-on-`d` action law. -/
def sameModeCurrentDLaw (F : PrimeLocalCARFamily PrimeLabel Op) : Prop :=
  ∀ p, dField F p * current F p = cField F p

/-- The explicit local current sends `c_p` to `d_p` on the same prime mode. -/
theorem sameModeCurrentCLaw_valid (F : PrimeLocalCARFamily PrimeLabel Op) :
    sameModeCurrentCLaw F := by
  intro p
  exact PrimeMajoranaCAR.ExteriorCARPair.cMajorana_mul_parityOp (F.pair p)

/-- The explicit local current sends `d_p` to `c_p` on the same prime mode. -/
theorem sameModeCurrentDLaw_valid (F : PrimeLocalCARFamily PrimeLabel Op) :
    sameModeCurrentDLaw F := by
  intro p
  exact PrimeMajoranaCAR.ExteriorCARPair.dMajorana_mul_parityOp (F.pair p)

end PrimeLocalCARFamily

namespace PrimeWeylGaugeCantorFockBridge.WeylGaugeTiltSwitchNormalization

open InfoGeometry.Arithmetic.PrimeWeylGaugeCantorFockBridge

variable {Idx Raw Op : Type*} [Ring Op]
variable (N : WeylGaugeTiltSwitchNormalization Idx Raw Op)

/-- Same-site current-on-`c` law in the normalized Weyl-gauge owner corridor. -/
def sameModeCurrentCLaw : Prop :=
  ∀ p, N.c p * (N.c p * N.d p) = N.d p

/-- Same-site current-on-`d` law in the normalized Weyl-gauge owner corridor. -/
def sameModeCurrentDLaw : Prop :=
  ∀ p, N.d p * (N.c p * N.d p) = N.c p

/-- Distinct-site current-on-`c` commutation law in the normalized owner corridor. -/
def offDiagCurrentCLaw : Prop :=
  ∀ p q, p ≠ q → (N.c p * N.d p) * N.c q = N.c q * (N.c p * N.d p)

/-- Distinct-site current-on-`d` commutation law in the normalized owner corridor. -/
def offDiagCurrentDLaw : Prop :=
  ∀ p q, p ≠ q → (N.c p * N.d p) * N.d q = N.d q * (N.c p * N.d p)

theorem sameModeCurrentCLaw_valid :
    sameModeCurrentCLaw N := by
  intro p
  calc
    N.c p * (N.c p * N.d p)
        = (N.c p * N.c p) * N.d p := by noncomm_ring
    _ = N.d p := by rw [N.c_sq p]; simp

theorem sameModeCurrentDLaw_valid :
    sameModeCurrentDLaw N := by
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

theorem offDiagCurrentCLaw_valid :
    offDiagCurrentCLaw N := by
  intro p q hpq
  exact N.localParity_commutes_c_offdiag p q hpq

theorem offDiagCurrentDLaw_valid :
    offDiagCurrentDLaw N := by
  intro p q hpq
  exact N.localParity_commutes_d_offdiag p q hpq

end PrimeWeylGaugeCantorFockBridge.WeylGaugeTiltSwitchNormalization

end InfoGeometry.Arithmetic.PrimonMajoranaCurrent
