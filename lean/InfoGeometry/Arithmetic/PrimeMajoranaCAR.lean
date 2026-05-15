import Mathlib

/-!
# InfoGeometry.Arithmetic.PrimeMajoranaCAR

Finite split-Majorana CAR surface for prime-indexed exterior/Fock lanes.

This module records the real split-Majorana algebra

`c = ε + ι`, `d = ε - ι`,

where `ε` is exterior creation and `ι` is contraction.  It proves the local
split-Clifford and parity identities from explicit CAR laws.

It does not assert an infinite tensor product, CFT OPE, Pfaffian determinant,
or zeta-function identity.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaCAR

/-- Anticommutator in a noncommutative ring. -/
def anticomm
    {Op : Type*} [NonUnitalNonAssocRing Op]
    (A B : Op) : Op :=
  A * B + B * A

/--
A local exterior CAR pair.

`eps` is exterior creation and `iota` is contraction.
-/
structure ExteriorCARPair
    (Op : Type*) [Ring Op] where
  eps : Op
  iota : Op
  eps_sq_zero : eps * eps = 0
  iota_sq_zero : iota * iota = 0
  iota_eps_add_eps_iota : iota * eps + eps * iota = 1

namespace ExteriorCARPair

variable {Op : Type*} [Ring Op]
variable (P : ExteriorCARPair Op)

/-- Occupancy projector `N = ε ι`. -/
def numberOp : Op :=
  P.eps * P.iota

/-- Split-Majorana `c = ε + ι`. -/
def cMajorana : Op :=
  P.eps + P.iota

/-- Split-Majorana `d = ε - ι`. -/
def dMajorana : Op :=
  P.eps - P.iota

/-- Local Möbius parity `Π = c d = 1 - 2N`. -/
def parityOp : Op :=
  P.cMajorana * P.dMajorana

/-- `ε ι + ι ε = 1`, reoriented. -/
theorem eps_iota_add_iota_eps :
    P.eps * P.iota + P.iota * P.eps = 1 := by
  simpa [add_comm] using P.iota_eps_add_eps_iota

/-- `ι ε = 1 - ε ι`. -/
theorem iota_mul_eps_eq_one_sub_eps_mul_iota :
    P.iota * P.eps = 1 - P.eps * P.iota := by
  exact eq_sub_of_add_eq P.iota_eps_add_eps_iota

/-- The number operator is idempotent. -/
theorem numberOp_idem :
    P.numberOp * P.numberOp = P.numberOp := by
  dsimp [numberOp]
  calc
    (P.eps * P.iota) * (P.eps * P.iota)
        = P.eps * (P.iota * P.eps) * P.iota := by
            noncomm_ring
    _ = P.eps * (1 - P.eps * P.iota) * P.iota := by
            rw [P.iota_mul_eps_eq_one_sub_eps_mul_iota]
    _ = P.eps * P.iota := by
            rw [mul_sub, sub_mul, mul_one]
            have hzero : P.eps * (P.eps * P.iota) * P.iota = 0 := by
              calc
                P.eps * (P.eps * P.iota) * P.iota
                    = (P.eps * P.eps) * P.iota * P.iota := by
                        noncomm_ring
                _ = 0 := by
                        rw [P.eps_sq_zero]
                        simp
            rw [hzero, sub_zero]

/-- `c² = 1`. -/
theorem cMajorana_sq :
    P.cMajorana * P.cMajorana = 1 := by
  dsimp [cMajorana]
  calc
    (P.eps + P.iota) * (P.eps + P.iota)
        =
      P.eps * P.eps + P.eps * P.iota
        + P.iota * P.eps + P.iota * P.iota := by
          noncomm_ring
    _ = 1 := by
          rw [P.eps_sq_zero, P.iota_sq_zero]
          simpa [add_assoc] using P.eps_iota_add_iota_eps

/-- `d² = -1`. -/
theorem dMajorana_sq :
    P.dMajorana * P.dMajorana = -1 := by
  dsimp [dMajorana]
  calc
    (P.eps - P.iota) * (P.eps - P.iota)
        =
      P.eps * P.eps - P.eps * P.iota
        - P.iota * P.eps + P.iota * P.iota := by
          noncomm_ring
    _ = -(P.eps * P.iota + P.iota * P.eps) := by
          rw [P.eps_sq_zero, P.iota_sq_zero]
          abel
    _ = -1 := by
          rw [P.eps_iota_add_iota_eps]

/-- `c d = 1 - 2N`. -/
theorem parityOp_eq_one_sub_two_numberOp :
    P.parityOp = 1 - (2 : Op) * P.numberOp := by
  dsimp [parityOp, cMajorana, dMajorana, numberOp]
  calc
    (P.eps + P.iota) * (P.eps - P.iota)
        =
      P.eps * P.eps - P.eps * P.iota
        + P.iota * P.eps - P.iota * P.iota := by
          noncomm_ring
    _ = P.iota * P.eps - P.eps * P.iota := by
          rw [P.eps_sq_zero, P.iota_sq_zero]
          abel
    _ = (1 - P.eps * P.iota) - P.eps * P.iota := by
          rw [P.iota_mul_eps_eq_one_sub_eps_mul_iota]
    _ = 1 - (2 : Op) * (P.eps * P.iota) := by
          noncomm_ring

/-- `d c = -c d`. -/
theorem dMajorana_mul_cMajorana_eq_neg :
    P.dMajorana * P.cMajorana = -P.parityOp := by
  dsimp [parityOp, cMajorana, dMajorana]
  calc
    (P.eps - P.iota) * (P.eps + P.iota)
        =
      P.eps * P.eps + P.eps * P.iota
        - P.iota * P.eps - P.iota * P.iota := by
          noncomm_ring
    _ = P.eps * P.iota - P.iota * P.eps := by
          rw [P.eps_sq_zero, P.iota_sq_zero]
          abel
    _ = -((P.eps + P.iota) * (P.eps - P.iota)) := by
          rw [show (P.eps + P.iota) * (P.eps - P.iota) =
              P.iota * P.eps - P.eps * P.iota by
            calc
              (P.eps + P.iota) * (P.eps - P.iota)
                  =
                P.eps * P.eps - P.eps * P.iota
                  + P.iota * P.eps - P.iota * P.iota := by
                    noncomm_ring
              _ = P.iota * P.eps - P.eps * P.iota := by
                    rw [P.eps_sq_zero, P.iota_sq_zero]
                    abel]
          abel

/--
The local parity squares to one.

This is the real split-Majorana version of the local Möbius parity involution.
-/
theorem parityOp_sq :
    P.parityOp * P.parityOp = 1 := by
  dsimp [parityOp, cMajorana, dMajorana]
  have hc : (P.eps + P.iota) * (P.eps + P.iota) = 1 :=
    P.cMajorana_sq
  have hd : (P.eps - P.iota) * (P.eps - P.iota) = -1 :=
    P.dMajorana_sq
  have hdc :
      (P.eps - P.iota) * (P.eps + P.iota)
        =
      -((P.eps + P.iota) * (P.eps - P.iota)) := by
    simpa [parityOp, cMajorana, dMajorana] using P.dMajorana_mul_cMajorana_eq_neg
  calc
    ((P.eps + P.iota) * (P.eps - P.iota))
        * ((P.eps + P.iota) * (P.eps - P.iota))
      =
    (P.eps + P.iota)
        * ((P.eps - P.iota) * (P.eps + P.iota))
        * (P.eps - P.iota) := by
          noncomm_ring
    _ =
    (P.eps + P.iota)
        * (-((P.eps + P.iota) * (P.eps - P.iota)))
        * (P.eps - P.iota) := by
          rw [hdc]
    _ =
    -(((P.eps + P.iota) * (P.eps + P.iota))
        * ((P.eps - P.iota) * (P.eps - P.iota))) := by
          noncomm_ring
    _ = -(1 * (-1)) := by
          rw [hc, hd]
    _ = 1 := by
          simp

end ExteriorCARPair

end InfoGeometry.Arithmetic.PrimeMajoranaCAR
