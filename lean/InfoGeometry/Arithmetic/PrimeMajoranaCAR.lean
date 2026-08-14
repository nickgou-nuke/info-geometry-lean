import Mathlib.Tactic


noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaCAR

def anticomm
    {Op : Type*} [NonUnitalNonAssocRing Op]
    (A B : Op) : Op :=
  A * B + B * A

theorem map_anticomm
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    (X Y : A) :
    φ (anticomm X Y) = anticomm (φ X) (φ Y) := by
  simp [anticomm]

theorem map_supercharge_closure
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Q R H Z : A}
    (h : anticomm Q R = H + Z) :
    anticomm (φ Q) (φ R) = φ H + φ Z := by
  calc
    anticomm (φ Q) (φ R) = φ (anticomm Q R) := by
      exact (map_anticomm φ Q R).symm
    _ = φ (H + Z) := by
      rw [h]
    _ = φ H + φ Z := by
      simp

theorem map_self_supercharge_closure
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Q H Z : A}
    (h : anticomm Q Q = H + Z) :
    anticomm (φ Q) (φ Q) = φ H + φ Z := by
  exact map_supercharge_closure φ h

theorem map_self_supercharge_closure_two
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Q H Z : A}
    (h : anticomm Q Q = (2 : A) * (H + Z)) :
    anticomm (φ Q) (φ Q) = (2 : B) * (φ H + φ Z) := by
  calc
    anticomm (φ Q) (φ Q) = φ (anticomm Q Q) := by
      exact (map_anticomm φ Q Q).symm
    _ = φ ((2 : A) * (H + Z)) := by
      rw [h]
    _ = (2 : B) * (φ H + φ Z) := by
      rw [map_mul, map_add]
      have h2 : φ 2 = 2 := map_ofNat φ 2
      rw [h2]

theorem map_commutes_with_image
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Z X : A}
    (hZX : Z * X = X * Z) :
    φ Z * φ X = φ X * φ Z := by
  calc
    φ Z * φ X = φ (Z * X) := by
      exact (map_mul φ Z X).symm
    _ = φ (X * Z) := by
      rw [hZX]
    _ = φ X * φ Z := by
      exact map_mul φ X Z

theorem ringEquiv_anticomm
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B)
    (X Y : A) :
    anticomm (e X) (e Y) = e (anticomm X Y) := by
  simp [anticomm]

theorem ringEquiv_supercharge_closure
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B)
    {Q R H Z : A}
    (h : anticomm Q R = H + Z) :
    anticomm (e Q) (e R) = e H + e Z := by
  calc
    anticomm (e Q) (e R) = e (anticomm Q R) := by
      exact ringEquiv_anticomm e Q R
    _ = e (H + Z) := by
      rw [h]
    _ = e H + e Z := by
      simp

theorem ringEquiv_self_supercharge_closure_two
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B)
    {Q H Z : A}
    (h : anticomm Q Q = (2 : A) * (H + Z)) :
    anticomm (e Q) (e Q) = (2 : B) * (e H + e Z) := by
  calc
    anticomm (e Q) (e Q) = e (anticomm Q Q) := by
      exact ringEquiv_anticomm e Q Q
    _ = e ((2 : A) * (H + Z)) := by
      rw [h]
    _ = (2 : B) * (e H + e Z) := by
      rw [map_mul, map_add]
      have h2 : e 2 = 2 := map_ofNat e 2
      rw [h2]

theorem ringEquiv_commutes_with_image
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B)
    {Z X : A}
    (hZX : Z * X = X * Z) :
    e Z * e X = e X * e Z := by
  calc
    e Z * e X = e (Z * X) := by
      exact (map_mul e Z X).symm
    _ = e (X * Z) := by
      rw [hZX]
    _ = e X * e Z := by
      exact map_mul e X Z

section RingHomInvariantTransport

variable {A B : Type*} [Ring A] [Ring B]
variable (f : A →+* B)

theorem ringHom_preserves_square_zero
    {x : A}
    (hx : x * x = 0) :
    f x * f x = 0 := by
  simpa using congrArg f hx

theorem ringHom_preserves_idempotent
    {p : A}
    (hp : p * p = p) :
    f p * f p = f p := by
  simpa using congrArg f hp

theorem ringHom_preserves_involution
    {e : A}
    (he : e * e = 1) :
    f e * f e = 1 := by
  simpa using congrArg f he

theorem ringHom_preserves_anticommutator_eq
    {x y c : A}
    (hxy : x * y + y * x = c) :
    f x * f y + f y * f x = f c := by
  simpa using congrArg f hxy

theorem ringHom_preserves_anticommutator_zero
    {x y : A}
    (hxy : x * y + y * x = 0) :
    f x * f y + f y * f x = 0 := by
  simpa using ringHom_preserves_anticommutator_eq (f := f) hxy

theorem ringHom_preserves_commutator_eq
    {x y c : A}
    (hxy : x * y - y * x = c) :
    f x * f y - f y * f x = f c := by
  simpa using congrArg f hxy

theorem ringHom_preserves_commutator_zero
    {x y : A}
    (hxy : x * y - y * x = 0) :
    f x * f y - f y * f x = 0 := by
  simpa using ringHom_preserves_commutator_eq (f := f) hxy

theorem ringHom_preserves_CAR_one
    {a adag : A}
    (hcar : a * adag + adag * a = 1) :
    f a * f adag + f adag * f a = 1 := by
  simpa using ringHom_preserves_anticommutator_eq (f := f) hcar

end RingHomInvariantTransport

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

def numberOp : Op :=
  P.eps * P.iota

def cMajorana : Op :=
  P.eps + P.iota

def dMajorana : Op :=
  P.eps - P.iota

def parityOp : Op :=
  P.cMajorana * P.dMajorana

theorem eps_iota_add_iota_eps :
    P.eps * P.iota + P.iota * P.eps = 1 := by
  simpa [add_comm] using P.iota_eps_add_eps_iota

theorem iota_mul_eps_eq_one_sub_eps_mul_iota :
    P.iota * P.eps = 1 - P.eps * P.iota := by
  exact eq_sub_of_add_eq P.iota_eps_add_eps_iota

theorem iota_mul_eps_eq_one_sub_numberOp :
    P.iota * P.eps = 1 - P.numberOp := by
  exact P.iota_mul_eps_eq_one_sub_eps_mul_iota

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

theorem iota_mul_eps_idem :
    (P.iota * P.eps) * (P.iota * P.eps) = P.iota * P.eps := by
  rw [P.iota_mul_eps_eq_one_sub_numberOp]
  have hN : P.numberOp * P.numberOp = P.numberOp := P.numberOp_idem
  calc
    (1 - P.numberOp) * (1 - P.numberOp) =
        1 - (2 : Op) * P.numberOp + P.numberOp * P.numberOp := by
          noncomm_ring
    _ = 1 - P.numberOp := by
      rw [hN]
      noncomm_ring

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

theorem cMajorana_dMajorana_anticomm_zero :
    P.cMajorana * P.dMajorana + P.dMajorana * P.cMajorana = 0 := by
  rw [P.dMajorana_mul_cMajorana_eq_neg]
  dsimp [parityOp]
  abel

theorem parityOp_sq :
    P.parityOp * P.parityOp = 1 := by
  rw [P.parityOp_eq_one_sub_two_numberOp]
  have hN : P.numberOp * P.numberOp = P.numberOp := P.numberOp_idem
  calc
    (1 - (2 : Op) * P.numberOp) * (1 - (2 : Op) * P.numberOp)
        = 1 - (4 : Op) * P.numberOp + (4 : Op) * (P.numberOp * P.numberOp) := by
            noncomm_ring
    _ = 1 - (4 : Op) * P.numberOp + (4 : Op) * P.numberOp := by
            rw [hN]
    _ = 1 := by
            abel

end ExteriorCARPair

end InfoGeometry.Arithmetic.PrimeMajoranaCAR
