import Mathlib.Tactic

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

/-- Ring homomorphisms preserve anticommutators. -/
theorem map_anticomm
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    (X Y : A) :
    φ (anticomm X Y) = anticomm (φ X) (φ Y) := by
  simp [anticomm]

/--
Transport of a two-supercharge closure relation.

If `{Q,R} = H + Z`, then after any ring homomorphism,
`{φ Q, φ R} = φ H + φ Z`.
-/
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

/--
Transport of a diagonal supercharge closure relation.
-/
theorem map_self_supercharge_closure
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Q H Z : A}
    (h : anticomm Q Q = H + Z) :
    anticomm (φ Q) (φ Q) = φ H + φ Z := by
  exact map_supercharge_closure φ h

/--
Transport of the normalized closure relation `{Q,Q} = 2 * (H + Z)`.
-/
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

/-- Centrality is preserved on the image of a ring homomorphism. -/
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

/-- Ring equivalences preserve anticommutators. -/
theorem ringEquiv_anticomm
    {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B)
    (X Y : A) :
    anticomm (e X) (e Y) = e (anticomm X Y) := by
  simp [anticomm]

/--
Duality transport of a two-supercharge closure relation.
-/
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

/--
Duality transport of the normalized closure relation `{Q,Q} = 2 * (H + Z)`.
-/
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

/-- Ring equivalences preserve centrality on transported elements. -/
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

/-! ## Finite-stage invariant transport under ring homomorphisms -/

section RingHomInvariantTransport

variable {A B : Type*} [Ring A] [Ring B]
variable (f : A →+* B)

/-- A ring homomorphism preserves square-zero operators. -/
theorem ringHom_preserves_square_zero
    {x : A}
    (hx : x * x = 0) :
    f x * f x = 0 := by
  simpa using congrArg f hx

/-- A ring homomorphism preserves idempotents. -/
theorem ringHom_preserves_idempotent
    {p : A}
    (hp : p * p = p) :
    f p * f p = f p := by
  simpa using congrArg f hp

/-- A ring homomorphism preserves involutions. -/
theorem ringHom_preserves_involution
    {e : A}
    (he : e * e = 1) :
    f e * f e = 1 := by
  simpa using congrArg f he

/--
A ring homomorphism preserves an anticommutator identity.

This is the finite-stage CAR transport lemma: if `{x,y} = c` in the source
algebra, then `{f x, f y} = f c`.
-/
theorem ringHom_preserves_anticommutator_eq
    {x y c : A}
    (hxy : x * y + y * x = c) :
    f x * f y + f y * f x = f c := by
  simpa using congrArg f hxy

/--
A ring homomorphism preserves a zero anticommutator.

This is the finite-stage odd-odd closure transport lemma.
-/
theorem ringHom_preserves_anticommutator_zero
    {x y : A}
    (hxy : x * y + y * x = 0) :
    f x * f y + f y * f x = 0 := by
  simpa using ringHom_preserves_anticommutator_eq (f := f) hxy

/--
A ring homomorphism preserves a commutator identity.

If `[x,y] = c`, then `[f x, f y] = f c`.
-/
theorem ringHom_preserves_commutator_eq
    {x y c : A}
    (hxy : x * y - y * x = c) :
    f x * f y - f y * f x = f c := by
  simpa using congrArg f hxy

/-- A ring homomorphism preserves a zero commutator. -/
theorem ringHom_preserves_commutator_zero
    {x y : A}
    (hxy : x * y - y * x = 0) :
    f x * f y - f y * f x = 0 := by
  simpa using ringHom_preserves_commutator_eq (f := f) hxy

/--
A ring homomorphism transports the one-mode CAR identity.

If `a a† + a† a = 1`, then the transported operators satisfy the same identity.
-/
theorem ringHom_preserves_CAR_one
    {a adag : A}
    (hcar : a * adag + adag * a = 1) :
    f a * f adag + f adag * f a = 1 := by
  simpa using ringHom_preserves_anticommutator_eq (f := f) hcar

end RingHomInvariantTransport

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

/-- The split Majoranas anticommute: `{c,d}=0`. -/
theorem cMajorana_dMajorana_anticomm_zero :
    P.cMajorana * P.dMajorana + P.dMajorana * P.cMajorana = 0 := by
  rw [P.dMajorana_mul_cMajorana_eq_neg]
  dsimp [parityOp]
  abel

/--
The local parity squares to one.

This is the real split-Majorana version of the local Möbius parity involution.
-/
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
