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
      simpa using congrArg (fun t : B => t * (φ H + φ Z)) (map_natCast φ 2)

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
      simpa using congrArg (fun t : B => t * (e H + e Z)) (map_natCast e 2)

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

/--
The finite exchange of creation and contraction.  This is only the local
CAR-preserving algebraic swap; it does not assert any downstream physical
interpretation.
-/
def exchange : ExteriorCARPair Op where
  eps := P.iota
  iota := P.eps
  eps_sq_zero := P.iota_sq_zero
  iota_sq_zero := P.eps_sq_zero
  iota_eps_add_eps_iota := by
    simpa [add_comm] using P.iota_eps_add_eps_iota

@[simp]
theorem exchange_eps : P.exchange.eps = P.iota :=
  rfl

@[simp]
theorem exchange_iota : P.exchange.iota = P.eps :=
  rfl

/-- The local exchange is an involution on the CAR pair. -/
theorem exchange_exchange : P.exchange.exchange = P := by
  cases P
  rfl

/-- Occupancy projector `N = ε ι`. -/
def numberOp : Op :=
  P.eps * P.iota

/-- Split-Majorana `c = ε + ι`. -/
def cMajorana : Op :=
  P.eps + P.iota

/-- Split-Majorana `d = ε - ι`. -/
def dMajorana : Op :=
  P.eps - P.iota

@[simp]
theorem exchange_numberOp :
    P.exchange.numberOp = P.iota * P.eps := by
  rfl

@[simp]
theorem exchange_cMajorana :
    P.exchange.cMajorana = P.cMajorana := by
  dsimp [exchange, cMajorana]
  abel

@[simp]
theorem exchange_dMajorana :
    P.exchange.dMajorana = -P.dMajorana := by
  dsimp [exchange, dMajorana]
  abel

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

@[simp]
theorem exchange_parityOp :
    P.exchange.parityOp = -P.parityOp := by
  dsimp [exchange, parityOp, cMajorana, dMajorana]
  noncomm_ring

/-- The local exchange preserves the split-Majorana square `c² = 1`. -/
theorem exchange_preserves_cMajorana_sq :
    P.exchange.cMajorana * P.exchange.cMajorana = 1 := by
  exact P.exchange.cMajorana_sq

/-- The local exchange preserves the split-Majorana square `d² = -1`. -/
theorem exchange_preserves_dMajorana_sq :
    P.exchange.dMajorana * P.exchange.dMajorana = -1 := by
  exact P.exchange.dMajorana_sq

/-- The local exchange preserves the split-Majorana anticommutator `{c,d}=0`. -/
theorem exchange_preserves_c_d_anticomm_zero :
    P.exchange.cMajorana * P.exchange.dMajorana +
      P.exchange.dMajorana * P.exchange.cMajorana = 0 := by
  exact P.exchange.cMajorana_dMajorana_anticomm_zero

/-! ## Finite families of local exchanges -/

/--
Apply the local exchange at one site of a finite-indexed CAR family.

This is only a pointwise algebraic operation on a family of already-owned local
CAR pairs.  No downstream physical or topological interpretation is asserted
here.
-/
def exchangeFamilyAt
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (i : α) : α → ExteriorCARPair Op :=
  fun j => if j = i then (F j).exchange else F j

@[simp]
theorem exchangeFamilyAt_self
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (i : α) :
    exchangeFamilyAt F i i = (F i).exchange := by
  simp [exchangeFamilyAt]

@[simp]
theorem exchangeFamilyAt_ne
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) {i j : α}
    (hji : j ≠ i) :
    exchangeFamilyAt F i j = F j := by
  simp [exchangeFamilyAt, hji]

/-- At the acted-on site, finite exchange fixes the `c` Majorana. -/
@[simp]
theorem exchangeFamilyAt_cMajorana_self
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (i : α) :
    (exchangeFamilyAt F i i).cMajorana = (F i).cMajorana := by
  simp [exchangeFamilyAt]

/-- At the acted-on site, finite exchange flips the `d` Majorana. -/
@[simp]
theorem exchangeFamilyAt_dMajorana_self
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (i : α) :
    (exchangeFamilyAt F i i).dMajorana = -(F i).dMajorana := by
  simp [exchangeFamilyAt]

/-- At the acted-on site, finite exchange flips the local parity. -/
@[simp]
theorem exchangeFamilyAt_parityOp_self
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (i : α) :
    (exchangeFamilyAt F i i).parityOp = -(F i).parityOp := by
  simp [exchangeFamilyAt]

/-- Away from the acted-on site, finite exchange leaves the `c` Majorana unchanged. -/
@[simp]
theorem exchangeFamilyAt_cMajorana_ne
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) {i j : α}
    (hji : j ≠ i) :
    (exchangeFamilyAt F i j).cMajorana = (F j).cMajorana := by
  simp [exchangeFamilyAt, hji]

/-- Away from the acted-on site, finite exchange leaves the `d` Majorana unchanged. -/
@[simp]
theorem exchangeFamilyAt_dMajorana_ne
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) {i j : α}
    (hji : j ≠ i) :
    (exchangeFamilyAt F i j).dMajorana = (F j).dMajorana := by
  simp [exchangeFamilyAt, hji]

/-- Away from the acted-on site, finite exchange leaves the local parity unchanged. -/
@[simp]
theorem exchangeFamilyAt_parityOp_ne
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) {i j : α}
    (hji : j ≠ i) :
    (exchangeFamilyAt F i j).parityOp = (F j).parityOp := by
  simp [exchangeFamilyAt, hji]

/-- Each pointwise finite exchange is an involution on the whole family. -/
theorem exchangeFamilyAt_involutive
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (i : α) :
    exchangeFamilyAt (exchangeFamilyAt F i) i = F := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [exchangeFamilyAt, exchange_exchange]
  · simp [exchangeFamilyAt, hji]

/-- Pointwise finite exchanges commute on a family of independent local CAR pairs. -/
theorem exchangeFamilyAt_comm
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (i j : α) :
    exchangeFamilyAt (exchangeFamilyAt F i) j =
      exchangeFamilyAt (exchangeFamilyAt F j) i := by
  funext k
  by_cases hki : k = i
  · by_cases hkj : k = j
    · subst hki
      subst hkj
      simp [exchangeFamilyAt, exchange_exchange]
    · subst hki
      simp [exchangeFamilyAt, hkj]
  · by_cases hkj : k = j
    · subst hkj
      simp [exchangeFamilyAt, hki]
    · simp [exchangeFamilyAt, hki, hkj]

/--
Rank-one Coxeter relation for a local finite CAR exchange: applying the same
site generator twice is the identity on the family.
-/
theorem exchangeFamilyAt_coxeter_square
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (i : α) :
    exchangeFamilyAt (exchangeFamilyAt F i) i = F := by
  exact exchangeFamilyAt_involutive F i

/--
Commuting-generator Coxeter relation for independent local finite CAR exchanges.

This is the only braid-style relation proved here: two pointwise exchanges on a
family commute.  It is not a physical braid representation.
-/
theorem exchangeFamilyAt_coxeter_commute
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (i j : α) :
    exchangeFamilyAt (exchangeFamilyAt F i) j =
      exchangeFamilyAt (exchangeFamilyAt F j) i := by
  exact exchangeFamilyAt_comm F i j

/--
Transport a finite CAR family along a finite word of local exchange sites.

This is a finite-prefix recurrence only: the empty word is the input family and
`i :: w` applies the local exchange at `i`, then continues along `w`.
-/
def exchangeFamilyAlong
    {α : Type*} [DecidableEq α]
    : List α → (α → ExteriorCARPair Op) → α → ExteriorCARPair Op
  | [], F => F
  | i :: w, F => exchangeFamilyAlong w (exchangeFamilyAt F i)

@[simp]
theorem exchangeFamilyAlong_nil
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) :
    exchangeFamilyAlong ([] : List α) F = F :=
  rfl

@[simp]
theorem exchangeFamilyAlong_cons
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (i : α) (w : List α) :
    exchangeFamilyAlong (i :: w) F = exchangeFamilyAlong w (exchangeFamilyAt F i) :=
  rfl

/-- A transported finite family still has `c² = 1` at every site. -/
theorem exchangeFamilyAlong_cMajorana_sq
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (w : List α) (j : α) :
    (exchangeFamilyAlong w F j).cMajorana *
        (exchangeFamilyAlong w F j).cMajorana = 1 := by
  exact (exchangeFamilyAlong w F j).cMajorana_sq

/-- A transported finite family still has `d² = -1` at every site. -/
theorem exchangeFamilyAlong_dMajorana_sq
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (w : List α) (j : α) :
    (exchangeFamilyAlong w F j).dMajorana *
        (exchangeFamilyAlong w F j).dMajorana = -1 := by
  exact (exchangeFamilyAlong w F j).dMajorana_sq

/-- A transported finite family still has `{c,d}=0` at every site. -/
theorem exchangeFamilyAlong_c_d_anticomm_zero
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (w : List α) (j : α) :
    (exchangeFamilyAlong w F j).cMajorana * (exchangeFamilyAlong w F j).dMajorana +
        (exchangeFamilyAlong w F j).dMajorana * (exchangeFamilyAlong w F j).cMajorana =
      0 := by
  exact (exchangeFamilyAlong w F j).cMajorana_dMajorana_anticomm_zero

/--
Finite compass-chain invariant for a transported prefix word: every transported
site retains the split-Majorana square and anticommutation laws.
-/
theorem exchangeFamilyAlong_local_symmetry_invariant
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (w : List α) (j : α) :
    (exchangeFamilyAlong w F j).cMajorana *
          (exchangeFamilyAlong w F j).cMajorana = 1 ∧
      (exchangeFamilyAlong w F j).dMajorana *
          (exchangeFamilyAlong w F j).dMajorana = -1 ∧
      (exchangeFamilyAlong w F j).cMajorana * (exchangeFamilyAlong w F j).dMajorana +
          (exchangeFamilyAlong w F j).dMajorana * (exchangeFamilyAlong w F j).cMajorana =
        0 := by
  exact ⟨exchangeFamilyAlong_cMajorana_sq F w j,
    exchangeFamilyAlong_dMajorana_sq F w j,
    exchangeFamilyAlong_c_d_anticomm_zero F w j⟩

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

/-- A transported finite family still has parity square `Π² = 1` at every site. -/
theorem exchangeFamilyAlong_parityOp_sq
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (w : List α) (j : α) :
    (exchangeFamilyAlong w F j).parityOp *
        (exchangeFamilyAlong w F j).parityOp = 1 := by
  exact (exchangeFamilyAlong w F j).parityOp_sq

/--
Finite compass-chain invariant including local parity: every transported site
retains `c² = 1`, `d² = -1`, `{c,d}=0`, and `Π² = 1`.
-/
theorem exchangeFamilyAlong_compass_chain_invariant
    {α : Type*} [DecidableEq α]
    (F : α → ExteriorCARPair Op) (w : List α) (j : α) :
    (exchangeFamilyAlong w F j).cMajorana *
          (exchangeFamilyAlong w F j).cMajorana = 1 ∧
      (exchangeFamilyAlong w F j).dMajorana *
          (exchangeFamilyAlong w F j).dMajorana = -1 ∧
      (exchangeFamilyAlong w F j).cMajorana * (exchangeFamilyAlong w F j).dMajorana +
          (exchangeFamilyAlong w F j).dMajorana * (exchangeFamilyAlong w F j).cMajorana =
        0 ∧
      (exchangeFamilyAlong w F j).parityOp * (exchangeFamilyAlong w F j).parityOp = 1 := by
  exact ⟨exchangeFamilyAlong_cMajorana_sq F w j,
    exchangeFamilyAlong_dMajorana_sq F w j,
    exchangeFamilyAlong_c_d_anticomm_zero F w j,
    exchangeFamilyAlong_parityOp_sq F w j⟩

end ExteriorCARPair

end InfoGeometry.Arithmetic.PrimeMajoranaCAR
