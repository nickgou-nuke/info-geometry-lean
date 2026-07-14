import Mathlib

/-!
# Finite N=2 inductive supercharge transport

No wrappers. No witness fields.

This proves that an N=2 supercharge closure relation is preserved under
iterated symmetry/bonding endomorphisms.

Local closure:

  Q² = 0, R² = 0, {Q,R} = H + Z

implies:

  (Q + R)² = H + Z

and for every finite iterate `φ^[n]`:

  {φ^[n]Q, φ^[n]R} = φ^[n]H + φ^[n]Z
  (φ^[n](Q+R))² = φ^[n]H + φ^[n]Z
-/

namespace FiniteN2Induction

variable {A B : Type*} [Ring A] [Ring B]

/-- Anticommutator in a possibly noncommutative ring. -/
def anticommutator (x y : A) : A :=
  x * y + y * x

/-- If `Q²=0` and `R²=0`, then `(Q+R)² = {Q,R}`. -/
theorem square_add_of_sq_zero
    (Q R : A)
    (hQ : Q * Q = 0)
    (hR : R * R = 0) :
    (Q + R) * (Q + R) = anticommutator Q R := by
  unfold anticommutator
  calc
    (Q + R) * (Q + R)
        = Q * Q + Q * R + R * Q + R * R := by
          noncomm_ring
    _ = 0 + Q * R + R * Q + 0 := by
          rw [hQ, hR]
    _ = Q * R + R * Q := by
          simp

/-- N=2 closure: if `{Q,R}=H+Z`, then `(Q+R)²=H+Z`. -/
theorem n2_supercharge_square_eq_even_plus_central
    (Q R H Z : A)
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hQR : anticommutator Q R = H + Z) :
    (Q + R) * (Q + R) = H + Z := by
  rw [square_add_of_sq_zero Q R hQ hR, hQR]

/-- Ring homomorphisms preserve anticommutators. -/
theorem map_anticommutator
    (φ : A →+* B)
    (Q R : A) :
    φ (anticommutator Q R) =
      anticommutator (φ Q) (φ R) := by
  simp [anticommutator]

/-- Ring homomorphisms preserve square-zero charges. -/
theorem map_sq_zero
    (φ : A →+* B)
    (Q : A)
    (hQ : Q * Q = 0) :
    φ Q * φ Q = 0 := by
  have h := congrArg φ hQ
  simpa using h

/-- Ring homomorphisms transport the N=2 closure relation. -/
theorem map_n2_closure
    (φ : A →+* B)
    (Q R H Z : A)
    (hQR : anticommutator Q R = H + Z) :
    anticommutator (φ Q) (φ R) = φ H + φ Z := by
  rw [← map_anticommutator φ Q R, hQR]
  simp

/--
Ring homomorphisms transport the full N=2 square closure.

If `Q²=0`, `R²=0`, and `{Q,R}=H+Z`, then

  `(φ(Q+R))² = φH + φZ`.
-/
theorem map_n2_supercharge_square_eq_even_plus_central
    (φ : A →+* B)
    (Q R H Z : A)
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hQR : anticommutator Q R = H + Z) :
    φ (Q + R) * φ (Q + R) = φ H + φ Z := by
  have hQ' : φ Q * φ Q = 0 :=
    map_sq_zero φ Q hQ
  have hR' : φ R * φ R = 0 :=
    map_sq_zero φ R hR
  have hQR' :
      anticommutator (φ Q) (φ R) = φ H + φ Z :=
    map_n2_closure φ Q R H Z hQR
  have hsq :
      (φ Q + φ R) * (φ Q + φ R) = φ H + φ Z :=
    n2_supercharge_square_eq_even_plus_central
      (Q := φ Q) (R := φ R) (H := φ H) (Z := φ Z)
      hQ' hR' hQR'
  simpa using hsq

/-! ## Finite iterated bonding/symmetry map -/

/-- Finite iterate of a ring endomorphism. -/
def iterateEnd (φ : A →+* A) : ℕ → A →+* A
  | 0 => RingHom.id A
  | n + 1 => (iterateEnd φ n).comp φ

@[simp]
theorem iterateEnd_zero (φ : A →+* A) :
    iterateEnd φ 0 = RingHom.id A := rfl

@[simp]
theorem iterateEnd_succ (φ : A →+* A) (n : ℕ) :
    iterateEnd φ (n + 1) = (iterateEnd φ n).comp φ := rfl

/--
Finite-stage transport of the odd-odd closure through an iterated bonding map.

This is the finite inductive-chain theorem:
if `{Q,R}=H+Z` at stage zero, then the same closure relation holds after
any finite iterate of the structure-preserving endomorphism.
-/
theorem iterateEnd_preserves_n2_closure
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : A)
    (hQR : anticommutator Q R = H + Z) :
    anticommutator ((iterateEnd φ n) Q) ((iterateEnd φ n) R) =
      (iterateEnd φ n) H + (iterateEnd φ n) Z := by
  exact map_n2_closure (iterateEnd φ n) Q R H Z hQR

/--
Finite-stage transport of the full supercharge-square closure through an
iterated bonding map.
-/
theorem iterateEnd_preserves_n2_square_closure
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : A)
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hQR : anticommutator Q R = H + Z) :
    (iterateEnd φ n) (Q + R) * (iterateEnd φ n) (Q + R) =
      (iterateEnd φ n) H + (iterateEnd φ n) Z := by
  exact
    map_n2_supercharge_square_eq_even_plus_central
      (iterateEnd φ n) Q R H Z hQ hR hQR

end FiniteN2Induction
