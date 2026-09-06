import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Tactic

namespace InfoGeometry.Modular.GrandSynthesis

variable {A : Type*} [Ring A]

/-!
=============================================================================
PART 1: Inner Modular Commutator Derivations & Lie-Jacobi Homomorphism
=============================================================================
-/

/-- The commutator adjoint map ad_K(X) = [K, X] = K * X - X * K. -/
def ad (K : A) : A →ₗ[ℤ] A where
  toFun X := K * X - X * K
  map_add' X Y := by
    simp only [mul_add, add_mul]
    abel
  map_smul' r X := by
    change K * (r • X) - (r • X) * K = r • (K * X - X * K)
    have hL : K * (r • X) = r • (K * X) := (AddMonoidHom.mulLeft K).map_zsmul X r
    have hR : (r • X) * K = r • (X * K) := (AddMonoidHom.mulRight K).map_zsmul X r
    rw [hL, hR, smul_sub]

@[simp] theorem ad_apply (K : A) (X : A) : ad K X = K * X - X * K := rfl

/-- 🏆 THEOREM 1: The inner commutator map satisfies the Leibniz rule (is a derivation). -/
theorem ad_leibniz (K X Y : A) :
    ad K (X * Y) = (ad K X) * Y + X * (ad K Y) := by
  simp only [ad_apply]
  calc
    K * (X * Y) - (X * Y) * K
      = (K * X * Y - X * K * Y) + (X * K * Y - X * Y * K) := by
        simp only [mul_assoc]
        abel
    _ = (K * X - X * K) * Y + X * (K * Y - Y * K) := by
        simp only [sub_mul, mul_sub, mul_assoc]

/-- 🏆 THEOREM 2: Inner derivations annihilate the identity element: ad_K(1) = 0. -/
@[simp]
theorem ad_one (K : A) : ad K 1 = 0 := by
  rw [ad_apply K 1, mul_one, one_mul, sub_self]

/-- 🏆 THEOREM 3: Inner derivations annihilate their own generator: ad_K(K) = 0. -/
@[simp]
theorem ad_self (K : A) : ad K K = 0 := by
  rw [ad_apply K K, sub_self]

/-- The Lie bracket commutator of two elements. -/
def bracket (X Y : A) : A :=
  X * Y - Y * X

/-- 🏆 THEOREM 4: The Jacobi Identity / Lie Algebra Homomorphism:
    ad([K₁, K₂]) = [ad_{K₁}, ad_{K₂}] = ad_{K₁} ∘ ad_{K₂} - ad_{K₂} ∘ ad_{K₁}. -/
theorem ad_bracket_hom (K1 K2 X : A) :
    ad (bracket K1 K2) X = ad K1 (ad K2 X) - ad K2 (ad K1 X) := by
  simp only [bracket, ad_apply]
  noncomm_ring

/-!
=============================================================================
PART 2: Non-Commutative Logarithmic Radon–Nikodym Cocycles
=============================================================================
-/

/-- Left logarithmic derivative: dlog_L(u) = u⁻¹ • D(u). -/
def dlogL (D : A → A) (u : Aˣ) : A :=
  (↑u⁻¹ : A) * D (u : A)

/-- Right logarithmic derivative: dlog_R(u) = D(u) • u⁻¹. -/
def dlogR (D : A → A) (u : Aˣ) : A :=
  D (u : A) * (↑u⁻¹ : A)

/-- 🏆 THEOREM 5: Non-Commutative Left Maurer–Cartan Cocycle Rule:
    dlog_L(u * v) = v⁻¹ * dlog_L(u) * v + dlog_L(v). -/
theorem dlogL_mul (D : A → A)
    (hLeibniz : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (u v : Aˣ) :
    dlogL D (u * v) = (↑v⁻¹ : A) * dlogL D u * (v : A) + dlogL D v := by
  have hunit : (↑(u * v)⁻¹ : A) = (↑v⁻¹ : A) * (↑u⁻¹ : A) := by
    rw [mul_inv_rev, Units.val_mul]
  have hu : (↑u⁻¹ : A) * (↑u : A) = 1 := Units.inv_mul u
  dsimp [dlogL]
  rw [hunit, hLeibniz (↑u : A) (↑v : A)]
  calc
    (↑v⁻¹ * ↑u⁻¹) * (D ↑u * ↑v + ↑u * D ↑v)
        = (↑v⁻¹ * ↑u⁻¹ * (D ↑u * ↑v)) + (↑v⁻¹ * ↑u⁻¹ * (↑u * D ↑v)) := by
          rw [mul_add]
      _ = (↑v⁻¹ * (↑u⁻¹ * D ↑u) * ↑v) + (↑v⁻¹ * (((↑u⁻¹ : A) * (↑u : A)) * D ↑v)) := by
          simp only [mul_assoc]
      _ = (↑v⁻¹ * (↑u⁻¹ * D ↑u) * ↑v) + (↑v⁻¹ * (1 * D ↑v)) := by
          rw [hu]
      _ = ↑v⁻¹ * (↑u⁻¹ * D ↑u) * ↑v + ↑v⁻¹ * D ↑v := by
          rw [one_mul]

/-- 🏆 THEOREM 6: Non-Commutative Right Maurer–Cartan Cocycle Rule:
    dlog_R(u * v) = dlog_R(u) + u * dlog_R(v) * u⁻¹. -/
theorem dlogR_mul (D : A → A)
    (hLeibniz : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (u v : Aˣ) :
    dlogR D (u * v) = dlogR D u + (u : A) * dlogR D v * (↑u⁻¹ : A) := by
  have hunit : (↑(u * v)⁻¹ : A) = (↑v⁻¹ : A) * (↑u⁻¹ : A) := by
    rw [mul_inv_rev, Units.val_mul]
  have hv : (v : A) * (↑v⁻¹ : A) = 1 := Units.mul_inv v
  dsimp [dlogR]
  rw [hunit, hLeibniz (↑u : A) (↑v : A)]
  calc
    (D ↑u * ↑v + ↑u * D ↑v) * (↑v⁻¹ * ↑u⁻¹)
        = (D ↑u * ↑v) * (↑v⁻¹ * ↑u⁻¹) + (↑u * D ↑v) * (↑v⁻¹ * ↑u⁻¹) := by
          rw [add_mul]
      _ = D ↑u * ((v : A) * (↑v⁻¹ : A)) * (↑u⁻¹ : A) + (u : A) * (D ↑v * ↑v⁻¹) * (↑u⁻¹ : A) := by
          simp only [mul_assoc]
      _ = D ↑u * 1 * (↑u⁻¹ : A) + (u : A) * (D ↑v * ↑v⁻¹) * (↑u⁻¹ : A) := by
          rw [hv]
      _ = D ↑u * (↑u⁻¹ : A) + (u : A) * (D ↑v * ↑v⁻¹) * (↑u⁻¹ : A) := by
          rw [mul_one]

/-- 🏆 THEOREM 7: Derivation of Unit Inverses in Non-Commutative Rings:
    D(u⁻¹) = - u⁻¹ * D(u) * u⁻¹. -/
theorem derivation_unit_inv_noncomm (D : A → A)
    (hLeibniz : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (hOne : D 1 = 0)
    (u : Aˣ) :
    D (↑u⁻¹ : A) = - (↑u⁻¹ : A) * D (u : A) * (↑u⁻¹ : A) := by
  have h_prod : D ((u : A) * (↑u⁻¹ : A)) = 0 := by
    rw [Units.mul_inv, hOne]
  have h_leib := hLeibniz (u : A) (↑u⁻¹ : A)
  rw [h_leib] at h_prod
  have h_shift : (u : A) * D (↑u⁻¹ : A) = - (D (u : A) * (↑u⁻¹ : A)) :=
    eq_neg_of_add_eq_zero_right h_prod
  have h_mult : (↑u⁻¹ : A) * ((u : A) * D (↑u⁻¹ : A)) = (↑u⁻¹ : A) * (- (D (u : A) * (↑u⁻¹ : A))) := by
    rw [h_shift]
  have hu : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  calc
    D (↑u⁻¹ : A) = 1 * D (↑u⁻¹ : A) := by rw [one_mul]
      _ = ((↑u⁻¹ : A) * (u : A)) * D (↑u⁻¹ : A) := by rw [hu]
      _ = (↑u⁻¹ : A) * ((u : A) * D (↑u⁻¹ : A)) := by rw [mul_assoc]
      _ = (↑u⁻¹ : A) * (- (D (u : A) * (↑u⁻¹ : A))) := by rw [h_mult]
      _ = - (↑u⁻¹ : A) * D (u : A) * (↑u⁻¹ : A) := by
        simp only [mul_assoc, neg_mul, mul_neg]

/-- 🏆 THEOREM 8: Left-Right Inversion Duality:
    dlog_L(u⁻¹) = - dlog_R(u). -/
theorem dlogL_inv (D : A → A)
    (hLeibniz : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (hOne : D 1 = 0)
    (u : Aˣ) :
    dlogL D (u⁻¹) = - dlogR D u := by
  dsimp [dlogL, dlogR]
  have h_u_inv : (u⁻¹ : Aˣ)⁻¹ = u := inv_inv u
  rw [h_u_inv]
  have h_inv_der := derivation_unit_inv_noncomm D hLeibniz hOne u
  rw [h_inv_der]
  have hu : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  calc
    (u : A) * (- (↑u⁻¹ : A) * D (u : A) * (↑u⁻¹ : A))
        = - ((u : A) * (↑u⁻¹ : A)) * (D (u : A) * (↑u⁻¹ : A)) := by
          simp only [mul_neg, neg_mul, mul_assoc]
      _ = - 1 * (D (u : A) * (↑u⁻¹ : A)) := by rw [hu]
      _ = - (D (u : A) * (↑u⁻¹ : A)) := by rw [neg_one_mul]

/-!
=============================================================================
PART 3: Inner Modular Derivations as Gauge Shifts
=============================================================================
-/

/-- 🏆 THEOREM 9: The Inner Modular Logarithmic Derivative is a Gauge Shift:
    dlog_L(ad_K, u) = u⁻¹ * K * u - K. -/
theorem dlogL_inner (K : A) (u : Aˣ) :
    dlogL (fun x => ad K x) u = (↑u⁻¹ : A) * K * (u : A) - K := by
  dsimp [dlogL, ad]
  calc
    (↑u⁻¹ : A) * (K * (u : A) - (u : A) * K)
        = (↑u⁻¹ : A) * K * (u : A) - ((↑u⁻¹ : A) * (u : A)) * K := by
          simp only [mul_sub, mul_assoc]
      _ = (↑u⁻¹ : A) * K * (u : A) - 1 * K := by rw [Units.inv_mul]
      _ = (↑u⁻¹ : A) * K * (u : A) - K := by rw [one_mul]

/-- 🏆 THEOREM 10: The Right Modular Logarithmic Derivative is a Gauge Shift:
    dlog_R(ad_K, u) = K - u * K * u⁻¹. -/
theorem dlogR_inner (K : A) (u : Aˣ) :
    dlogR (fun x => ad K x) u = K - (u : A) * K * (↑u⁻¹ : A) := by
  dsimp [dlogR, ad]
  calc
    (K * (u : A) - (u : A) * K) * (↑u⁻¹ : A)
        = K * ((u : A) * (↑u⁻¹ : A)) - (u : A) * K * (↑u⁻¹ : A) := by
          simp only [sub_mul, mul_assoc]
      _ = K * 1 - (u : A) * K * (↑u⁻¹ : A) := by rw [Units.mul_inv]
      _ = K - (u : A) * K * (↑u⁻¹ : A) := by rw [mul_one]

end InfoGeometry.Modular.GrandSynthesis
