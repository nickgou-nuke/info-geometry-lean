import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Pure Noncommutative Modular Derivations and Logarithmic Forms

This module formalizes purely noncommutative modular derivations and logarithmic derivatives
on an arbitrary, possibly noncommutative ring `A` without any commutative or scalar assumptions.

1. Inner derivations: `ad_K(X) = [K, X] = K * X - X * K`
2. Noncommutative Leibniz rule: `ad_K(X * Y) = (ad_K X) * Y + X * (ad_K Y)`
3. Identity annihilation: `ad_K(1) = 0`
4. Inner Lie bracket preservation: `[ad_{K₁}, ad_{K₂}] = ad_{[K₁, K₂]}`
5. Noncommutative logarithmic derivative (Maurer–Cartan): `dlog_L(D, u) = u⁻¹ * D(u)`
6. Non-abelian product rule: `dlog_L(u * v) = v⁻¹ * dlog_L(u) * v + dlog_L(v)`
7. Non-abelian inversion: `dlog_L(u⁻¹) = - (u * dlog_L(u) * u⁻¹)`
8. Exact modular gauge shift: `dlog_L(ad_K, u) = u⁻¹ * K * u - K`

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Modular.Noncommutative

variable {A : Type*} [Ring A]

/-!
=============================================================================
SECTION 1: Inner Derivations on Arbitrary Noncommutative Rings
=============================================================================
-/

/-- The Adjoint Action (Modular Commutator) on an arbitrary noncommutative ring A:
    ad_K(X) = [K, X] = K * X - X * K -/
def adK (K : A) : A →ₗ[ℤ] A where
  toFun X := K * X - X * K
  map_add' X Y := by
    simp only [mul_add, add_mul]
    abel
  map_smul' r X := by
    change K * (r • X) - (r • X) * K = r • (K * X - X * K)
    have hL : K * (r • X) = r • (K * X) := (AddMonoidHom.mulLeft K).map_zsmul X r
    have hR : (r • X) * K = r • (X * K) := (AddMonoidHom.mulRight K).map_zsmul X r
    rw [hL, hR, smul_sub]

@[simp]
theorem adK_apply (K X : A) : adK K X = K * X - X * K := rfl

/-- 
  THEOREM 1: The Noncommutative Leibniz Rule for Modular Commutators.
  ad_K(X * Y) = (ad_K X) * Y + X * (ad_K Y)
  This proves that the modular flow generates an automorphism of the noncommutative algebra.
-/
theorem adK_is_derivation (K : A) (X Y : A) :
    adK K (X * Y) = (adK K X) * Y + X * (adK K Y) := by
  simp only [adK_apply]
  calc
    K * (X * Y) - (X * Y) * K
      = (K * X * Y - X * K * Y) + (X * K * Y - X * Y * K) := by
        simp only [mul_assoc]
        abel
    _ = (K * X - X * K) * Y + X * (K * Y - Y * K) := by
        simp only [sub_mul, mul_sub, mul_assoc]

/-- THEOREM 2: The Modular Derivation annihilates the identity element: ad_K(1) = 0. -/
@[simp]
theorem adK_one (K : A) : adK K 1 = 0 := by
  simp [adK_apply]

/-- 
  THEOREM 3: Inner Lie Bracket Preservation.
  [ad_{K₁}, ad_{K₂}](X) = ad_{[K₁, K₂]}(X)
  Inner derivations form a Lie subalgebra under the commutator.
-/
theorem adK_commutator_eq_adK_bracket (K₁ K₂ X : A) :
    adK K₁ (adK K₂ X) - adK K₂ (adK K₁ X) = adK (adK K₁ K₂) X := by
  dsimp [adK]
  calc
    K₁ * (K₂ * X - X * K₂) - (K₂ * X - X * K₂) * K₁ -
      (K₂ * (K₁ * X - X * K₁) - (K₁ * X - X * K₁) * K₂)
      = (K₁ * K₂ - K₂ * K₁) * X - X * (K₁ * K₂ - K₂ * K₁) := by
        simp only [mul_sub, sub_mul, mul_assoc]
        abel
    _ = adK (adK K₁ K₂) X := by rfl

/-!
=============================================================================
SECTION 2: Pure Noncommutative Logarithmic Derivations (Maurer-Cartan)
=============================================================================
-/

/-- A `ℤ`-linear Leibniz derivation on a possibly noncommutative ring A. -/
def IsNCDerivation (D : A →ₗ[ℤ] A) : Prop :=
  ∀ x y, D (x * y) = D x * y + x * D y

/-- The Left Noncommutative Logarithmic Derivative of a Unit:
    dlog_L(D, u) = u⁻¹ * D(u) -/
def dlogL (D : A →ₗ[ℤ] A) (u : Aˣ) : A :=
  (↑(u⁻¹) : A) * D (u : A)

/-- The right Maurer--Cartan logarithmic derivative of a unit. -/
def dlogR (D : A →ₗ[ℤ] A) (u : Aˣ) : A :=
  D (u : A) * (↑(u⁻¹) : A)

/-- The left logarithmic derivative detects stationary units exactly. -/
theorem dlogL_eq_zero_iff (D : A →ₗ[ℤ] A) (u : Aˣ) :
    dlogL D u = 0 ↔ D (u : A) = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun x : A => (u : A) * x) h
    simpa [dlogL, mul_assoc, u.val_inv] using h'
  · intro h
    simp [dlogL, h]

/-- The right logarithmic derivative detects stationary units exactly. -/
theorem dlogR_eq_zero_iff (D : A →ₗ[ℤ] A) (u : Aˣ) :
    dlogR D u = 0 ↔ D (u : A) = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun x : A => x * (u : A)) h
    simpa [dlogR, mul_assoc, u.val_inv] using h'
  · intro h
    simp [dlogR, h]

/-- The right logarithmic derivative vanishes on the identity unit. -/
@[simp]
theorem dlogR_one (D : A →ₗ[ℤ] A) (hD : IsNCDerivation D) :
    dlogR D 1 = 0 := by
  dsimp [dlogR]
  have h := hD 1 1
  have h_one : D (1 : A) = 0 := by
    have h' : D 1 = D 1 + D 1 := by simpa only [mul_one, one_mul] using h
    have h'' : D 1 + 0 = D 1 + D 1 := by simpa using h'
    exact (add_left_cancel h'').symm
  simp [h_one]

/-- Derivation annihilates 1 in any ring -/
theorem derivation_map_one (D : A →ₗ[ℤ] A) (hD : IsNCDerivation D) : D 1 = 0 := by
  have h := hD 1 1
  have h' : D 1 = D 1 + D 1 := by
    simpa only [mul_one, one_mul] using h
  have h'' : D 1 + 0 = D 1 + D 1 := by simpa using h'
  exact (add_left_cancel h'').symm

/-- THEOREM 4: Annihilation of the Identity Unit under Logarithmic Derivative: dlog_L(1) = 0. -/
@[simp]
theorem dlogL_one (D : A →ₗ[ℤ] A) (hD : IsNCDerivation D) :
    dlogL D 1 = 0 := by
  dsimp [dlogL]
  rw [derivation_map_one D hD, mul_zero]

/-- 
  THEOREM 5: Noncommutative Logarithmic Product Rule (Maurer–Cartan Formula).
  dlog_L(u * v) = v⁻¹ * dlog_L(u) * v + dlog_L(v)
  This is the exact non-abelian chain rule without assuming commutativity.
-/
theorem dlogL_mul (D : A →ₗ[ℤ] A) (hD : IsNCDerivation D) (u v : Aˣ) :
    dlogL D (u * v) =
      (↑(v⁻¹) : A) * dlogL D u * (v : A) + dlogL D v := by
  dsimp [dlogL]
  have hprod : D ((u : A) * (v : A)) = D (u : A) * (v : A) + (u : A) * D (v : A) := hD _ _
  rw [mul_inv_rev]
  change ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) * D ((u : A) * (v : A)) = _
  rw [hprod]
  have hu : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
  calc
    ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) * (D (u : A) * (v : A) + (u : A) * D (v : A))
      = ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) * (D (u : A) * (v : A)) +
        ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) * ((u : A) * D (v : A)) := by
          rw [mul_add]
    _ = (↑(v⁻¹) : A) * ((↑(u⁻¹) : A) * D (u : A)) * (v : A) +
        (↑(v⁻¹) : A) * (((↑(u⁻¹) : A) * (u : A)) * D (v : A)) := by
          simp only [mul_assoc]
    _ = (↑(v⁻¹) : A) * ((↑(u⁻¹) : A) * D (u : A)) * (v : A) +
        (↑(v⁻¹) : A) * D (v : A) := by
          rw [hu, one_mul]

/-- Under the precise commutation hypothesis that kills the conjugation term,
the left noncommutative logarithmic derivative becomes additive. -/
theorem dlogL_mul_of_commute (D : A →ₗ[ℤ] A)
    (hD : IsNCDerivation D) (u v : Aˣ)
    (hcomm : Commute (v : A) (dlogL D u)) :
    dlogL D (u * v) = dlogL D u + dlogL D v := by
  rw [dlogL_mul D hD u v]
  have hconj :
      (↑(v⁻¹) : A) * dlogL D u * (v : A) = dlogL D u := by
    calc
      (↑(v⁻¹) : A) * dlogL D u * (v : A) =
          (↑(v⁻¹) : A) * (dlogL D u * (v : A)) := by
        simp only [mul_assoc]
      _ = (↑(v⁻¹) : A) * ((v : A) * dlogL D u) := by
        rw [hcomm.eq]
      _ = (↑(v⁻¹) : A) * (v : A) * dlogL D u := by
        simp only [mul_assoc]
      _ = dlogL D u := by
        have hv : (↑(v⁻¹) : A) * (v : A) = 1 := v.inv_val
        rw [hv, one_mul]
  rw [hconj]

/-- 
  THEOREM 6: Noncommutative Logarithmic Inversion Law.
  dlog_L(u⁻¹) = - (u * dlog_L(u) * u⁻¹)
  Non-abelian time-reversal under adjoint gauge conjugation.
-/
theorem dlogL_inv (D : A →ₗ[ℤ] A) (hD : IsNCDerivation D) (u : Aˣ) :
    dlogL D (u⁻¹) =
      - ((u : A) * dlogL D u * (↑(u⁻¹) : A)) := by
  dsimp [dlogL]
  have hone : D (1 : A) = 0 := derivation_map_one D hD
  have hprod : D ((u : A) * (↑(u⁻¹) : A)) =
      D (u : A) * (↑(u⁻¹) : A) + (u : A) * D (↑(u⁻¹) : A) := hD _ _
  have hunit : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
  rw [hunit, hone] at hprod
  have hinv : (u : A) * D (↑(u⁻¹) : A) = - (D (u : A) * (↑(u⁻¹) : A)) := by
    exact eq_neg_of_add_eq_zero_right hprod.symm
  calc
    (↑((u⁻¹)⁻¹) : A) * D (↑(u⁻¹) : A) =
        (u : A) * D (↑(u⁻¹) : A) := by simp
    _ = - (D (u : A) * (↑(u⁻¹) : A)) := hinv
    _ = - ((u : A) * ((↑(u⁻¹) : A) * D (u : A)) * (↑(u⁻¹) : A)) := by
        have hrewrite : (u : A) * ((↑(u⁻¹) : A) * D (u : A)) * (↑(u⁻¹) : A) =
            D (u : A) * (↑(u⁻¹) : A) := by
          calc
            (u : A) * ((↑(u⁻¹) : A) * D (u : A)) * (↑(u⁻¹) : A)
              = ((u : A) * (↑(u⁻¹) : A)) * D (u : A) * (↑(u⁻¹) : A) := by simp only [mul_assoc]
            _ = 1 * D (u : A) * (↑(u⁻¹) : A) := by rw [hunit]
            _ = D (u : A) * (↑(u⁻¹) : A) := by rw [one_mul]
        rw [hrewrite]

/-- The right noncommutative product rule. -/
theorem dlogR_mul (D : A →ₗ[ℤ] A) (hD : IsNCDerivation D) (u v : Aˣ) :
    dlogR D (u * v) =
      dlogR D u + (u : A) * dlogR D v * (↑(u⁻¹) : A) := by
  dsimp [dlogR]
  have hprod : D ((u : A) * (v : A)) = D (u : A) * (v : A) +
      (u : A) * D (v : A) := hD _ _
  rw [hprod]
  have h_inv : ((u * v)⁻¹ : Aˣ).val = (v⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val := by
    rw [mul_inv_rev, Units.val_mul]
  rw [h_inv]
  have hv : (v : A) * (↑(v⁻¹) : A) = 1 := v.val_inv
  calc
    (D (u : A) * (v : A) + (u : A) * D (v : A)) *
        ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) =
        (D (u : A) * (v : A)) * ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) +
          ((u : A) * D (v : A)) * ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) := by
            rw [add_mul]
    _ = D (u : A) * ((v : A) * (↑(v⁻¹) : A) * (↑(u⁻¹) : A)) +
          ((u : A) * (D (v : A) * (↑(v⁻¹) : A))) * (↑(u⁻¹) : A) := by
            simp only [mul_assoc]
    _ = D (u : A) * (1 * (↑(u⁻¹) : A)) +
          ((u : A) * (D (v : A) * (↑(v⁻¹) : A))) * (↑(u⁻¹) : A) := by rw [hv]
    _ = D (u : A) * (↑(u⁻¹) : A) +
          (u : A) * (D (v : A) * (↑(v⁻¹) : A)) * (↑(u⁻¹) : A) := by
            rw [one_mul]

/-- Right logarithmic additivity under the precise commutation condition. -/
theorem dlogR_mul_of_commute (D : A →ₗ[ℤ] A)
    (hD : IsNCDerivation D) (u v : Aˣ)
    (hcomm : Commute (u : A) (dlogR D v)) :
    dlogR D (u * v) = dlogR D u + dlogR D v := by
  rw [dlogR_mul D hD u v]
  have hconj :
      (u : A) * dlogR D v * (↑(u⁻¹) : A) = dlogR D v := by
    calc
      (u : A) * dlogR D v * (↑(u⁻¹) : A) =
          (dlogR D v) * (u : A) * (↑(u⁻¹) : A) := by
            rw [hcomm.eq]
      _ = (dlogR D v) * ((u : A) * (↑(u⁻¹) : A)) := by
            simp only [mul_assoc]
      _ = dlogR D v := by
            change dlogR D v * (u.val * u.inv) = dlogR D v
            rw [u.val_inv, mul_one]
  rw [hconj]

/-- Inversion exchanges left and right logarithmic derivatives. -/
theorem dlogL_inv_eq_neg_dlogR (D : A →ₗ[ℤ] A)
    (hD : IsNCDerivation D) (u : Aˣ) :
    dlogL D (u⁻¹) = -dlogR D u := by
  rw [dlogL_inv D hD u]
  dsimp [dlogL, dlogR]
  have hu : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
  calc
    -((u : A) * ((↑(u⁻¹) : A) * D (u : A)) * (↑(u⁻¹) : A)) =
        -(((u : A) * (↑(u⁻¹) : A)) * D (u : A) * (↑(u⁻¹) : A)) := by
          simp only [mul_assoc]
    _ = -(D (u : A) * (↑(u⁻¹) : A)) := by rw [hu, one_mul]

/-- Inversion exchanges the right and left logarithmic derivatives. -/
theorem dlogR_inv_eq_neg_dlogL (D : A →ₗ[ℤ] A)
    (hD : IsNCDerivation D) (u : Aˣ) :
    dlogR D (u⁻¹) = -dlogL D u := by
  have h := dlogL_inv_eq_neg_dlogR D hD (u⁻¹)
  have hneg := congrArg Neg.neg h
  simpa using hneg.symm

/-!
=============================================================================
SECTION 3: Inner Modular Logarithmic Derivatives as Discrete Gauge Shifts
=============================================================================
-/

/-- 
  THEOREM 7: Exact Inner Modular Logarithmic Derivative.
  dlog_L(ad_K, u) = u⁻¹ * K * u - K = Ad_{u⁻¹}(K) - K
  For inner modular flows, the logarithmic derivative is identically the 
  non-abelian gauge transformation shift of the generator K.
-/
theorem dlogL_adK (K : A) (u : Aˣ) :
    dlogL (adK K) u = (↑(u⁻¹) : A) * K * (u : A) - K := by
  dsimp [dlogL, adK]
  have hu : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
  calc
    (↑(u⁻¹) : A) * (K * (u : A) - (u : A) * K)
      = (↑(u⁻¹) : A) * (K * (u : A)) - (↑(u⁻¹) : A) * ((u : A) * K) := by
        rw [mul_sub]
    _ = (↑(u⁻¹) : A) * K * (u : A) - ((↑(u⁻¹) : A) * (u : A)) * K := by
        simp only [mul_assoc]
    _ = (↑(u⁻¹) : A) * K * (u : A) - 1 * K := by
        rw [hu]
    _ = (↑(u⁻¹) : A) * K * (u : A) - K := by
        rw [one_mul]

/-- The right logarithmic derivative of an inner modular derivation is the
right gauge shift of its generator. -/
theorem dlogR_adK (K : A) (u : Aˣ) :
    dlogR (adK K) u = K - (u : A) * K * (↑(u⁻¹) : A) := by
  dsimp [dlogR, adK]
  have hu : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
  calc
    (K * (u : A) - (u : A) * K) * (↑(u⁻¹) : A) =
        K * ((u : A) * (↑(u⁻¹) : A)) -
          (u : A) * K * (↑(u⁻¹) : A) := by
            rw [sub_mul]
            simp only [mul_assoc]
    _ = K - (u : A) * K * (↑(u⁻¹) : A) := by rw [hu, mul_one]

/-- The right gauge shift vanishes exactly on the same centralizer. -/
theorem dlogR_adK_eq_zero_iff (K : A) (u : Aˣ) :
    dlogR (adK K) u = 0 ↔ Commute K (u : A) := by
  rw [dlogR_adK]
  constructor
  · intro h
    have hshift : (u : A) * K * (↑(u⁻¹) : A) = K :=
      (sub_eq_zero.mp h).symm
    calc
      K * (u : A) = ((u : A) * K * (↑(u⁻¹) : A)) * (u : A) := by
        rw [hshift]
      _ = (u : A) * K * ((↑(u⁻¹) : A) * (u : A)) := by
        simp only [mul_assoc]
      _ = (u : A) * K := by
        have hleft : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
        rw [hleft, mul_one]
  · intro hcomm
    apply sub_eq_zero.mpr
    calc
      K = (K * (u : A)) * (↑(u⁻¹) : A) := by
        have hright : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
        calc
          K = K * 1 := (mul_one K).symm
          _ = K * ((u : A) * (↑(u⁻¹) : A)) := by rw [hright]
          _ = (K * (u : A)) * (↑(u⁻¹) : A) := by rw [mul_assoc]
      _ = ((u : A) * K) * (↑(u⁻¹) : A) := by rw [hcomm.eq]
      _ = (u : A) * K * (↑(u⁻¹) : A) := by simp only [mul_assoc]

/-- The inner logarithmic derivative vanishes exactly on the centralizer of
the chosen unit. -/
theorem dlogL_adK_eq_zero_iff (K : A) (u : Aˣ) :
    dlogL (adK K) u = 0 ↔ Commute K (u : A) := by
  rw [dlogL_adK]
  constructor
  · intro h
    have hconj : (↑(u⁻¹) : A) * K * (u : A) = K := sub_eq_zero.mp h
    calc
      K * (u : A) = ((u : A) * (↑(u⁻¹) : A)) * K * (u : A) := by
        have huv : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
        rw [huv, one_mul]
      _ = (u : A) * ((↑(u⁻¹) : A) * K * (u : A)) := by
        simp only [mul_assoc]
      _ = (u : A) * K := by rw [hconj]
  · intro hcomm
    apply sub_eq_zero.mpr
    calc
      (↑(u⁻¹) : A) * K * (u : A) =
          (↑(u⁻¹) : A) * (K * (u : A)) := by
        simp only [mul_assoc]
      _ = (↑(u⁻¹) : A) * ((u : A) * K) := by
        rw [hcomm.eq]
      _ = K := by
        have hui : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
        rw [← mul_assoc, hui, one_mul]

end InfoGeometry.Modular.Noncommutative

end noncomputable section
