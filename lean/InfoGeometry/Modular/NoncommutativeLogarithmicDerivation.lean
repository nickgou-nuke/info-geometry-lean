import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Modular.Noncommutative

variable {A : Type*} [Ring A]

/-!
=============================================================================
PART 1: Inner Derivations on Arbitrary Noncommutative Rings
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

/-- 🏆 THEOREM 1: The Noncommutative Leibniz Rule for Modular Commutators:
    ad_K(X * Y) = (ad_K X) * Y + X * (ad_K Y) -/
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

/-- THEOREM 2: Annihilation of the Identity: ad_K(1) = 0 -/
@[simp]
theorem adK_one (K : A) : adK K 1 = 0 := by
  simp [adK_apply]

/-- 🏆 THEOREM 3: Inner Lie Bracket Homomorphism:
    [ad_{K₁}, ad_{K₂}](X) = ad_{[K₁, K₂]}(X) -/
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
PART 2: Noncommutative Logarithmic Derivations (Maurer-Cartan Forms)
=============================================================================
-/

/-- A `ℤ`-linear Leibniz derivation on a possibly noncommutative ring A. -/
def IsNCDerivation (D : A →ₗ[ℤ] A) : Prop :=
  ∀ x y, D (x * y) = D x * y + x * D y

/-- The Left Noncommutative Logarithmic Derivative of a Unit:
    dlog_L(D, u) = u⁻¹ * D(u) -/
def dlogL (D : A →ₗ[ℤ] A) (u : Aˣ) : A :=
  (↑(u⁻¹) : A) * D (u : A)

/-- The Right Noncommutative Logarithmic Derivative of a Unit:
    dlog_R(D, u) = D(u) * u⁻¹ -/
def dlogR (D : A →ₗ[ℤ] A) (u : Aˣ) : A :=
  D (u : A) * (↑(u⁻¹) : A)

/-- The right logarithmic derivative is the unit-conjugate of the left one.
    This is the noncommutative Maurer--Cartan conversion law. -/
theorem dlogR_eq_conjugate_dlogL (D : A →ₗ[ℤ] A) (u : Aˣ) :
    dlogR D u =
      (u : A) * dlogL D u * (↑(u⁻¹) : A) := by
  unfold dlogR dlogL
  have hu : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
  calc
    D (u : A) * (↑(u⁻¹) : A) =
        ((u : A) * (↑(u⁻¹) : A)) * D (u : A) *
          (↑(u⁻¹) : A) := by
      rw [hu, one_mul]
    _ = (u : A) * ((↑(u⁻¹) : A) * D (u : A)) *
          (↑(u⁻¹) : A) := by
      simp only [mul_assoc]

/-- Derivation annihilates 1 in any ring -/
theorem derivation_map_one (D : A →ₗ[ℤ] A) (hD : IsNCDerivation D) : D 1 = 0 := by
  have h := hD 1 1
  have h' : D 1 = D 1 + D 1 := by
    simpa only [mul_one, one_mul] using h
  have h'' : D 1 + 0 = D 1 + D 1 := by simpa using h'
  exact (add_left_cancel h'').symm

@[simp]
theorem dlogL_one (D : A →ₗ[ℤ] A) (hD : IsNCDerivation D) :
    dlogL D 1 = 0 := by
  dsimp [dlogL]
  rw [derivation_map_one D hD, mul_zero]

@[simp]
theorem dlogR_one (D : A →ₗ[ℤ] A) (hD : IsNCDerivation D) :
    dlogR D 1 = 0 := by
  dsimp [dlogR]
  rw [derivation_map_one D hD, zero_mul]

/-- The right noncommutative logarithmic product rule. -/
theorem dlogR_mul (D : A →ₗ[ℤ] A) (hD : IsNCDerivation D) (u v : Aˣ) :
    dlogR D (u * v) =
      dlogR D u + (u : A) * dlogR D v * (↑(u⁻¹) : A) := by
  unfold dlogR
  rw [mul_inv_rev]
  change D ((u : A) * (v : A)) *
      ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) = _
  rw [hD _ _, add_mul]
  have hv : (v : A) * (↑(v⁻¹) : A) = 1 := v.val_inv
  calc
    D (u : A) * (v : A) * ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) +
        (u : A) * D (v : A) * ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) =
      (D (u : A) * ((v : A) * (↑(v⁻¹) : A))) *
          (↑(u⁻¹) : A) +
        (u : A) * (D (v : A) * (↑(v⁻¹) : A)) *
          (↑(u⁻¹) : A) := by
      simp only [mul_assoc]
    _ = D (u : A) * (↑(u⁻¹) : A) +
        (u : A) * (D (v : A) * (↑(v⁻¹) : A)) *
          (↑(u⁻¹) : A) := by
      rw [hv, mul_one]

/-- The right noncommutative logarithmic inversion law. -/
theorem dlogR_inv (D : A →ₗ[ℤ] A) (hD : IsNCDerivation D) (u : Aˣ) :
    dlogR D (u⁻¹) =
      -((↑(u⁻¹) : A) * dlogR D u * (u : A)) := by
  rw [dlogR_eq_conjugate_dlogL, dlogL_inv,
    dlogR_eq_conjugate_dlogL]
  simp only [Units.val_inv_eq_inv_val, mul_assoc]
  rw [u.inv_val, one_mul]

/-- 🏆 THEOREM 4: Noncommutative Logarithmic Product Rule (Maurer–Cartan):
    dlog_L(u * v) = v⁻¹ * dlog_L(u) * v + dlog_L(v)
    This is the exact non-abelian chain rule without assuming commutativity! -/
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

/-- 🏆 THEOREM 5: Noncommutative Logarithmic Inversion Law:
    dlog_L(u⁻¹) = - (u * dlog_L(u) * u⁻¹) -/
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

/-!
=============================================================================
PART 3: Inner Modular Logarithmic Derivatives as Discrete Gauge Shifts
=============================================================================
-/

/-- 🏆 THEOREM 6: Exact Inner Modular Logarithmic Derivative:
    dlog_L(ad_K, u) = u⁻¹ * K * u - K = Ad_{u⁻¹}(K) - K
    This proves that for inner modular flows, the logarithmic derivative is
    identically the non-abelian gauge transformation shift of the Hamiltonian K! -/
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

end InfoGeometry.Modular.Noncommutative

end noncomputable section
