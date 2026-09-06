import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Algebraic and Analytic Foundations of the Logarithmic Radon–Nikodym Derivation (`explogRNder`)

This module formalizes the rigorous mathematical theory of logarithmic derivations,
lifted to general **non-commutative operator rings and algebras** `[Ring A]`, as well as
their commutative density and smooth differentiable specializations.

## Non-Commutative Operator Algebra Layer (`[Ring A]`):
1. **Infinitesimal Derivations**: Additive maps $D : A \to A$ satisfying Leibniz product rule:
   $$D(x y) = D(x) y + x D(y)$$
2. **Multiplicative Unit Annihilation**: $D(1) = 0$ in any ring.
3. **Non-Commutative Inverse Rule**: $D(u^{-1}) = - u^{-1} D(u) u^{-1}$.
4. **Left & Right Logarithmic Derivations (Maurer–Cartan Forms / Score Operators)**:
   $$\operatorname{dlogL}_D(u) := u^{-1} D(u), \qquad \operatorname{dlogR}_D(u) := D(u) u^{-1}$$
5. **Non-Commutative Cocycle Transformation Law**:
   $$\operatorname{dlogL}_D(u \cdot v) = v^{-1} \operatorname{dlogL}_D(u) v + \operatorname{dlogL}_D(v)$$
   $$\operatorname{dlogR}_D(u \cdot v) = \operatorname{dlogR}_D(u) + u \operatorname{dlogR}_D(v) u^{-1}$$
6. **Inversion Duality**:
   $$\operatorname{dlogL}_D(u^{-1}) = - \operatorname{dlogR}_D(u), \qquad \operatorname{dlogR}_D(u^{-1}) = - \operatorname{dlogL}_D(u)$$
7. **Inner Derivations (Heisenberg Hamiltonian flows)**:
   Every commutator map $\operatorname{ad}_H(X) = [H, X] = H X - X H$ is a derivation, with:
   $$\operatorname{dlogL}_{\operatorname{ad}_H}(u) = u^{-1} H u - H = \operatorname{Ad}_{u^{-1}}(H) - H$$
   $$\operatorname{dlogR}_{\operatorname{ad}_H}(u) = H - u H u^{-1} = H - \operatorname{Ad}_u(H)$$

## Commutative & Analytic Specializations:
- On `[CommRing A]`, Left and Right logarithmic derivations coincide, making $\operatorname{dlog}_D$
  a strict group homomorphism from $(A^\times, \cdot)$ to $(A, +)$.
- Infinitesimal differentiable calculus on $\mathbb{R}$ links smooth density flows $\rho(t)$,
  exponential potential generators $K(t) = \log \rho(t)$, and the Fisher–Rao metric energy element.

All proofs are 100% native Mathlib with zero `sorry`s, zero placeholders, and zero custom axioms.
-/

namespace InfoGeometry.Probability.ExpLogRNDerivation

open BigOperators

/-!
=============================================================================
PART 1: Non-Commutative Operator Ring Layer (`[Ring A]`)
=============================================================================
-/

section NonCommutativeRing

variable {A : Type*} [Ring A]

/-- A linear/additive map on a ring is a derivation if it satisfies the Leibniz product rule. -/
def IsDerivation (D : A → A) : Prop :=
  (∀ x y, D (x + y) = D x + D y) ∧ (∀ x y, D (x * y) = D x * y + x * D y)

/-- Derivations preserve the additive zero: D(0) = 0. -/
theorem derivation_zero (D : A → A) (hD : IsDerivation D) : D 0 = 0 := by
  have h : D 0 + D 0 = D 0 + 0 := by
    calc
      D 0 + D 0 = D (0 + 0) := (hD.1 0 0).symm
      _ = D 0 := by rw [add_zero]
      _ = D 0 + 0 := by rw [add_zero]
  exact add_left_cancel h

/-- THEOREM: Every derivation strictly annihilates the multiplicative unit 1: D(1) = 0. -/
theorem derivation_one (D : A → A) (hD : IsDerivation D) : D 1 = 0 := by
  have hmul : D 1 = D 1 + D 1 := by
    calc
      D 1 = D (1 * 1) := by rw [mul_one]
      _ = D 1 * 1 + 1 * D 1 := hD.2 1 1
      _ = D 1 + D 1 := by rw [mul_one, one_mul]
  have h : D 1 + D 1 = D 1 + 0 := by rw [← hmul, add_zero]
  exact add_left_cancel h

/-- Derivations preserve negation: D(-x) = - D(x). -/
theorem derivation_neg (D : A → A) (hD : IsDerivation D) (x : A) : D (-x) = - D x := by
  have h : D x + D (-x) = 0 := by
    calc
      D x + D (-x) = D (x + -x) := (hD.1 x (-x)).symm
      _ = D 0 := by rw [add_neg_cancel]
      _ = 0 := derivation_zero D hD
  exact eq_neg_of_add_eq_zero_right h

/-- Derivations preserve subtraction: D(x - y) = D(x) - D(y). -/
theorem derivation_sub (D : A → A) (hD : IsDerivation D) (x y : A) : D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, hD.1, derivation_neg D hD, ← sub_eq_add_neg]

/-- Derivations preserve natural number scalar multiplication: D(n • x) = n • D(x). -/
theorem derivation_nsmul (D : A → A) (hD : IsDerivation D) (n : ℕ) (x : A) :
    D (n • x) = n • D x := by
  induction n with
  | zero => simp only [zero_smul, derivation_zero D hD]
  | succ n ih => rw [succ_nsmul, succ_nsmul, hD.1, ih]

/-- Derivations preserve integer scalar multiplication: D(z • x) = z • D(x). -/
theorem derivation_zsmul (D : A → A) (hD : IsDerivation D) (z : ℤ) (x : A) :
    D (z • x) = z • D x := by
  cases z with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, natCast_zsmul, natCast_zsmul, derivation_nsmul D hD]
  | negSucc n =>
      simp only [negSucc_zsmul, derivation_neg D hD, derivation_nsmul D hD]

/-- Derivation of a 3-element product in non-commutative rings. -/
theorem derivation_mul3 (D : A → A) (hD : IsDerivation D) (x y z : A) :
    D (x * y * z) = D x * y * z + x * D y * z + x * y * D z := by
  rw [hD.2 (x * y) z, hD.2 x y, add_mul, mul_assoc, add_assoc]

/--
  THEOREM: The Derivation of an Invertible Operator Element:
  D(u⁻¹) = - u⁻¹ · D(u) · u⁻¹
-/
theorem derivation_inv (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    D (↑u⁻¹ : A) = - (↑u⁻¹ : A) * D (u : A) * (↑u⁻¹ : A) := by
  have h_prod : D ((u : A) * (↑u⁻¹ : A)) = 0 := by
    rw [Units.mul_inv, derivation_one D hD]
  have h_leib : D (u : A) * (↑u⁻¹ : A) + (u : A) * D (↑u⁻¹ : A) = 0 := by
    rw [← hD.2 (u : A) (↑u⁻¹ : A), h_prod]
  have h_shift : (u : A) * D (↑u⁻¹ : A) = - (D (u : A) * (↑u⁻¹ : A)) :=
    eq_neg_of_add_eq_zero_right h_leib
  have h_mult : (↑u⁻¹ : A) * ((u : A) * D (↑u⁻¹ : A)) = (↑u⁻¹ : A) * (- (D (u : A) * (↑u⁻¹ : A))) := by
    rw [h_shift]
  have h_assoc : (↑u⁻¹ : A) * ((u : A) * D (↑u⁻¹ : A)) = D (↑u⁻¹ : A) := by
    calc
      (↑u⁻¹ : A) * ((u : A) * D (↑u⁻¹ : A)) = ((↑u⁻¹ : A) * (u : A)) * D (↑u⁻¹ : A) := by rw [mul_assoc]
      _ = 1 * D (↑u⁻¹ : A) := by rw [Units.inv_mul u]
      _ = D (↑u⁻¹ : A) := by rw [one_mul]
  rw [h_assoc] at h_mult
  rw [h_mult, mul_neg, mul_assoc, neg_mul]

/--
  The Left Logarithmic Derivation (Left Maurer–Cartan Score Generator):
  dlogL_D(u) = u⁻¹ · D(u)
-/
def dlogL (D : A → A) (u : Aˣ) : A :=
  (↑u⁻¹ : A) * D (u : A)

/--
  The Right Logarithmic Derivation (Right Maurer–Cartan Score Generator):
  dlogR_D(u) = D(u) · u⁻¹
-/
def dlogR (D : A → A) (u : Aˣ) : A :=
  D (u : A) * (↑u⁻¹ : A)

/-- Canonical definition of dlog on general rings as Left logarithmic derivative. -/
def dlog (D : A → A) (u : Aˣ) : A :=
  dlogL D u

@[simp]
theorem dlog_eq_dlogL (D : A → A) (u : Aˣ) :
    dlog D u = dlogL D u := rfl

/-- Left logarithmic derivation of identity is zero. -/
@[simp]
theorem dlogL_one (D : A → A) (hD : IsDerivation D) :
    dlogL D 1 = 0 := by
  dsimp [dlogL]
  rw [derivation_one D hD, mul_zero]

/-- Right logarithmic derivation of identity is zero. -/
@[simp]
theorem dlogR_one (D : A → A) (hD : IsDerivation D) :
    dlogR D 1 = 0 := by
  dsimp [dlogR]
  rw [derivation_one D hD, zero_mul]

@[simp]
theorem dlog_one (D : A → A) (hD : IsDerivation D) :
    dlog D 1 = 0 :=
  dlogL_one D hD

/--
  THEOREM: Non-Commutative Inversion Duality (Left to Right):
  dlogL_D(u⁻¹) = - dlogR_D(u)
-/
theorem dlogL_inv (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    dlogL D (u⁻¹) = - dlogR D u := by
  dsimp [dlogL, dlogR]
  rw [inv_inv, derivation_inv D hD u, neg_mul, neg_mul, mul_neg,
      ← mul_assoc (u : A) (↑u⁻¹ * D (u : A)) (↑u⁻¹ : A),
      ← mul_assoc (u : A) (↑u⁻¹ : A) (D (u : A)),
      Units.mul_inv, one_mul]

/--
  THEOREM: Non-Commutative Inversion Duality (Right to Left):
  dlogR_D(u⁻¹) = - dlogL_D(u)
-/
theorem dlogR_inv (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    dlogR D (u⁻¹) = - dlogL D u := by
  dsimp [dlogL, dlogR]
  rw [inv_inv, derivation_inv D hD u, neg_mul, neg_mul, neg_mul,
      mul_assoc (↑u⁻¹ * D (u : A)) (↑u⁻¹ : A) (u : A),
      Units.inv_mul, mul_one]

/--
  THEOREM (The Non-Commutative Left Cocycle Transformation Law):
  dlogL_D(u · v) = v⁻¹ · dlogL_D(u) · v + dlogL_D(v)
-/
theorem dlogL_mul (D : A → A) (hD : IsDerivation D) (u v : Aˣ) :
    dlogL D (u * v) = (↑v⁻¹ : A) * dlogL D u * (v : A) + dlogL D v := by
  dsimp [dlogL]
  have h_inv : (↑(u * v)⁻¹ : A) = (↑v⁻¹ : A) * (↑u⁻¹ : A) := by
    rw [mul_inv_rev, Units.val_mul]
  have h_leib : D ((u : A) * (v : A)) = D (u : A) * (v : A) + (u : A) * D (v : A) :=
    hD.2 (u : A) (v : A)
  rw [h_inv, h_leib, mul_add]
  have h_left : (↑v⁻¹ : A) * (↑u⁻¹ : A) * (D (u : A) * (v : A)) =
      (↑v⁻¹ : A) * ((↑u⁻¹ : A) * D (u : A)) * (v : A) := by
    calc
      (↑v⁻¹ : A) * (↑u⁻¹ : A) * (D (u : A) * (v : A))
        = (↑v⁻¹ : A) * (↑u⁻¹ : A) * D (u : A) * (v : A) := by
          rw [mul_assoc ((↑v⁻¹ : A) * (↑u⁻¹ : A)) (D (u : A)) (v : A)]
      _ = (↑v⁻¹ : A) * ((↑u⁻¹ : A) * D (u : A)) * (v : A) := by
          rw [mul_assoc (↑v⁻¹ : A) (↑u⁻¹ : A) (D (u : A))]
  have h_right : (↑v⁻¹ : A) * (↑u⁻¹ : A) * ((u : A) * D (v : A)) = (↑v⁻¹ : A) * D (v : A) := by
    calc
      (↑v⁻¹ : A) * (↑u⁻¹ : A) * ((u : A) * D (v : A))
        = (↑v⁻¹ : A) * ((↑u⁻¹ : A) * ((u : A) * D (v : A))) := by rw [mul_assoc (↑v⁻¹ : A) (↑u⁻¹ : A)]
      _ = (↑v⁻¹ : A) * (((↑u⁻¹ : A) * (u : A)) * D (v : A)) := by rw [← mul_assoc (↑u⁻¹ : A) (u : A)]
      _ = (↑v⁻¹ : A) * (1 * D (v : A)) := by rw [Units.inv_mul u]
      _ = (↑v⁻¹ : A) * D (v : A) := by rw [one_mul]
  rw [h_left, h_right]

/--
  THEOREM (The Non-Commutative Right Cocycle Transformation Law):
  dlogR_D(u · v) = dlogR_D(u) + u · dlogR_D(v) · u⁻¹
-/
theorem dlogR_mul (D : A → A) (hD : IsDerivation D) (u v : Aˣ) :
    dlogR D (u * v) = dlogR D u + (u : A) * dlogR D v * (↑u⁻¹ : A) := by
  dsimp [dlogR]
  have h_inv : (↑(u * v)⁻¹ : A) = (↑v⁻¹ : A) * (↑u⁻¹ : A) := by
    rw [mul_inv_rev, Units.val_mul]
  have h_leib : D ((u : A) * (v : A)) = D (u : A) * (v : A) + (u : A) * D (v : A) :=
    hD.2 (u : A) (v : A)
  rw [h_inv, h_leib, add_mul]
  have h_left : D (u : A) * (v : A) * ((↑v⁻¹ : A) * (↑u⁻¹ : A)) = D (u : A) * (↑u⁻¹ : A) := by
    calc
      D (u : A) * (v : A) * ((↑v⁻¹ : A) * (↑u⁻¹ : A))
        = D (u : A) * ((v : A) * (↑v⁻¹ : A)) * (↑u⁻¹ : A) := by
          rw [mul_assoc (D (u : A)) (v : A), ← mul_assoc (v : A) (↑v⁻¹ : A), ← mul_assoc (D (u : A))]
      _ = D (u : A) * 1 * (↑u⁻¹ : A) := by rw [Units.mul_inv v]
      _ = D (u : A) * (↑u⁻¹ : A) := by rw [mul_one]
  have h_right : (u : A) * D (v : A) * ((↑v⁻¹ : A) * (↑u⁻¹ : A)) =
      (u : A) * (D (v : A) * (↑v⁻¹ : A)) * (↑u⁻¹ : A) := by
    calc
      (u : A) * D (v : A) * ((↑v⁻¹ : A) * (↑u⁻¹ : A))
        = (u : A) * (D (v : A) * ((↑v⁻¹ : A) * (↑u⁻¹ : A))) := by rw [mul_assoc (u : A) (D (v : A))]
      _ = (u : A) * ((D (v : A) * (↑v⁻¹ : A)) * (↑u⁻¹ : A)) := by rw [mul_assoc (D (v : A)) (↑v⁻¹ : A)]
      _ = (u : A) * (D (v : A) * (↑v⁻¹ : A)) * (↑u⁻¹ : A) := by rw [← mul_assoc (u : A)]
  rw [h_left, h_right]

/--
  THEOREM (Non-Commutative 3-Cocycle Radon–Nikodym Chain Rule):
  dlogL_D(u · v · w) = (v · w)⁻¹ · dlogL_D(u) · (v · w) + w⁻¹ · dlogL_D(v) · w + dlogL_D(w)
-/
theorem dlogL_mul3 (D : A → A) (hD : IsDerivation D) (u v w : Aˣ) :
    dlogL D (u * v * w) =
      (↑(v * w)⁻¹ : A) * dlogL D u * (↑(v * w) : A) +
      (↑w⁻¹ : A) * dlogL D v * (w : A) +
      dlogL D w := by
  rw [dlogL_mul D hD (u * v) w, dlogL_mul D hD u v]
  have h1 : (↑w⁻¹ : A) * ((↑v⁻¹ : A) * dlogL D u * (v : A) + dlogL D v) * (w : A) =
      (↑(v * w)⁻¹ : A) * dlogL D u * (↑(v * w) : A) + (↑w⁻¹ : A) * dlogL D v * (w : A) := by
    rw [mul_add, add_mul]
    have h_inv : (↑(v * w)⁻¹ : A) = (↑w⁻¹ : A) * (↑v⁻¹ : A) := by
      rw [mul_inv_rev, Units.val_mul]
    have h_val : (↑(v * w) : A) = (v : A) * (w : A) := by
      rw [Units.val_mul]
    rw [h_inv, h_val]
    congr 1
    simp only [mul_assoc]
  rw [h1, add_assoc]

/-- When v commutes with dlogL_D(u), the non-commutative conjugation vanishes. -/
theorem dlogL_mul_of_comm (D : A → A) (hD : IsDerivation D) (u v : Aˣ)
    (hcomm : (v : A) * dlogL D u = dlogL D u * (v : A)) :
    dlogL D (u * v) = dlogL D u + dlogL D v := by
  rw [dlogL_mul D hD u v]
  have h_adj : (↑v⁻¹ : A) * dlogL D u * (v : A) = dlogL D u := by
    calc
      (↑v⁻¹ : A) * dlogL D u * (v : A)
        = (↑v⁻¹ : A) * (dlogL D u * (v : A)) := by rw [mul_assoc]
      _ = (↑v⁻¹ : A) * ((v : A) * dlogL D u) := by rw [← hcomm]
      _ = ((↑v⁻¹ : A) * (v : A)) * dlogL D u := by rw [← mul_assoc]
      _ = 1 * dlogL D u := by rw [Units.inv_mul v]
      _ = dlogL D u := by rw [one_mul]
  rw [h_adj]

/--
  Inner derivation generated by an operator element H:
  ad_H(X) = [H, X] = H · X - X · H
-/
def ad (H : A) : A → A := fun X => H * X - X * H

/-- THEOREM: Every inner derivation ad_H is a genuine derivation on any non-commutative ring A. -/
theorem isDerivation_ad (H : A) : IsDerivation (ad H) := by
  constructor
  · intro x y
    dsimp [ad]
    simp only [mul_add, add_mul]
    abel
  · intro x y
    dsimp [ad]
    simp only [sub_mul, mul_sub, mul_assoc]
    abel

/--
  THEOREM: Left Logarithmic Derivation under Inner Derivation is the Hamiltonian Shift:
  dlogL_{ad_H}(u) = u⁻¹ · H · u - H
-/
theorem dlogL_ad (H : A) (u : Aˣ) :
    dlogL (ad H) u = (↑u⁻¹ : A) * H * (u : A) - H := by
  dsimp [dlogL, ad]
  rw [mul_sub, mul_assoc (↑u⁻¹ : A) H (u : A)]
  have h1 : (↑u⁻¹ : A) * ((u : A) * H) = H := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [h1]

/--
  THEOREM: Right Logarithmic Derivation under Inner Derivation:
  dlogR_{ad_H}(u) = H - u · H · u⁻¹
-/
theorem dlogR_ad (H : A) (u : Aˣ) :
    dlogR (ad H) u = H - (u : A) * H * (↑u⁻¹ : A) := by
  dsimp [dlogR, ad]
  rw [sub_mul, mul_assoc (u : A) H (↑u⁻¹ : A)]
  have h1 : H * (u : A) * (↑u⁻¹ : A) = H := by
    rw [mul_assoc, Units.mul_inv, mul_one]
  rw [h1]

end NonCommutativeRing

/-!
=============================================================================
PART 2: Commutative Density Algebra Specialization (`[CommRing A]`)
=============================================================================
-/

section CommutativeRing

variable {A : Type*} [CommRing A]

/-- On commutative rings, Left and Right logarithmic derivations coincide identically. -/
theorem dlogL_eq_dlogR (D : A → A) (u : Aˣ) :
    dlogL D u = dlogR D u := by
  dsimp [dlogL, dlogR]
  exact mul_comm (↑u⁻¹ : A) (D (u : A))

/--
  THEOREM (Commutative Inverse Derivative Rule):
  On a commutative density ring the non-commutative rule collapses to the squared form:
  D(u⁻¹) = - u⁻² · D(u).
-/
theorem derivation_inv_comm (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    D (↑u⁻¹ : A) = -(↑u⁻¹ : A) * (↑u⁻¹ : A) * D (u : A) := by
  rw [derivation_inv D hD u]
  ring

/--
  THEOREM (The Fundamental Logarithmic Homomorphism on Commutative Density Rings):
  dlog_D(u · v) = dlog_D(u) + dlog_D(v)
-/
theorem dlog_mul (D : A → A) (hD : IsDerivation D) (u v : Aˣ) :
    dlog D (u * v) = dlog D u + dlog D v := by
  have hcomm : (v : A) * dlogL D u = dlogL D u * (v : A) := mul_comm (v : A) (dlogL D u)
  exact dlogL_mul_of_comm D hD u v hcomm

/-- Logarithmic derivation of inverse in commutative ring: dlog_D(u⁻¹) = - dlog_D(u). -/
theorem dlog_inv (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    dlog D (u⁻¹) = - dlog D u := by
  have h := dlog_mul D hD u (u⁻¹)
  rw [mul_inv_cancel, dlog_one D hD] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Logarithmic derivation of division: dlog_D(u / v) = dlog_D(u) - dlog_D(v). -/
theorem dlog_div (D : A → A) (hD : IsDerivation D) (u v : Aˣ) :
    dlog D (u / v) = dlog D u - dlog D v := by
  rw [div_eq_mul_inv, dlog_mul D hD, dlog_inv D hD, sub_eq_add_neg]

/-- Natural number powers scale linearly: dlog_D(u^n) = n • dlog_D(u). -/
theorem dlog_pow
    (D : A → A) (hD : IsDerivation D) (u : Aˣ) (n : ℕ) :
    dlog D (u ^ n) = n • dlog D u := by
  induction n with
  | zero =>
      simp only [pow_zero, zero_smul]
      exact dlog_one D hD
  | succ n ih =>
      rw [pow_succ, dlog_mul D hD, ih]
      simp only [succ_nsmul, add_comm]

/-- Integer powers scale linearly: dlog_D(u^z) = z • dlog_D(u). -/
theorem dlog_zpow (D : A → A) (hD : IsDerivation D) (u : Aˣ) (z : ℤ) :
    dlog D (u ^ z) = z • dlog D u := by
  cases z with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, natCast_zsmul, dlog_pow D hD]
  | negSucc n =>
      simp only [zpow_negSucc, negSucc_zsmul]
      rw [dlog_inv D hD, dlog_pow D hD]

/-- Finite products transform to sums: dlog_D(∏ u_i) = ∑ dlog_D(u_i). -/
theorem dlog_prod {ι : Type*} (D : A → A) (hD : IsDerivation D)
    (s : Finset ι) (f : ι → Aˣ) :
    dlog D (∏ i ∈ s, f i) = ∑ i ∈ s, dlog D (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, dlog_one D hD]
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.sum_cons, dlog_mul D hD, ih]

/--
  THEOREM (The Radon–Nikodym 4-Cocycle Chain Rule):
  dlog_D(ρ₁₂ · ρ₂₃ · ρ₃₄) = dlog_D(ρ₁₂) + dlog_D(ρ₂₃) + dlog_D(ρ₃₄).
-/
theorem radon_nikodym_4cocycle_dlog
    (D : A → A) (hD : IsDerivation D)
    (rho_12 rho_23 rho_34 : Aˣ) :
    dlog D (rho_12 * rho_23 * rho_34) = dlog D rho_12 + dlog D rho_23 + dlog D rho_34 := by
  rw [dlog_mul D hD, dlog_mul D hD, add_assoc]

/-! Bundled form of the multiplicative-to-additive logarithmic derivative. -/
def dlogMonoidHom (D : A → A) (hD : IsDerivation D) :
    Aˣ →* Multiplicative A where
  toFun u := Multiplicative.ofAdd (dlog D u)
  map_one' := by
    apply Multiplicative.ext
    simp only [dlog, dlogL_one D hD, toAdd_ofAdd, toAdd_one]
  map_mul' u v := by
    apply Multiplicative.ext
    exact dlog_mul D hD u v

@[simp]
theorem dlogMonoidHom_apply
    (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    dlogMonoidHom D hD u = Multiplicative.ofAdd (dlog D u) := rfl

theorem dlogMonoidHom_pow
    (D : A → A) (hD : IsDerivation D) (u : Aˣ) (n : ℕ) :
    dlogMonoidHom D hD (u ^ n) =
      Multiplicative.ofAdd (n • dlog D u) := by
  rw [map_pow, dlogMonoidHom_apply, ofAdd_nsmul]

theorem dlogMonoidHom_inv
    (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    dlogMonoidHom D hD (u⁻¹) =
      (dlogMonoidHom D hD u)⁻¹ := by
  exact map_inv (dlogMonoidHom D hD) u

theorem dlogMonoidHom_prod {ι : Type*}
    (D : A → A) (hD : IsDerivation D)
    (s : Finset ι) (f : ι → Aˣ) :
    dlogMonoidHom D hD (∏ i ∈ s, f i) =
      Multiplicative.ofAdd (∑ i ∈ s, dlog D (f i)) := by
  rw [dlogMonoidHom_apply, dlog_prod D hD]

end CommutativeRing

/-!
=============================================================================
PART 3: Module-Algebra Derivation Compatibility (`Derivation R A A`)
=============================================================================
-/

section ModuleAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Every Mathlib bundled derivation `D : Derivation R A A` satisfies `IsDerivation D`. -/
theorem derivation_isDerivation (D : Derivation R A A) : IsDerivation (fun x => D x) := by
  refine ⟨fun x y => map_add D x y, fun x y => ?_⟩
  dsimp
  have h := D.leibniz x y
  simp only [smul_eq_mul] at h
  rw [h]
  ring

/-- The logarithmic derivation of a unit with respect to a bundled Mathlib derivation. -/
def dlogDeriv (D : Derivation R A A) (u : Aˣ) : A :=
  dlog (fun x => D x) u

@[simp]
theorem dlogDeriv_eq (D : Derivation R A A) (u : Aˣ) :
    dlogDeriv D u = (↑u⁻¹ : A) * D (u : A) := rfl

theorem dlogDeriv_mul (D : Derivation R A A) (u v : Aˣ) :
    dlogDeriv D (u * v) = dlogDeriv D u + dlogDeriv D v :=
  dlog_mul (fun x => D x) (derivation_isDerivation D) u v

theorem dlogDeriv_inv (D : Derivation R A A) (u : Aˣ) :
    dlogDeriv D (u⁻¹) = - dlogDeriv D u :=
  dlog_inv (fun x => D x) (derivation_isDerivation D) u

@[simp]
theorem dlogDeriv_one (D : Derivation R A A) :
    dlogDeriv D 1 = 0 :=
  dlog_one (fun x => D x) (derivation_isDerivation D)

theorem dlogDeriv_pow (D : Derivation R A A) (u : Aˣ) (n : ℕ) :
    dlogDeriv D (u ^ n) = n • dlogDeriv D u :=
  dlog_pow (fun x => D x) (derivation_isDerivation D) u n

end ModuleAlgebra

/-!
=============================================================================
PART 4: Real Analytic Calculus of the Radon–Nikodym Density
=============================================================================
-/

section Analytic

/--
  THEOREM: The Infinitesimal Logarithmic Derivative of a Positive Density Flow:
  d/dt [log ρ(t)] = ρ'(t) / ρ(t)
-/
theorem hasDerivAt_log_radon_nikodym
    (rho : ℝ → ℝ) (rho' : ℝ) (t : ℝ)
    (h_diff : HasDerivAt rho rho' t)
    (h_pos : 0 < rho t) :
    HasDerivAt (fun s => Real.log (rho s)) (rho' / rho t) t := by
  have h_ne : rho t ≠ 0 := ne_of_gt h_pos
  exact HasDerivAt.log h_diff h_ne

/-- Derivative value equality for log density flow. -/
theorem deriv_log_radon_nikodym
    (rho : ℝ → ℝ) (rho' : ℝ) (t : ℝ)
    (h_diff : HasDerivAt rho rho' t)
    (h_pos : 0 < rho t) :
    deriv (fun s => Real.log (rho s)) t = rho' / rho t :=
  (hasDerivAt_log_radon_nikodym rho rho' t h_diff h_pos).deriv

/-- Product rule for logarithmic density curves: d/dt [log(ρ₁ · ρ₂)] = ρ₁'/ρ₁ + ρ₂'/ρ₂. -/
theorem hasDerivAt_log_density_mul
    (rho1 rho2 : ℝ → ℝ) (rho1' rho2' : ℝ) (t : ℝ)
    (h_diff1 : HasDerivAt rho1 rho1' t)
    (h_diff2 : HasDerivAt rho2 rho2' t)
    (h_pos1 : 0 < rho1 t)
    (h_pos2 : 0 < rho2 t) :
    HasDerivAt (fun s => Real.log (rho1 s * rho2 s)) (rho1' / rho1 t + rho2' / rho2 t) t := by
  have h_mul_diff : HasDerivAt (fun s => rho1 s * rho2 s) (rho1' * rho2 t + rho1 t * rho2') t :=
    h_diff1.mul h_diff2
  have h_mul_pos : 0 < rho1 t * rho2 t := mul_pos h_pos1 h_pos2
  have h_log := HasDerivAt.log h_mul_diff (ne_of_gt h_mul_pos)
  have h_alg : (rho1' * rho2 t + rho1 t * rho2') / (rho1 t * rho2 t) = rho1' / rho1 t + rho2' / rho2 t := by
    have h1 : rho1 t ≠ 0 := ne_of_gt h_pos1
    have h2 : rho2 t ≠ 0 := ne_of_gt h_pos2
    field_simp
  rw [h_alg] at h_log
  exact h_log

/--
  THEOREM: The Exponential Flow Generated by an Additive Potential K(t):
  d/dt [exp(K(t))] = K'(t) • exp(K(t))
-/
theorem hasDerivAt_exp_potential
    (K : ℝ → ℝ) (K' : ℝ) (t : ℝ)
    (h_diff : HasDerivAt K K' t) :
    HasDerivAt (fun s => Real.exp (K s)) (K' * Real.exp (K t)) t := by
  have h := HasDerivAt.exp h_diff
  rw [mul_comm] at h
  exact h

/-- Commuted form of exponential derivative: d/dt [exp(K(t))] = exp(K(t)) • K'(t). -/
theorem hasDerivAt_exp_potential_comm
    (K : ℝ → ℝ) (K' : ℝ) (t : ℝ)
    (h_diff : HasDerivAt K K' t) :
    HasDerivAt (fun s => Real.exp (K s)) (Real.exp (K t) * K') t :=
  HasDerivAt.exp h_diff

theorem hasDerivAt_log_exp_potential
    (K : ℝ → ℝ) (K' : ℝ) (t : ℝ)
    (h_diff : HasDerivAt K K' t) :
    HasDerivAt (fun s => Real.log (Real.exp (K s))) K' t := by
  have h_id : (fun s => Real.log (Real.exp (K s))) = K := by
    ext s
    exact Real.log_exp (K s)
  rw [h_id]
  exact h_diff

/--
  THEOREM: The Fundamental `explogRNder` Inversion Identities:
  1. log(exp(K)) = K
  2. exp(log(ρ)) = ρ  (for ρ > 0)
-/
theorem explog_involutions (K_val : ℝ) (rho_val : ℝ) (h_pos : 0 < rho_val) :
    Real.log (Real.exp K_val) = K_val ∧ Real.exp (Real.log rho_val) = rho_val := by
  exact ⟨Real.log_exp K_val, Real.exp_log h_pos⟩

/--
  THEOREM: Duality between Density Velocity and Potential Velocity:
  If ρ(t) = exp(K(t)), then dlog(ρ(t)) = K'(t).
-/
theorem dlog_density_eq_potential_derivative
    (K : ℝ → ℝ) (K' : ℝ) (t : ℝ) :
    let rho := fun s => Real.exp (K s)
    let rho' := K' * Real.exp (K t)
    rho' / rho t = K' := by
  dsimp
  have h_exp_pos : Real.exp (K t) ≠ 0 := ne_of_gt (Real.exp_pos (K t))
  exact mul_div_cancel_right₀ K' h_exp_pos

/--
  THEOREM: Exponential Flow of the Radon–Nikodym Derivative:
  For an exponential tilting `ρ(t) = ρ₀ * exp(t * v)` with `0 < ρ₀`,
  the logarithmic derivative (score function) is identically the velocity generator `v`:
  `d/dt [log (ρ₀ * exp(t * v))] = v`.
-/
theorem hasDerivAt_log_exp_tilting
    (rho0 v t : ℝ) (h_pos : 0 < rho0) :
    HasDerivAt (fun s => Real.log (rho0 * Real.exp (s * v))) v t := by
  have h_log_split : (fun s => Real.log (rho0 * Real.exp (s * v))) = (fun s => Real.log rho0 + s * v) := by
    ext s
    rw [Real.log_mul (ne_of_gt h_pos) (ne_of_gt (Real.exp_pos (s * v))), Real.log_exp]
  rw [h_log_split]
  have h_const : HasDerivAt (fun _ : ℝ => Real.log rho0) 0 t := hasDerivAt_const t (Real.log rho0)
  have h_lin : HasDerivAt (fun s => s * v) v t := by
    have h_id := (hasDerivAt_id t).mul_const v
    simpa using h_id
  have h_add := h_const.add h_lin
  rw [zero_add] at h_add
  exact h_add

/-- Score derivative for an exponential family at time zero is identically the generator v. -/
theorem deriv_log_exp_tilting_zero
    (rho0 v : ℝ) (h_pos : 0 < rho0) :
    deriv (fun s => Real.log (rho0 * Real.exp (s * v))) 0 = v :=
  (hasDerivAt_log_exp_tilting rho0 v 0 h_pos).deriv

/--
  THEOREM: Score Energy and Fisher Information Metric Element:
  The squared logarithmic derivative matches the Fisher–Rao metric density element:
  `ρ(t) * (d/dt log ρ(t))² = (ρ'(t))² / ρ(t)`.
-/
theorem fisher_score_energy_eq
    (rho_val rho' : ℝ) (h_pos : 0 < rho_val) :
    let score := rho' / rho_val
    rho_val * (score ^ 2) = (rho' ^ 2) / rho_val := by
  dsimp
  have h_ne : rho_val ≠ 0 := ne_of_gt h_pos
  field_simp

end Analytic

end InfoGeometry.Probability.ExpLogRNDerivation
