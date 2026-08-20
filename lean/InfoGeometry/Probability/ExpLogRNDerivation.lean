import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Algebraic and Analytic Foundations of the Logarithmic Radon–Nikodym Derivation (`explogRNder`)

This module formalizes the exact bridge between:
1. Multiplicative Radon–Nikodym densities `ρ = dμ/dν ∈ Aˣ`
2. Additive logarithmic surprisal potentials `K = -log ρ`
3. Infinitesimal derivations `D : A → A` and their logarithmic derivatives `dlog_D(u) = u⁻¹ D(u)`

All proofs are complete in native Mathlib with zero custom axioms.
-/

namespace InfoGeometry.Probability.ExpLogRNDerivation

/-!
=============================================================================
PART 1: Algebraic Logarithmic Derivation on Commutative Density Rings
=============================================================================
-/

variable {A : Type*} [CommRing A]

/-- A linear/additive map is a derivation if it satisfies the Leibniz product rule. -/
def IsDerivation (D : A → A) : Prop :=
  (∀ x y, D (x + y) = D x + D y) ∧ (∀ x y, D (x * y) = D x * y + x * D y)

theorem isDerivation_zero : IsDerivation (0 : A → A) := by
  constructor <;> simp

theorem isDerivation_add {D E : A → A}
    (hD : IsDerivation D) (hE : IsDerivation E) :
    IsDerivation (D + E) := by
  constructor
  · intro x y
    simp only [Pi.add_apply, hD.1 x y, hE.1 x y]
    abel
  · intro x y
    simp only [Pi.add_apply, hD.2 x y, hE.2 x y]
    ring

theorem isDerivation_neg {D : A → A}
    (hD : IsDerivation D) : IsDerivation (-D) := by
  constructor
  · intro x y
    simp only [Pi.neg_apply, hD.1 x y, neg_add]
  · intro x y
    simp only [Pi.neg_apply, hD.2 x y, neg_add, neg_mul]
    ring

/-- Pointwise commutator of two derivation maps. -/
def derivationCommutator (D E : A → A) : A → A :=
  fun x => D (E x) - E (D x)

theorem isDerivation_commutator {D E : A → A}
    (hD : IsDerivation D) (hE : IsDerivation E) :
    IsDerivation (derivationCommutator D E) := by
  constructor
  · intro x y
    dsimp [derivationCommutator]
    rw [hE.1, hD.1, hD.1, hE.1]
    abel
  · intro x y
    dsimp [derivationCommutator]
    rw [hE.2 x y, hD.2 x y, hD.1, hE.1,
      hD.2, hD.2, hE.2, hE.2]
    ring

theorem derivationCommutator_apply (D E : A → A) (x : A) :
    derivationCommutator D E x = D (E x) - E (D x) := rfl

theorem derivationCommutator_self (D : A → A) :
    derivationCommutator D D = 0 := by
  funext x
  simp [derivationCommutator]

theorem derivationCommutator_swap (D E : A → A) :
    derivationCommutator E D = -derivationCommutator D E := by
  funext x
  simp [derivationCommutator, sub_eq_add_neg]

/-- THEOREM: Every derivation strictly annihilates the multiplicative unit 1. -/
theorem derivation_one (D : A → A) (hD : IsDerivation D) : D 1 = 0 := by
  have hmul : D 1 = D 1 + D 1 := by
    calc
      D 1 = D (1 * 1) := by rw [mul_one]
      _ = D 1 * 1 + 1 * D 1 := hD.2 1 1
      _ = D 1 + D 1 := by rw [mul_one, one_mul]
  have h : D 1 + D 1 = D 1 + 0 := by rw [← hmul, add_zero]
  exact add_left_cancel h

theorem derivation_map_zero (D : A → A) (hD : IsDerivation D) : D 0 = 0 := by
  have h := hD.1 0 0
  have h' : D 0 + D 0 = D 0 + 0 := by simpa using h.symm
  exact add_left_cancel h'

theorem derivationCommutator_one
    (D E : A → A)
    (hD : IsDerivation D) (hE : IsDerivation E) :
    derivationCommutator D E 1 = 0 := by
  dsimp [derivationCommutator]
  rw [derivation_one E hE, derivation_map_zero D hD,
    derivation_one D hD, derivation_map_zero E hE, sub_self]

theorem derivation_map_neg (D : A → A) (hD : IsDerivation D) (x : A) :
    D (-x) = -D x := by
  have h := hD.1 x (-x)
  rw [add_neg_cancel, derivation_map_zero D hD] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem derivation_map_sub (D : A → A) (hD : IsDerivation D) (x y : A) :
    D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, hD.1, derivation_map_neg D hD]
  rw [sub_eq_add_neg]

theorem derivationCommutator_jacobi
    (D E F : A → A)
    (hD : IsDerivation D) (hE : IsDerivation E) (hF : IsDerivation F)
    (x : A) :
    derivationCommutator D (derivationCommutator E F) x +
        derivationCommutator E (derivationCommutator F D) x +
        derivationCommutator F (derivationCommutator D E) x = 0 := by
  dsimp [derivationCommutator]
  rw [derivation_map_sub D hD, derivation_map_sub E hE,
    derivation_map_sub F hF]
  ring

theorem derivationCommutator_add_left (D E F : A → A)
    (hF : IsDerivation F) :
    derivationCommutator (D + E) F =
      derivationCommutator D F + derivationCommutator E F := by
  funext x
  simp only [Pi.add_apply, derivationCommutator]
  rw [hF.1]
  ring

theorem derivationCommutator_add_right (D E F : A → A)
    (hD : IsDerivation D) :
    derivationCommutator D (E + F) =
      derivationCommutator D E + derivationCommutator D F := by
  funext x
  simp only [Pi.add_apply, derivationCommutator]
  rw [hD.1]
  ring

/-- 
  The Logarithmic Derivation (Score Function Generator):
  dlog_D(u) = u⁻¹ • D(u)
-/
def dlog (D : A → A) (u : Aˣ) : A :=
  (u⁻¹ : Aˣ).val * D (u : A)

/-- 
  THEOREM: The Derivation of an Invertible Density Element:
  D(u⁻¹) = - u⁻² D(u)
-/
theorem derivation_inv (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    D (u⁻¹ : Aˣ).val = - (u⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val * D (u : A) := by
  have h_one : (u : A) * (u⁻¹ : Aˣ).val = 1 := Units.mul_inv u
  have h_prod : D ((u : A) * (u⁻¹ : Aˣ).val) = 0 := by
    rw [h_one, derivation_one D hD]
  have h_leib := hD.2 (u : A) (u⁻¹ : Aˣ).val
  rw [h_prod] at h_leib
  have h_shift : (u : A) * D (u⁻¹ : Aˣ).val = - D (u : A) * (u⁻¹ : Aˣ).val := by
    linear_combination h_leib.symm
  have h_mult : (u⁻¹ : Aˣ).val * ((u : A) * D (u⁻¹ : Aˣ).val) = (u⁻¹ : Aˣ).val * (- D (u : A) * (u⁻¹ : Aˣ).val) := by
    rw [h_shift]
  have h_inv_mul : (u⁻¹ : Aˣ).val * (u : A) = 1 := Units.inv_mul u
  calc
    D (u⁻¹ : Aˣ).val = 1 * D (u⁻¹ : Aˣ).val := by rw [one_mul]
    _ = ((u⁻¹ : Aˣ).val * (u : A)) * D (u⁻¹ : Aˣ).val := by rw [h_inv_mul]
    _ = (u⁻¹ : Aˣ).val * ((u : A) * D (u⁻¹ : Aˣ).val) := by rw [mul_assoc]
    _ = (u⁻¹ : Aˣ).val * (- D (u : A) * (u⁻¹ : Aˣ).val) := h_mult
    _ = - (u⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val * D (u : A) := by ring

/-- 
  THEOREM (The Fundamental Logarithmic Homomorphism):
  The logarithmic derivative turns multiplicative Radon–Nikodym composition 
  into additive potential generators:
  dlog_D(u · v) = dlog_D(u) + dlog_D(v)
-/
theorem dlog_mul (D : A → A) (hD : IsDerivation D) (u v : Aˣ) :
    dlog D (u * v) = dlog D u + dlog D v := by
  dsimp [dlog]
  rw [hD.2 (u : A) (v : A)]
  have h_inv : ((u * v)⁻¹ : Aˣ).val = (u⁻¹ : Aˣ).val * (v⁻¹ : Aˣ).val := by
    rw [mul_inv_rev, Units.val_mul, mul_comm]
  rw [h_inv, mul_add]
  have h_left : (u⁻¹ : Aˣ).val * (v⁻¹ : Aˣ).val * (D (u : A) * (v : A)) = (u⁻¹ : Aˣ).val * D (u : A) := by
    have h_v : (v⁻¹ : Aˣ).val * (v : A) = 1 := Units.inv_mul v
    calc
      (u⁻¹ : Aˣ).val * (v⁻¹ : Aˣ).val * (D (u : A) * (v : A))
        = ((u⁻¹ : Aˣ).val * D (u : A)) * ((v⁻¹ : Aˣ).val * (v : A)) := by ring
      _ = ((u⁻¹ : Aˣ).val * D (u : A)) * 1 := by rw [h_v]
      _ = (u⁻¹ : Aˣ).val * D (u : A) := by rw [mul_one]
  have h_right : (u⁻¹ : Aˣ).val * (v⁻¹ : Aˣ).val * ((u : A) * D (v : A)) = (v⁻¹ : Aˣ).val * D (v : A) := by
    have h_u : (u⁻¹ : Aˣ).val * (u : A) = 1 := Units.inv_mul u
    calc
      (u⁻¹ : Aˣ).val * (v⁻¹ : Aˣ).val * ((u : A) * D (v : A))
        = ((v⁻¹ : Aˣ).val * D (v : A)) * ((u⁻¹ : Aˣ).val * (u : A)) := by ring
      _ = ((v⁻¹ : Aˣ).val * D (v : A)) * 1 := by rw [h_u]
      _ = (v⁻¹ : Aˣ).val * D (v : A) := by rw [mul_one]
  rw [h_left, h_right]

/-- THEOREM: Logarithmic derivation of the unit element is zero. -/
@[simp]
theorem dlog_one (D : A → A) (hD : IsDerivation D) :
    dlog D 1 = 0 := by
  dsimp [dlog]
  rw [derivation_one D hD, mul_zero]

/-- 
  THEOREM: Logarithmic derivation of the inverse density (Surprisal Reflection):
  dlog_D(u⁻¹) = - dlog_D(u)
-/
theorem dlog_inv (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    dlog D (u⁻¹) = - dlog D u := by
  have h := dlog_mul D hD u (u⁻¹)
  rw [mul_inv_cancel, dlog_one D hD] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- 
  THEOREM (The Radon–Nikodym Cocycle Chain Rule):
  If ρ₁₂ = dμ₁/dμ₂ and ρ₂₃ = dμ₂/dμ₃, then ρ₁₃ = ρ₁₂ · ρ₂₃, and:
  dlog_D(ρ₁₃) = dlog_D(ρ₁₂) + dlog_D(ρ₂₃)
-/
theorem radon_nikodym_cocycle_dlog
    (D : A → A) (hD : IsDerivation D)
    (rho_12 rho_23 : Aˣ) :
    dlog D (rho_12 * rho_23) = dlog D rho_12 + dlog D rho_23 :=
  dlog_mul D hD rho_12 rho_23

theorem dlog_mul_three
    (D : A → A) (hD : IsDerivation D)
    (u v w : Aˣ) :
    dlog D (u * v * w) = dlog D u + dlog D v + dlog D w := by
  rw [dlog_mul D hD (u * v) w, dlog_mul D hD u v]

/-!
=============================================================================
PART 2: Analytic Differentiable Calculus of the Radon–Nikodym Density
=============================================================================
-/

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

/-- 
  THEOREM: The Exponential Flow Generated by an Additive Potential K(t):
  d/dt [exp(K(t))] = K'(t) • exp(K(t))
-/
theorem hasDerivAt_exp_potential
    (K : ℝ → ℝ) (K' : ℝ) (t : ℝ)
    (h_diff : HasDerivAt K K' t) :
    HasDerivAt (fun s => Real.exp (K s)) (K' * Real.exp (K t)) t := by
  have h := HasDerivAt.exp h_diff
  have h_comm : Real.exp (K t) * K' = K' * Real.exp (K t) := mul_comm (Real.exp (K t)) K'
  rw [h_comm] at h
  exact h

/-- The logarithm of the exponential potential has the original derivative. -/
theorem hasDerivAt_log_exp_potential
    (K : ℝ → ℝ) (K' : ℝ) (t : ℝ)
    (h_diff : HasDerivAt K K' t) :
    HasDerivAt (fun s => Real.log (Real.exp (K s))) K' t := by
  simpa using h_diff

/-- The exponential of the logarithmic density has the original derivative. -/
theorem hasDerivAt_exp_log_density
    (rho : ℝ → ℝ) (rho' : ℝ) (t : ℝ)
    (h_diff : HasDerivAt rho rho' t)
    (h_pos : 0 < rho t) :
    HasDerivAt (fun s => Real.exp (Real.log (rho s))) rho' t := by
  have hlog : HasDerivAt (fun s => Real.log (rho s))
      (rho' / rho t) t :=
    hasDerivAt_log_radon_nikodym rho rho' t h_diff h_pos
  have hexp := HasDerivAt.exp hlog
  have hne : rho t ≠ 0 := ne_of_gt h_pos
  have hder : rho t * (rho' / rho t) = rho' := by
    field_simp
  simpa [Real.exp_log h_pos, hder] using hexp

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
    (K : ℝ → ℝ) (K' : ℝ) (t : ℝ)
    (h_diff : HasDerivAt K K' t) :
    let rho := fun s => Real.exp (K s)
    let rho' := K' * Real.exp (K t)
    rho' / rho t = K' := by
  dsimp
  have h_exp_pos : Real.exp (K t) ≠ 0 := ne_of_gt (Real.exp_pos (K t))
  exact mul_div_cancel_right₀ K' h_exp_pos

end InfoGeometry.Probability.ExpLogRNDerivation
