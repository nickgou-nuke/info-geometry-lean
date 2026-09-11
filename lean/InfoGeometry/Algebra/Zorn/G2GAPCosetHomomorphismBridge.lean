import Mathlib.Algebra.Group.Subgroup.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Group

/-!
# Homomorphism Bridge: GAP Permutation Arrays to QuotientGroup.mk

Formalizes the exact algebraic bridge between:
  1. Discrete GAP permutation arrays on `Fin 189` and `Fin 63`.
  2. Canonical Mathlib quotient coset spaces `G ⧸ B₀` and `G ⧸ P`.
  3. Action homomorphisms `ρ : G →* Equiv.Perm (Fin n)` intertwining with `QuotientGroup.mk`.
  4. Commutativity of the projection `discreteProj : Fin 189 → Fin 63` with the G-action.
-/

variable {G : Type*} [Group G]

namespace InfoGeometry.Algebra.Zorn.G2GAPQuotientBridge

/-! =========================================================================
    1. Group Action and Permutation Equivalence on G ⧸ H
    ========================================================================= -/

/-- Left translation action of `g ∈ G` on the coset space `G ⧸ H`. -/
def cosetAction (H : Subgroup G) (g : G) : (G ⧸ H) → (G ⧸ H) :=
  Quotient.map' (fun x => g * x) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have h_eq : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by group
    rw [h_eq]
    exact hab)

@[simp]
theorem cosetAction_mk (H : Subgroup G) (g x : G) :
    cosetAction H g (QuotientGroup.mk x) = QuotientGroup.mk (g * x) :=
  rfl

theorem cosetAction_one (H : Subgroup G) (c : G ⧸ H) :
    cosetAction H 1 c = c := by
  induction c using Quotient.inductionOn'
  simp only [cosetAction_mk, one_mul]

theorem cosetAction_mul (H : Subgroup G) (g₁ g₂ : G) (c : G ⧸ H) :
    cosetAction H (g₁ * g₂) c = cosetAction H g₁ (cosetAction H g₂ c) := by
  induction c using Quotient.inductionOn'
  simp only [cosetAction_mk, mul_assoc]

/-- The invertible bijection on `G ⧸ H` induced by left translation by `g`. -/
def cosetActionEquiv (H : Subgroup G) (g : G) : Equiv.Perm (G ⧸ H) where
  toFun := cosetAction H g
  invFun := cosetAction H g⁻¹
  left_inv c := by
    rw [← cosetAction_mul, inv_mul_cancel, cosetAction_one]
  right_inv c := by
    rw [← cosetAction_mul, mul_inv_cancel, cosetAction_one]

/-! =========================================================================
    2. GAP Action Homomorphism ρ : G →* Equiv.Perm (Fin n)
    ========================================================================= -/

/--
Permutation representation on `Fin n` induced by an enumeration `enum : Fin n ≃ G ⧸ H`.
-/
def permOfGroupElem (H : Subgroup G) {n : ℕ} (enum : Fin n ≃ G ⧸ H) (g : G) :
    Equiv.Perm (Fin n) :=
  (enum.trans (cosetActionEquiv H g)).trans enum.symm

/--
MAIN THEOREM (Action Homomorphism into Perm(Fin n)):
The GAP-exported permutation generator map forms a genuine group homomorphism:
  `ρ : G →* Equiv.Perm (Fin n)`
-/
def actionHom (H : Subgroup G) {n : ℕ} (enum : Fin n ≃ G ⧸ H) :
    G →* Equiv.Perm (Fin n) where
  toFun := permOfGroupElem H enum
  map_one' := by
    ext i
    dsimp [permOfGroupElem, cosetActionEquiv]
    rw [cosetAction_one, Equiv.symm_apply_apply]
  map_mul' g₁ g₂ := by
    ext i
    dsimp [permOfGroupElem, cosetActionEquiv]
    rw [cosetAction_mul, Equiv.apply_symm_apply]

/-! =========================================================================
    3. Intertwining with QuotientGroup.mk and Coset Representatives
    ========================================================================= -/

/--
MAIN THEOREM (Kernel Intertwining with QuotientGroup.mk):
Applying the GAP permutation `actionHom g i` corresponds to group multiplication
on the coset representative `QuotientGroup.mk (g * reps(i))`.
-/
theorem perm_intertwines_quotient (H : Subgroup G) {n : ℕ} (enum : Fin n ≃ G ⧸ H)
    (reps : Fin n → G) (h_enum : ∀ i, enum i = QuotientGroup.mk (reps i))
    (g : G) (i : Fin n) :
    enum (actionHom H enum g i) = QuotientGroup.mk (g * reps i) := by
  dsimp [actionHom, permOfGroupElem, cosetActionEquiv]
  rw [Equiv.apply_symm_apply, h_enum, cosetAction_mk]

/-! =========================================================================
    4. Canonical Coset Projection and Discrete Equivariance
    ========================================================================= -/

/-- Canonical projection `G ⧸ B₀ → G ⧸ P` for `B₀ ≤ P`. -/
def cosetProj (B₀ P : Subgroup G) (hBP : B₀ ≤ P) : (G ⧸ B₀) → (G ⧸ P) :=
  Quotient.map' (fun g => g) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact hBP hab)

@[simp]
theorem cosetProj_mk (B₀ P : Subgroup G) (hBP : B₀ ≤ P) (g : G) :
    cosetProj B₀ P hBP (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

/--
Discrete projection `Fin 189 → Fin 63` exported from GAP, structurally defined
via the coset bijections `enumB` and `enumP`.
-/
def discreteProj (B₀ P : Subgroup G) (hBP : B₀ ≤ P)
    (enumB : Fin 189 ≃ G ⧸ B₀) (enumP : Fin 63 ≃ G ⧸ P) (i : Fin 189) : Fin 63 :=
  enumP.symm (cosetProj B₀ P hBP (enumB i))

/--
THEOREM (Geometric Compatibility with Canonical Projection):
The discrete projection tracks the mathematical projection `cosetProj`.
-/
theorem discreteProj_spec (B₀ P : Subgroup G) (hBP : B₀ ≤ P)
    (enumB : Fin 189 ≃ G ⧸ B₀) (enumP : Fin 63 ≃ G ⧸ P) (i : Fin 189) :
    enumP (discreteProj B₀ P hBP enumB enumP i) = cosetProj B₀ P hBP (enumB i) := by
  dsimp [discreteProj]
  simp only [Equiv.apply_symm_apply]

/--
MAIN THEOREM (Equivariance of Discrete Projection under Action Homomorphisms):
The discrete map `discreteProj : Fin 189 → Fin 63` commutes with the GAP permutation
actions of `G` on both spaces:
  `π_GAP(ρ_{B₀}(g) · i) = ρ_P(g) · π_GAP(i)`
-/
theorem discreteProj_equivariant (B₀ P : Subgroup G) (hBP : B₀ ≤ P)
    (enumB : Fin 189 ≃ G ⧸ B₀) (enumP : Fin 63 ≃ G ⧸ P)
    (g : G) (i : Fin 189) :
    discreteProj B₀ P hBP enumB enumP (actionHom B₀ enumB g i) =
      actionHom P enumP g (discreteProj B₀ P hBP enumB enumP i) := by
  dsimp [discreteProj, actionHom, permOfGroupElem, cosetActionEquiv]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  congr 1
  induction (enumB i) using Quotient.inductionOn' with | h a =>
  simp only [cosetAction_mk, cosetProj_mk]

/-! =========================================================================
    5. Stabilizer Characterization of Base Points
    ========================================================================= -/

/--
THEOREM (Base Point Stabilizer Equivalence):
An element `g ∈ G` fixes the base point `0` in `Fin n` if and only if `g ∈ H`.
-/
theorem base_point_stabilizer (H : Subgroup G) {n : ℕ} (enum : Fin n ≃ G ⧸ H)
    (i₀ : Fin n) (h_base : enum i₀ = QuotientGroup.mk 1) (g : G) :
    actionHom H enum g i₀ = i₀ ↔ g ∈ H := by
  dsimp [actionHom, permOfGroupElem, cosetActionEquiv]
  constructor
  · intro h_fix
    have h_eval : cosetAction H g (enum i₀) = enum i₀ := by
      have h_eq : enum.symm (cosetAction H g (enum i₀)) = enum.symm (enum i₀) := by
        rw [Equiv.symm_apply_apply, h_fix]
      exact enum.symm.injective h_eq
    rw [h_base, cosetAction_mk, mul_one, QuotientGroup.eq, mul_one] at h_eval
    simpa only [inv_inv] using H.inv_mem h_eval
  · intro hg
    have h_act : cosetAction H g (enum i₀) = enum i₀ := by
      rw [h_base, cosetAction_mk, mul_one]
      have : (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk 1 := by
        rw [QuotientGroup.eq, mul_one]
        exact H.inv_mem hg
      rw [this]
    rw [h_act, Equiv.symm_apply_apply]

end InfoGeometry.Algebra.Zorn.G2GAPQuotientBridge
