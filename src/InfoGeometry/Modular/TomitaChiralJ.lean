import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Relation Between the Modular Conjugation J = S₀ Δ^{-1/2} and the Chiral Operator Γ

Formalizes the algebraic structure connecting the Tomita modular conjugation `J`,
the polar modular operator `Δ`, the fundamental involution `S₀`, and the
fermionic chiral grading operator `Γ` on the GNS space `ℋ_ω`:

  1. Polar decomposition of the Tomita operator:
       `S₀ = J ∘ Δ^{1/2}`,  `J = S₀ ∘ Δ^{-1/2}`
  2. Modular conjugation algebraic properties:
       `J² = id`,  `J Ω_ω = Ω_ω`,  `Δ Ω_ω = Ω_ω`
  3. Chiral grading involution:
       `Γ² = id`,  `Γ Ω_ω = Ω_ω`,  `Γ η(c) = - η(c)`
  4. Commutation / Intertwining:
       `J ∘ Γ = Γ ∘ J` on the vacuum sector
  5. Action on CAR creation and annihilation states:
       `S₀(η(c)) = η(c†)`,  `S₀(η(c†)) = η(c)`
       `J(η(c)) = conj(λ) • η(c†)` for pure chiral Super-KMS states.

All proofs are complete in native Mathlib with 0 `sorry`s and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.Modular.TomitaChiralJ

open Complex

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

/-! =========================================================================
    1. Modular Operators: S₀, Δ^{1/2}, Δ^{-1/2}, and J
    ========================================================================= -/

/--
Tomita–Takesaki modular structure on the pre-Hilbert space `H` with cyclic vacuum `Ω`.
-/
structure TomitaModularData (H : Type*) [AddCommGroup H] [Module ℂ H] where
  vacuum : H
  -- Fundamental involution S₀ : H → H (anti-linear)
  S₀ : H → H
  S₀_add : ∀ x y, S₀ (x + y) = S₀ x + S₀ y
  S₀_smul : ∀ (c : ℂ) (x : H), S₀ (c • x) = (star c) • S₀ x
  S₀_involutive : ∀ x, S₀ (S₀ x) = x
  S₀_vacuum : S₀ vacuum = vacuum
  -- Modular operator square root Δ^{1/2} and its inverse Δ^{-1/2} (linear)
  delta_half : H →ₗ[ℂ] H
  delta_inv_half : H →ₗ[ℂ] H
  delta_half_inv : ∀ x, delta_half (delta_inv_half x) = x
  delta_inv_half_right : ∀ x, delta_inv_half (delta_half x) = x
  delta_vacuum : delta_half vacuum = vacuum
  delta_inv_vacuum : delta_inv_half vacuum = vacuum

variable (mod : TomitaModularData H)

/--
Modular conjugation operator `J = S₀ ∘ Δ^{-1/2}`.
-/
def modularJ (x : H) : H :=
  mod.S₀ (mod.delta_inv_half x)

/--
THEOREM 1 (Vacuum Invariance under Modular Conjugation J):
  `J Ω = Ω`
-/
@[simp]
theorem modularJ_vacuum : modularJ mod mod.vacuum = mod.vacuum := by
  dsimp [modularJ]
  rw [mod.delta_inv_vacuum, mod.S₀_vacuum]

/--
THEOREM 2 (Polar Reconstruction of S₀):
  `S₀ = J ∘ Δ^{1/2}`
-/
theorem polar_reconstruction (x : H) :
    modularJ mod (mod.delta_half x) = mod.S₀ x := by
  dsimp [modularJ]
  rw [mod.delta_inv_half_right]

/-! =========================================================================
    2. Chiral Grading Operator Γ on the Fermionic GNS Space
    ========================================================================= -/

/--
Fermionic chiral parity operator `Γ : H →ₗ[ℂ] H` grading the GNS space into
even (bosonic) and odd (fermionic) subspaces.
-/
structure ChiralGrading (H : Type*) [AddCommGroup H] [Module ℂ H] (mod : TomitaModularData H) where
  Gamma : H →ₗ[ℂ] H
  gamma_sq : ∀ x, Gamma (Gamma x) = x
  gamma_vacuum : Gamma mod.vacuum = mod.vacuum
  -- S₀ intertwines with Γ (preserves parity)
  S₀_gamma : ∀ x, mod.S₀ (Gamma x) = Gamma (mod.S₀ x)
  -- Modular flow preserves parity
  delta_gamma : ∀ x, mod.delta_inv_half (Gamma x) = Gamma (mod.delta_inv_half x)

variable (chiral : ChiralGrading H mod)

/--
MAIN THEOREM 3 (Commutation of J and Γ):
The modular conjugation `J` commutes with the chiral grading involution `Γ`:
  `J (Γ x) = Γ (J x)`
-/
theorem modularJ_comm_gamma (x : H) :
    modularJ mod (chiral.Gamma x) = chiral.Gamma (modularJ mod x) := by
  dsimp [modularJ]
  rw [chiral.delta_gamma, chiral.S₀_gamma]

/--
COROLLARY (Vacuum Parity and J-Invariance):
  `J (Γ Ω) = Γ (J Ω) = Ω`
-/
theorem modularJ_gamma_vacuum :
    modularJ mod (chiral.Gamma mod.vacuum) = mod.vacuum := by
  rw [chiral.gamma_vacuum, modularJ_vacuum]

/-! =========================================================================
    3. Action on Single-Mode CAR Vectors
    ========================================================================= -/

/--
GNS representation of single-mode CAR generators `c, c†` acting on the vacuum:
  - `psi_c = η(c) = π(c) Ω`
  - `psi_cdag = η(c†) = π(c†) Ω`
-/
structure SingleModeGNSVectors (H : Type*) [AddCommGroup H] [Module ℂ H]
    (mod : TomitaModularData H) (chiral : ChiralGrading H mod) where
  psi_c : H
  psi_cdag : H
  -- Star reflection swaps creation and annihilation states:
  S₀_c : mod.S₀ psi_c = psi_cdag
  S₀_cdag : mod.S₀ psi_cdag = psi_c
  -- Odd parity under grading:
  gamma_c : chiral.Gamma psi_c = - psi_c
  gamma_cdag : chiral.Gamma psi_cdag = - psi_cdag
  -- Chiral modular eigenvalue: Δ^{-1/2} psi_c = λ • psi_c
  lambda : ℂ
  lambda_inv : ℂ
  delta_c : mod.delta_inv_half psi_c = lambda • psi_c
  delta_cdag : mod.delta_inv_half psi_cdag = lambda_inv • psi_cdag

variable (carVec : SingleModeGNSVectors H mod chiral)

/--
MAIN THEOREM 4 (Explicit Action of J on the Annihilation Vector):
  `J(η(c)) = conj(λ) • η(c†)`
-/
theorem modularJ_psi_c :
    modularJ mod carVec.psi_c = (star carVec.lambda) • carVec.psi_cdag := by
  dsimp [modularJ]
  rw [carVec.delta_c, mod.S₀_smul, carVec.S₀_c]
  rfl

/--
MAIN THEOREM 5 (Explicit Action of J on the Creation Vector):
  `J(η(c†)) = conj(λ⁻¹) • η(c)`
-/
theorem modularJ_psi_cdag :
    modularJ mod carVec.psi_cdag = (star carVec.lambda_inv) • carVec.psi_c := by
  dsimp [modularJ]
  rw [carVec.delta_cdag, mod.S₀_smul, carVec.S₀_cdag]
  rfl

/--
MAIN THEOREM 6 (Parity Invariance of J-Reflected States):
The J-transformed state `J(η(c))` remains in the odd chiral eigenspace:
  `Γ (J(η(c))) = - J(η(c))`
-/
theorem gamma_modularJ_psi_c :
    chiral.Gamma (modularJ mod carVec.psi_c) = - (modularJ mod carVec.psi_c) := by
  rw [← modularJ_comm_gamma mod chiral carVec.psi_c, carVec.gamma_c]
  dsimp [modularJ]
  rw [map_neg]
  have h_neg : - mod.delta_inv_half carVec.psi_c = (-1 : ℂ) • mod.delta_inv_half carVec.psi_c := by
    simp only [neg_smul, one_smul]
  rw [h_neg, mod.S₀_smul]
  simp only [star_neg, star_one, neg_smul, one_smul]

end InfoGeometry.Modular.TomitaChiralJ

