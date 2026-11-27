/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Abstract Interface for `J = S₀ ∘ Δ^{-1/2}` and Chiral Grading `Γ`

Defines abstract module-level interfaces (`TomitaModularData`, `ChiralGrading`,
`SingleModeGNSVectors`) over a `ℂ`-module `H`, taking `S₀`, `delta_half`,
`delta_inv_half`, `Gamma`, commutation laws, and eigenvalue equations as fields:

  1. `modularJ`: `J := S₀ ∘ Δ^{-1/2}`
  2. `modularJ_vacuum`: `J Ω = Ω` (from supplied vacuum-invariance fields)
  3. `polar_reconstruction`: `J (Δ^{1/2} x) = S₀ x` (from `delta_inv_half_right`)
  4. `modularJ_comm_gamma` & `modularJ_gamma_vacuum`: `[J, Γ] = 0` from supplied intertwining fields
  5. `modularJ_psi_c`, `modularJ_psi_cdag`, `gamma_modularJ_psi_c`: action on supplied
     creation/annihilation eigenvectors (`J(ψ_c) = conj(λ) • ψ_{c†}`, odd parity).

Note: `J² = id` is not proved in this file; `S₀` and `Δ^{±1/2}` are supplied as structure fields.
-/

noncomputable section

namespace InfoGeometry.Modular.TomitaChiralJ

open Complex

section GNSModel

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

/-! =========================================================================
    4. Operator-Level vs. Vector-Level Tomita Action & 2×2 Peirce Quadrants
    =========================================================================

Vector-level Tomita `J = S₀ ∘ Δ^{-1/2}` is antilinear (`J(c • v) = star c • J v`).
At the operator level on `Module.End ℂ H`:
* `tomitaAdJ J A := J ∘ A ∘ J` is **multiplicative** and **conjugate-linear**
  → Row 1 (if `Ad_J P = P`) or Row 2 (if `Ad_J P = 1 - P`);
* `tomitaAntiJ J adj A := J ∘ adj A ∘ J` is **anti-multiplicative** and **ℂ-linear**
  → Row 3 (if `j P = P`) or Row 4 (if `j P = 1 - P`, double-reversal cancellation). -/

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- Vector-level `modularJ mod` is additive. -/
theorem modularJ_add (x y : H) :
    modularJ mod (x + y) = modularJ mod x + modularJ mod y := by
  dsimp [modularJ]
  rw [map_add, mod.S₀_add]

/-- Vector-level `modularJ mod` is antilinear (`ℂ`-conjugate-homogeneous). -/
theorem modularJ_smul (c : ℂ) (x : H) :
    modularJ mod (c • x) = (star c) • modularJ mod x := by
  dsimp [modularJ]
  rw [LinearMap.map_smul, mod.S₀_smul]
  rfl

end GNSModel

section EndPeirceQuadrants

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

/-- Operator-level Tomita adjoint `Ad_J(A) = J ∘ A ∘ J` on `Module.End ℂ H`.
Even though `J` is antilinear on vectors, `Ad_J(A)` is a `ℂ`-linear endomorphism
and `Ad_J` itself is **multiplicative** and **conjugate-linear** in `A`. -/
def tomitaAdJ (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (A : Module.End ℂ H) : Module.End ℂ H where
  toFun := fun x => J (A (J x))
  map_add' := fun x y => by rw [hJ_add, A.map_add, hJ_add]
  map_smul' := fun c x => by
    simp only [RingHom.id_apply]
    rw [hJ_smul, A.map_smul, hJ_smul, star_star]

@[simp]
theorem tomitaAdJ_apply (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (A : Module.End ℂ H) (x : H) :
    tomitaAdJ J hJ_add hJ_smul A x = J (A (J x)) :=
  rfl

/-- `tomitaAdJ` is conjugate-linear (`ℂ`-antilinear) in the operator `A`. -/
theorem tomitaAdJ_smul (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (c : ℂ) (A : Module.End ℂ H) :
    tomitaAdJ J hJ_add hJ_smul (c • A) = (star c) • tomitaAdJ J hJ_add hJ_smul A := by
  ext x
  simp [tomitaAdJ, hJ_smul]

/-- `tomitaAdJ` is **multiplicative**: `Ad_J(A * B) = Ad_J(A) * Ad_J(B)`. -/
theorem tomitaAdJ_mul (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (hJ_inv : ∀ x, J (J x) = x) (A B : Module.End ℂ H) :
    tomitaAdJ J hJ_add hJ_smul (A * B) =
      tomitaAdJ J hJ_add hJ_smul A * tomitaAdJ J hJ_add hJ_smul B := by
  ext x
  change J (A (B (J x))) = J (A (J (J (B (J x)))))
  rw [hJ_inv]

/-- `tomitaAdJ` is involutive when `J² = id`. -/
theorem tomitaAdJ_involutive (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (hJ_inv : ∀ x, J (J x) = x) (A : Module.End ℂ H) :
    tomitaAdJ J hJ_add hJ_smul (tomitaAdJ J hJ_add hJ_smul A) = A := by
  ext x
  change J (J (A (J (J x)))) = A x
  rw [hJ_inv, hJ_inv]

/-- `tomitaAdJ` preserves the identity operator `1`. -/
theorem tomitaAdJ_one (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (hJ_inv : ∀ x, J (J x) = x) :
    tomitaAdJ J hJ_add hJ_smul (1 : Module.End ℂ H) = 1 := by
  ext x
  exact hJ_inv x

private lemma antilinear_map_zero (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y) : J 0 = 0 := by
  have h := hJ_add 0 0
  rw [add_zero] at h
  have h' : J 0 + 0 = J 0 + J 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

private lemma antilinear_map_neg (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y) (x : H) : J (-x) = -J x := by
  apply eq_neg_of_add_eq_zero_left
  rw [← hJ_add, neg_add_cancel, antilinear_map_zero J hJ_add]

private lemma antilinear_map_sub (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y) (x y : H) :
    J (x - y) = J x - J y := by
  rw [sub_eq_add_neg, hJ_add, antilinear_map_neg J hJ_add, ← sub_eq_add_neg]

/-- `tomitaAdJ` preserves subtraction. -/
theorem tomitaAdJ_sub (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (A B : Module.End ℂ H) :
    tomitaAdJ J hJ_add hJ_smul (A - B) =
      tomitaAdJ J hJ_add hJ_smul A - tomitaAdJ J hJ_add hJ_smul B := by
  ext x
  change J (A (J x) - B (J x)) = J (A (J x)) - J (B (J x))
  exact antilinear_map_sub J hJ_add _ _

/-- **Row 1 under `Ad_J`**: when `Ad_J P = P`, `Ad_J` preserves all four Peirce corners individually. -/
theorem tomitaAdJ_row1_fixing_projector (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (hJ_inv : ∀ x, J (J x) = x) (P : Module.End ℂ H)
    (hP_fix : tomitaAdJ J hJ_add hJ_smul P = P) (A : Module.End ℂ H) :
    tomitaAdJ J hJ_add hJ_smul (peirce11 P A) = peirce11 P (tomitaAdJ J hJ_add hJ_smul A) ∧
    tomitaAdJ J hJ_add hJ_smul (peirce00 P A) = peirce00 P (tomitaAdJ J hJ_add hJ_smul A) ∧
    tomitaAdJ J hJ_add hJ_smul (conePlus P A) = conePlus P (tomitaAdJ J hJ_add hJ_smul A) ∧
    tomitaAdJ J hJ_add hJ_smul (coneMinus P A) = coneMinus P (tomitaAdJ J hJ_add hJ_smul A) := by
  have hQ_fix : tomitaAdJ J hJ_add hJ_smul (1 - P) = 1 - P := by
    rw [tomitaAdJ_sub, tomitaAdJ_one J hJ_add hJ_smul hJ_inv, hP_fix]
  have hmul := tomitaAdJ_mul J hJ_add hJ_smul hJ_inv
  dsimp [peirce11, peirce00, conePlus, coneMinus]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmul, hmul, hP_fix]
  · rw [hmul, hmul, hQ_fix]
  · rw [hmul, hmul, hP_fix, hQ_fix]
  · rw [hmul, hmul, hQ_fix, hP_fix]

/-- **Row 2 under `Ad_J`**: when `Ad_J P = 1 - P`, `Ad_J` swaps the even body corners,
swaps the odd chiral soul corners `conePlus ↔ coneMinus`, and forces any fixed single-corner
fermion to vanish. -/
theorem tomitaAdJ_row2_swapping_projector (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (hJ_inv : ∀ x, J (J x) = x) (P : Module.End ℂ H) (hP : P * P = P)
    (hP_swap : tomitaAdJ J hJ_add hJ_smul P = 1 - P) (A : Module.End ℂ H) :
    tomitaAdJ J hJ_add hJ_smul (peirce11 P A) = peirce00 P (tomitaAdJ J hJ_add hJ_smul A) ∧
    tomitaAdJ J hJ_add hJ_smul (peirce00 P A) = peirce11 P (tomitaAdJ J hJ_add hJ_smul A) ∧
    tomitaAdJ J hJ_add hJ_smul (conePlus P A) = coneMinus P (tomitaAdJ J hJ_add hJ_smul A) ∧
    tomitaAdJ J hJ_add hJ_smul (coneMinus P A) = conePlus P (tomitaAdJ J hJ_add hJ_smul A) ∧
    (tomitaAdJ J hJ_add hJ_smul (conePlus P A) = conePlus P A → conePlus P A = 0) ∧
    (tomitaAdJ J hJ_add hJ_smul (coneMinus P A) = coneMinus P A → coneMinus P A = 0) := by
  have hQ_swap : tomitaAdJ J hJ_add hJ_smul (1 - P) = P := by
    rw [tomitaAdJ_sub, tomitaAdJ_one J hJ_add hJ_smul hJ_inv, hP_swap, sub_sub_cancel]
  have hmul := tomitaAdJ_mul J hJ_add hJ_smul hJ_inv
  have hC := multSheetSwap_corners (tomitaAdJ J hJ_add hJ_smul) hmul hP_swap hQ_swap A
  have hZ := multSheetSwap_singleCorner_fixed_zero hP (tomitaAdJ J hJ_add hJ_smul) hmul hP_swap hQ_swap A
  exact ⟨hC.1, hC.2.1, hC.2.2.1, hC.2.2.2, hZ.1, hZ.2⟩

/-- Operator-level Tomita anti-automorphism `j(A) = J ∘ A† ∘ J` built from an adjoint `adj`.
Composing two conjugate-linear operations yields a **ℂ-linear** and **anti-multiplicative** map! -/
def tomitaAntiJ (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (adj : Module.End ℂ H → Module.End ℂ H) (A : Module.End ℂ H) : Module.End ℂ H :=
  tomitaAdJ J hJ_add hJ_smul (adj A)

/-- Unlike `Ad_J`, `tomitaAntiJ` is **ℂ-linear** in `A` (`j(c • A) = c • j(A)`). -/
theorem tomitaAntiJ_smul (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (adj : Module.End ℂ H → Module.End ℂ H)
    (hadj_smul : ∀ (c : ℂ) (A : Module.End ℂ H), adj (c • A) = (star c) • adj A)
    (c : ℂ) (A : Module.End ℂ H) :
    tomitaAntiJ J hJ_add hJ_smul adj (c • A) = c • tomitaAntiJ J hJ_add hJ_smul adj A := by
  dsimp [tomitaAntiJ]
  rw [hadj_smul, tomitaAdJ_smul, star_star]

/-- Unlike `Ad_J`, `tomitaAntiJ` is **anti-multiplicative**: `j(A * B) = j(B) * j(A)`. -/
theorem tomitaAntiJ_mul (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (hJ_inv : ∀ x, J (J x) = x)
    (adj : Module.End ℂ H → Module.End ℂ H)
    (hadj_mul : ∀ A B : Module.End ℂ H, adj (A * B) = adj B * adj A)
    (A B : Module.End ℂ H) :
    tomitaAntiJ J hJ_add hJ_smul adj (A * B) =
      tomitaAntiJ J hJ_add hJ_smul adj B * tomitaAntiJ J hJ_add hJ_smul adj A := by
  dsimp [tomitaAntiJ]
  rw [hadj_mul, tomitaAdJ_mul J hJ_add hJ_smul hJ_inv]

/-- **Row 3 under `j(A) = J A† J`**: when `j(P) = P`, `j` fixes `peirce11`, `peirce00`,
**swaps** `conePlus ↔ coneMinus`, and forces any fixed single-corner element to vanish. -/
theorem tomitaAntiJ_row3_fixing_projector (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (hJ_inv : ∀ x, J (J x) = x)
    (adj : Module.End ℂ H → Module.End ℂ H)
    (hadj_mul : ∀ A B : Module.End ℂ H, adj (A * B) = adj B * adj A)
    (hadj_one : adj 1 = 1)
    (hadj_sub : ∀ A B : Module.End ℂ H, adj (A - B) = adj A - adj B)
    (P : Module.End ℂ H) (hP : P * P = P) (hadjP : adj P = P)
    (hAdJP : tomitaAdJ J hJ_add hJ_smul P = P) (A : Module.End ℂ H) :
    let j := tomitaAntiJ J hJ_add hJ_smul adj
    j P = P ∧
    j (1 - P) = 1 - P ∧
    j (peirce11 P A) = peirce11 P (j A) ∧
    j (peirce00 P A) = peirce00 P (j A) ∧
    j (conePlus P A) = coneMinus P (j A) ∧
    j (coneMinus P A) = conePlus P (j A) ∧
    (j (conePlus P A) = conePlus P A → conePlus P A = 0) ∧
    (j (coneMinus P A) = coneMinus P A → coneMinus P A = 0) := by
  intro j
  have hjP : j P = P := by dsimp [j, tomitaAntiJ]; rw [hadjP, hAdJP]
  have hjQ : j (1 - P) = 1 - P := by
    dsimp [j, tomitaAntiJ]
    rw [hadj_sub, hadj_one, hadjP, tomitaAdJ_sub, tomitaAdJ_one J hJ_add hJ_smul hJ_inv, hAdJP]
  have hmul : ∀ X Y : Module.End ℂ H, j (X * Y) = j Y * j X :=
    tomitaAntiJ_mul J hJ_add hJ_smul hJ_inv adj hadj_mul
  have hPlus : j (conePlus P A) = coneMinus P (j A) := by
    dsimp [conePlus, coneMinus]
    rw [hmul, hmul, hjQ, hjP, ← mul_assoc]
  have hMinus : j (coneMinus P A) = conePlus P (j A) := by
    dsimp [conePlus, coneMinus]
    rw [hmul, hmul, hjP, hjQ, ← mul_assoc]
  refine ⟨hjP, hjQ, ?_, ?_, hPlus, hMinus, ?_, ?_⟩
  · dsimp [peirce11]; rw [hmul, hmul, hjP, ← mul_assoc]
  · dsimp [peirce00]; rw [hmul, hmul, hjQ, ← mul_assoc]
  · intro hFix
    calc conePlus P A = P * conePlus P A := (P_mul_conePlus hP A).symm
      _ = P * j (conePlus P A) := by rw [hFix]
      _ = P * coneMinus P (j A) := by rw [hPlus]
      _ = 0 := P_mul_coneMinus hP (j A)
  · intro hFix
    calc coneMinus P A = coneMinus P A * P := (coneMinus_mul_P hP A).symm
      _ = j (coneMinus P A) * P := by rw [hFix]
      _ = conePlus P (j A) * P := by rw [hMinus]
      _ = 0 := conePlus_mul_P hP (j A)

/-- **Row 4 under `j(A) = J A† J`**: when `Ad_J P = 1 - P` and `P† = P`,
`j` swaps `P ↔ 1 - P`, swaps `peirce11 ↔ peirce00`, and by double-reversal cancellation
**preserves** each odd chiral soul corner `conePlus` and `coneMinus` individually! -/
theorem tomitaAntiJ_row4_swapping_projector (J : H → H)
    (hJ_add : ∀ x y, J (x + y) = J x + J y)
    (hJ_smul : ∀ (c : ℂ) x, J (c • x) = (star c) • J x)
    (hJ_inv : ∀ x, J (J x) = x)
    (adj : Module.End ℂ H → Module.End ℂ H)
    (hadj_mul : ∀ A B : Module.End ℂ H, adj (A * B) = adj B * adj A)
    (hadj_one : adj 1 = 1)
    (hadj_sub : ∀ A B : Module.End ℂ H, adj (A - B) = adj A - adj B)
    (P : Module.End ℂ H) (hadjP : adj P = P)
    (hAdJP : tomitaAdJ J hJ_add hJ_smul P = 1 - P) (A : Module.End ℂ H) :
    let j := tomitaAntiJ J hJ_add hJ_smul adj
    j P = 1 - P ∧
    j (1 - P) = P ∧
    j (peirce11 P A) = peirce00 P (j A) ∧
    j (peirce00 P A) = peirce11 P (j A) ∧
    j (conePlus P A) = conePlus P (j A) ∧
    j (coneMinus P A) = coneMinus P (j A) := by
  intro j
  have hjP : j P = 1 - P := by dsimp [j, tomitaAntiJ]; rw [hadjP, hAdJP]
  have hjQ : j (1 - P) = P := by
    dsimp [j, tomitaAntiJ]
    rw [hadj_sub, hadj_one, hadjP, tomitaAdJ_sub, tomitaAdJ_one J hJ_add hJ_smul hJ_inv, hAdJP,
        sub_sub_cancel]
  have hmul : ∀ X Y : Module.End ℂ H, j (X * Y) = j Y * j X :=
    tomitaAntiJ_mul J hJ_add hJ_smul hJ_inv adj hadj_mul
  have hC := antiMultSheetSwap_corners j hmul hjP hjQ A
  exact ⟨hjP, hjQ, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2⟩

end EndPeirceQuadrants

/-! =========================================================================
    5. Concrete Non-Zero Row-4 Matrix Witness `τ(A) = X Aᵀ X` on `M₂(ℝ)`
    ========================================================================= -/

section Row4MatrixWitness

open Matrix InfoGeometry.OperatorAlgebra.PeirceSpine

def mat2PPlus : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
def mat2X : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def mat2UPlus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def mat2VMinus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

def mat2Row4Tau (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  mat2X * Aᵀ * mat2X

/-- Explicit non-commutativity witness for the `M₂(ℝ)` Peirce chiral corner generators. -/
theorem mat2_peirce_noncommutative :
    mat2UPlus * mat2VMinus ≠ mat2VMinus * mat2UPlus := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [mat2UPlus, mat2VMinus, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Concrete non-degenerate Row-4 witness in `M₂(ℝ)`: `τ(A) = X Aᵀ X` swaps `P₊ ↔ 1 - P₊`
while fixing both non-zero, non-commuting chiral corner generators `u⁺` and `v⁻` pointwise. -/
theorem mat2Row4_nondegenerate_witness :
    mat2PPlus * mat2PPlus = mat2PPlus ∧
    mat2Row4Tau mat2PPlus = 1 - mat2PPlus ∧
    mat2Row4Tau (1 - mat2PPlus) = mat2PPlus ∧
    mat2UPlus = conePlus mat2PPlus mat2UPlus ∧
    mat2VMinus = coneMinus mat2PPlus mat2VMinus ∧
    mat2Row4Tau mat2UPlus = mat2UPlus ∧
    mat2Row4Tau mat2VMinus = mat2VMinus ∧
    mat2UPlus ≠ 0 ∧
    mat2VMinus ≠ 0 ∧
    mat2UPlus * mat2VMinus ≠ mat2VMinus * mat2UPlus := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, mat2_peirce_noncommutative⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2PPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2Row4Tau, mat2PPlus, mat2X, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Matrix.transpose_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2Row4Tau, mat2PPlus, mat2X, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Matrix.transpose_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [conePlus, mat2PPlus, mat2UPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [coneMinus, mat2PPlus, mat2VMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2Row4Tau, mat2X, mat2UPlus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Matrix.transpose_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2Row4Tau, mat2X, mat2VMinus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Matrix.transpose_apply, Fin.sum_univ_two]
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp [mat2UPlus] at h01
  · intro h
    have h10 := congrFun (congrFun h 1) 0
    simp [mat2VMinus] at h10

/-- The concrete map `A ↦ X Aᵀ X` is the generic Row 4 self-adjoint unit
conjugation from `PeirceSpine.StarGrading`.  The generic corner theorem therefore
applies to this same map: it reverses products, is involutive, swaps the two
diagonal corners, and preserves each off-diagonal corner.  The final conjunct
records the concrete fixed nonzero corner elements, so the abstract corner law
is connected to the nontrivial `M₂(ℝ)` realization. -/
theorem mat2Row4Tau_is_generic_Peirce_row4 :
    (∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      mat2Row4Tau A = mat2X * star A * mat2X) ∧
    (∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      mat2Row4Tau (mat2Row4Tau A) = A) ∧
    (∀ A C : Matrix (Fin 2) (Fin 2) ℝ,
      mat2Row4Tau (A * C) = mat2Row4Tau C * mat2Row4Tau A) ∧
    mat2Row4Tau mat2PPlus = 1 - mat2PPlus ∧
    mat2Row4Tau (1 - mat2PPlus) = mat2PPlus ∧
    (∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      mat2Row4Tau (conePlus mat2PPlus A) =
        conePlus mat2PPlus (mat2Row4Tau A)) ∧
    (∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      mat2Row4Tau (coneMinus mat2PPlus A) =
        coneMinus mat2PPlus (mat2Row4Tau A)) ∧
    mat2Row4Tau mat2UPlus = mat2UPlus ∧
    mat2Row4Tau mat2VMinus = mat2VMinus ∧
    mat2UPlus ≠ 0 ∧ mat2VMinus ≠ 0 := by
  have hPstar : star mat2PPlus = mat2PPlus := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat2PPlus]
  have hX2 : mat2X * mat2X = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mat2X, Matrix.mul_apply, Fin.sum_univ_two]
  have hXstar : star mat2X = mat2X := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat2X]
  have hXP : mat2X * mat2PPlus * mat2X = 1 - mat2PPlus := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mat2X, mat2PPlus, Matrix.mul_apply, Fin.sum_univ_two]
  have hRow := unitStarConjugation_is_row4_antiMultSheetSwap
    hPstar mat2X hX2 hXstar hXP
  rcases hRow with ⟨hInvolutive, hAntiMultiplicative, hRowP, hRowQ,
    hRowPlus, hRowMinus⟩
  rcases mat2Row4_nondegenerate_witness with
    ⟨_, _, _, _, _, hUFixed, hVFixed, hUNe, hVNe, _⟩
  have hTau (A : Matrix (Fin 2) (Fin 2) ℝ) :
      mat2Row4Tau A = mat2X * star A * mat2X := by
    simp [mat2Row4Tau, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨hTau, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    rw [hTau A, hTau (mat2X * star A * mat2X)]
    exact hInvolutive A
  · intro A C
    rw [hTau (A * C), hTau A, hTau C]
    exact hAntiMultiplicative A C
  · rw [hTau mat2PPlus]
    exact hRowP
  · rw [hTau (1 - mat2PPlus)]
    exact hRowQ
  · intro A
    rw [hTau (conePlus mat2PPlus A), hTau A]
    exact hRowPlus A
  · intro A
    rw [hTau (coneMinus mat2PPlus A), hTau A]
    exact hRowMinus A
  · exact hUFixed
  · exact hVFixed
  · exact hUNe
  · exact hVNe

end Row4MatrixWitness

end InfoGeometry.Modular.TomitaChiralJ

