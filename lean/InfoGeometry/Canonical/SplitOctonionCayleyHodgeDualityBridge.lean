import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

/-!
# Cayley Conjugation vs. Hodge Star and Exterior Duality

This module formalizes the exact operator relationship between:
1. Cayley conjugation $C_{\mathrm{Cayley}} : (a, \mathbf{v}, \boldsymbol{\varphi}, d) \mapsto (d, -\mathbf{v}, -\boldsymbol{\varphi}, a)$
2. Hodge star $\star : (a, \mathbf{v}, \boldsymbol{\varphi}, d) \mapsto (d, \boldsymbol{\varphi}, \mathbf{v}, a)$
3. Graded chirality $\Gamma = (-1)^{\mathrm{deg}} : (a, \mathbf{v}, \boldsymbol{\varphi}, d) \mapsto (a, -\mathbf{v}, \boldsymbol{\varphi}, -d)$
4. Middle-degree exchange operator $E : (a, \mathbf{v}, \boldsymbol{\varphi}, d) \mapsto (a, -\boldsymbol{\varphi}, -\mathbf{v}, d)$

## Key Theorems:
- `cayleyConjugation_sq`: $C^2 = I$
- `hodgeStar_sq`: $\star^2 = I$
- `gradedChirality_sq`: $\Gamma^2 = I$
- `cayley_eq_middleExchange_comp_hodge`: $C_{\mathrm{Cayley}} = E \circ \star = \star \circ E$
- `cayley_ne_hodge_comp_chirality`: $C_{\mathrm{Cayley}} \neq \star \circ \Gamma$
  (proving that Cayley conjugation is NOT simply the composition of Hodge star and chirality).
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge

open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

abbrev Coord := Exterior3Coordinates

/-- The Cayley conjugation operator on graded 1+3+3+1 coordinates:
    (a, v, φ, d) ↦ (d, -v, -φ, a). -/
def cayleyConjugation : Coord →ₗ[ℝ] Coord where
  toFun x := (x.2.2.2, -x.2.1, -x.2.2.1, x.1)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' c x := by
    ext <;> simp

/-- The geometric Hodge star duality mapping ⋀ᵏ ↔ ⋀³⁻ᵏ:
    (a, v, φ, d) ↦ (d, φ, v, a). -/
def hodgeStar : Coord →ₗ[ℝ] Coord where
  toFun x := (x.2.2.2, x.2.2.1, x.2.1, x.1)
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

/-- Graded parity / chirality involution Γ = (-1)^deg:
    (a, v, φ, d) ↦ (a, -v, φ, -d). -/
def gradedChirality : Coord →ₗ[ℝ] Coord where
  toFun x := (x.1, -x.2.1, x.2.2.1, -x.2.2.2)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' c x := by
    ext <;> simp

/-- Middle-degree exchange operator E: swaps Grade 1 (V₃) and Grade 2 (V₃*), with sign flip:
    (a, v, φ, d) ↦ (a, -φ, -v, d). -/
def middleDegreeExchange : Coord →ₗ[ℝ] Coord where
  toFun x := (x.1, -x.2.2.1, -x.2.1, x.2.2.2)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' c x := by
    ext <;> simp

/-- 🏆 THEOREM: Cayley conjugation is involutive: C² = I. -/
theorem cayleyConjugation_sq :
    cayleyConjugation * cayleyConjugation = 1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [cayleyConjugation]

/-- 🏆 THEOREM: Hodge star is involutive: ⋆² = I on ℝ³. -/
theorem hodgeStar_sq :
    hodgeStar * hodgeStar = 1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [hodgeStar]

/-- 🏆 THEOREM: Graded chirality is involutive: Γ² = I. -/
theorem gradedChirality_sq :
    gradedChirality * gradedChirality = 1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [gradedChirality]

/-- 🏆 THEOREM: Exact factorization of Cayley conjugation through Hodge star and Middle Degree Exchange:
    C_Cayley = E ∘ ⋆ = ⋆ ∘ E. -/
theorem cayley_eq_middleExchange_comp_hodge :
    cayleyConjugation = middleDegreeExchange ∘ₗ hodgeStar := by
  apply LinearMap.ext
  intro x
  ext <;> simp [cayleyConjugation, middleDegreeExchange, hodgeStar]

theorem cayley_eq_hodge_comp_middleExchange :
    cayleyConjugation = hodgeStar ∘ₗ middleDegreeExchange := by
  apply LinearMap.ext
  intro x
  ext <;> simp [cayleyConjugation, middleDegreeExchange, hodgeStar]

/-- 🏆 THEOREM: Cayley conjugation is NOT simply ⋆ ∘ Γ (it differs on Grade 0, 1, 2, 3). -/
theorem cayley_ne_hodge_comp_chirality :
    cayleyConjugation ≠ hodgeStar ∘ₗ gradedChirality := by
  intro h
  have h_eval := LinearMap.congr_fun h (0, 0, 0, 1)
  dsimp [cayleyConjugation, hodgeStar, gradedChirality] at h_eval
  have h_first := congrArg Prod.fst h_eval
  norm_num at h_first

end InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge
