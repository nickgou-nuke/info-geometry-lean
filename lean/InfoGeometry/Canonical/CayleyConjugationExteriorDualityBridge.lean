import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

/-!
# Cayley Conjugation vs Exterior Duality Operator Bridge

This module formalizes the exact operator-level decomposition of Cayley conjugation
$C_{\mathrm{Cayley}}$ on the graded $(1 + 3 + 3 + 1)$ exterior coordinate carrier:
$$C_{\mathrm{Cayley}}(a, v, \varphi, d) = (d, -v, -\varphi, a).$$

## Key Structural Theorems:
1. **Scalar Swap $\sigma_{\mathrm{scalar}}$**: swaps degrees 0 and 3 ($\Lambda^0 \leftrightarrow \Lambda^3$),
   preserving middle degrees ($\sigma_{\mathrm{scalar}}(a, v, \varphi, d) = (d, v, \varphi, a)$).
2. **Middle Sign Flip $\mu_{\mathrm{mid}}$**: flips the sign of degrees 1 and 2,
   leaving scalars fixed ($\mu_{\mathrm{mid}}(a, v, \varphi, d) = (a, -v, -\varphi, d)$).
3. **Canonical Factorization**:
   $$C_{\mathrm{Cayley}} = \sigma_{\mathrm{scalar}} \circ \mu_{\mathrm{mid}} = \mu_{\mathrm{mid}} \circ \sigma_{\mathrm{scalar}}.$$
4. **Hodge Star $\star$ Factorization**:
   $$\star = \sigma_{\mathrm{scalar}} \circ \tau_{\mathrm{mid}} = \tau_{\mathrm{mid}} \circ \sigma_{\mathrm{scalar}},$$
   where $\tau_{\mathrm{mid}}(a, v, \varphi, d) = (a, \varphi, v, d)$ is the vector-covector exchange.
5. **Bridge between Cayley Conjugation and Hodge Star**:
   $$C_{\mathrm{Cayley}} = \star \circ \Xi_{\mathrm{mid}} = \Xi_{\mathrm{mid}} \circ \star,$$
   where $\Xi_{\mathrm{mid}} := \tau_{\mathrm{mid}} \circ \mu_{\mathrm{mid}} = (a, -\varphi, -v, d)$ is the
   middle-degree exchange-flip operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge

open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

abbrev Coord := Exterior3Coordinates -- ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) × ℝ
abbrev CoordEnd := Module.End ℝ Coord

/-- Cayley conjugation on the (1 + 3 + 3 + 1) coordinate carrier:
    (a, v, φ, d) ↦ (d, -v, -φ, a). -/
def cayleyConj : CoordEnd where
  toFun x := (x.2.2.2, -x.2.1, -x.2.2.1, x.1)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' c x := by ext <;> simp

@[simp] theorem cayleyConj_apply (x : Coord) :
    cayleyConj x = (x.2.2.2, -x.2.1, -x.2.2.1, x.1) := rfl

/-- 🏆 THEOREM: Cayley conjugation is an involution: C_Cayley² = I. -/
theorem cayleyConj_sq : cayleyConj * cayleyConj = 1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp

/-- Scalar exchange involution: σ_scalar(a, v, φ, d) = (d, v, φ, a). -/
def scalarExchange : CoordEnd where
  toFun x := (x.2.2.2, x.2.1, x.2.2.1, x.1)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp] theorem scalarExchange_apply (x : Coord) :
    scalarExchange x = (x.2.2.2, x.2.1, x.2.2.1, x.1) := rfl

theorem scalarExchange_sq : scalarExchange * scalarExchange = 1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp

/-- Middle-degree sign flip / Krein fundamental symmetry:
    η(a, v, φ, d) = (a, -v, -φ, d) = diag(+1, -I₃, -I₃, +1). -/
def middleSignFlip : CoordEnd where
  toFun x := (x.1, -x.2.1, -x.2.2.1, x.2.2.2)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' c x := by ext <;> simp

@[simp] theorem middleSignFlip_apply (x : Coord) :
    middleSignFlip x = (x.1, -x.2.1, -x.2.2.1, x.2.2.2) := rfl

theorem middleSignFlip_sq : middleSignFlip * middleSignFlip = 1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp

/-- The longitudinal/transverse grading carried by the middle-degree sign flip.

This is only an involution.  No Krein form or fundamental-symmetry structure
is asserted in this coordinate owner. -/
abbrev longitudinalTransverseGrading : CoordEnd := middleSignFlip

/-- 🏆 THEOREM: Cayley conjugation factorizes into scalar exchange and middle sign flip / Krein symmetry:
    C_Cayley = σ_scalar ∘ η = η ∘ σ_scalar. -/
theorem cayleyConj_eq_scalarExchange_mul_middleSignFlip :
    cayleyConj = scalarExchange * middleSignFlip := by
  apply LinearMap.ext
  intro x
  ext <;> simp

theorem cayleyConj_eq_middleSignFlip_mul_scalarExchange :
    cayleyConj = middleSignFlip * scalarExchange := by
  apply LinearMap.ext
  intro x
  ext <;> simp

theorem cayleyConj_eq_scalarExchange_mul_longitudinalTransverseGrading :
    cayleyConj = scalarExchange * longitudinalTransverseGrading :=
  cayleyConj_eq_scalarExchange_mul_middleSignFlip

theorem cayleyConj_eq_longitudinalTransverseGrading_mul_scalarExchange :
    cayleyConj = longitudinalTransverseGrading * scalarExchange :=
  cayleyConj_eq_middleSignFlip_mul_scalarExchange

/-- Chiral grading: Γ(a, v, φ, d) = (a, -v, φ, -d). -/
def chiralGrading : CoordEnd where
  toFun x := (x.1, -x.2.1, x.2.2.1, -x.2.2.2)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' c x := by ext <;> simp

@[simp] theorem chiralGrading_apply (x : Coord) :
    chiralGrading x = (x.1, -x.2.1, x.2.2.1, -x.2.2.2) := rfl

theorem chiralGrading_sq : chiralGrading * chiralGrading = 1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp

/-- Canonical Hodge duality on the coordinate carrier:
    ⋆(a, v, φ, d) = (d, φ, v, a). -/
def hodgeStar : CoordEnd where
  toFun x := (x.2.2.2, x.2.2.1, x.2.1, x.1)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp] theorem hodgeStar_apply (x : Coord) :
    hodgeStar x = (x.2.2.2, x.2.2.1, x.2.1, x.1) := rfl

theorem hodgeStar_sq : hodgeStar * hodgeStar = 1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp

/-- In odd exterior dimension, Hodge duality is odd for degree parity. -/
theorem chiralGrading_anticommutes_hodgeStar :
    chiralGrading * hodgeStar = -(hodgeStar * chiralGrading) := by
  apply LinearMap.ext
  intro x
  ext <;> simp [chiralGrading, hodgeStar]

/-- Middle exchange operator:
    τ_mid(a, v, φ, d) = (a, φ, v, d). -/
def middleExchange : CoordEnd where
  toFun x := (x.1, x.2.2.1, x.2.1, x.2.2.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp] theorem middleExchange_apply (x : Coord) :
    middleExchange x = (x.1, x.2.2.1, x.2.1, x.2.2.2) := rfl

theorem middleExchange_sq : middleExchange * middleExchange = 1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp

/-- 🏆 THEOREM: Hodge duality factorizes through scalar exchange and middle exchange:
    ⋆ = σ_scalar ∘ τ_mid = τ_mid ∘ σ_scalar. -/
theorem hodgeStar_eq_scalarExchange_mul_middleExchange :
    hodgeStar = scalarExchange * middleExchange := by
  apply LinearMap.ext
  intro x
  ext <;> simp

theorem hodgeStar_eq_middleExchange_mul_scalarExchange :
    hodgeStar = middleExchange * scalarExchange := by
  apply LinearMap.ext
  intro x
  ext <;> simp

/-- Middle exchange and flip operator:
    Ξ_mid(a, v, φ, d) = (a, -φ, -v, d). -/
def middleExchangeFlip : CoordEnd where
  toFun x := (x.1, -x.2.2.1, -x.2.1, x.2.2.2)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' c x := by ext <;> simp

@[simp] theorem middleExchangeFlip_apply (x : Coord) :
    middleExchangeFlip x = (x.1, -x.2.2.1, -x.2.1, x.2.2.2) := rfl

theorem middleExchangeFlip_sq : middleExchangeFlip * middleExchangeFlip = 1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp

/-- 🏆 THEOREM: Ξ_mid factorizes into middle exchange and middle sign flip:
    Ξ_mid = τ_mid ∘ μ_mid = μ_mid ∘ τ_mid. -/
theorem middleExchangeFlip_eq_middleExchange_mul_middleSignFlip :
    middleExchangeFlip = middleExchange * middleSignFlip := by
  apply LinearMap.ext
  intro x
  ext <;> simp

theorem middleExchangeFlip_eq_middleSignFlip_mul_middleExchange :
    middleExchangeFlip = middleSignFlip * middleExchange := by
  apply LinearMap.ext
  intro x
  ext <;> simp

/-- 🏆 THEOREM: Cayley conjugation factorizes through Hodge duality:
    C_Cayley = ⋆ ∘ Ξ_mid = Ξ_mid ∘ ⋆. -/
theorem cayleyConj_eq_hodgeStar_mul_middleExchangeFlip :
    cayleyConj = hodgeStar * middleExchangeFlip := by
  apply LinearMap.ext
  intro x
  ext <;> simp

theorem cayleyConj_eq_middleExchangeFlip_mul_hodgeStar :
    cayleyConj = middleExchangeFlip * hodgeStar := by
  apply LinearMap.ext
  intro x
  ext <;> simp

/-- Commutation: σ_scalar and μ_mid strictly commute. -/
theorem scalarExchange_commutes_middleSignFlip :
    scalarExchange * middleSignFlip = middleSignFlip * scalarExchange := by
  rw [← cayleyConj_eq_scalarExchange_mul_middleSignFlip,
      ← cayleyConj_eq_middleSignFlip_mul_scalarExchange]

/-- Commutation: ⋆ and Ξ_mid strictly commute. -/
theorem hodgeStar_commutes_middleExchangeFlip :
    hodgeStar * middleExchangeFlip = middleExchangeFlip * hodgeStar := by
  rw [← cayleyConj_eq_hodgeStar_mul_middleExchangeFlip,
      ← cayleyConj_eq_middleExchangeFlip_mul_hodgeStar]

/-- Commutation: τ_mid and μ_mid strictly commute. -/
theorem middleExchange_commutes_middleSignFlip :
    middleExchange * middleSignFlip = middleSignFlip * middleExchange := by
  rw [← middleExchangeFlip_eq_middleExchange_mul_middleSignFlip,
      ← middleExchangeFlip_eq_middleSignFlip_mul_middleExchange]

end InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge
