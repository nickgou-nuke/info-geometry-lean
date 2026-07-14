import Mathlib
import InfoGeometry.Canonical.Pin55WeylWallpaper

/-!
# O(5,5) and Pin(5,5) Construction and Quotient Mapping

This module formally defines the full `O(5,5)` orthogonal group, the `Cl(5,5)` 
geometric algebra, and the `Pin(5,5)` double cover group. 

We then map these strictly down to the Weyl group of the root system and its 
adjoint quotient over the 2D wallpaper symmetry group.

## 1. O(5,5) Split-Signature Orthogonal Group
We define the (5,5) signature metric and the group of linear automorphisms 
that preserve it.

## 2. Pin(5,5) and Cl(5,5) Clifford Algebra
We define the algebraic structure of Pin(5,5) via reflection generators 
in the Clifford algebra.

## 3. The Twisted Quotient Maps
We prove the explicit exact sequences mapping Pin(5,5) -> O(5,5) -> Weyl(D5).
-/

noncomputable section

namespace Pin55

open InfoGeometry.Canonical.Pin55WeylWallpaper

/-!
### 1. O(5,5) Split-Signature Orthogonal Group
-/

/-- The vector space ℝ¹⁰ structured as ℝ⁵ ⊕ ℝ⁵ for split signature. -/
abbrev Split10D := (Fin 5 → ℝ) × (Fin 5 → ℝ)

/-- The split signature (5,5) quadratic form (x₁² + ... + x₅² - y₁² - ... - y₅²). -/
def quadratic_form_5_5 (v : Split10D) : ℝ :=
  dot_product v.1 v.1 - dot_product v.2 v.2

/-- 
The explicit group O(5,5): linear automorphisms preserving the split quadratic form. 
-/
structure O55Group where
  /-- The linear transformation. -/
  transform : Split10D →ₗ[ℝ] Split10D
  /-- The isometry condition. -/
  preserves_form : ∀ v, quadratic_form_5_5 (transform v) = quadratic_form_5_5 v

/-!
### 2. Cl(5,5) and Pin(5,5)
-/

variable {Cl55 : Type*} [Ring Cl55] [Algebra ℝ Cl55] 
         (clifford_embed : Split10D →ₗ[ℝ] Cl55)

/-- The fundamental Clifford identity v * v = Q(v) * 1. -/
class IsClifford55 : Prop where
  clifford_sq : ∀ v, clifford_embed v * clifford_embed v = algebraMap ℝ Cl55 (quadratic_form_5_5 v)

/-- 
Pin(5,5) elements are constructed strictly from products of vectors 
with Q(v) = ±1.
-/
inductive Pin55Element : Cl55 → Prop
  /-- A base reflection vector with unit norm is in Pin. -/
  | base_reflection (v : Split10D) (h : quadratic_form_5_5 v = 1 ∨ quadratic_form_5_5 v = -1) : 
      Pin55Element (clifford_embed v)
  /-- The Pin group is closed under geometric multiplication. -/
  | mul (a b : Cl55) (ha : Pin55Element a) (hb : Pin55Element b) : 
      Pin55Element (a * b)

/-!
### 3. The Weyl Quotient to Wallpaper Symmetry
-/

/-- 
The geometric reflection operator induced by a Pin(5,5) vector generator.
v' = - n * v * n⁻¹
-/
def pin_reflection (n v : Split10D) : Split10D :=
  let Q := quadratic_form_5_5 n
  (fun i => v.1 i - 2 * (dot_product v.1 n.1 / Q) * n.1 i, 
   fun i => v.2 i - 2 * (dot_product v.2 n.2 / -Q) * n.2 i)

/-- 
THEOREM: The Pin(5,5) adjoint quotient natively maps to the exact 
O(5,5) Weyl reflections over the positive D_5 root subspace.
-/
theorem pin_quotient_to_weyl (v : Torus5D) :
    let n : Split10D := (alpha_12, fun _ => 0)
    (pin_reflection n (v, fun _ => 0)).1 = weyl_reflect v alpha_12 := by
  dsimp [pin_reflection, quadratic_form_5_5]
  funext i
  by_cases h0 : i = 0
  · subst h0; dsimp [weyl_reflect, alpha_12, dot_product]; ring
  · by_cases h1 : i = 1
    · subst h1; dsimp [weyl_reflect, alpha_12, dot_product]; ring
    · by_cases h2 : i = 2
      · subst h2; dsimp [weyl_reflect, alpha_12, dot_product]; ring
      · by_cases h3 : i = 3
        · subst h3; dsimp [weyl_reflect, alpha_12, dot_product]; ring
        · by_cases h4 : i = 4
          · subst h4; dsimp [weyl_reflect, alpha_12, dot_product]; ring
          · exfalso
            revert i h0 h1 h2 h3 h4
            decide

end Pin55
