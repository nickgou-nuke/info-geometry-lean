import Mathlib.Data.ZMod.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Cubic Dickson Invariant and Alternating 3-Form for G₂(2) on 𝔽₂⁷

Formalizes the cubic Dickson polynomial invariant and the alternating trilinear
3-form preserved by the exceptional group `G₂(2) ⊂ GL(7, 𝔽₂)` acting on the
7-dimensional imaginary octonion space `Im(𝕆(𝔽₂)) ≃ 𝔽₂⁷` via the Fano plane.
-/

namespace InfoGeometry.Algebra.Zorn.G2DicksonCubicInvariant

variable {R : Type*} [CommRing R]

/-! =========================================================================
    1. Fano Plane Triads and 3x3 Determinant Kernel
    ========================================================================= -/

/--
The 7 oriented collinear triads of the Fano plane `ℙ²(𝔽₂)`, encoding the
octonionic multiplication rules `e_i * e_j = e_k` on `Im(𝕆)`.
-/
def fanoTriads : List (Fin 7 × Fin 7 × Fin 7) :=
  [ (0, 1, 3),
    (1, 2, 4),
    (2, 3, 5),
    (3, 4, 6),
    (4, 5, 0),
    (5, 6, 1),
    (6, 0, 2) ]

/--
Sub-determinant of three vectors `(u, v, w)` restricted to the coordinate triad `(i, j, k)`:
  `det₃(u, v, w; i, j, k) = uᵢ(vⱼ wₖ - vₖ wⱼ) - uⱼ(vᵢ wₖ - vₖ wᵢ) + uₖ(vᵢ wⱼ - vⱼ wᵢ)`
-/
def det3 (u v w : Fin 7 → R) (i j k : Fin 7) : R :=
  u i * (v j * w k - v k * w j) -
  u j * (v i * w k - v k * w i) +
  u k * (v i * w j - v j * w i)

/-! =========================================================================
    2. Cubic Dickson Form and Alternating Trilinear 3-Form
    ========================================================================= -/

/--
The cubic Dickson polynomial invariant on `𝔽₂⁷`:
  `𝒟(x) = ∑_{(i,j,k) ∈ Fano} xᵢ xⱼ xₖ`
-/
def dicksonCubicForm (x : Fin 7 → R) : R :=
  x 0 * x 1 * x 3 +
  x 1 * x 2 * x 4 +
  x 2 * x 3 * x 5 +
  x 3 * x 4 * x 6 +
  x 4 * x 5 * x 0 +
  x 5 * x 6 * x 1 +
  x 6 * x 0 * x 2

/--
The alternating trilinear 3-form `Φ(u, v, w)` on `𝔽₂⁷`:
  `Φ(u, v, w) = ∑_{(i,j,k) ∈ Fano} det₃(u, v, w; i, j, k)`
-/
def dicksonTrilinear (u v w : Fin 7 → R) : R :=
  det3 u v w 0 1 3 +
  det3 u v w 1 2 4 +
  det3 u v w 2 3 5 +
  det3 u v w 3 4 6 +
  det3 u v w 4 5 0 +
  det3 u v w 5 6 1 +
  det3 u v w 6 0 2

/-! =========================================================================
    3. Multilinearity and Alternating Properties
    ========================================================================= -/

/--
THEOREM: Left linearity under vector addition:
  `Φ(u₁ + u₂, v, w) = Φ(u₁, v, w) + Φ(u₂, v, w)`
-/
theorem dicksonTrilinear_add_left (u₁ u₂ v w : Fin 7 → R) :
    dicksonTrilinear (u₁ + u₂) v w =
      dicksonTrilinear u₁ v w + dicksonTrilinear u₂ v w := by
  dsimp [dicksonTrilinear, det3]
  ring

/--
THEOREM: Middle linearity under vector addition:
  `Φ(u, v₁ + v₂, w) = Φ(u, v₁, w) + Φ(u, v₂, w)`
-/
theorem dicksonTrilinear_add_mid (u v₁ v₂ w : Fin 7 → R) :
    dicksonTrilinear u (v₁ + v₂) w =
      dicksonTrilinear u v₁ w + dicksonTrilinear u v₂ w := by
  dsimp [dicksonTrilinear, det3]
  ring

/--
THEOREM: Right linearity under vector addition:
  `Φ(u, v, w₁ + w₂) = Φ(u, v, w₁) + Φ(u, v, w₂)`
-/
theorem dicksonTrilinear_add_right (u v w₁ w₂ : Fin 7 → R) :
    dicksonTrilinear u v (w₁ + w₂) =
      dicksonTrilinear u v w₁ + dicksonTrilinear u v w₂ := by
  dsimp [dicksonTrilinear, det3]
  ring

/--
THEOREM (Alternating Property on Slots 1 & 2):
  `Φ(u, u, w) = 0`
-/
theorem dicksonTrilinear_self_12 (u w : Fin 7 → R) :
    dicksonTrilinear u u w = 0 := by
  dsimp [dicksonTrilinear, det3]
  ring

/--
THEOREM (Alternating Property on Slots 2 & 3):
  `Φ(u, v, v) = 0`
-/
theorem dicksonTrilinear_self_23 (u v : Fin 7 → R) :
    dicksonTrilinear u v v = 0 := by
  dsimp [dicksonTrilinear, det3]
  ring

/--
THEOREM (Alternating Property on Slots 1 & 3):
  `Φ(u, v, u) = 0`
-/
theorem dicksonTrilinear_self_13 (u v : Fin 7 → R) :
    dicksonTrilinear u v u = 0 := by
  dsimp [dicksonTrilinear, det3]
  ring

/--
THEOREM (Skew-Symmetry under Swap 1 ↔ 2):
  `Φ(v, u, w) = - Φ(u, v, w)`
-/
theorem dicksonTrilinear_skew_12 (u v w : Fin 7 → R) :
    dicksonTrilinear v u w = - dicksonTrilinear u v w := by
  dsimp [dicksonTrilinear, det3]
  ring

/--
THEOREM (Skew-Symmetry under Swap 2 ↔ 3):
  `Φ(u, w, v) = - Φ(u, v, w)`
-/
theorem dicksonTrilinear_skew_23 (u v w : Fin 7 → R) :
    dicksonTrilinear u w v = - dicksonTrilinear u v w := by
  dsimp [dicksonTrilinear, det3]
  ring

/-! =========================================================================
    4. G₂(2) Automorphism Group Action and Form Preservation
    ========================================================================= -/

/-- Predicate for linear transformations on `𝔽₂⁷` preserving the alternating 3-form. -/
def PreservesDicksonTrilinear (g : (Fin 7 → R) → (Fin 7 → R)) : Prop :=
  ∀ u v w, dicksonTrilinear (g u) (g v) (g w) = dicksonTrilinear u v w

/--
THEOREM: The identity automorphism unconditionally preserves the Dickson 3-form.
-/
theorem id_preserves_dicksonTrilinear :
    PreservesDicksonTrilinear (fun x => x : (Fin 7 → R) → (Fin 7 → R)) := by
  intro u v w
  rfl

/--
THEOREM: Composition of 3-form preserving automorphisms preserves the 3-form.
-/
theorem comp_preserves_dicksonTrilinear
    (g₁ g₂ : (Fin 7 → R) → (Fin 7 → R))
    (h₁ : PreservesDicksonTrilinear g₁)
    (h₂ : PreservesDicksonTrilinear g₂) :
    PreservesDicksonTrilinear (g₁ ∘ g₂) := by
  intro u v w
  dsimp
  rw [h₁, h₂]

theorem zmod2_neg (x : ZMod 2) : -x = x := by
  fin_cases x <;> decide

/--
COROLLARY (Characteristic 2 Symmetry Collapse):
Over `𝔽₂` (where `-1 = 1`), the alternating 3-form is completely symmetric
under all permutations of arguments:
  `Φ(u, v, w) = Φ(v, u, w) = Φ(u, w, v)`
-/
theorem dicksonTrilinear_char2_symm (u v w : Fin 7 → ZMod 2) :
    dicksonTrilinear v u w = dicksonTrilinear u v w ∧
    dicksonTrilinear u w v = dicksonTrilinear u v w := by
  constructor
  · have h := dicksonTrilinear_skew_12 (R := ZMod 2) u v w
    rw [h, zmod2_neg]
  · have h := dicksonTrilinear_skew_23 (R := ZMod 2) u v w
    rw [h, zmod2_neg]

end InfoGeometry.Algebra.Zorn.G2DicksonCubicInvariant
