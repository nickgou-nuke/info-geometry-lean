import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Non-Degenerate Split Quadratic Form and G₂(2) Compatibility on 𝔽₂⁷

Formalizes the non-degenerate quadratic form `Q(x)` and its associated symmetric
bilinear polar form `B(u, v)` on the 7-dimensional imaginary octonion space `𝔽₂⁷`.
Proves non-degeneracy, pairing duality with the Fano cross product `u × v`,
orthogonality to the Dickson 3-form `Φ(u, v, w)`, and simultaneous `G₂(2)` invariance.
-/

namespace InfoGeometry.Algebra.Zorn.G2QuadraticCompatibility

variable {R : Type*} [CommRing R]

/-! =========================================================================
    1. Quadratic Form, Polar Bilinear Form, and Basis Vectors
    ========================================================================= -/

/--
The canonical non-degenerate quadratic form on the 7-dimensional space:
  `Q(x) = ∑_{i=0}^6 xᵢ²`
-/
def quadForm (x : Fin 7 → R) : R :=
  (x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 + (x 4)^2 + (x 5)^2 + (x 6)^2

/--
The symmetric bilinear polar form:
  `B(u, v) = ∑_{i=0}^6 uᵢ vᵢ`
-/
def bilinearForm (u v : Fin 7 → R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4 + u 5 * v 5 + u 6 * v 6

/-- Standard basis vectors `eₖ` for `k ∈ Fin 7`. -/
def basisVec (k : Fin 7) : Fin 7 → R
  | 0 => if k = 0 then 1 else 0
  | 1 => if k = 1 then 1 else 0
  | 2 => if k = 2 then 1 else 0
  | 3 => if k = 3 then 1 else 0
  | 4 => if k = 4 then 1 else 0
  | 5 => if k = 5 then 1 else 0
  | 6 => if k = 6 then 1 else 0

/--
THEOREM (Polarization Identity):
  `Q(u + v) = Q(u) + Q(v) + 2 • B(u, v)`
-/
theorem quadForm_add (u v : Fin 7 → R) :
    quadForm (u + v) = quadForm u + quadForm v + 2 * bilinearForm u v := by
  dsimp [quadForm, bilinearForm]
  ring

/--
THEOREM: The polar form `B(u, v)` is strictly symmetric:
  `B(u, v) = B(v, u)`
-/
theorem bilinearForm_symm (u v : Fin 7 → R) :
    bilinearForm u v = bilinearForm v u := by
  dsimp [bilinearForm]
  ring

/--
THEOREM: Left linearity under vector addition:
  `B(u₁ + u₂, v) = B(u₁, v) + B(u₂, v)`
-/
theorem bilinearForm_add_left (u₁ u₂ v : Fin 7 → R) :
    bilinearForm (u₁ + u₂) v = bilinearForm u₁ v + bilinearForm u₂ v := by
  dsimp [bilinearForm]
  ring

/--
LEMMA: Sifting property of the standard basis vectors:
  `B(eₖ, u) = uₖ`
-/
theorem bilinearForm_basisVec (u : Fin 7 → R) (k : Fin 7) :
    bilinearForm (basisVec k) u = u k := by
  fin_cases k
  · dsimp [bilinearForm, basisVec]; ring
  · dsimp [bilinearForm, basisVec]; ring
  · dsimp [bilinearForm, basisVec]; ring
  · dsimp [bilinearForm, basisVec]; ring
  · dsimp [bilinearForm, basisVec]; ring
  · dsimp [bilinearForm, basisVec]; ring
  · dsimp [bilinearForm, basisVec]; ring

/--
THEOREM (Non-Degeneracy of the Bilinear Polar Form):
If `B(v, u) = 0` for all test vectors `v`, then `u = 0`.
-/
theorem bilinearForm_nondegenerate (u : Fin 7 → R)
    (h : ∀ v, bilinearForm v u = 0) : u = 0 := by
  funext k
  have h_k := h (basisVec k)
  rw [bilinearForm_basisVec] at h_k
  exact h_k

/-! =========================================================================
    2. Fano Cross Product and Dickson Trilinear Form
    ========================================================================= -/

/--
The non-associative Fano cross product `u × v` on `Im(𝕆)` defined via the
oriented triads of `ℙ²(𝔽₂)`:
-/
def crossProd (u v : Fin 7 → R) : Fin 7 → R
  | 0 => (u 1 * v 3 - u 3 * v 1) + (u 4 * v 5 - u 5 * v 4) + (u 2 * v 6 - u 6 * v 2)
  | 1 => (u 3 * v 0 - u 0 * v 3) + (u 2 * v 4 - u 4 * v 2) + (u 5 * v 6 - u 6 * v 5)
  | 2 => (u 4 * v 1 - u 1 * v 4) + (u 3 * v 5 - u 5 * v 3) + (u 6 * v 0 - u 0 * v 6)
  | 3 => (u 0 * v 1 - u 1 * v 0) + (u 5 * v 2 - u 2 * v 5) + (u 4 * v 6 - u 6 * v 4)
  | 4 => (u 1 * v 2 - u 2 * v 1) + (u 6 * v 3 - u 3 * v 6) + (u 5 * v 0 - u 0 * v 5)
  | 5 => (u 2 * v 3 - u 3 * v 2) + (u 0 * v 4 - u 4 * v 0) + (u 6 * v 1 - u 1 * v 6)
  | 6 => (u 3 * v 4 - u 4 * v 3) + (u 1 * v 5 - u 5 * v 1) + (u 0 * v 2 - u 2 * v 0)

/-- Sub-determinant of three vectors restricted to a Fano triad. -/
def det3 (u v w : Fin 7 → R) (i j k : Fin 7) : R :=
  u i * (v j * w k - v k * w j) -
  u j * (v i * w k - v k * w i) +
  u k * (v i * w j - v j * w i)

/-- Alternating trilinear Dickson 3-form `Φ(u, v, w)`. -/
def dicksonTrilinear (u v w : Fin 7 → R) : R :=
  det3 u v w 0 1 3 +
  det3 u v w 1 2 4 +
  det3 u v w 2 3 5 +
  det3 u v w 3 4 6 +
  det3 u v w 4 5 0 +
  det3 u v w 5 6 1 +
  det3 u v w 6 0 2

/-! =========================================================================
    3. Compatibility Theorems: Duality, Orthogonality, and Skew-Symmetry
    ========================================================================= -/

/--
THEOREM (Cross Product Skew-Symmetry):
  `v × u = - (u × v)`
-/
theorem crossProd_skew (u v : Fin 7 → R) :
    crossProd v u = - crossProd u v := by
  funext i
  fin_cases i <;> { dsimp [crossProd]; ring }

/--
MAIN THEOREM (Metric Pairing Duality):
The bilinear pairing of the cross product with a third vector evaluates identically
to the alternating Dickson 3-form:
  `B(u × v, w) = Φ(u, v, w)`
-/
theorem bilinearForm_crossProd_eq_dicksonTrilinear (u v w : Fin 7 → R) :
    bilinearForm (crossProd u v) w = dicksonTrilinear u v w := by
  dsimp [bilinearForm, crossProd, dicksonTrilinear, det3]
  ring

/--
THEOREM (Left Orthogonality):
The cross product `u × v` is orthogonal to `u` under the metric:
  `B(u × v, u) = 0`
-/
theorem crossProd_orthogonal_left (u v : Fin 7 → R) :
    bilinearForm (crossProd u v) u = 0 := by
  rw [bilinearForm_crossProd_eq_dicksonTrilinear]
  dsimp [dicksonTrilinear, det3]
  ring

/--
THEOREM (Right Orthogonality):
The cross product `u × v` is orthogonal to `v` under the metric:
  `B(u × v, v) = 0`
-/
theorem crossProd_orthogonal_right (u v : Fin 7 → R) :
    bilinearForm (crossProd u v) v = 0 := by
  rw [bilinearForm_crossProd_eq_dicksonTrilinear]
  dsimp [dicksonTrilinear, det3]
  ring

/-! =========================================================================
    4. G₂(2) Automorphism Group Invariance
    ========================================================================= -/

/-- Predicate for linear transformations preserving the bilinear metric `B(u, v)`. -/
def PreservesBilinear (g : (Fin 7 → R) → (Fin 7 → R)) : Prop :=
  ∀ u v, bilinearForm (g u) (g v) = bilinearForm u v

/-- Predicate for linear transformations preserving the Dickson 3-form `Φ(u, v, w)`. -/
def PreservesDicksonTrilinear (g : (Fin 7 → R) → (Fin 7 → R)) : Prop :=
  ∀ u v w, dicksonTrilinear (g u) (g v) (g w) = dicksonTrilinear u v w

/--
The exceptional group `G₂(2)` is the simultaneous stabilizer of the metric
and the alternating 3-form:
  `G₂(2) = Stab_{GL(7, 𝔽₂)}(B, Φ)`
-/
def IsG2Automorphism (g : (Fin 7 → R) → (Fin 7 → R)) : Prop :=
  PreservesBilinear g ∧ PreservesDicksonTrilinear g

/--
THEOREM: Every `G₂(2)` automorphism unconditionally preserves the quadratic form `Q(x)`:
  `Q(g(x)) = Q(x)`
-/
theorem g2_preserves_quadratic (g : (Fin 7 → R) → (Fin 7 → R))
    (h : IsG2Automorphism g) (x : Fin 7 → R) :
    quadForm (g x) = quadForm x := by
  dsimp [quadForm]
  have h_bilin := h.1 x x
  dsimp [bilinearForm] at h_bilin
  calc
    (g x 0)^2 + (g x 1)^2 + (g x 2)^2 + (g x 3)^2 + (g x 4)^2 + (g x 5)^2 + (g x 6)^2
      = g x 0 * g x 0 + g x 1 * g x 1 + g x 2 * g x 2 + g x 3 * g x 3 +
        g x 4 * g x 4 + g x 5 * g x 5 + g x 6 * g x 6 := by ring
    _ = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 +
        x 4 * x 4 + x 5 * x 5 + x 6 * x 6 := h_bilin
    _ = (x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 + (x 4)^2 + (x 5)^2 + (x 6)^2 := by ring

/--
MAIN THEOREM (Equivariance of Fano Cross Product under G₂(2)):
Every bijective `G₂(2)` automorphism commutes with the octonionic cross product:
  `g(u × v) = g(u) × g(v)`
-/
theorem g2_crossProd_equivariant
    (g : (Fin 7 → R) → (Fin 7 → R))
    (g_inv : (Fin 7 → R) → (Fin 7 → R))
    (h_inv : ∀ v, g (g_inv v) = v)
    (h_aut : IsG2Automorphism g)
    (u v : Fin 7 → R) :
    g (crossProd u v) = crossProd (g u) (g v) := by
  funext k
  have h_k : (g (crossProd u v)) k = bilinearForm (basisVec k) (g (crossProd u v)) :=
    (bilinearForm_basisVec (g (crossProd u v)) k).symm
  rw [h_k]
  have h_pairing : bilinearForm (g_inv (basisVec k)) (crossProd u v) =
      bilinearForm (basisVec k) (g (crossProd u v)) := by
    calc
      bilinearForm (g_inv (basisVec k)) (crossProd u v)
        = bilinearForm (g (g_inv (basisVec k))) (g (crossProd u v)) := by rw [← h_aut.1]
      _ = bilinearForm (basisVec k) (g (crossProd u v)) := by rw [h_inv]
  rw [← h_pairing]
  rw [bilinearForm_symm (g_inv (basisVec k)) (crossProd u v)]
  rw [bilinearForm_crossProd_eq_dicksonTrilinear]
  calc
    dicksonTrilinear u v (g_inv (basisVec k))
      = dicksonTrilinear (g u) (g v) (g (g_inv (basisVec k))) := by rw [← h_aut.2]
    _ = dicksonTrilinear (g u) (g v) (basisVec k) := by rw [h_inv]
    _ = bilinearForm (crossProd (g u) (g v)) (basisVec k) := by
        rw [bilinearForm_crossProd_eq_dicksonTrilinear]
    _ = bilinearForm (basisVec k) (crossProd (g u) (g v)) := by rw [bilinearForm_symm]
    _ = (crossProd (g u) (g v)) k := by rw [bilinearForm_basisVec]

end InfoGeometry.Algebra.Zorn.G2QuadraticCompatibility
