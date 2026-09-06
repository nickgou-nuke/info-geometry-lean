import Mathlib

/-!
# Convex algebraic duality anchors

Finite algebraic lemmas inspired by Rostalski--Sturmfels,
"Dualities in Convex Algebraic Geometry" (arXiv:1006.4894):

* spectrahedra as affine slices of PSD cones, here modeled by a diagonal `2×2`
  slice / simplex;
* convex closure of that spectrahedron;
* projective duality for a conic via the gradient/tangent hyperplane;
* scalar KKT/Lagrange stationarity.
-/

noncomputable section

namespace ConvexAlgebraicDuality

open Matrix

/-! ## Toy spectrahedron: diagonal PSD simplex -/

/-- Diagonal `2×2` matrix with entries `x,y`. -/
def diag2 (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x, 0;
     0, y]

/-- The diagonal PSD cone for the toy `2×2` slice as a rigorous `ConvexCone`. -/
def diagPSD2Cone : ConvexCone ℝ (ℝ × ℝ) where
  carrier := { p | 0 ≤ p.1 ∧ 0 ≤ p.2 }
  smul_mem' c hc p hp := by
    constructor
    · exact mul_nonneg hc.le hp.1
    · exact mul_nonneg hc.le hp.2
  add_mem' x hx y hy := ⟨add_nonneg hx.1 hy.1, add_nonneg hx.2 hy.2⟩

/-- The diagonal PSD condition for the toy `2×2` slice. -/
def DiagPSD2 (x y : ℝ) : Prop :=
  (x, y) ∈ diagPSD2Cone

/-- The trace-one diagonal spectrahedron: the one-simplex. -/
def TraceOneDiagSpectrahedron (x y : ℝ) : Prop :=
  DiagPSD2 x y ∧ x + y = 1

/-- Convex combination of two points in the trace-one diagonal spectrahedron. -/
theorem traceOneDiag_convex {x₁ y₁ x₂ y₂ t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h₁ : TraceOneDiagSpectrahedron x₁ y₁)
    (h₂ : TraceOneDiagSpectrahedron x₂ y₂) :
    TraceOneDiagSpectrahedron (t * x₁ + (1 - t) * x₂)
      (t * y₁ + (1 - t) * y₂) := by
  rcases h₁ with ⟨⟨hx₁, hy₁⟩, hsum₁⟩
  rcases h₂ with ⟨⟨hx₂, hy₂⟩, hsum₂⟩
  constructor
  · constructor
    · have ht1' : 0 ≤ 1 - t := by linarith
      have htx₁ : 0 ≤ t * x₁ := mul_nonneg ht0 hx₁
      have htx₂ : 0 ≤ (1 - t) * x₂ := mul_nonneg ht1' hx₂
      linarith
    · have ht1' : 0 ≤ 1 - t := by linarith
      have hty₁ : 0 ≤ t * y₁ := mul_nonneg ht0 hy₁
      have hty₂ : 0 ≤ (1 - t) * y₂ := mul_nonneg ht1' hy₂
      linarith
  · nlinarith

/-- The two Penrose frequency weights define a trace-one diagonal spectrahedron
point when supplied as nonnegative data. -/
theorem frequencies_form_trace_one_diag {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b = 1) :
    TraceOneDiagSpectrahedron a b :=
  ⟨⟨ha, hb⟩, hsum⟩

/-! ## Projective duality anchor: conic gradient gives tangent hyperplane -/

/-- Homogeneous conic/light-cone equation `x²+y²-z²`. -/
def conicF (x y z : ℝ) : ℝ := x^2 + y^2 - z^2

/-- Gradient/projective-dual covector of the conic. -/
def conicGrad (x y z : ℝ) : Fin 3 → ℝ
  | 0 => 2*x
  | 1 => 2*y
  | 2 => -2*z

/-- Homogeneous dot product. -/
def dot3 (u v : Fin 3 → ℝ) : ℝ := ∑ i, u i * v i

/-- Point vector. -/
def point3 (x y z : ℝ) : Fin 3 → ℝ
  | 0 => x
  | 1 => y
  | 2 => z

/-- Euler identity for the quadratic conic: `<∇F(p),p>=2F(p)`. -/
theorem conic_euler (x y z : ℝ) :
    dot3 (conicGrad x y z) (point3 x y z) = 2 * conicF x y z := by
  simp [dot3, conicGrad, point3, conicF, Fin.sum_univ_three]
  ring

/-- If `p` lies on the conic, the gradient covector is tangent/projectively dual:
its pairing with `p` vanishes. -/
theorem conic_tangent_hyperplane {x y z : ℝ} (h : conicF x y z = 0) :
    dot3 (conicGrad x y z) (point3 x y z) = 0 := by
  rw [conic_euler, h]
  ring

/-! ## KKT / Lagrange stationarity anchor -/

/-- Scalar quadratic objective. -/
def quadObj (c x : ℝ) : ℝ := (x - c)^2

/-- Lagrangian for constraint `x=r`: `L=(x-c)^2+λ(x-r)`. -/
def lagrangian (c r x lam : ℝ) : ℝ :=
  (x - c)^2 + lam * (x - r)

/-- Algebraic stationarity equation for the scalar KKT example. -/
def Stationary (c x lam : ℝ) : Prop :=
  2 * (x - c) + lam = 0

/-- At the feasible point `x=r`, choose `λ=-2(r-c)` to satisfy stationarity. -/
theorem scalar_kkt_stationary (c r : ℝ) :
    Stationary c r (-2 * (r - c)) := by
  unfold Stationary
  ring

/-- Complementary slackness toy equation. -/
def ComplementarySlackness (lam g : ℝ) : Prop := lam * g = 0

@[simp] theorem complementary_slackness_zero_constraint (lam : ℝ) :
    ComplementarySlackness lam 0 := by
  simp [ComplementarySlackness]


theorem convex_algebraic_duality_anchors :
    (∀ x₁ y₁ x₂ y₂ t : ℝ, 0 ≤ t → t ≤ 1 →
      TraceOneDiagSpectrahedron x₁ y₁ → TraceOneDiagSpectrahedron x₂ y₂ →
      TraceOneDiagSpectrahedron (t * x₁ + (1 - t) * x₂)
        (t * y₁ + (1 - t) * y₂)) ∧
    (∀ x y z : ℝ, conicF x y z = 0 → dot3 (conicGrad x y z) (point3 x y z) = 0) ∧
    (∀ c r : ℝ, Stationary c r (-2 * (r - c))) := by
  constructor
  · intro x₁ y₁ x₂ y₂ t ht0 ht1 h₁ h₂
    exact traceOneDiag_convex ht0 ht1 h₁ h₂
  · constructor
    · intro x y z h
      exact conic_tangent_hyperplane h
    · intro c r
      exact scalar_kkt_stationary c r

end ConvexAlgebraicDuality
