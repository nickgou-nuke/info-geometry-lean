import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.MD003IsomorphicRepresentations

/-!
# Repaired MD 004: finite geometric structures

Source: `github-nick:nickgou-nuke/MD`, file `004.md`.

Chapter 4 discusses hyperkähler geometry of the Hermitian `2 × 2` matrix
coordinate space and Kähler/symplectic geometry of the ambient `M₂(ℂ)`.  The
full manuscript uses smooth-manifold, Levi-Civita, curvature, Ricci, and
closed-form language.  This file extracts the finite algebraic skeleton:

* the three real coordinate complex structures `I,J,K` square to `-1` and obey
  quaternion multiplication;
* each preserves the Euclidean coordinate metric;
* the associated fundamental forms `ω_A(X,Y)=g(AX,Y)` are skew-symmetric and
  nondegenerate in the finite coordinate sense;
* the ambient `ℂ⁴ ≃ ℝ⁸` standard complex structure squares to `-1`, preserves
  the Euclidean metric, and has a skew/nondegenerate fundamental form.

No theorem about integrability, Levi-Civita connections, closed differential
forms, Ricci-flatness, Kähler-Einstein geometry, or symplectic manifolds is
asserted here.  The word nondegenerate below means only that the displayed
finite bilinear form has trivial algebraic kernel.
-/

noncomputable section

namespace InfoGeometry.Physics.MD004GeometricStructures

set_option linter.unnecessarySeqFocus false

/-- Real four-coordinate shadow of the Hermitian Pauli matrix space. -/
structure Coord4 where
  (t x y z : ℝ)

/-- Euclidean metric/readout on the four-coordinate shadow. -/
def dot4 (a b : Coord4) : ℝ :=
  a.t * b.t + a.x * b.x + a.y * b.y + a.z * b.z

/-- Coordinate negation. -/
def neg4 (a : Coord4) : Coord4 :=
  ⟨-a.t, -a.x, -a.y, -a.z⟩

/-- Zero coordinate in the four-coordinate shadow. -/
def zero4 : Coord4 := ⟨0, 0, 0, 0⟩

/-- First finite complex structure from the Pauli-coordinate table. -/
def I4 (a : Coord4) : Coord4 :=
  ⟨-a.x, a.t, -a.z, a.y⟩

/-- Second finite complex structure from the Pauli-coordinate table. -/
def J4 (a : Coord4) : Coord4 :=
  ⟨-a.y, a.z, a.t, -a.x⟩

/-- Third finite complex structure from the Pauli-coordinate table. -/
def K4 (a : Coord4) : Coord4 :=
  ⟨-a.z, -a.y, a.x, a.t⟩

/-- `I² = -1` on coordinates. -/
theorem I4_sq (a : Coord4) : I4 (I4 a) = neg4 a := by
  cases a; rfl

/-- `J² = -1` on coordinates. -/
theorem J4_sq (a : Coord4) : J4 (J4 a) = neg4 a := by
  cases a; rfl

/-- `K² = -1` on coordinates. -/
theorem K4_sq (a : Coord4) : K4 (K4 a) = neg4 a := by
  cases a; rfl

/-- Quaternion multiplication `IJ = K`. -/
theorem I4_mul_J4 (a : Coord4) : I4 (J4 a) = K4 a := by
  cases a; simp [I4, J4, K4]

/-- Quaternion multiplication `JK = I`. -/
theorem J4_mul_K4 (a : Coord4) : J4 (K4 a) = I4 a := by
  cases a; simp [I4, J4, K4]

/-- Quaternion multiplication `KI = J`. -/
theorem K4_mul_I4 (a : Coord4) : K4 (I4 a) = J4 a := by
  cases a; simp [I4, J4, K4]

/-- Opposite multiplication `JI = -K`. -/
theorem J4_mul_I4 (a : Coord4) : J4 (I4 a) = neg4 (K4 a) := by
  cases a; simp [I4, J4, K4, neg4]

/-- Opposite multiplication `KJ = -I`. -/
theorem K4_mul_J4 (a : Coord4) : K4 (J4 a) = neg4 (I4 a) := by
  cases a; simp [I4, J4, K4, neg4]

/-- Opposite multiplication `IK = -J`. -/
theorem I4_mul_K4 (a : Coord4) : I4 (K4 a) = neg4 (J4 a) := by
  cases a; simp [I4, J4, K4, neg4]

/-- `I` preserves the finite Euclidean metric. -/
theorem I4_preserves_dot4 (a b : Coord4) : dot4 (I4 a) (I4 b) = dot4 a b := by
  cases a; cases b; simp [dot4, I4]; ring

/-- `J` preserves the finite Euclidean metric. -/
theorem J4_preserves_dot4 (a b : Coord4) : dot4 (J4 a) (J4 b) = dot4 a b := by
  cases a; cases b; simp [dot4, J4]; ring

/-- `K` preserves the finite Euclidean metric. -/
theorem K4_preserves_dot4 (a b : Coord4) : dot4 (K4 a) (K4 b) = dot4 a b := by
  cases a; cases b; simp [dot4, K4]; ring

/-- Fundamental 2-form for `I`. -/
def omegaI (a b : Coord4) : ℝ := dot4 (I4 a) b

/-- Fundamental 2-form for `J`. -/
def omegaJ (a b : Coord4) : ℝ := dot4 (J4 a) b

/-- Fundamental 2-form for `K`. -/
def omegaK (a b : Coord4) : ℝ := dot4 (K4 a) b

/-- The finite `I` fundamental form is skew-symmetric. -/
theorem omegaI_skew (a b : Coord4) : omegaI b a = - omegaI a b := by
  cases a; cases b; simp [omegaI, dot4, I4]; ring

/-- The finite `J` fundamental form is skew-symmetric. -/
theorem omegaJ_skew (a b : Coord4) : omegaJ b a = - omegaJ a b := by
  cases a; cases b; simp [omegaJ, dot4, J4]; ring

/-- The finite `K` fundamental form is skew-symmetric. -/
theorem omegaK_skew (a b : Coord4) : omegaK b a = - omegaK a b := by
  cases a; cases b; simp [omegaK, dot4, K4]; ring

/-- The finite `I` fundamental form has trivial algebraic kernel. -/
theorem omegaI_nondegenerate (a : Coord4) (h : ∀ b : Coord4, omegaI a b = 0) :
    a = zero4 := by
  cases a with
  | mk t x y z =>
    have h0 := h ⟨1, 0, 0, 0⟩
    have h1 := h ⟨0, 1, 0, 0⟩
    have h2 := h ⟨0, 0, 1, 0⟩
    have h3 := h ⟨0, 0, 0, 1⟩
    simp [omegaI, dot4, I4] at h0 h1 h2 h3
    subst x; subst t; subst z; subst y
    rfl

/-- The finite `J` fundamental form has trivial algebraic kernel. -/
theorem omegaJ_nondegenerate (a : Coord4) (h : ∀ b : Coord4, omegaJ a b = 0) :
    a = zero4 := by
  cases a with
  | mk t x y z =>
    have h0 := h ⟨1, 0, 0, 0⟩
    have h1 := h ⟨0, 1, 0, 0⟩
    have h2 := h ⟨0, 0, 1, 0⟩
    have h3 := h ⟨0, 0, 0, 1⟩
    simp [omegaJ, dot4, J4] at h0 h1 h2 h3
    subst y; subst z; subst t; subst x
    rfl

/-- The finite `K` fundamental form has trivial algebraic kernel. -/
theorem omegaK_nondegenerate (a : Coord4) (h : ∀ b : Coord4, omegaK a b = 0) :
    a = zero4 := by
  cases a with
  | mk t x y z =>
    have h0 := h ⟨1, 0, 0, 0⟩
    have h1 := h ⟨0, 1, 0, 0⟩
    have h2 := h ⟨0, 0, 1, 0⟩
    have h3 := h ⟨0, 0, 0, 1⟩
    simp [omegaK, dot4, K4] at h0 h1 h2 h3
    subst z; subst y; subst x; subst t
    rfl

/-- Real eight-coordinate shadow of the ambient complex vector space `M₂(ℂ) ≃ ℂ⁴`. -/
structure Coord8 where
  (a0 b0 a1 b1 a2 b2 a3 b3 : ℝ)

/-- Euclidean metric/readout on the ambient real eight-coordinate shadow. -/
def dot8 (u v : Coord8) : ℝ :=
  u.a0 * v.a0 + u.b0 * v.b0 + u.a1 * v.a1 + u.b1 * v.b1 +
    u.a2 * v.a2 + u.b2 * v.b2 + u.a3 * v.a3 + u.b3 * v.b3

/-- Coordinate negation in `ℝ⁸`. -/
def neg8 (u : Coord8) : Coord8 :=
  ⟨-u.a0, -u.b0, -u.a1, -u.b1, -u.a2, -u.b2, -u.a3, -u.b3⟩

/-- Zero coordinate in the ambient eight-coordinate shadow. -/
def zero8 : Coord8 := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Standard complex structure on `ℂ⁴ ≃ ℝ⁸`. -/
def J0 (u : Coord8) : Coord8 :=
  ⟨-u.b0, u.a0, -u.b1, u.a1, -u.b2, u.a2, -u.b3, u.a3⟩

/-- The ambient standard complex structure squares to `-1`. -/
theorem J0_sq (u : Coord8) : J0 (J0 u) = neg8 u := by
  cases u; rfl

/-- The ambient standard complex structure preserves the Euclidean metric. -/
theorem J0_preserves_dot8 (u v : Coord8) : dot8 (J0 u) (J0 v) = dot8 u v := by
  cases u; cases v; simp [dot8, J0]; ring

/-- Ambient finite Kähler-form shadow. -/
def omega0 (u v : Coord8) : ℝ := dot8 (J0 u) v

/-- The ambient finite Kähler-form shadow is skew-symmetric. -/
theorem omega0_skew (u v : Coord8) : omega0 v u = - omega0 u v := by
  cases u; cases v; simp [omega0, dot8, J0]; ring

/-- The ambient finite Kähler-form shadow has trivial algebraic kernel. -/
theorem omega0_nondegenerate (u : Coord8) (h : ∀ v : Coord8, omega0 u v = 0) :
    u = zero8 := by
  cases u with
  | mk a0 b0 a1 b1 a2 b2 a3 b3 =>
    have h0 := h ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
    have h1 := h ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
    have h2 := h ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
    have h3 := h ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
    have h4 := h ⟨0, 0, 0, 0, 1, 0, 0, 0⟩
    have h5 := h ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
    have h6 := h ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
    have h7 := h ⟨0, 0, 0, 0, 0, 0, 0, 1⟩
    simp [omega0, dot8, J0] at h0 h1 h2 h3 h4 h5 h6 h7
    subst b0; subst a0; subst b1; subst a1; subst b2; subst a2; subst b3; subst a3
    rfl

/-- Repaired theorem-safe Chapter 4 finite geometry packet. -/
theorem repaired_MD004_geometric_structures_packet (a b : Coord4) (u v : Coord8) :
    I4 (I4 a) = neg4 a ∧
    J4 (J4 a) = neg4 a ∧
    K4 (K4 a) = neg4 a ∧
    I4 (J4 a) = K4 a ∧
    dot4 (I4 a) (I4 b) = dot4 a b ∧
    dot4 (J4 a) (J4 b) = dot4 a b ∧
    dot4 (K4 a) (K4 b) = dot4 a b ∧
    omegaI b a = - omegaI a b ∧
    omegaJ b a = - omegaJ a b ∧
    omegaK b a = - omegaK a b ∧
    (∀ x : Coord4, (∀ y : Coord4, omegaI x y = 0) → x = zero4) ∧
    (∀ x : Coord4, (∀ y : Coord4, omegaJ x y = 0) → x = zero4) ∧
    (∀ x : Coord4, (∀ y : Coord4, omegaK x y = 0) → x = zero4) ∧
    J0 (J0 u) = neg8 u ∧
    dot8 (J0 u) (J0 v) = dot8 u v ∧
    omega0 v u = - omega0 u v ∧
    (∀ x : Coord8, (∀ y : Coord8, omega0 x y = 0) → x = zero8) := by
  exact ⟨I4_sq a, J4_sq a, K4_sq a, I4_mul_J4 a,
    I4_preserves_dot4 a b, J4_preserves_dot4 a b, K4_preserves_dot4 a b,
    omegaI_skew a b, omegaJ_skew a b, omegaK_skew a b,
    fun x h => omegaI_nondegenerate x h,
    fun x h => omegaJ_nondegenerate x h,
    fun x h => omegaK_nondegenerate x h,
    J0_sq u, J0_preserves_dot8 u v, omega0_skew u v,
    fun x h => omega0_nondegenerate x h⟩

end InfoGeometry.Physics.MD004GeometricStructures

end noncomputable section
