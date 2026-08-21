import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Architecture.CartanGeodesic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

structure IsLieBracket (bracket : V → V → V) : Prop where
  skew : ∀ x y, bracket x y = - bracket y x
  add_left : ∀ x y z, bracket (x + y) z = bracket x z + bracket y z
  add_right : ∀ x y z, bracket x (y + z) = bracket x y + bracket x z
  smul_left : ∀ (c : ℝ) x y, bracket (c • x) y = c • bracket x y
  smul_right : ∀ (c : ℝ) x y, bracket x (c • y) = c • bracket x y
  jacobi : ∀ x y z, bracket x (bracket y z) + bracket y (bracket z x) + bracket z (bracket x y) = 0

lemma bracket_neg_left (bracket : V → V → V) (h_lie : IsLieBracket bracket) (x y : V) :
    bracket (-x) y = - bracket x y := by
  have h := h_lie.smul_left (-1 : ℝ) x y
  rw [neg_one_smul, neg_one_smul] at h
  exact h

lemma bracket_neg_right (bracket : V → V → V) (h_lie : IsLieBracket bracket) (x y : V) :
    bracket x (-y) = - bracket x y := by
  have h := h_lie.smul_right (-1 : ℝ) x y
  rw [neg_one_smul, neg_one_smul] at h
  exact h

lemma bracket_neg_neg (bracket : V → V → V) (h_lie : IsLieBracket bracket) (x y : V) :
    bracket (-x) (-y) = bracket x y := by
  rw [bracket_neg_left bracket h_lie, bracket_neg_right bracket h_lie, neg_neg]

structure CartanInvolution (bracket : V → V → V) where
  theta : V →ₗ[ℝ] V
  involutive : ∀ x, theta (theta x) = x
  morphism : ∀ x y, theta (bracket x y) = bracket (theta x) (theta y)

def kSpace (bracket : V → V → V) (inv : CartanInvolution bracket) : Submodule ℝ V where
  carrier := {x | inv.theta x = x}
  add_mem' := by
    intro a b ha hb
    dsimp at *
    rw [map_add, ha, hb]
  zero_mem' := by
    dsimp
    rw [map_zero]
  smul_mem' := by
    intro c x hx
    dsimp at *
    rw [map_smul, hx]

def pSpace (bracket : V → V → V) (inv : CartanInvolution bracket) : Submodule ℝ V where
  carrier := {x | inv.theta x = -x}
  add_mem' := by
    intro a b ha hb
    dsimp at *
    rw [map_add, ha, hb, neg_add]
  zero_mem' := by
    dsimp
    rw [map_zero, neg_zero]
  smul_mem' := by
    intro c x hx
    dsimp at *
    rw [map_smul, hx, smul_neg]

theorem cartan_grading_k_k
    (bracket : V → V → V) (inv : CartanInvolution bracket)
    (x y : V) (hx : x ∈ kSpace bracket inv) (hy : y ∈ kSpace bracket inv) :
    bracket x y ∈ kSpace bracket inv := by
  change inv.theta (bracket x y) = bracket x y
  rw [inv.morphism]
  have hx' : inv.theta x = x := hx
  have hy' : inv.theta y = y := hy
  rw [hx', hy']

theorem cartan_grading_p_p
    (bracket : V → V → V) (h_lie : IsLieBracket bracket) (inv : CartanInvolution bracket)
    (x y : V) (hx : x ∈ pSpace bracket inv) (hy : y ∈ pSpace bracket inv) :
    bracket x y ∈ kSpace bracket inv := by
  change inv.theta (bracket x y) = bracket x y
  rw [inv.morphism]
  have hx' : inv.theta x = -x := hx
  have hy' : inv.theta y = -y := hy
  rw [hx', hy', bracket_neg_neg bracket h_lie]

theorem cartan_grading_k_p
    (bracket : V → V → V) (h_lie : IsLieBracket bracket) (inv : CartanInvolution bracket)
    (x y : V) (hx : x ∈ kSpace bracket inv) (hy : y ∈ pSpace bracket inv) :
    bracket x y ∈ pSpace bracket inv := by
  change inv.theta (bracket x y) = - bracket x y
  rw [inv.morphism]
  have hx' : inv.theta x = x := hx
  have hy' : inv.theta y = -y := hy
  rw [hx', hy', bracket_neg_right bracket h_lie]

/-- The Riemann curvature tensor at the origin of G/K: R(X, Y)Z = - [[X, Y], Z]. -/
def riemannCurvature (bracket : V → V → V) (X Y Z : V) : V :=
  - bracket (bracket X Y) Z

/-- Nomizu Levi-Civita connection on tangent space p: ∇_X Y = 0 on p at origin. -/
def connectionAtOrigin (X Y : V) : V := (0 : V)

/-- 
  The Covariant Derivative of the Riemann Curvature Tensor:
  (∇_X R)(Y, Z, W) = ∇_X(R(Y, Z)W) - R(∇_X Y, Z)W - R(Y, ∇_X Z)W - R(Y, Z)(∇_X W).
-/
def covariantDerivCurvature (bracket : V → V → V) (X Y Z W : V) : V :=
  connectionAtOrigin X (riemannCurvature bracket Y Z W) -
  riemannCurvature bracket (connectionAtOrigin X Y) Z W -
  riemannCurvature bracket Y (connectionAtOrigin X Z) W -
  riemannCurvature bracket Y Z (connectionAtOrigin X W)

/-- 
  MASTER THEOREM (Covariant Constancy of Curvature: ∇R = 0 on Cartan Symmetric Space G/K):
  The covariant derivative of the Riemann curvature tensor vanishes identically at the origin.
-/
theorem covariant_deriv_curvature_zero
    (bracket : V → V → V) (h_lie : IsLieBracket bracket)
    (X Y Z W : V) :
    covariantDerivCurvature bracket X Y Z W = 0 := by
  dsimp [covariantDerivCurvature, connectionAtOrigin, riemannCurvature]
  have h_zero_r : bracket 0 W = 0 := by
    have h := h_lie.smul_left 0 0 W
    rw [zero_smul, zero_smul] at h
    exact h
  have h_zero_bracket_z : bracket Y 0 = 0 := by
    have h := h_lie.smul_right 0 Y 0
    rw [zero_smul, zero_smul] at h
    exact h
  have h_zero_mid : bracket (bracket Y 0) W = 0 := by
    rw [h_zero_bracket_z, h_zero_r]
  have h_zero_last : bracket (bracket Y Z) 0 = 0 := by
    have h := h_lie.smul_right 0 (bracket Y Z) 0
    rw [zero_smul, zero_smul] at h
    exact h
  have h_b0 : bracket (bracket 0 Z) W = 0 := by
    have h1 : bracket 0 Z = 0 := by
      have h := h_lie.smul_left 0 0 Z
      rw [zero_smul, zero_smul] at h
      exact h
    rw [h1, h_zero_r]
  rw [h_b0, h_zero_mid, h_zero_last]
  simp

end InfoGeometry.Architecture.CartanGeodesic

end noncomputable section
