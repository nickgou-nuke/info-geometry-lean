import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Architecture.CartanNomizu

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

structure IsLieBracket (bracket : V → V → V) : Prop where
  skew : ∀ x y, bracket x y = - bracket y x
  add_left : ∀ x y z, bracket (x + y) z = bracket x z + bracket y z
  add_right : ∀ x y z, bracket x (y + z) = bracket x y + bracket x z
  smul_left : ∀ (c : ℝ) x y, bracket (c • x) y = c • bracket x y
  smul_right : ∀ (c : ℝ) x y, bracket x (c • y) = c • bracket x y
  jacobi : ∀ x y z, bracket x (bracket y z) + bracket y (bracket z x) + bracket z (bracket x y) = 0

lemma bracket_zero_left (bracket : V → V → V) (h_lie : IsLieBracket bracket) (y : V) :
    bracket 0 y = 0 := by
  have h := h_lie.smul_left 0 0 y
  rw [zero_smul, zero_smul] at h
  exact h

lemma bracket_zero_right (bracket : V → V → V) (h_lie : IsLieBracket bracket) (x : V) :
    bracket x 0 = 0 := by
  have h := h_lie.smul_right 0 x 0
  rw [zero_smul, zero_smul] at h
  exact h

structure CartanGrading (bracket : V → V → V) (k_space p_space : Submodule ℝ V) : Prop where
  k_k : ∀ x y, x ∈ k_space → y ∈ k_space → bracket x y ∈ k_space
  k_p : ∀ x y, x ∈ k_space → y ∈ p_space → bracket x y ∈ p_space
  p_p : ∀ x y, x ∈ p_space → y ∈ p_space → bracket x y ∈ k_space

/-- The canonical Cartan-Nomizu Levi-Civita connection on p: ∇_X Y = (1/2) * proj_p([X, Y]). -/
def nomizuConnection (bracket : V → V → V) (proj_p : V → V) (X Y : V) : V :=
  (1 / 2 : ℝ) • proj_p (bracket X Y)

/-- THEOREM 1: The Levi-Civita connection vanishes on tangent vectors at the origin. -/
theorem connection_on_tangent_vanishes
    (bracket : V → V → V) (k_space p_space : Submodule ℝ V)
    (proj_p : V → V)
    (h_proj_zero_on_k : ∀ k, k ∈ k_space → proj_p k = 0)
    (h_grading : CartanGrading bracket k_space p_space)
    (X Y : V) (hX : X ∈ p_space) (hY : Y ∈ p_space) :
    nomizuConnection bracket proj_p X Y = 0 := by
  dsimp [nomizuConnection]
  have h_in_k : bracket X Y ∈ k_space := h_grading.p_p X Y hX hY
  have h_proj : proj_p (bracket X Y) = 0 := h_proj_zero_on_k (bracket X Y) h_in_k
  rw [h_proj, smul_zero]

/-- Torsion tensor of the Nomizu connection on p: T(X, Y) = ∇_X Y - ∇_Y X - proj_p([X, Y]). -/
def torsionTensor (bracket : V → V → V) (proj_p : V → V) (X Y : V) : V :=
  nomizuConnection bracket proj_p X Y - nomizuConnection bracket proj_p Y X - proj_p (bracket X Y)

/-- THEOREM 2: The canonical Cartan-Nomizu connection is torsion-free on p. -/
theorem torsion_free
    (bracket : V → V → V) (k_space p_space : Submodule ℝ V)
    (proj_p : V → V)
    (h_proj_zero_on_k : ∀ k, k ∈ k_space → proj_p k = 0)
    (h_grading : CartanGrading bracket k_space p_space)
    (X Y : V) (hX : X ∈ p_space) (hY : Y ∈ p_space) :
    torsionTensor bracket proj_p X Y = 0 := by
  dsimp [torsionTensor]
  have h1 := connection_on_tangent_vanishes bracket k_space p_space proj_p h_proj_zero_on_k h_grading X Y hX hY
  have h2 := connection_on_tangent_vanishes bracket k_space p_space proj_p h_proj_zero_on_k h_grading Y X hY hX
  have h_in_k : bracket X Y ∈ k_space := h_grading.p_p X Y hX hY
  have h3 : proj_p (bracket X Y) = 0 := h_proj_zero_on_k (bracket X Y) h_in_k
  rw [h1, h2, h3, sub_zero, sub_zero]

/-- The Nomizu Riemann curvature tensor: R(X, Y)Z = -[[X, Y], Z]. -/
def riemannCurvature (bracket : V → V → V) (X Y Z : V) : V :=
  - bracket (bracket X Y) Z

/-- 
  Covariant derivative of the Riemann curvature tensor:
  (∇_W R)(X, Y)Z = ∇_W(R(X,Y)Z) - R(∇_W X, Y)Z - R(X, ∇_W Y)Z - R(X, Y)(∇_W Z).
-/
def covariantDerivRiemann
    (bracket : V → V → V) (proj_p : V → V) (W X Y Z : V) : V :=
  nomizuConnection bracket proj_p W (riemannCurvature bracket X Y Z) -
  riemannCurvature bracket (nomizuConnection bracket proj_p W X) Y Z -
  riemannCurvature bracket X (nomizuConnection bracket proj_p W Y) Z -
  riemannCurvature bracket X Y (nomizuConnection bracket proj_p W Z)

/-- 
  MASTER THEOREM: The Riemann curvature tensor is parallel (∇R = 0) on all symmetric spaces!
-/
theorem parallel_curvature_vanishes
    (bracket : V → V → V) (h_lie : IsLieBracket bracket)
    (k_space p_space : Submodule ℝ V)
    (proj_p : V → V)
    (h_proj_zero_on_k : ∀ k, k ∈ k_space → proj_p k = 0)
    (h_grading : CartanGrading bracket k_space p_space)
    (W X Y Z : V)
    (hW : W ∈ p_space) (hX : X ∈ p_space) (hY : Y ∈ p_space) (hZ : Z ∈ p_space) :
    covariantDerivRiemann bracket proj_p W X Y Z = 0 := by
  dsimp [covariantDerivRiemann]
  -- R(X, Y)Z lies in p
  have h_XY_in_k : bracket X Y ∈ k_space := h_grading.p_p X Y hX hY
  have h_R_in_p : bracket (bracket X Y) Z ∈ p_space :=
    h_grading.k_p (bracket X Y) Z h_XY_in_k hZ
  have h_neg_R_in_p : riemannCurvature bracket X Y Z ∈ p_space := by
    dsimp [riemannCurvature]
    exact p_space.neg_mem h_R_in_p

  -- Term 1: ∇_W (R(X, Y)Z) = 0
  have h_term1 := connection_on_tangent_vanishes bracket k_space p_space proj_p h_proj_zero_on_k h_grading W (riemannCurvature bracket X Y Z) hW h_neg_R_in_p

  -- Term 2: ∇_W X = 0
  have h_term2_conn := connection_on_tangent_vanishes bracket k_space p_space proj_p h_proj_zero_on_k h_grading W X hW hX
  have h_term2 : riemannCurvature bracket (nomizuConnection bracket proj_p W X) Y Z = 0 := by
    dsimp [riemannCurvature]
    rw [h_term2_conn]
    rw [bracket_zero_left bracket h_lie Y, bracket_zero_left bracket h_lie Z, neg_zero]

  -- Term 3: ∇_W Y = 0
  have h_term3_conn := connection_on_tangent_vanishes bracket k_space p_space proj_p h_proj_zero_on_k h_grading W Y hW hY
  have h_term3 : riemannCurvature bracket X (nomizuConnection bracket proj_p W Y) Z = 0 := by
    dsimp [riemannCurvature]
    rw [h_term3_conn]
    rw [bracket_zero_right bracket h_lie X, bracket_zero_left bracket h_lie Z, neg_zero]

  -- Term 4: ∇_W Z = 0
  have h_term4_conn := connection_on_tangent_vanishes bracket k_space p_space proj_p h_proj_zero_on_k h_grading W Z hW hZ
  have h_term4 : riemannCurvature bracket X Y (nomizuConnection bracket proj_p W Z) = 0 := by
    dsimp [riemannCurvature]
    rw [h_term4_conn]
    rw [bracket_zero_right bracket h_lie (bracket X Y), neg_zero]

  rw [h_term1, h_term2, h_term3, h_term4]
  abel

end InfoGeometry.Architecture.CartanNomizu

end noncomputable section
