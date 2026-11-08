import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Phase-Space Non-Abelian Berry Connection and Anomalous Hall Ray Deflection

This module formalizes:
1. 3D vector algebra with dot and cross products (`ChiralVector3`).
2. Transversality of the cross product: `(u × v) · u = 0` and `(u × v) · v = 0`.
3. 2x2 Matrix algebra for the non-Abelian su(2) Berry connection (`Matrix2x2`).
4. Theorem: The trace of any matrix commutator vanishes: `Tr([A, B]) = 0`.
5. Theorem: Tracelessness of the su(2) non-Abelian field strength forces
   opposite abelian Berry curvatures: `Ω₋ = - Ω₊`.
6. Semiclassical anomalous Hall velocity: `v_anom = - (F × Ω)`.
7. Theorem (Zero Work / Transversality): `v_anom · F = 0`.
8. Theorem (Transversality to Curvature): `v_anom · Ω = 0`.
9. Theorem (Opposite Chiral Deflection): `v_anom(-) = - v_anom(+)`.
10. Theorem (Net Transverse Chiral Splitting): `v_anom(+) - v_anom(-) = 2 • v_anom(+)`.
11. Explicit 2D planar Hall deflection along the orthogonal y-axis:
    `F = (F_x, 0, 0) ∧ Ω = (0, 0, Ω_z) → v_anom = (0, F_x * Ω_z, 0)`.
-/

/-!
### 1. ChiralVector3 Geometry and Cross Product Orthogonality
-/

structure ChiralVector3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace ChiralVector3

@[ext]
theorem ext {u v : ChiralVector3} (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) : u = v := by
  cases u; cases v; dsimp at hx hy hz; rw [hx, hy, hz]

def zero : ChiralVector3 := ⟨0, 0, 0⟩
instance : Zero ChiralVector3 := ⟨zero⟩

def add (u v : ChiralVector3) : ChiralVector3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
instance : Add ChiralVector3 := ⟨add⟩

def neg (u : ChiralVector3) : ChiralVector3 := ⟨-u.x, -u.y, -u.z⟩
instance : Neg ChiralVector3 := ⟨neg⟩

def sub (u v : ChiralVector3) : ChiralVector3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
instance : Sub ChiralVector3 := ⟨sub⟩

def smul (c : ℝ) (u : ChiralVector3) : ChiralVector3 := ⟨c * u.x, c * u.y, c * u.z⟩
instance : HSMul ℝ ChiralVector3 ChiralVector3 := ⟨smul⟩

@[simp] lemma zero_x : (0 : ChiralVector3).x = 0 := rfl
@[simp] lemma zero_y : (0 : ChiralVector3).y = 0 := rfl
@[simp] lemma zero_z : (0 : ChiralVector3).z = 0 := rfl

@[simp] lemma add_x (u v : ChiralVector3) : (u + v).x = u.x + v.x := rfl
@[simp] lemma add_y (u v : ChiralVector3) : (u + v).y = u.y + v.y := rfl
@[simp] lemma add_z (u v : ChiralVector3) : (u + v).z = u.z + v.z := rfl

@[simp] lemma neg_x (u : ChiralVector3) : (-u).x = -u.x := rfl
@[simp] lemma neg_y (u : ChiralVector3) : (-u).y = -u.y := rfl
@[simp] lemma neg_z (u : ChiralVector3) : (-u).z = -u.z := rfl

@[simp] lemma sub_x (u v : ChiralVector3) : (u - v).x = u.x - v.x := rfl
@[simp] lemma sub_y (u v : ChiralVector3) : (u - v).y = u.y - v.y := rfl
@[simp] lemma sub_z (u v : ChiralVector3) : (u - v).z = u.z - v.z := rfl

@[simp] lemma smul_x (c : ℝ) (u : ChiralVector3) : (c • u).x = c * u.x := rfl
@[simp] lemma smul_y (c : ℝ) (u : ChiralVector3) : (c • u).y = c * u.y := rfl
@[simp] lemma smul_z (c : ℝ) (u : ChiralVector3) : (c • u).z = c * u.z := rfl

def dot (u v : ChiralVector3) : ℝ :=
  u.x * v.x + u.y * v.y + u.z * v.z

def cross (u v : ChiralVector3) : ChiralVector3 :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

@[simp] lemma cross_x (u v : ChiralVector3) : (cross u v).x = u.y * v.z - u.z * v.y := rfl
@[simp] lemma cross_y (u v : ChiralVector3) : (cross u v).y = u.z * v.x - u.x * v.z := rfl
@[simp] lemma cross_z (u v : ChiralVector3) : (cross u v).z = u.x * v.y - u.y * v.x := rfl

/-- **Theorem**: `(u × v) · u = 0`. -/
theorem dot_cross_self_left (u v : ChiralVector3) : dot (cross u v) u = 0 := by
  dsimp [dot]
  ring

/-- **Theorem**: `(u × v) · v = 0`. -/
theorem dot_cross_self_right (u v : ChiralVector3) : dot (cross u v) v = 0 := by
  dsimp [dot]
  ring

theorem cross_neg_right (u v : ChiralVector3) : cross u (-v) = - cross u v := by
  ext <;> (dsimp; ring)

end ChiralVector3

/-!
### 2. Non-Abelian su(2) Gauge Curvature and Chiral Anti-Symmetry
-/

structure Matrix2x2 where
  m00 : ℝ
  m01 : ℝ
  m10 : ℝ
  m11 : ℝ

namespace Matrix2x2

def trace (M : Matrix2x2) : ℝ := M.m00 + M.m11

def sub (A B : Matrix2x2) : Matrix2x2 :=
  ⟨A.m00 - B.m00, A.m01 - B.m01, A.m10 - B.m10, A.m11 - B.m11⟩
instance : Sub Matrix2x2 := ⟨sub⟩

def mul (A B : Matrix2x2) : Matrix2x2 :=
  ⟨A.m00 * B.m00 + A.m01 * B.m10,
   A.m00 * B.m01 + A.m01 * B.m11,
   A.m10 * B.m00 + A.m11 * B.m10,
   A.m10 * B.m01 + A.m11 * B.m11⟩
instance : Mul Matrix2x2 := ⟨mul⟩

@[simp] lemma mul_m00 (A B : Matrix2x2) : (A * B).m00 = A.m00 * B.m00 + A.m01 * B.m10 := rfl
@[simp] lemma mul_m01 (A B : Matrix2x2) : (A * B).m01 = A.m00 * B.m01 + A.m01 * B.m11 := rfl
@[simp] lemma mul_m10 (A B : Matrix2x2) : (A * B).m10 = A.m10 * B.m00 + A.m11 * B.m10 := rfl
@[simp] lemma mul_m11 (A B : Matrix2x2) : (A * B).m11 = A.m10 * B.m01 + A.m11 * B.m11 := rfl

@[simp] lemma sub_m00 (A B : Matrix2x2) : (A - B).m00 = A.m00 - B.m00 := rfl
@[simp] lemma sub_m01 (A B : Matrix2x2) : (A - B).m01 = A.m01 - B.m01 := rfl
@[simp] lemma sub_m10 (A B : Matrix2x2) : (A - B).m10 = A.m10 - B.m10 := rfl
@[simp] lemma sub_m11 (A B : Matrix2x2) : (A - B).m11 = A.m11 - B.m11 := rfl

def commutator (A B : Matrix2x2) : Matrix2x2 := A * B - B * A

theorem trace_mul_comm (A B : Matrix2x2) : trace (A * B) = trace (B * A) := by
  dsimp [trace]
  ring

theorem trace_sub (A B : Matrix2x2) : trace (A - B) = trace A - trace B := by
  dsimp [trace]
  ring

/-- **Theorem (Vanishing Commutator Trace)**:
    `Tr([A, B]) = 0` for any 2x2 matrices. -/
theorem trace_commutator_zero (A B : Matrix2x2) : trace (commutator A B) = 0 := by
  dsimp [commutator]
  rw [trace_sub, trace_mul_comm]
  ring

end Matrix2x2

/-- Data representing an su(2) non-Abelian Berry connection in phase space. -/
structure NonAbelianBerryCurvature where
  dAx_dy : Matrix2x2
  dAy_dx : Matrix2x2
  Ax : Matrix2x2
  Ay : Matrix2x2
  h_tr_dAx : Matrix2x2.trace dAx_dy = 0
  h_tr_dAy : Matrix2x2.trace dAy_dx = 0

namespace NonAbelianBerryCurvature

/-- Non-Abelian field strength: `F_{xy} = ∂_x A_y - ∂_y A_x - [A_x, A_y]`. -/
def fieldStrength (F : NonAbelianBerryCurvature) : Matrix2x2 :=
  (F.dAy_dx - F.dAx_dy) - Matrix2x2.commutator F.Ax F.Ay

/-- **Theorem (Field Strength is Traceless)**:
    `Tr(F_{xy}) = 0`. -/
theorem fieldStrength_trace_zero (F : NonAbelianBerryCurvature) :
    Matrix2x2.trace (F.fieldStrength) = 0 := by
  dsimp [fieldStrength]
  rw [Matrix2x2.trace_sub, Matrix2x2.trace_sub]
  rw [F.h_tr_dAy, F.h_tr_dAx, Matrix2x2.trace_commutator_zero]
  ring

/-- **Theorem (Chiral Curvature Anti-Symmetry)**:
    In the diagonal chiral eigenbasis, tracelessness forces `Ω₋ = - Ω₊`. -/
theorem chiral_branch_opposite (F : NonAbelianBerryCurvature)
    (omega_plus omega_minus : ℝ)
    (h_diag : F.fieldStrength = ⟨omega_plus, 0, 0, omega_minus⟩) :
    omega_minus = - omega_plus := by
  have h_tr := F.fieldStrength_trace_zero
  rw [h_diag] at h_tr
  dsimp [Matrix2x2.trace] at h_tr
  linarith

end NonAbelianBerryCurvature

/-!
### 3. Anomalous Hall Velocity and Transverse Ray Splitting
-/

/-- Configuration of a chiral acoustic ray in phase space. -/
structure ChiralAcousticRaySystem where
  omega_plus : ChiralVector3
  driving_force : ChiralVector3

namespace ChiralAcousticRaySystem

variable (S : ChiralAcousticRaySystem)

/-- Negative chiral branch Berry curvature: `Ω₋ = - Ω₊`. -/
def omega_minus : ChiralVector3 := - S.omega_plus

/-- Anomalous velocity for the positive branch: `v₊ = - (F × Ω₊)`. -/
def v_anom_plus : ChiralVector3 :=
  - ChiralVector3.cross S.driving_force S.omega_plus

/-- Anomalous velocity for the negative branch: `v₋ = - (F × Ω₋)`. -/
def v_anom_minus : ChiralVector3 :=
  - ChiralVector3.cross S.driving_force S.omega_minus

/-- **Main Theorem 1 (Zero Work Done / Transversality to Force)**:
    `v_anom · F = 0`. The anomalous velocity performs no mechanical work. -/
theorem work_done_zero_plus :
    ChiralVector3.dot S.v_anom_plus S.driving_force = 0 := by
  dsimp [v_anom_plus, ChiralVector3.dot]
  have h := ChiralVector3.dot_cross_self_left S.driving_force S.omega_plus
  dsimp [ChiralVector3.dot] at h
  linarith

theorem work_done_zero_minus :
    ChiralVector3.dot S.v_anom_minus S.driving_force = 0 := by
  dsimp [v_anom_minus, omega_minus]
  rw [ChiralVector3.cross_neg_right]
  dsimp [ChiralVector3.dot]
  have h := ChiralVector3.dot_cross_self_left S.driving_force S.omega_plus
  dsimp [ChiralVector3.dot] at h
  linarith

/-- **Main Theorem 2 (Transversality to Berry Curvature)**:
    `v_anom · Ω = 0`. -/
theorem berry_transverse_plus :
    ChiralVector3.dot S.v_anom_plus S.omega_plus = 0 := by
  dsimp [v_anom_plus, ChiralVector3.dot]
  have h := ChiralVector3.dot_cross_self_right S.driving_force S.omega_plus
  dsimp [ChiralVector3.dot] at h
  linarith

/-- **Main Theorem 3 (Opposite Chiral Deflections)**:
    `v_anom(-) = - v_anom(+)`. -/
theorem anomalous_hall_opposite :
    S.v_anom_minus = - S.v_anom_plus := by
  dsimp [v_anom_minus, v_anom_plus, omega_minus]
  rw [ChiralVector3.cross_neg_right]

/-- **Main Theorem 4 (Chiral Ray Splitting)**:
    The relative velocity between the two chiral sound rays is strictly transverse
    and equal to twice the individual anomalous velocity:
    `v₊ - v₋ = 2 • v₊`. -/
theorem chiral_transverse_splitting :
    S.v_anom_plus - S.v_anom_minus = (2 : ℝ) • S.v_anom_plus := by
  rw [anomalous_hall_opposite]
  ext <;> (dsimp; ring)

/-- **Main Theorem 5 (Planar 2D Anomalous Hall Drift)**:
    Under an in-plane force along x and an out-of-plane Berry curvature along z,
    the anomalous velocities are purely directed along the transverse y-axis:
    `v₊ = (0, F_x * Ω_z, 0)` and `v₋ = (0, - F_x * Ω_z, 0)`. -/
theorem hall_deflection_2D_planar
    (F_x Omega_z : ℝ)
    (hF : S.driving_force = ⟨F_x, 0, 0⟩)
    (hOmega : S.omega_plus = ⟨0, 0, Omega_z⟩) :
    S.v_anom_plus = ⟨0, F_x * Omega_z, 0⟩ ∧
    S.v_anom_minus = ⟨0, - (F_x * Omega_z), 0⟩ := by
  constructor
  · dsimp [v_anom_plus]
    rw [hF, hOmega]
    ext <;> (dsimp; ring)
  · rw [anomalous_hall_opposite]
    dsimp [v_anom_plus]
    rw [hF, hOmega]
    ext <;> (dsimp; ring)

/-- **Master Certified Conjunction for Anomalous Hall Ray Deflection** -/
theorem certified_chiral_anomalous_hall_synthesis :
    ChiralVector3.dot S.v_anom_plus S.driving_force = 0 ∧
    ChiralVector3.dot S.v_anom_minus S.driving_force = 0 ∧
    ChiralVector3.dot S.v_anom_plus S.omega_plus = 0 ∧
    S.v_anom_minus = - S.v_anom_plus ∧
    S.v_anom_plus - S.v_anom_minus = (2 : ℝ) • S.v_anom_plus := by
  refine ⟨S.work_done_zero_plus,
          S.work_done_zero_minus,
          S.berry_transverse_plus,
          S.anomalous_hall_opposite,
          S.chiral_transverse_splitting⟩

end ChiralAcousticRaySystem
