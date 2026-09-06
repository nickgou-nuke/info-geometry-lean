import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Prequantum.LiouvilleCapacity

The theorem-safe core here is purely algebraic:

* a nonzero abstract volume cell;
* a minimal metriplectic interface with Liouville invariance as a field;
* a 2D symplectic-area identity under linear maps;
* a zero-gradient vacuum readout.

This does **not** formalize Gromov non-squeezing as a theorem.
-/

set_option autoImplicit false

namespace InfoGeometry.Prequantum.LiouvilleCapacity

/-- An abstract nonzero volume cell. -/
structure SymplecticVolume (A : Type*) [Ring A] where
  I : A
  is_non_degenerate : I ≠ 0

/-- Minimal metriplectic packet with a real-valued metric channel. -/
structure MetriplecticSystem (A : Type*) [Ring A] [Algebra ℝ A] where
  poisson : A → A → A
  metric : A → A → ℝ
  liouville_invariance : ∀ X I, poisson X I = 0
  metric_add_right : ∀ x y z, metric x (y + z) = metric x y + metric x z
  metric_scale_right : ∀ (c : ℝ) x y,
    metric x ((algebraMap ℝ A c) * y) = c * metric x y

/-- Souriau-style grandcanonical potential. -/
def S_potential {A : Type*} [Ring A] [Algebra ℝ A]
    (H N : A) (β μ : ℝ) : A :=
  - (algebraMap ℝ A β) * (H - (algebraMap ℝ A μ) * N)

/-- The isotropic vacuum is the zero-gradient condition. -/
def is_isotropic_vacuum (dμ : ℝ) : Prop :=
  dμ = 0

/-- The metric flux vanishes at isotropic vacuum. -/
theorem vacuum_flux_vanishes {A : Type*} [Ring A] [Algebra ℝ A]
    (M : MetriplecticSystem A) (X _H N : A) (β dμ : ℝ)
    (h_vac : is_isotropic_vacuum dμ) :
    dμ * (β * M.metric X N) = 0 := by
  unfold is_isotropic_vacuum at h_vac
  rw [h_vac]
  ring

/-- The stored volume cell is nonzero by construction. -/
theorem volume_unit_indestructible {A : Type*} [Ring A]
    (V : SymplecticVolume A) :
    V.I ≠ 0 :=
  V.is_non_degenerate

/-- Liouville invariance: the conservative Poisson channel does not move the volume cell. -/
theorem poisson_volume_unit_indestructible {A : Type*} [Ring A] [Algebra ℝ A]
    (M : MetriplecticSystem A) (X I : A) :
    M.poisson X I = 0 :=
  M.liouville_invariance X I

/-- At zero chemical gradient, dissipation vanishes and the Poisson channel preserves volume. -/
theorem vacuum_flux_zero_and_poisson_volume_preserved
    {A : Type*} [Ring A] [Algebra ℝ A]
    (M : MetriplecticSystem A) (X H N I : A) (β dμ : ℝ)
    (h_vac : is_isotropic_vacuum dμ) :
    dμ * (β * M.metric X N) = 0 ∧ M.poisson X I = 0 :=
  ⟨vacuum_flux_vanishes M X H N β dμ h_vac,
    poisson_volume_unit_indestructible M X I⟩

/-- 2D phase-space vectors. -/
structure Vector2D where
  x1 : ℝ
  x2 : ℝ

/-- 2D real linear maps. -/
structure Matrix2D where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

/-- The 2D symplectic area form. -/
def omega (x y : Vector2D) : ℝ :=
  x.x1 * y.x2 - x.x2 * y.x1

/-! ## The finite para-complex compatibility packet -/

/-- The split involution on the two-dimensional phase-space carrier. -/
def paraK (v : Vector2D) : Vector2D :=
  ⟨v.x1, -v.x2⟩

/-- The neutral bilinear form obtained from `omega` and the split involution. -/
def neutralMetric (x y : Vector2D) : ℝ :=
  omega x (paraK y)

theorem paraK_square (v : Vector2D) :
    paraK (paraK v) = v := by
  cases v
  simp [paraK]

theorem omega_paraK_anti_invariant (x y : Vector2D) :
    omega (paraK x) (paraK y) = -omega x y := by
  unfold omega paraK
  ring

theorem neutralMetric_formula (x y : Vector2D) :
    neutralMetric x y = -(x.x1 * y.x2 + x.x2 * y.x1) := by
  unfold neutralMetric omega paraK
  ring

theorem neutralMetric_symmetric (x y : Vector2D) :
    neutralMetric x y = neutralMetric y x := by
  rw [neutralMetric_formula, neutralMetric_formula]
  ring

theorem neutralMetric_paraK_anti_isometry (x y : Vector2D) :
    neutralMetric (paraK x) (paraK y) = -neutralMetric x y := by
  simp [neutralMetric_formula, paraK]
  ring

theorem neutralMetric_nondegenerate (x : Vector2D)
    (h : ∀ y : Vector2D, neutralMetric x y = 0) :
    x = ⟨0, 0⟩ := by
  have h₁ := h ⟨0, 1⟩
  have h₂ := h ⟨1, 0⟩
  rw [neutralMetric_formula] at h₁ h₂
  norm_num at h₁ h₂
  have hx₁ : x.x1 = 0 := by
    exact h₁
  have hx₂ : x.x2 = 0 := by
    exact h₂
  cases x
  simp_all

/-- The determinant of a `2 × 2` real matrix. -/
def det_2d (L : Matrix2D) : ℝ :=
  L.a * L.d - L.b * L.c

/-- Matrix action on 2D phase-space vectors. -/
def apply (L : Matrix2D) (v : Vector2D) : Vector2D :=
  ⟨L.a * v.x1 + L.b * v.x2, L.c * v.x1 + L.d * v.x2⟩

/-- Basis vector `e₁`. -/
def e1 : Vector2D := ⟨1, 0⟩

/-- Basis vector `e₂`. -/
def e2 : Vector2D := ⟨0, 1⟩

/-- The symplectic area scales by the determinant. -/
theorem symplectic_area_scales_by_det (L : Matrix2D) (x y : Vector2D) :
    omega (apply L x) (apply L y) = det_2d L * omega x y := by
  unfold omega apply det_2d
  ring

/-- Backward-compatible name for the determinant scaling identity. -/
theorem symplectic_preservation_eq_det_one (L : Matrix2D) (x y : Vector2D) :
    omega (apply L x) (apply L y) = det_2d L * omega x y :=
  symplectic_area_scales_by_det L x y

/-- A unit-determinant 2D linear map preserves the symplectic area form. -/
theorem symplectic_area_preserved_of_det_one (L : Matrix2D)
    (hdet : det_2d L = 1) (x y : Vector2D) :
    omega (apply L x) (apply L y) = omega x y := by
  rw [symplectic_area_scales_by_det L x y, hdet, one_mul]

/-- Preserving the symplectic area is equivalent to unit determinant. -/
theorem symplectic_preservation_iff_det_one (L : Matrix2D) :
    (∀ x y : Vector2D, omega (apply L x) (apply L y) = omega x y) ↔ det_2d L = 1 := by
  constructor
  · intro h
    have h' := h e1 e2
    dsimp [e1, e2, omega, apply, det_2d] at h'
    ring_nf at h'
    exact h'
  · intro hdet x y
    calc
      omega (apply L x) (apply L y) = det_2d L * omega x y :=
        symplectic_preservation_eq_det_one L x y
      _ = omega x y := by rw [hdet, one_mul]

end InfoGeometry.Prequantum.LiouvilleCapacity
