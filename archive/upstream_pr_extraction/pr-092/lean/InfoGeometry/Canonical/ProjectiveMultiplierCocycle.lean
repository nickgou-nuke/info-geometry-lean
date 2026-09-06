import Mathlib.Tactic

/-!
# Projective multipliers and the cocycle identity

This is the algebraic lift layer.  It records a chosen family of operators
whose multiplication is scalar-valued up to a group law.  The cocycle class
itself is intentionally not identified here; that requires a concrete group
and a cohomology computation.
-/

noncomputable section

namespace InfoGeometry.Canonical.ProjectiveMultiplierCocycle

structure ProjectiveMultiplierData (G A : Type*) [Group G] [Ring A]
    [Algebra ℂ A] where
  lift : G → A
  multiplier : G → G → ℂ
  lift_nonzero : ∀ g, lift g ≠ 0
  lift_mul : ∀ g h, lift g * lift h = multiplier g h • lift (g * h)

theorem scalar_separation {A : Type*} [Ring A] [Algebra ℂ A]
    {a b : ℂ} {x : A} (hx : x ≠ 0) (h : a • x = b • x) : a = b := by
  have hzero : (a - b) • x = 0 := by
    rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hx)

theorem multiplier_cocycle {G A : Type*} [Group G] [Ring A] [Algebra ℂ A]
    (D : ProjectiveMultiplierData G A) (g h k : G) :
    D.multiplier g h * D.multiplier (g * h) k =
      D.multiplier h k * D.multiplier g (h * k) := by
  have hassoc : (D.lift g * D.lift h) * D.lift k =
      D.lift g * (D.lift h * D.lift k) := by rw [mul_assoc]
  have hleft :
      (D.lift g * D.lift h) * D.lift k =
        (D.multiplier g h * D.multiplier (g * h) k) • D.lift (g * h * k) := by
    calc
      (D.lift g * D.lift h) * D.lift k =
          (D.multiplier g h • D.lift (g * h)) * D.lift k := by rw [D.lift_mul]
      _ = D.multiplier g h • (D.lift (g * h) * D.lift k) := by
        rw [smul_mul_assoc]
      _ = D.multiplier g h •
          (D.multiplier (g * h) k • D.lift (g * h * k)) := by
        rw [D.lift_mul]
      _ = (D.multiplier g h * D.multiplier (g * h) k) •
          D.lift (g * h * k) := by rw [smul_smul]
  have hright :
      D.lift g * (D.lift h * D.lift k) =
        (D.multiplier h k * D.multiplier g (h * k)) • D.lift (g * (h * k)) := by
    calc
      D.lift g * (D.lift h * D.lift k) =
          D.lift g * (D.multiplier h k • D.lift (h * k)) := by rw [D.lift_mul]
      _ = D.multiplier h k • (D.lift g * D.lift (h * k)) := by
        rw [mul_smul_comm]
      _ = D.multiplier h k •
          (D.multiplier g (h * k) • D.lift (g * (h * k))) := by
        rw [D.lift_mul]
      _ = (D.multiplier h k * D.multiplier g (h * k)) •
          D.lift (g * (h * k)) := by rw [smul_smul]
  have hscalar :
      (D.multiplier g h * D.multiplier (g * h) k) • D.lift (g * h * k) =
        (D.multiplier h k * D.multiplier g (h * k)) • D.lift (g * (h * k)) := by
    calc
      _ = (D.lift g * D.lift h) * D.lift k := hleft.symm
      _ = D.lift g * (D.lift h * D.lift k) := hassoc
      _ = _ := hright
  apply scalar_separation (D.lift_nonzero (g * h * k))
  simpa [mul_assoc] using hscalar

end InfoGeometry.Canonical.ProjectiveMultiplierCocycle

end noncomputable section
