import Mathlib

/-!
# Projective multipliers and honest actions on observables

The scalar defect is recorded at the lift level.  Conjugation removes that
defect, so observables always carry an honest action.  The cocycle theorem is
stated only when the scalar embedding is central and injective.
-/

noncomputable section

namespace InfoGeometry.Canonical.ProjectiveRepresentationCocycle

structure Data (G U C : Type*) [Group G] [Group U] [Group C]
    (scalar : C →* U) where
  lift : G → U
  multiplier : G → G → C
  lift_one : lift 1 = 1
  scalar_central : ∀ c u, scalar c * u = u * scalar c
  lift_mul : ∀ g h,
    lift (g * h) = scalar (multiplier g h) * (lift g * lift h)

def adjointAction {G U C : Type*} [Group G] [Group U] [Group C]
    {scalar : C →* U} (P : Data G U C scalar) (g : G) (u : U) : U :=
  P.lift g * u * (P.lift g)⁻¹

theorem adjointAction_one {G U C : Type*} [Group G] [Group U] [Group C]
    {scalar : C →* U} (P : Data G U C scalar) (u : U) :
    adjointAction P 1 u = u := by
  simp [adjointAction, P.lift_one]

theorem adjointAction_mul {G U C : Type*} [Group G] [Group C]
    [Group U] {scalar : C →* U} (P : Data G U C scalar) (g h : G) (u : U) :
    adjointAction P (g * h) u =
      adjointAction P g (adjointAction P h u) := by
  simp only [adjointAction]
  rw [P.lift_mul]
  simp only [mul_inv_rev, mul_assoc]
  rw [P.scalar_central]
  group

/-- Associativity of a projective lift forces its multiplier to be a
2-cocycle, provided the scalar embedding is injective. -/
theorem multiplier_cocycle
    {G U C : Type*} [Group G] [Group C] [Group U]
    {scalar : C →* U} (hscalar : Function.Injective scalar)
    (P : Data G U C scalar) (g h k : G) :
    P.multiplier g h * P.multiplier (g * h) k =
      P.multiplier h k * P.multiplier g (h * k) := by
  have hEq : P.lift ((g * h) * k) = P.lift (g * (h * k)) := by
    rw [mul_assoc]
  rw [P.lift_mul, P.lift_mul, P.lift_mul, P.lift_mul] at hEq
  simp only [← mul_assoc] at hEq
  have hswap :
      scalar (P.multiplier (g * h) k) * scalar (P.multiplier g h) =
        scalar (P.multiplier g h) * scalar (P.multiplier (g * h) k) :=
    P.scalar_central _ _
  rw [hswap] at hEq
  have hmove :
      scalar (P.multiplier g (h * k)) * P.lift g *
          scalar (P.multiplier h k) * P.lift h * P.lift k =
        scalar (P.multiplier h k) * scalar (P.multiplier g (h * k)) *
          P.lift g * P.lift h * P.lift k := by
    calc
      scalar (P.multiplier g (h * k)) * P.lift g *
            scalar (P.multiplier h k) * P.lift h * P.lift k =
          scalar (P.multiplier g (h * k)) *
            (P.lift g * scalar (P.multiplier h k)) *
              P.lift h * P.lift k := by simp only [mul_assoc]
      _ = scalar (P.multiplier g (h * k)) *
            (scalar (P.multiplier h k) * P.lift g) *
              P.lift h * P.lift k := by rw [← P.scalar_central]
      _ = (scalar (P.multiplier g (h * k)) *
            scalar (P.multiplier h k)) * P.lift g * P.lift h * P.lift k := by
            simp only [mul_assoc]
      _ = (scalar (P.multiplier h k) *
            scalar (P.multiplier g (h * k))) * P.lift g * P.lift h * P.lift k := by
            rw [P.scalar_central]
      _ = scalar (P.multiplier h k) * scalar (P.multiplier g (h * k)) *
            P.lift g * P.lift h * P.lift k := by simp only [mul_assoc]
  rw [hmove] at hEq
  apply hscalar
  apply mul_right_cancel (b := P.lift g * P.lift h * P.lift k)
  simpa [mul_assoc] using hEq

theorem rephase_multiplier
    {G U C : Type*} [Group G] [Group U] [Group C]
    {scalar : C →* U} (P : Data G U C scalar)
    (f : G → C) (g h : G) :
    scalar (f g * f h * (f (g * h))⁻¹) *
        scalar (P.multiplier g h) =
      scalar (f g) * scalar (f h) *
        (scalar (f (g * h)))⁻¹ * scalar (P.multiplier g h) := by
  simp [map_mul, mul_assoc]

end InfoGeometry.Canonical.ProjectiveRepresentationCocycle

end noncomputable section
