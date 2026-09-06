import InfoGeometry.Convex.Legendre
import InfoGeometry.Convex.Bregman
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import InfoGeometry.Dynamics.DuallyFlatOperatorFamily

namespace InfoGeometry.Thermo.ProjectiveQuadraticPotential

open InfoGeometry.Convex.LegendrePotential
open InfoGeometry.Dynamics.DuallyFlat

/-!
# A concrete nonlinear scalar potential for the projective chart corridor

The projective scaling readout is affine and therefore has zero Hessian.  This
owner supplies the separate strictly convex scalar model needed by the
Amari--Souriau `LegendrePotential` interface.
-/

def quadraticPotential (t : ℝ) : ℝ := t ^ (2 : ℕ)

noncomputable def scalarInteraction : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ :=
  (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

noncomputable def scalarQuadraticOperatorFamily :
    OperatorFamily scalarInteraction where
  Psi := quadraticPotential
  entropy := fun _ => 0
  spaceToMatter := id
  matterToSpace := id
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  legendre_identity := by
    intro x
    simp [scalarInteraction, quadraticPotential, pow_two]

theorem scalarQuadraticOperatorFamily_bregman_self (x : ℝ) :
    OperatorFamily.bregmanDivergence scalarInteraction
      scalarQuadraticOperatorFamily x x = 0 := by
  exact OperatorFamily.bregmanDivergence_self scalarInteraction
    scalarQuadraticOperatorFamily x

def quadraticLegendrePotential : InfoGeometry.Convex.LegendrePotential where
  f := quadraticPotential
  smooth := by
    simpa [quadraticPotential] using
      ((contDiff_id : ContDiff ℝ 2 id).pow 2)
  strict_convex := by
    simpa [quadraticPotential] using
      (Even.strictConvexOn_pow (n := 2)
        (by decide : Even 2) (by decide : (2 : ℕ) ≠ 0))

theorem quadraticPotential_deriv (t : ℝ) :
    deriv quadraticPotential t = 2 * t := by
  unfold quadraticPotential
  simpa using (deriv_pow_field (x := t) (n := 2))

theorem quadraticLegendrePotential_fisher (t : ℝ) :
    InfoGeometry.Convex.LegendrePotential.fisher quadraticLegendrePotential t = 2 := by
  simp only [InfoGeometry.Convex.LegendrePotential.fisher,
    quadraticLegendrePotential]
  have hderiv : deriv quadraticPotential = fun t : ℝ => 2 * t := by
    funext t
    exact quadraticPotential_deriv t
  rw [hderiv]
  simpa using (hasDerivAt_id t).const_mul 2 |>.deriv

theorem quadraticLegendrePotential_fisher_pos (t : ℝ) :
    0 < InfoGeometry.Convex.LegendrePotential.fisher quadraticLegendrePotential t := by
  rw [quadraticLegendrePotential_fisher]
  norm_num

/-- The quadratic potential has the expected squared-distance Bregman defect. -/
theorem quadraticPotential_bregman_formula (x y : ℝ) :
    InfoGeometry.bregmanDiv quadraticPotential x y = (x - y) ^ 2 := by
  unfold InfoGeometry.bregmanDiv
  rw [quadraticPotential_deriv]
  dsimp [quadraticPotential]
  ring

end InfoGeometry.Thermo.ProjectiveQuadraticPotential
