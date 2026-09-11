import InfoGeometry.Canonical.FiniteHeisenbergGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ProjectiveMultiplierCocycle

/-!
# Projective cocycles on the finite Heisenberg carrier

This file is only the concrete finite-group adapter.  The operator-valued lift
and its scalar multiplier are supplied by the caller; the cocycle identity is
inherited from the canonical projective-multiplier owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteHeisenbergProjectiveCocycle

open InfoGeometry.Canonical.FiniteHeisenbergCore

abbrev Data (n : ℕ) (A : Type*) [Ring A] [Algebra ℂ A] :=
  ProjectiveMultiplierCocycle.ProjectiveMultiplierData
    (FiniteHeisenberg n) A

/-- A supplied projective lift on the finite Heisenberg group has the native
multiplier cocycle identity. -/
theorem multiplier_cocycle {n : ℕ} {A : Type*} [Ring A] [Algebra ℂ A]
    (D : Data n A) (g h k : FiniteHeisenberg n) :
    D.multiplier g h * D.multiplier (g * h) k =
      D.multiplier h k * D.multiplier g (h * k) := by
  exact ProjectiveMultiplierCocycle.multiplier_cocycle D g h k

/-- The finite Heisenberg commutator is the explicitly central coordinate
defect carried by the underlying group law. -/
theorem commutator_central_coordinate
    {n : ℕ} (x y : FiniteHeisenberg n) :
    x * y * x⁻¹ * y⁻¹ =
      finiteHeisenbergCenterElement
        (x.coord.1.1 * y.coord.1.2 - y.coord.1.1 * x.coord.1.2) := by
  exact finiteHeisenberg_group_commutator x y

end InfoGeometry.Canonical.FiniteHeisenbergProjectiveCocycle

end noncomputable section
