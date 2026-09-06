import InfoGeometry.Spectral.Homology.Basic

/-!
# Suspension shifts (the algebraic core of the sphere calculation)

The old `homology/sphere.hlean` proves a repeated suspension shift.  This file
ports that reusable algebraic statement; it does not add a topological sphere
carrier that is absent from the current Lean project.
-/

namespace InfoGeometry.Spectral.Homology.Sphere

open InfoGeometry.Spectral.Cohomology.Basic

universe u

def suspensionPow (T : HomologyTheory) : ℕ → Type u → Type u
  | 0, X => X
  | n + 1, X => T.suspension (suspensionPow T n X)

def iteratedSuspensionShift (T : HomologyTheory) (n : ℤ) (m : ℕ) (X : Type u) :
    T.carrier (n + m) (suspensionPow T m X) ≃ T.carrier n X := by
  induction m with
  | zero =>
      convert (Equiv.refl (T.carrier n X)) using 1 <;>
        simp [suspensionPow]
  | succ m ih =>
      convert (T.susp_iso (n + m) (suspensionPow T m X)).trans ih using 1 <;>
        simp [suspensionPow, add_assoc]

@[simp]
theorem suspensionPow_zero (T : HomologyTheory) (X : Type u) :
    suspensionPow T 0 X = X :=
  rfl

end InfoGeometry.Spectral.Homology.Sphere
