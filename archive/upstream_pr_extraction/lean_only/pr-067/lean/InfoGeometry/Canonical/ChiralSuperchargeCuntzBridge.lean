import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.ChiralSuperchargeCuntzBridge

/-- **Definition**: Chiral Supercharges Q and Qbar obeying Nilpotency Q² = 0, Qbar² = 0. -/
structure ChiralSupercharges (V : Type*) [AddCommGroup V] where
  Q : V → V
  Qbar : V → V
  Q_sq : ∀ x : V, Q (Q x) = 0
  Qbar_sq : ∀ x : V, Qbar (Qbar x) = 0

namespace ChiralSupercharges

variable {V : Type*} [AddCommGroup V] (s : ChiralSupercharges V)

/-- **Theorem**: Chiral Supercharge Nilpotency Q² = 0. -/
theorem supercharge_nilpotent (x : V) :
    s.Q (s.Q x) = 0 ∧ s.Qbar (s.Qbar x) = 0 := by
  constructor
  · exact s.Q_sq x
  · exact s.Qbar_sq x

end ChiralSupercharges

/-- **Definition**: Chiral Cuntz Algebra Generators S+, S- obeying Isometry and Range Orthogonality. -/
structure ChiralCuntzGenerators (R : Type*) [Ring R] where
  Splus : R
  Sminus : R
  Splus_star : R
  Sminus_star : R
  isometry_plus : Splus_star * Splus = 1
  isometry_minus : Sminus_star * Sminus = 1
  ortho_pm : Splus_star * Sminus = 0
  ortho_mp : Sminus_star * Splus = 0

namespace ChiralCuntzGenerators

variable {R : Type*} [Ring R] (c : ChiralCuntzGenerators R)

/-- **Definition**: Chiral Projection Idempotents e+ = S+ S+*, e- = S- S-*. -/
def ePlus : R := c.Splus * c.Splus_star
def eMinus : R := c.Sminus * c.Sminus_star

/-- **Theorem**: Chiral Projection Idempotency e+² = e+, e-² = e-. -/
theorem chiral_projections_idempotent :
    c.ePlus * c.ePlus = c.ePlus ∧ c.eMinus * c.eMinus = c.eMinus := by
  constructor
  · dsimp [ePlus]
    calc c.Splus * c.Splus_star * (c.Splus * c.Splus_star)
      _ = c.Splus * (c.Splus_star * c.Splus) * c.Splus_star := by noncomm_ring
      _ = c.Splus * 1 * c.Splus_star := by rw [c.isometry_plus]
      _ = c.Splus * c.Splus_star := by noncomm_ring
  · dsimp [eMinus]
    calc c.Sminus * c.Sminus_star * (c.Sminus * c.Sminus_star)
      _ = c.Sminus * (c.Sminus_star * c.Sminus) * c.Sminus_star := by noncomm_ring
      _ = c.Sminus * 1 * c.Sminus_star := by rw [c.isometry_minus]
      _ = c.Sminus * c.Sminus_star := by noncomm_ring

end ChiralCuntzGenerators

/-- **Theorem**: Master Chiral Supercharges & Cuntz Algebra Synthesis.
    Unifies:
    1. Chiral supercharge nilpotency Q² = 0, Qbar² = 0.
    2. Cuntz algebra isometry S* S = 1 and range orthogonality S+* S- = 0.
    3. Chiral projection idempotency e+² = e+, e-² = e-. -/
theorem master_chiral_supercharge_cuntz_synthesis
    {V R : Type*} [AddCommGroup V] [Ring R]
    (s : ChiralSupercharges V) (c : ChiralCuntzGenerators R) (v : V) :
    (s.Q (s.Q v) = 0) ∧
    (s.Qbar (s.Qbar v) = 0) ∧
    (c.Splus_star * c.Splus = 1) ∧
    (c.Splus_star * c.Sminus = 0) ∧
    (c.ePlus * c.ePlus = c.ePlus) ∧
    (c.eMinus * c.eMinus = c.eMinus) := by
  have hq := s.supercharge_nilpotent v
  exact ⟨
  hq.1,
  hq.2,
  c.isometry_plus,
  c.ortho_pm,
  (c.chiral_projections_idempotent).1,
  (c.chiral_projections_idempotent).2
⟩

end InfoGeometry.Canonical.ChiralSuperchargeCuntzBridge
