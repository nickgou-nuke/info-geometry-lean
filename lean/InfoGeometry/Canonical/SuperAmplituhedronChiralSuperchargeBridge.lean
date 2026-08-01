import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.SuperAmplituhedronChiralSuperchargeBridge

/-- **Definition**: Super-Amplituhedron State Space V with Chiral Supercharge Q and Form Ω. -/
structure SuperAmplituhedronState (V : Type*) [AddCommGroup V] where
  Q : V →+ V
  Omega : V
  ePlus : V →+ V
  Q_sq : ∀ x : V, Q (Q x) = 0
  Q_invariance : Q Omega = 0
  ePlus_commute_Q : ∀ x : V, Q (ePlus x) = ePlus (Q x)

namespace SuperAmplituhedronState

variable {V : Type*} [AddCommGroup V] (s : SuperAmplituhedronState V)

/-- **Theorem**: Chiral Supercharge Invariance of Super-Amplituhedron Form Ω (Q(Ω) = 0). -/
theorem form_invariance :
    s.Q s.Omega = 0 :=
  s.Q_invariance

/-- **Theorem**: Nilpotent Chiral Supercharge Action on Form Ω (Q(Q Ω) = 0). -/
theorem form_nilpotent :
    s.Q (s.Q s.Omega) = 0 := by
  rw [s.Q_invariance, map_zero]

/-- **Theorem**: Boundary Chiral Cuntz Projector Invariance under Chiral Supercharges (Q(e+ Ω) = 0). -/
theorem boundary_projector_invariance :
    s.Q (s.ePlus s.Omega) = 0 := by
  rw [s.ePlus_commute_Q, s.Q_invariance, map_zero]

end SuperAmplituhedronState

end InfoGeometry.Canonical.SuperAmplituhedronChiralSuperchargeBridge
