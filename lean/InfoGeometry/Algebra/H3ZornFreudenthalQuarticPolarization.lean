import InfoGeometry.Algebra.H3ZornFreudenthalScaling
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# H₃(Zorn) finite-difference quartic polarization

This is the normalized four-variable finite difference of the existing
Freudenthal quartic.  It is deliberately kept separate from the symplectic
rank-two operator: the latter becomes a quartic-gradient object only after a
further compatibility theorem.
-/

noncomputable section

namespace InfoGeometry.Algebra.H3ZornFreudenthal

open InfoGeometry.Exceptional.Freudenthal

def quarticPolarization
    (Q : Fin 4 → FreudenthalCharge (H3Zorn ℝ)) : ℝ :=
  (1 / 24 : ℝ) * (
    quarticInvariant (Q 0 + Q 1 + Q 2 + Q 3)
      - quarticInvariant (Q 0 + Q 1 + Q 2)
      - quarticInvariant (Q 0 + Q 1 + Q 3)
      - quarticInvariant (Q 0 + Q 2 + Q 3)
      - quarticInvariant (Q 1 + Q 2 + Q 3)
      + quarticInvariant (Q 0 + Q 1)
      + quarticInvariant (Q 0 + Q 2)
      + quarticInvariant (Q 0 + Q 3)
      + quarticInvariant (Q 1 + Q 2)
      + quarticInvariant (Q 1 + Q 3)
      + quarticInvariant (Q 2 + Q 3)
      - quarticInvariant (Q 0)
      - quarticInvariant (Q 1)
      - quarticInvariant (Q 2)
      - quarticInvariant (Q 3))

theorem quarticPolarization_diagonal
    (Q : FreudenthalCharge (H3Zorn ℝ)) :
    quarticPolarization (fun _ => Q) = quarticInvariant Q := by
  unfold quarticPolarization
  have h2 : quarticInvariant (Q + Q) = (2 : ℝ) ^ 4 * quarticInvariant Q := by
    have h : Q + Q = (2 : ℝ) • Q := by module
    rw [h, quarticInvariant_smul]
  have h3 : quarticInvariant (Q + Q + Q) = (3 : ℝ) ^ 4 * quarticInvariant Q := by
    have h : Q + Q + Q = (3 : ℝ) • Q := by module
    rw [h, quarticInvariant_smul]
  have h4 : quarticInvariant (Q + Q + Q + Q) = (4 : ℝ) ^ 4 * quarticInvariant Q := by
    have h : Q + Q + Q + Q = (4 : ℝ) • Q := by module
    rw [h, quarticInvariant_smul]
  simp [h4, h3, h2]
  ring




end InfoGeometry.Algebra.H3ZornFreudenthal
