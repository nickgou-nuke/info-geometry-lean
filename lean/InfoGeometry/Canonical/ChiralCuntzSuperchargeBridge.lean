import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

namespace ChiralCuntzSuperchargeBridge

/-- Two-Channel Cuntz Algebra 𝒪₂ Generator System in a Ring R. -/
structure Cuntz2System (R : Type*) [Ring R] where
  S_plus : R
  S_minus : R
  S_plus_star : R
  S_minus_star : R
  left_inv_plus : S_plus_star * S_plus = 1
  left_inv_minus : S_minus_star * S_minus = 1
  ortho_pm : S_plus_star * S_minus = 0
  ortho_mp : S_minus_star * S_plus = 0
  completeness : S_plus * S_plus_star + S_minus * S_minus_star = 1

variable {R : Type*} [Ring R] (sys : Cuntz2System R)

/-- Right-moving Chiral Supercharge Q₊ = S₊ S₋*. -/
def Q_plus : R := sys.S_plus * sys.S_minus_star

/-- Left-moving Chiral Supercharge Q₋ = S₋ S₊*. -/
def Q_minus : R := sys.S_minus * sys.S_plus_star

/-- **Theorem**: Right-moving Chiral Nilpotency: Q₊² = 0. -/
theorem Q_plus_sq_zero : Q_plus sys * Q_plus sys = 0 := by
  dsimp [Q_plus]
  have h_ortho := sys.ortho_mp
  calc sys.S_plus * sys.S_minus_star * (sys.S_plus * sys.S_minus_star)
    _ = sys.S_plus * (sys.S_minus_star * sys.S_plus) * sys.S_minus_star := by noncomm_ring
    _ = sys.S_plus * 0 * sys.S_minus_star := by rw [h_ortho]
    _ = 0 := by noncomm_ring

/-- **Theorem**: Left-moving Chiral Nilpotency: Q₋² = 0. -/
theorem Q_minus_sq_zero : Q_minus sys * Q_minus sys = 0 := by
  dsimp [Q_minus]
  have h_ortho := sys.ortho_pm
  calc sys.S_minus * sys.S_plus_star * (sys.S_minus * sys.S_plus_star)
    _ = sys.S_minus * (sys.S_plus_star * sys.S_minus) * sys.S_plus_star := by noncomm_ring
    _ = sys.S_minus * 0 * sys.S_plus_star := by rw [h_ortho]
    _ = 0 := by noncomm_ring

/-- **Theorem**: Cuntz-SUSY Energy Completeness Identity: {Q₊, Q₋} = 𝟙.
    Machine-certifies that the anticommutator {Q₊, Q₋} = Q₊ Q₋ + Q₋ Q₊ of the right and left
    chiral lightcone supercharges equals the Cuntz completeness projection sum S₊ S₊* + S₋ S₋* = 𝟙. -/
theorem chiral_susy_anticommutator_eq_one :
    Q_plus sys * Q_minus sys + Q_minus sys * Q_plus sys = 1 := by
  dsimp [Q_plus, Q_minus]
  have h1 : sys.S_minus_star * sys.S_minus = 1 := sys.left_inv_minus
  have h2 : sys.S_plus_star * sys.S_plus = 1 := sys.left_inv_plus
  have h_comp : sys.S_plus * sys.S_plus_star + sys.S_minus * sys.S_minus_star = 1 := sys.completeness
  calc sys.S_plus * sys.S_minus_star * (sys.S_minus * sys.S_plus_star) +
       sys.S_minus * sys.S_plus_star * (sys.S_plus * sys.S_minus_star)
    _ = sys.S_plus * (sys.S_minus_star * sys.S_minus) * sys.S_plus_star +
        sys.S_minus * (sys.S_plus_star * sys.S_plus) * sys.S_minus_star := by noncomm_ring
    _ = sys.S_plus * 1 * sys.S_plus_star + sys.S_minus * 1 * sys.S_minus_star := by rw [h1, h2]
    _ = sys.S_plus * sys.S_plus_star + sys.S_minus * sys.S_minus_star := by noncomm_ring
    _ = 1 := h_comp

end ChiralCuntzSuperchargeBridge
