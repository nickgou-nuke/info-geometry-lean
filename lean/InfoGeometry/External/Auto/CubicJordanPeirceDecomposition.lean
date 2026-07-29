import Mathlib.Tactic

/-!
# Cubic Jordan / Peirce tripotent anchors

Finite associative-ring Peirce anchors for the canonical tripotent
`P = E₁ - E₂`.  The true Albert/Jordan/split-octonion setting is represented by
sockets elsewhere; here we prove the diagonal Peirce algebra identities without
commutativity assumptions by explicitly requiring two-sided orthogonality.
-/

noncomputable section

namespace CubicJordanPeirceDecomposition

/-- Two-sided orthogonal Peirce idempotents. -/
abbrev PeirceIdempotents {A : Type*} [Ring A] (E1 E2 E3 : A) : Prop :=
  (E1 * E1 = E1 ∧ E2 * E2 = E2 ∧ E3 * E3 = E3) ∧
  (E1 * E2 = 0 ∧ E2 * E1 = 0 ∧ E2 * E3 = 0 ∧ E3 * E2 = 0 ∧
    E3 * E1 = 0 ∧ E1 * E3 = 0)

variable {A : Type*} [Ring A]
variable (E1 E2 E3 : A)

/-- Canonical Peirce tripotent. -/
def Pcanonical : A := E1 - E2

/-- Square of the canonical Peirce tripotent. -/
theorem Pcanonical_sq (h : PeirceIdempotents E1 E2 E3) :
    Pcanonical E1 E2 * Pcanonical E1 E2 = E1 + E2 := by
  unfold Pcanonical
  calc
    (E1 - E2) * (E1 - E2)
        = E1 * E1 - E1 * E2 - E2 * E1 + E2 * E2 := by noncomm_ring
    _ = E1 - 0 - 0 + E2 := by rw [h.1.1, h.2.1, h.2.2.1, h.1.2.1]
    _ = E1 + E2 := by simp

/-- Verification of the tripotent condition `P³=P` for `P=E₁-E₂`. -/
theorem Pcanonical_is_tripotent (h : PeirceIdempotents E1 E2 E3) :
    Pcanonical E1 E2 * Pcanonical E1 E2 * Pcanonical E1 E2 = Pcanonical E1 E2 := by
  unfold Pcanonical
  rw [show (E1 - E2) * (E1 - E2) = E1 + E2 by
    simpa [Pcanonical] using Pcanonical_sq (E1 := E1) (E2 := E2) (E3 := E3) h]
  calc
    (E1 + E2) * (E1 - E2)
        = E1 * E1 - E1 * E2 + E2 * E1 - E2 * E2 := by noncomm_ring
    _ = E1 - 0 + 0 - E2 := by rw [h.1.1, h.2.1, h.2.2.1, h.1.2.1]
    _ = E1 - E2 := by simp

/-- `E₁` belongs to the `+1` eigenspace of left multiplication by `P`. -/
theorem L_P_E1_eigen (h : PeirceIdempotents E1 E2 E3) :
    Pcanonical E1 E2 * E1 = E1 := by
  unfold Pcanonical
  rw [sub_mul, h.1.1, h.2.2.1, sub_zero]

/-- `E₂` belongs to the `-1` eigenspace of left multiplication by `P`. -/
theorem L_P_E2_eigen (h : PeirceIdempotents E1 E2 E3) :
    Pcanonical E1 E2 * E2 = -E2 := by
  unfold Pcanonical
  rw [sub_mul, h.2.1, h.1.2.1, zero_sub]

/-- `E₃` belongs to the `0` eigenspace of left multiplication by `P`. -/
theorem L_P_E3_zero (h : PeirceIdempotents E1 E2 E3) :
    Pcanonical E1 E2 * E3 = 0 := by
  unfold Pcanonical
  rw [sub_mul, h.2.2.2.2.2.2, h.2.2.2.1, sub_self]



end CubicJordanPeirceDecomposition
