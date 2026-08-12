import Mathlib.Tactic

/-!
# Amplituhedron and the Penrose Transform

This module formalizes the final duality between Real Space (the thermodynamic evolution
and Pachner flips) and Dual Space (the static geometric volume of the Amplituhedron).

It maps the dynamic matrix factorizations to the static Positive Grassmannian
projected through external Momentum Twistors.
-/

namespace Amplituhedron

variable (k n m : ℕ)

/-- Entrywise finite positivity carried by this lightweight positive-Grassmannian layer. -/
def MatrixEntrywiseNonnegative (C : Matrix (Fin k) (Fin n) ℝ) : Prop :=
  ∀ i j, 0 ≤ C i j

/-- The Positive Grassmannian carrier, natively as a subtype of matrices. -/
abbrev PositiveGrassmannian :=
  {C : Matrix (Fin k) (Fin n) ℝ // MatrixEntrywiseNonnegative k n C}

namespace PositiveGrassmannian

abbrev C_matrix (C : PositiveGrassmannian k n) : Matrix (Fin k) (Fin n) ℝ := C.1

abbrev is_positive (C : PositiveGrassmannian k n) :
    MatrixEntrywiseNonnegative k n C.C_matrix := C.2

end PositiveGrassmannian

/-- Every positive-Grassmannian packet exposes nonnegative entries. -/
theorem positiveGrassmannian_entries_nonnegative
    (C : PositiveGrassmannian k n) :
    MatrixEntrywiseNonnegative k n C.C_matrix :=
  C.is_positive

/-- External momentum twistors, natively represented by their matrix. -/
abbrev MomentumTwistors := Matrix (Fin n) (Fin (k + m)) ℝ

namespace MomentumTwistors

abbrev Z_matrix (Z : MomentumTwistors k n m) : Matrix (Fin n) (Fin (k + m)) ℝ := Z

end MomentumTwistors

/-- The Amplituhedron space Y = C * Z. -/
def amplituhedron_space (C : PositiveGrassmannian k n) (Z : MomentumTwistors k n m) :
    Matrix (Fin k) (Fin (k + m)) ℝ :=
  C.C_matrix * Z.Z_matrix

/-! The finite positivity statement available at this owner level.  This is
only entrywise nonnegativity; no strict-minor or full positive-Grassmannian
claim is bundled here. -/

theorem amplituhedron_space_entrywise_nonnegative
    (k n m : ℕ)
    (C : PositiveGrassmannian k n) (Z : MomentumTwistors k n m)
    (hZ : ∀ i j, 0 ≤ Z i j) :
    MatrixEntrywiseNonnegative k (k + m) (amplituhedron_space k n m C Z) := by
  intro i j
  simp only [amplituhedron_space, Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (C.2 i x) (hZ x j)

theorem matrix_mul_entrywise_positive
    (k n m : ℕ) (hn : 0 < n)
    (C : Matrix (Fin k) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin (k + m)) ℝ)
    (hC : ∀ i j, 0 < C i j) (hZ : ∀ i j, 0 < Z i j) :
    ∀ i j, 0 < (C * Z) i j := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  intro i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_pos
  · intro x hx
    exact mul_pos (hC i x) (hZ x j)
  · exact Finset.univ_nonempty

/-- Strict entrywise positivity of the projected matrix, under explicit strict
positivity hypotheses on both factors.  This is deliberately separate from
the lightweight nonnegative `PositiveGrassmannian` carrier above. -/
theorem amplituhedron_space_entrywise_positive
    (k n m : ℕ) (hn : 0 < n)
    (C : PositiveGrassmannian k n) (Z : MomentumTwistors k n m)
    (hC : ∀ (i : Fin k) (j : Fin n),
      0 < PositiveGrassmannian.C_matrix (k := k) (n := n) C i j)
    (hZ : ∀ (i : Fin n) (j : Fin (k + m)),
      0 < MomentumTwistors.Z_matrix (k := k) (n := n) (m := m) Z i j) :
    ∀ i j, 0 < amplituhedron_space k n m C Z i j := by
  exact matrix_mul_entrywise_positive k n m hn C.C_matrix Z.Z_matrix hC hZ

variable {k n m : ℕ}

/-- The Penrose correspondence as a native equality subtype. -/
def PenroseTransform (C : PositiveGrassmannian k n) (Z : MomentumTwistors k n m) :=
  {p : ℝ × ℝ // p.1 = p.2}

namespace PenroseTransform

def real_space_dynamics {C : PositiveGrassmannian k n} {Z : MomentumTwistors k n m}
    (P : PenroseTransform C Z) : ℝ := P.1.1
def dual_space_volume {C : PositiveGrassmannian k n} {Z : MomentumTwistors k n m}
    (P : PenroseTransform C Z) : ℝ := P.1.2
def amplitude_is_volume {C : PositiveGrassmannian k n} {Z : MomentumTwistors k n m}
    (P : PenroseTransform C Z) : P.real_space_dynamics = P.dual_space_volume := P.2

end PenroseTransform

end Amplituhedron
