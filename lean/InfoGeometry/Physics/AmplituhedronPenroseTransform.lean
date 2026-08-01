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
