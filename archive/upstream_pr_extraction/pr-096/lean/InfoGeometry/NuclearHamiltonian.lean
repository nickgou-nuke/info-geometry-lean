import Mathlib.Tactic
import InfoGeometry.Canonical.ZornSpinor

namespace InfoGeometry

/-!
The top-level carrier is the existing canonical Zorn-matrix algebra used by
the TKK/isospin owners.  This keeps the compatibility name while exposing a
genuine noncommutative algebraic carrier instead of an empty placeholder.
-/
abbrev NuclearHamiltonian : Type := InfoGeometry.Canonical.ZornMatrix ℚ

end InfoGeometry
