import proofs.NilpotentItakuraSaito

/-!
# Klein nilpotent thermodynamic sink

Repair of the external file without using an unproved analytic matrix
exponential theorem.  The finite algebraic content is the truncated nilpotent
Itakura--Saito remainder already used by the active nilpotent boundary module.
-/

noncomputable section

namespace HolographicThermo

abbrev Mat2 := NilpotentItakuraSaito.M2C

def IsNilpotent2 (Z : Mat2) : Prop :=
  InfoGeometry.Physics.SplitOctonionBraidSU3.zornMul Z Z =
    InfoGeometry.Physics.SplitOctonionBraidSU3.zornZero

/-- Concrete nilpotent boundary mode. -/
def KNil : Mat2 := NilpotentItakuraSaito.KNil

/-- Concrete nilpotency of the boundary mode. -/
theorem KNil_sq_zero : IsNilpotent2 KNil := NilpotentItakuraSaito.KNil_sq_zero

/-- Truncated Itakura--Saito divergence used for square-zero boundary modes. -/
def ItakuraSaitoDivergence (K : Mat2) : Mat2 := NilpotentItakuraSaito.nilItakuraSaito K

/-- The truncated divergence vanishes for every matrix by algebraic cancellation. -/
theorem divergence_vanishes (K : Mat2) :
    ItakuraSaitoDivergence K =
      InfoGeometry.Physics.SplitOctonionBraidSU3.zornZero := by
  exact NilpotentItakuraSaito.nilItakuraSaito_zero K

/-- In particular, the concrete nilpotent mode has zero truncated divergence. -/
theorem divergence_vanishes_on_nilpotent :
    ItakuraSaitoDivergence KNil =
      InfoGeometry.Physics.SplitOctonionBraidSU3.zornZero := by
  exact divergence_vanishes KNil

#check KNil_sq_zero
#check divergence_vanishes_on_nilpotent

end HolographicThermo
