import InfoGeometry.Algebra.H3ZornJordanIdentity

/-!
# Resolved H₃ Zorn obstruction audit

This module keeps the historical sparse pair used during obstruction searches
and records the current verified Jordan-law surface.  The global product law is
proved in `H3ZornJordanIdentity`, so the historical sparse pair satisfies the
law as well.
-/

namespace InfoGeometry.Algebra

open H3Zorn

/-- Historical first argument used in rejected obstruction searches. -/
noncomputable def formerJordanObstructionA : H3Zorn ℝ :=
  { α₁ := 0, α₂ := 0, α₃ := 0
    a := ZornVectorMatrix.E11
    b := ZornVectorMatrix.E11
    c := ZornVectorMatrix.zero }

/-- Historical second argument used in rejected obstruction searches. -/
noncomputable def formerJordanObstructionB : H3Zorn ℝ :=
  { α₁ := 1, α₂ := 0, α₃ := 0
    a := ZornVectorMatrix.zero
    b := ZornVectorMatrix.zero
    c := ZornVectorMatrix.zero }

/-- Pointwise Jordan-law statement for the historical obstruction pair. -/
def formerJordanObstructionQuestion : Prop :=
  H3ZornJordanProductLawAt formerJordanObstructionA formerJordanObstructionB

/-- The historical pair satisfies the Jordan law by the native global proof. -/
theorem formerJordanObstructionQuestion_proof :
    formerJordanObstructionQuestion := by
  exact H3ZornJordanProductLaw_holds
    formerJordanObstructionA formerJordanObstructionB

/-- The historical pair also satisfies the scalar-free `T`-commutation
readback. -/
def formerJordanObstructionQuestion_T : Prop :=
  T (T formerJordanObstructionA 1 formerJordanObstructionB) 1
      (T formerJordanObstructionA 1 formerJordanObstructionA) =
    T formerJordanObstructionA 1
      (T formerJordanObstructionB 1 (T formerJordanObstructionA 1 formerJordanObstructionA))

/-- The historical pair satisfies the scalar-free `T`-commutation readback. -/
theorem formerJordanObstructionQuestion_T_proof :
    formerJordanObstructionQuestion_T := by
  exact (H3ZornJordanProductLawAt_iff_TJordanCommutation
    formerJordanObstructionA formerJordanObstructionB).1
    formerJordanObstructionQuestion_proof

end InfoGeometry.Algebra
