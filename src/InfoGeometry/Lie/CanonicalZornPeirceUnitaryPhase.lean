import Mathlib.LinearAlgebra.UnitaryGroup
import InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge

/-!
# Complex unitary and independent phase layers

The real Peirce derivation stabilizer is an `SL₃(ℝ)` object.  This file keeps
the complex unitary real-form layer and the `U(1)` phase factor separate from
that real Lie-algebra stabilizer.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornPeirceUnitaryPhase

abbrev ComplexVector3 := Fin 3 → ℂ
abbrev ComplexOffDiagonal := ComplexVector3 × ComplexVector3
abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ
abbrev U1 := Matrix.unitaryGroup (Fin 1) ℂ
abbrev SU3U1 := SU3 × U1

/-- Fundamental complex action on the upper Peirce colour slot. -/
def su3UpperAction (g : SU3) (u : ComplexVector3) : ComplexVector3 :=
  g.1.mulVec u

/-- Contragradient complex action on the lower Peirce anticolour slot. -/
def su3LowerAction (g : SU3) (v : ComplexVector3) : ComplexVector3 :=
  (g⁻¹ : SU3).1.transpose.mulVec v

/-- The complexified colour action on the two off-diagonal slots. -/
def su3OffDiagonalAction (g : SU3) (z : ComplexOffDiagonal) :
    ComplexOffDiagonal :=
  (su3UpperAction g z.1, su3LowerAction g z.2)

@[simp] theorem su3UpperAction_one (u : ComplexVector3) :
    su3UpperAction (1 : SU3) u = u := by
  ext i
  simp [su3UpperAction]

@[simp] theorem su3LowerAction_one (v : ComplexVector3) :
    su3LowerAction (1 : SU3) v = v := by
  ext i
  simp [su3LowerAction]

@[simp] theorem su3OffDiagonalAction_one (z : ComplexOffDiagonal) :
    su3OffDiagonalAction (1 : SU3) z = z := by
  cases z
  simp [su3OffDiagonalAction]

/-- The scalar entry of a one-dimensional unitary matrix.  This is the
independent phase carrier; no identification with a derivation is made. -/
def u1Scalar (z : U1) : ℂ := z.1 0 0

@[simp] theorem u1Scalar_one : u1Scalar (1 : U1) = 1 := by
  simp [u1Scalar]

theorem u1Scalar_mul (z w : U1) :
    u1Scalar (z * w) = u1Scalar z * u1Scalar w := by
  change (z.1 * w.1) 0 0 = z.1 0 0 * w.1 0 0
  rw [Matrix.mul_apply, Fin.sum_univ_one]

/-- The independent `U(1)` phase action on a complex field. -/
def u1PhaseAction (z : U1) (w : ℂ) : ℂ :=
  u1Scalar z * w

@[simp] theorem u1PhaseAction_one (w : ℂ) :
    u1PhaseAction (1 : U1) w = w := by
  simp [u1PhaseAction]

theorem u1PhaseAction_mul (z w : U1) (q : ℂ) :
    u1PhaseAction (z * w) q = u1PhaseAction z (u1PhaseAction w q) := by
  simp [u1PhaseAction, u1Scalar_mul, mul_assoc]

/-- A separate colour-plus-phase action datum.  Its phase component is an
independent extension and is not asserted to lie in the real Peirce
stabilizer. -/
def su3U1OffDiagonalAction
    (g : SU3U1) (z : ComplexOffDiagonal) : ComplexOffDiagonal :=
  (fun i => u1PhaseAction g.2 (su3UpperAction g.1 z.1 i),
   fun i => u1PhaseAction g.2 (su3LowerAction g.1 z.2 i))

end InfoGeometry.Lie.CanonicalZornPeirceUnitaryPhase

end
