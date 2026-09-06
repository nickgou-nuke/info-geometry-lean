import InfoGeometry.Canonical.NormalOrderedCurrent
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.MajoranaPHSZeroMode
import InfoGeometry.Canonical.SuperchargeCARCCRBridge

/-!
# InfoGeometry.Canonical.BoundaryMajoranaCircuitModel

Theorem-only synthesis surface for the boundary Majorana circuit model.

This file does not introduce a new structure or a new algebraic model. It
packages the already-owned theorem surfaces into one conjunction:

* the finite Majorana/PHS swap;
* the canonical boundary zero-mode lane;
* the finite matrix-unit Wick current anomaly;
* the completed boundary current Heisenberg law.

The boundary algebra is still carried by the existing owner files. This
module is just the theorem-level synthesis point.
-/

namespace InfoGeometry.Canonical.BoundaryMajoranaCircuitModel

open InfoGeometry.Canonical.NormalOrderedCurrent
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.MajoranaPHSZeroMode
open InfoGeometry.Canonical.SuperchargeCARCCRBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The boundary Majorana circuit model packages the PHS swap, the canonical
boundary zero-mode lane, the Wick-corrected matrix-unit current law, and the
completed current central term.  It does not identify the boundary with the
center of an operator algebra and it does not assert a Riemann-spectrum theorem.
-/
theorem boundaryMajoranaCircuitModel :
    IsPHSInvariant
      ((concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) :
        InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E)
      ∧ IsBoundaryZeroMode
          (cptSuperchargeOp (E := E))
          (cptSuperchargeOp (E := E))
      ∧ (∀ {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
          (occ : ι → ℤ) (a b c d : ι),
            algebraCommutator
                (normalOrderedMatrixUnit (R := R) occ a b)
                (normalOrderedMatrixUnit (R := R) occ c d)
              =
              (if b = c then normalOrderedMatrixUnit (R := R) occ a d else 0)
                - (if a = d then normalOrderedMatrixUnit (R := R) occ c b else 0)
                + wickCorrection (R := R) occ a b c d)
      ∧ (∀ {A : Type*} [Ring A]
          (C : InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeAlgebra A)
          (m n : Int),
            InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted C
                (InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
                (InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n) =
              if m + n = 0 then
                m • InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
              else 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact concrete_majorana_swap_is_phs_invariant (E := E)
  · exact cptSuperchargeOp_is_boundary_zero_mode (E := E)
  · intro ι R _ _ _ occ a b c d
    simpa using
      (normalOrdered_matrixUnit_commutator (R := R) occ a b c d)
  · intro A _ C m n
    simpa using
      (RawCARModeAlgebra.normalOrderedCurrent_heisenberg_from_matrixUnit
        (C := C) (m := m) (n := n))

/--
Bosonization theorem in boundary-Majorana form.

This is the explicit bosonization surface for the finite Tomita-Krein atom:
PHS-invariant Majorana swap, boundary zero-mode lane, and the completed
current Heisenberg law packaged together.
-/
theorem majoranaBosonizationTheorem :
    IsPHSInvariant
      ((concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) :
        InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E)
      ∧ IsBoundaryZeroMode
          (cptSuperchargeOp (E := E))
          (cptSuperchargeOp (E := E))
      ∧ (∀ {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
          (occ : ι → ℤ) (a b c d : ι),
            algebraCommutator
                (normalOrderedMatrixUnit (R := R) occ a b)
                (normalOrderedMatrixUnit (R := R) occ c d)
              =
              (if b = c then normalOrderedMatrixUnit (R := R) occ a d else 0)
                - (if a = d then normalOrderedMatrixUnit (R := R) occ c b else 0)
                + wickCorrection (R := R) occ a b c d)
      ∧ (∀ {A : Type*} [Ring A]
          (C : InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeAlgebra A)
          (m n : Int),
            InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted C
                (InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
                (InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n) =
              if m + n = 0 then
                m • InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
              else 0) := by
  simpa using boundaryMajoranaCircuitModel (E := E)

end Core

end InfoGeometry.Canonical.BoundaryMajoranaCircuitModel
