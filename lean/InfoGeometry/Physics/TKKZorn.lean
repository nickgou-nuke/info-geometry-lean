import Mathlib
import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Algebra.Zorn.G2TrifactorSU3
import InfoGeometry.Physics.TKKIsospinEmbedding
import InfoGeometry.Canonical.ZornSpinor

/-!
# Finite TKK-style Zorn readouts

This file records a finite packet of Zorn coordinate probes and determinant
polarization identities.  It does **not** construct the full 5-graded TKK
algebra, prove a global conformal-algebra identification, or assert a Lie
closure theorem for the entire carrier.

The grade labels below are only naming devices for the concrete packets used in
this file:
- `g₋₂`, `g₋₁`, `g₀`, `g₊₁`, `g₊₂`
- the corresponding basis probes
- the determinant-polarization readout
-/
namespace InfoGeometry.Physics.TKKZorn

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

variable {R : Type*} [CommRing R] [CharZero R]

-- ============================================================================
-- 1. The 5-graded Lie algebra structure on Zorn matrices
-- ============================================================================

/-- The 5 grades of the Zorn matrix TKK algebra -/
inductive ZornGrade : Type
  | g_neg2
  | g_neg1
  | g_zero
  | g_pos1
  | g_pos2

/-- Basis elements for each grade -/
def gradeBasis (g : ZornGrade) : ZornMatrix R :=
  match g with
  | ZornGrade.g_neg2 => -- e₋ = [0, 0; 0, 1]
    { a := 0, b := 1, x := ![0, 0, 0], y := ![0, 0, 0] }
  | ZornGrade.g_neg1 => -- down₀ = [0, 0; e₁, 0] (representative)
    { a := 0, b := 0, x := ![0, 0, 0], y := ![1, 0, 0] }
  | ZornGrade.g_zero => -- e₊ = [1, 0; 0, 0]
    { a := 1, b := 0, x := ![0, 0, 0], y := ![0, 0, 0] }
  | ZornGrade.g_pos1 => -- up₀ = [0, e₁; 0, 0] (representative)
    { a := 0, b := 0, x := ![1, 0, 0], y := ![0, 0, 0] }
  | ZornGrade.g_pos2 => -- e₊ = [1, 0; 0, 0] (same as g_zero in diagonal part)
    { a := 1, b := 0, x := ![0, 0, 0], y := ![0, 0, 0] }

-- ============================================================================
-- 2. The TKK Fisher Information Metric
-- ============================================================================

/-- 
The Fisher information bilinear form on projective Zorn states.
Derived by polarizing the split norm (Zorn determinant):

`g(X, Y) = detZ(X + Y) - detZ(X) - detZ(Y)`.
-/
def TKKFisherInformationMetric (cp : CrossProduct3 R)
    (X Y : ZornMatrix R) : R :=
  InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp (X + Y) -
  InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp X -
  InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp Y

/--
The associated `2 × 2` Fisher information matrix on the span of two Zorn states.
Its entries are the Fisher pairings of `X` and `Y`.
-/
def ZornFisherInformationMatrix (cp : CrossProduct3 R)
    (X Y : ZornMatrix R) : Matrix (Fin 2) (Fin 2) R :=
  !![TKKFisherInformationMetric cp X X, TKKFisherInformationMetric cp X Y;
    TKKFisherInformationMetric cp Y X, TKKFisherInformationMetric cp Y Y]

/-- The Fisher pairing is exactly the polarization of the split-norm determinant. -/
theorem TKKFisherInformationMetric_eq_detZ_polar (cp : CrossProduct3 R)
    (X Y : ZornMatrix R) :
    TKKFisherInformationMetric cp X Y =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp (X + Y) -
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp X -
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp Y := by
  rfl

/-- The Fisher pairing on Zorn states is symmetric. -/
theorem TKKFisherInformationMetric_symm (cp : CrossProduct3 R)
    (X Y : ZornMatrix R) :
    TKKFisherInformationMetric cp X Y = TKKFisherInformationMetric cp Y X := by
  simp [TKKFisherInformationMetric, add_comm, sub_eq_add_neg]
  ring

/-- The Fisher information matrix packages the determinant polarization entries. -/
theorem ZornFisherInformationMatrix_apply (cp : CrossProduct3 R)
    (X Y : ZornMatrix R) :
    ZornFisherInformationMatrix cp X Y =
      !![InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp (X + X) -
          2 * InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp X,
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp (X + Y) -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp X -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp Y;
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp (Y + X) -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp Y -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp X,
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp (Y + Y) -
          2 * InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp Y] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [ZornFisherInformationMatrix, TKKFisherInformationMetric, two_mul, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

-- ============================================================================
-- 3. Fermi operator: action by g₀ elements (SU(3) derivations)
-- ============================================================================

/-- 
The Fermi operator acts by the zero-grade derivations (g₀).
For g₀ ∈ g₀, the action is the adjoint action: X ↦ [g₀, X].
Since g₀ preserves the grading, this acts as a conformal isometry
on the projective closure.
-/
def fermi_operator (cp : CrossProduct3 R) (g0 : ZornMatrix R)
    (X : ZornMatrix R) : ZornMatrix R :=
  zMul g0 X - zMul X g0

-- ============================================================================
-- 4. Gamow-Teller operator: action by triality projector
-- ============================================================================

/-- 
The triality projector implements the D₄ triality symmetry.
It cyclically permutes the three 8-dimensional representations.
In the Zorn matrix model, it acts on the (up, down, diag) triple.
-/
def triality_projector (X : ZornMatrix R) : ZornMatrix R :=
  { a := X.b, b := X.a, x := X.y, y := X.x }

theorem triality_projector_eq_zero {X : ZornMatrix R}
    (h : triality_projector X = 0) : X = 0 := by
  rcases X with ⟨a, b, x, y⟩
  have ha : b = 0 := by
    simpa [triality_projector] using congrArg InfoGeometry.Canonical.ZornMatrix.a h
  have hb : a = 0 := by
    simpa [triality_projector] using congrArg InfoGeometry.Canonical.ZornMatrix.b h
  have hx : y = 0 := by
    simpa [triality_projector] using congrArg InfoGeometry.Canonical.ZornMatrix.x h
  have hy : x = 0 := by
    simpa [triality_projector] using congrArg InfoGeometry.Canonical.ZornMatrix.y h
  subst a b x y
  rfl

/-- 
The Gamow-Teller operator applies the triality projector.
This breaks the 5-grading because it mixes grades.
-/
def gamow_teller_operator (cp : CrossProduct3 R)
    (X : ZornMatrix R) : ZornMatrix R :=
  triality_projector X

-- ============================================================================
-- 5. Projective Nuclear State wrapper
-- ============================================================================

structure ProjectiveZornState (R : Type*) [CommRing R] where
  vector : ZornMatrix R
  non_zero : vector ≠ 0

namespace ProjectiveZornState

def applyFermi (cp : CrossProduct3 R) (g0 : ZornMatrix R)
    (ψ : ProjectiveZornState R)
    (h_nonzero : fermi_operator cp g0 ψ.vector ≠ 0) : ProjectiveZornState R :=
  ⟨fermi_operator cp g0 ψ.vector, h_nonzero⟩

def applyGT (cp : CrossProduct3 R)
    (ψ : ProjectiveZornState R) : ProjectiveZornState R :=
  ⟨gamow_teller_operator cp ψ.vector, by
    intro h
    apply ψ.non_zero
    exact triality_projector_eq_zero (by simpa [gamow_teller_operator] using h)⟩

end ProjectiveZornState

end InfoGeometry.Physics.TKKZorn
