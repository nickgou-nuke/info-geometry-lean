import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.Canonical.OperatorCartanSuperbracketClosure
import InfoGeometry.Canonical.FibonacciParafermionAtoms

noncomputable section

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace InfoGeometry.Algebra.OSp12

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The operator carrier used in this file. -/
abbrev Op (V : Type*) [AddCommGroup V] [Module ℝ V] := Module.End ℝ V

/-
Tripotent operator lane.

This file is now operator-first: the ambient carrier is an endomorphism ring,
and `O^3 = O` is used to split the operator into vacuum / `+1` / `-1`
projectors.

There are two related but distinct pictures that must not be conflated.

1. Tripotent/projector picture.
   The operator `O` determines the vacuum / `+1` / `-1` decomposition through
   `projVac O`, `projUp O`, and `projDown O`, with active tripotent support
   `O^2 = projUp O + projDown O`.

   This is the same algebraic split that elsewhere in the repo is used as a
   bulk-plus-boundary / regular-plus-defect decomposition.  In that broader
   language, `projVac O = 1 - O^2` is the lower-dimensional boundary/vacuum
   side and `O^2` is the active bulk/support side.  This file only uses that
   split at the operator level; it does not by itself add a separate volume,
   index, or topological-boundary theorem.

2. Null-pair witness picture.
   On a concrete `3 × 3` witness carrier one may have square-zero operators
   `E12`, `E21` with anticommutator `E12 * E21 + E21 * E12 = diag(1, 1, 0)`.
   Compressing that active block to the intrinsic `2 × 2` sector yields the
   reduced null-pair relation `E12 * E21 + E21 * E12 = 1`.

This file records the operator/decomposition surface and the grading/superbracket
surface without fixing a basis or asserting that the tripotent support `O^2`
and a concrete null-pair support projector coincide in every witness model.
-/

/-- Scalar-smul projector onto the vacuum sector `1 - O^2`. -/
def projVac (O : Op V) : Op V :=
  1 - O ^ 2

/-- Scalar-smul projector onto the `+1` sector `(1/2)(O^2 + O)`. -/
def projUp (O : Op V) : Op V :=
  (1 / 2 : ℝ) • (O ^ 2 + O)

/-- Scalar-smul projector onto the `-1` sector `(1/2)(O^2 - O)`. -/
def projDown (O : Op V) : Op V :=
  (1 / 2 : ℝ) • (O ^ 2 - O)

/-- Under `O^3 = O`, the vacuum projector is idempotent. -/
theorem projVac_idempotent (O : Op V) (hO3 : O ^ 3 = O) :
    projVac O * projVac O = projVac O := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy O *
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy O =
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy O
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy_idempotent O hO3

/-- Under `O^3 = O`, the `+1` projector is idempotent. -/
theorem projUp_idempotent (O : Op V) (hO3 : O ^ 3 = O) :
    projUp O * projUp O = projUp O := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O *
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O =
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up_idempotent O hO3

/-- Under `O^3 = O`, the `-1` projector is idempotent. -/
theorem projDown_idempotent (O : Op V) (hO3 : O ^ 3 = O) :
    projDown O * projDown O = projDown O := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O *
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O =
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down_idempotent O hO3

/--
Bulk-plus-boundary completeness for the operator-side tripotent split.

This is the OSp12 readback of the repo-native identity
`(1 - O^2) + O^2 = 1`, refined through the `+1` and `-1` sectors as
`projVac O + projUp O + projDown O = 1`.
-/
theorem projVac_add_projUp_add_projDown (O : Op V) :
    projVac O + projUp O + projDown O = 1 := by
  have hdrazin :
      projUp O + projDown O =
        InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_projector O := by
    calc
      projUp O + projDown O
          = InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O +
              InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O := by
              rfl
      _ = InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_projector O := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_eq_chiral_sum
                (O := O)).symm
  calc
    projVac O + projUp O + projDown O
        = projVac O + (projUp O + projDown O) := by
            abel
    _ = projVac O + InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_projector O := by
            rw [hdrazin]
    _ = 1 := by
            simpa [projVac] using
              (InfoGeometry.Canonical.FibonacciParafermionAtoms.bulk_boundary_completeness
                (O := O))

/--
The active bulk/support projector is the sum of the `+1` and `-1` sectors.

This is the operator-side readback of the repo-native Drazin/support projector
`O^2`.  In broader bulk/boundary language, this is the bulk/support side of the
tripotent split.
-/
theorem supportProjector_eq (O : Op V) :
    projUp O + projDown O = O ^ 2 := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O +
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O = O ^ 2
  exact (InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_eq_chiral_sum
    (O := O)).symm

/--
The vacuum projector is the complement of the active bulk/support projector.

In the broader repo vocabulary, this is the boundary/vacuum side of the
tripotent split.  Any stronger zero-volume or topological-boundary reading
requires extra hypotheses supplied in the dedicated boundary/volume lanes.
-/
theorem vacuumComplement_eq (O : Op V) :
    projVac O = 1 - (projUp O + projDown O) := by
  rw [supportProjector_eq]
  rfl

/-- The `+1` and `-1` projectors are orthogonal. -/
theorem projUp_mul_projDown (O : Op V) (hO3 : O ^ 3 = O) :
    projUp O * projDown O = 0 := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O *
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O = 0
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up_orthogonal_down O hO3

/-- Under `O³ = O`, the `-1` projector times the `+1` projector is zero. -/
theorem projDown_mul_projUp (O : Op V) (hO3 : O ^ 3 = O) :
    projDown O * projUp O = 0 := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O *
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O = 0
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down_orthogonal_up O hO3

/--
Operator osp(1|2) surface.

The ambient data are endomorphisms on a real module.  The file keeps the
grading involution explicit and records the five operator generators and their
superbracket table without choosing a coordinate basis.

The null-pair / Clifford witnesses that feed the operator surface are handled
in the ambient `Cl(5,5)` lane; this file only records the operator-theoretic
readback.  The `2 × 2` CAR/null-pair sector is the compressed active support.
The larger carrier retains the vacuum-resolved projector envelope, and `O^2`
is not identified with the active null-pair support projector.

Bulk/boundary readout:
* the bulk/support side is the resolved operator support `O^2 = projUp O + projDown O`;
* the boundary/vacuum side is `projVac O = 1 - O^2`;
* in the broader repo development, lower-dimensional or zero-volume topological
  boundary interpretations are additional boundary-lane structures, not automatic
  consequences of the OSp12 operator surface alone.
-/
structure OperatorSurface where
  Γ : Op V
  hΓ : Γ * Γ = 1
  H : Op V
  Ep : Op V
  Em : Op V
  G1 : Op V
  G2 : Op V
  H_even : Γ * H = H * Γ
  Ep_even : Γ * Ep = Ep * Γ
  Em_even : Γ * Em = Em * Γ
  G1_odd : Γ * G1 = -G1 * Γ
  G2_odd : Γ * G2 = -G2 * Γ
  H_Ep : InfoGeometry.Algebra.SupergradedBracket.superBracket false false H Ep = (2 : ℝ) • Ep
  H_Em : InfoGeometry.Algebra.SupergradedBracket.superBracket false false H Em = (-2 : ℝ) • Em
  Ep_Em : InfoGeometry.Algebra.SupergradedBracket.superBracket false false Ep Em = H
  H_G1 : InfoGeometry.Algebra.SupergradedBracket.superBracket false true H G1 = (1 : ℝ) • G1
  H_G2 : InfoGeometry.Algebra.SupergradedBracket.superBracket false true H G2 = (-1 : ℝ) • G2
  Ep_G2 : InfoGeometry.Algebra.SupergradedBracket.superBracket false true Ep G2 = G1
  Em_G1 : InfoGeometry.Algebra.SupergradedBracket.superBracket false true Em G1 = G2
  G1_G1 : InfoGeometry.Algebra.SupergradedBracket.superBracket true true G1 G1 = (2 : ℝ) • Ep
  G2_G2 : InfoGeometry.Algebra.SupergradedBracket.superBracket true true G2 G2 = (-2 : ℝ) • Em
  G1_G2 : InfoGeometry.Algebra.SupergradedBracket.superBracket true true G1 G2 = -H

namespace OperatorSurface

/-- Even projection by grading conjugation. -/
def evenProjection (Γ T : Op V) : Op V :=
  (1 / 2 : ℝ) • (T + Γ * T * Γ)

/-- Odd projection by grading conjugation. -/
def oddProjection (Γ T : Op V) : Op V :=
  (1 / 2 : ℝ) • (T - Γ * T * Γ)

/-- Even plus odd recovers the original operator. -/
theorem even_add_odd (Γ T : Op V) :
    evenProjection Γ T + oddProjection Γ T = T := by
  calc
    evenProjection Γ T + oddProjection Γ T
        = (1 / 2 : ℝ) • T + (1 / 2 : ℝ) • T := by
            rw [evenProjection, oddProjection, smul_add, smul_sub]
            simp [sub_eq_add_neg, add_left_comm, add_assoc]
    _ = T := by
          have hhalf : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
          rw [← add_smul, hhalf, one_smul]

/--
This is the tripotent support identity `projUp O + projDown O = O^2`.

It packages the operator-side support coming from the `O^3 = O` decomposition.
It does not identify `O^2` with a separate null-pair anticommutator projector
from a concrete `3 × 3` witness model; that stronger identification must be
stated separately when it is actually proved for a chosen witness.
-/
theorem active_support_compression (O : Op V) :
    projUp O + projDown O = O ^ 2 := by
  exact supportProjector_eq O

end OperatorSurface

end OSp12
