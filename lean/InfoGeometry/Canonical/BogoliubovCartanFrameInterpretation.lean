import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.PolarizedSector
import InfoGeometry.Krein.OrthogonalGroup
import InfoGeometry.Krein.Automorphisms
import InfoGeometry.Krein.CartanDecomposition
import InfoGeometry.Canonical.KreinDoubledAtom

/-!
# Bogoliubov–Cartan Frame Interpretation

This module is a thin repository-native bridge that fixes terminology:

* "Bogoliubov frame" is realized by conjugation along the real
  Hessian-orthogonal group `HessianOrthogonalGroup`.
* The Cartan/Krein involution is the fixed conjugation by `neutralJ`.
* The diagonal sector is the Cartan-readout after such a frame change and a
  polarized decomposition.
* `KreinDoubledAtom` supplies the underlying real doubled `Cl(1,1)` primitives.

These are not new foundations, only a naming/connection layer over existing
declarations.
-/

noncomputable section

namespace InfoGeometry.Canonical

open scoped InnerProductSpace
open InfoGeometry.Krein
open PolarizedSector
open KreinSpace NeutralSpace

section BogoliubovCartanInterpretation

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
In this repository, a Bogoliubov frame acts on neutral-space operators by
continuous-linear conjugation.
-/
theorem bogoliubovFrameAction_eq_conjugate
    (U : HessianOrthogonalGroup E)
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    InfoGeometry.Krein.conjugateCLM U.equiv A =
      InfoGeometry.Krein.conjugateCLM
        ((U : NeutralSpace E ≃L[ℝ] NeutralSpace E)) A := by
  rfl

/--
The Cartan involution is exactly conjugation by the neutral swap involution
`neutralJ`.
-/
theorem cartanInvolution_is_neutralJ_conjugation
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (E := E) A =
      InfoGeometry.Krein.conjugateCLM
        ((neutralJ (E := E)).toContinuousLinearEquiv) A := by
  rfl

/--
Group-level Cartan conjugation is conjugation by the Hessian-orthogonal neutral
swap element.
-/
theorem cartanInvolutionGroup_is_modular_j_orthogonal
    (U : HessianOrthogonalGroup E) :
    cartanInvolutionGroup (E := E) U =
      modular_jHessianOrthogonal (E := E) *
        U *
        modular_jHessianOrthogonal (E := E) := by
  rfl

/--
The doubled polarized carrier is reconstructed from the positive and negative
spectral sheets.
-/
theorem doubledCarrier_sheet_reconstruction
    (u : DoubledSpace E) :
    spectralPlusProj (E := E) u +
        spectralMinusProj (E := E) u = u := by
  exact spectralProj_decomposition (E := E) u

/--
The doubled real Clifford axis has complex-squared behavior `K^2 = -Id`.
-/
theorem doubledCliffordAxis_square
    (X : KreinDoubledAtom) :
    (X.K : Module.End ℝ X) * (X.K : Module.End ℝ X) =
      -(1 : Module.End ℝ X) :=
  X.K_sq_eq_neg_one

/-! ## Bogoliubov/KAN chart discipline -/

/-- Neutral-space endomorphisms: the noncommutative operator carrier. -/
abbrev NeutralEnd : Type _ :=
  NeutralSpace E →L[ℝ] NeutralSpace E

/--
A Bogoliubov/KAN frame on the neutral Krein carrier.

The frame is a Hessian-orthogonal real Bogoliubov implementer.  The fields
`Kpart`, `Apart`, and `Npart` record a supplied KAN factorization.  This packet
does not assert a global KAN theorem; it records the concrete chart used for a
readout.
-/
structure BogoliubovKANFrame where
  /-- Full Bogoliubov/Krein frame. -/
  frame : HessianOrthogonalGroup E
  /-- Compact/K-sector coordinate of the chosen chart. -/
  Kpart : HessianOrthogonalGroup E
  /-- Cartan/A-sector coordinate of the chosen chart. -/
  Apart : HessianOrthogonalGroup E
  /-- Nilpotent/N-sector coordinate of the chosen chart. -/
  Npart : HessianOrthogonalGroup E
  /-- Supplied KAN factorization in the Hessian-orthogonal group. -/
  kan_factorization : frame = Kpart * Apart * Npart

namespace BogoliubovKANFrame

variable (F : BogoliubovKANFrame (E := E))

/-- Full noncommutative operator action by the Bogoliubov frame. -/
noncomputable def frameAction (A : NeutralEnd (E := E)) : NeutralEnd (E := E) :=
  conjugateCLM ((F.frame : NeutralSpace E ≃L[ℝ] NeutralSpace E)) A

/--
Diagonal/Cartan operator readout in the chosen KAN chart.

This is deliberately only the `A`-component conjugation.  It is not the owner
of the modular operator.
-/
noncomputable def diagonalOperatorReadout
    (A : NeutralEnd (E := E)) : NeutralEnd (E := E) :=
  conjugateCLM ((F.Apart : NeutralSpace E ≃L[ℝ] NeutralSpace E)) A

@[simp] theorem frameAction_eq_frame_conjugation
    (A : NeutralEnd (E := E)) :
    F.frameAction A =
      conjugateCLM ((F.frame : NeutralSpace E ≃L[ℝ] NeutralSpace E)) A :=
  rfl

@[simp] theorem diagonalOperatorReadout_eq_Apart_conjugation
    (A : NeutralEnd (E := E)) :
    F.diagonalOperatorReadout A =
      conjugateCLM ((F.Apart : NeutralSpace E ≃L[ℝ] NeutralSpace E)) A :=
  rfl

/-- The KAN chart remembers its supplied group-level factorization. -/
theorem frame_eq_KAN :
    F.frame = F.Kpart * F.Apart * F.Npart :=
  F.kan_factorization

/-- The full frame action preserves products of neutral-space endomorphisms. -/
@[simp] theorem frameAction_mul
    (A B : NeutralEnd (E := E)) :
    F.frameAction (A * B) = F.frameAction A * F.frameAction B := by
  simp [frameAction]

/-- The diagonal Cartan readout preserves products because it is conjugation. -/
@[simp] theorem diagonalOperatorReadout_mul
    (A B : NeutralEnd (E := E)) :
    F.diagonalOperatorReadout (A * B) =
      F.diagonalOperatorReadout A * F.diagonalOperatorReadout B := by
  simp [diagonalOperatorReadout]

end BogoliubovKANFrame

/--
Predicate saying that a proposed diagonal object is only the Cartan/KAN
`A`-component readout of a primitive noncommutative operator.

This is the named guard against treating a diagonal expression as the owner
lane.  The owner remains the original `operator`.
-/
def IsDiagonalCartanShadow
    (frame : BogoliubovKANFrame (E := E))
    (operator readout : NeutralEnd (E := E)) : Prop :=
  readout = frame.diagonalOperatorReadout operator

/--
An operator represented in a chosen Bogoliubov/KAN chart.

The primitive object is `operator`.  `framedOperator` and `diagonalReadout` are
derived chart readouts, pinned by equations so downstream code cannot silently
treat the diagonal form as foundational.
-/
structure OperatorInBogoliubovKANChart where
  /-- Primitive noncommutative operator. -/
  operator : NeutralEnd (E := E)
  /-- Chosen Bogoliubov/KAN frame. -/
  frame : BogoliubovKANFrame (E := E)
  /-- Full frame-conjugated operator. -/
  framedOperator : NeutralEnd (E := E)
  /-- Diagonal/Cartan shadow readout. -/
  diagonalReadout : NeutralEnd (E := E)
  /-- The framed operator is obtained by the full Bogoliubov frame action. -/
  framedOperator_eq : framedOperator = frame.frameAction operator
  /-- The diagonal readout is obtained only from the `A`-component. -/
  diagonalReadout_eq : diagonalReadout = frame.diagonalOperatorReadout operator

namespace OperatorInBogoliubovKANChart

variable (O : OperatorInBogoliubovKANChart (E := E))

/-- The primitive owner of the chart is the original neutral-space operator. -/
theorem primitive_operator_owner :
    O.operator = O.operator :=
  rfl

/-- Re-export: the framed operator is the full Bogoliubov frame action. -/
theorem framedOperator_eq_frameAction :
    O.framedOperator = O.frame.frameAction O.operator :=
  O.framedOperator_eq

/-- Re-export: the diagonal object is only the Cartan/A-component readout. -/
theorem diagonalReadout_eq_Apart_readout :
    O.diagonalReadout = O.frame.diagonalOperatorReadout O.operator :=
  O.diagonalReadout_eq

/--
The chart package explicitly witnesses that its diagonal readout is only a
Cartan/KAN shadow of the primitive noncommutative operator.
-/
theorem diagonalReadout_is_Cartan_shadow :
    IsDiagonalCartanShadow (E := E) O.frame O.operator O.diagonalReadout :=
  O.diagonalReadout_eq

end OperatorInBogoliubovKANChart

end BogoliubovCartanInterpretation

end InfoGeometry.Canonical
