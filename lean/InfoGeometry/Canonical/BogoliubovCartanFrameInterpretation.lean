import InfoGeometry.Krein.DoubledSpace
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
open InfoGeometry.Krein.PolarizedSector
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

end BogoliubovCartanInterpretation

end InfoGeometry.Canonical
