import Mathlib.Tactic
import InfoGeometry.Thermo.SplitChiralPolarizationBasis
import InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator

/-!
# InfoGeometry.Arithmetic.SplitChiralCantorDirac

Native chiral decomposition on the finite prime Cantor carrier.

This module does not rebuild a split-complex algebra. It reuses the idempotent
split basis already proved in `SplitChiralPolarizationBasis` and specializes it
to the prime Cantor carrier used by the finite Cantor--Dirac operator.

The content is deliberately finite and algebraic:

* pointwise left/right projection of split-valued fields;
* pointwise left/right projection of split-valued kernels;
* exact reconstruction by the idempotent split basis.

No deferred interface.
No property.
No CFT claim.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.SplitChiralCantorDirac

open InfoGeometry.Thermo.SplitChiralPolarizationBasis
open InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator

/-- A split-valued field on the finite prime Cantor carrier. -/
@[rep_depth thermo]
abbrev SplitCantorField (P : PrimeCutoff) :=
  Vertex P → ChiralScalar

/-- A split-valued kernel on the finite prime Cantor carrier. -/
@[rep_depth thermo]
abbrev SplitCantorKernel (P : PrimeCutoff) :=
  Vertex P → Vertex P → ChiralScalar

/-- Pointwise reconstruction of a split-valued Cantor field. -/
@[rep_depth thermo]
def reconstructField {P : PrimeCutoff} (F : SplitCantorField P) :
    SplitCantorField P :=
  fun x => reconstruct (leftPart (F x)) (rightPart (F x))

/-- Every split-valued Cantor field reconstructs from its left and right parts. -/
@[simp, rep_depth thermo]
theorem reconstructField_eq (P : PrimeCutoff) (F : SplitCantorField P) :
    reconstructField F = F := by
  funext x
  simp [reconstructField, reconstruct_left_right]

/-- Pointwise reconstruction of a split-valued Cantor kernel. -/
@[rep_depth thermo]
def reconstructKernel {P : PrimeCutoff} (K : SplitCantorKernel P) :
    SplitCantorKernel P :=
  fun x y => reconstruct (leftPart (K x y)) (rightPart (K x y))

/-- Every split-valued Cantor kernel reconstructs from its left and right parts. -/
@[simp, rep_depth thermo]
theorem reconstructKernel_eq (P : PrimeCutoff) (K : SplitCantorKernel P) :
    reconstructKernel K = K := by
  funext x y
  simp [reconstructKernel, reconstruct_left_right]

/-- A split Cantor field built from explicit left/right channel laws. -/
@[rep_depth thermo]
def chiralField {P : PrimeCutoff}
    (φL φR : Vertex P → ℝ) : SplitCantorField P :=
  fun x => reconstruct (φL x) (φR x)

end InfoGeometry.Arithmetic.SplitChiralCantorDirac
