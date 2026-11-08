import InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge

/-!
# Nilpotent differential-form Laplacian bridge

This owner complements the earlier form/Hodge/Clifford carrier.  It keeps the
nilpotence laws explicit and derives the Dirac--Kähler square from them; no
analytic continuation or geometric interpretation is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornDifferentialFormsLaplacianBridge

open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

structure FormDifferentialLaplacianData where
  differential : Module.End R (ExteriorAlgebra R V)
  codifferential : Module.End R (ExteriorAlgebra R V)
  differential_sq : differential.comp differential = 0
  codifferential_sq : codifferential.comp codifferential = 0

def diracOperator (D : FormDifferentialLaplacianData (R := R) (V := V)) :
    Module.End R (ExteriorAlgebra R V) :=
  D.differential + D.codifferential

def hodgeLaplacian (D : FormDifferentialLaplacianData (R := R) (V := V)) :
    Module.End R (ExteriorAlgebra R V) :=
  D.differential.comp D.codifferential +
  D.codifferential.comp D.differential

def hodgeConjugateCodifferential
    (hodgeStar differential : Module.End R (ExteriorAlgebra R V)) :
    Module.End R (ExteriorAlgebra R V) :=
  hodgeStar.comp (differential.comp hodgeStar)

@[simp] theorem hodgeConjugateCodifferential_apply
    (hodgeStar differential : Module.End R (ExteriorAlgebra R V))
    (ω : ExteriorAlgebra R V) :
    hodgeConjugateCodifferential hodgeStar differential ω =
      hodgeStar (differential (hodgeStar ω)) := by
  rfl

theorem hodgeLaplacian_eq_of_codifferential_eq_hodgeConjugate
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (hodgeStar : Module.End R (ExteriorAlgebra R V))
    (hcod : D.codifferential =
      hodgeConjugateCodifferential hodgeStar D.differential) :
    hodgeLaplacian D =
      D.differential.comp
          (hodgeConjugateCodifferential hodgeStar D.differential) +
        (hodgeConjugateCodifferential hodgeStar D.differential).comp
          D.differential := by
  simp [hodgeLaplacian, hcod]

theorem diracOperator_square (D : FormDifferentialLaplacianData (R := R) (V := V)) :
    (diracOperator D).comp (diracOperator D) = hodgeLaplacian D := by
  exact DiracKahlerLaplacianOperatorBridge.dirac_kahler_sq_eq_laplacian
    D.differential D.codifferential D.differential_sq D.codifferential_sq

theorem diracOperator_square_apply
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (ω : ExteriorAlgebra R V) :
    diracOperator D (diracOperator D ω) = hodgeLaplacian D ω := by
  have h := congrArg
    (fun f : Module.End R (ExteriorAlgebra R V) => f ω)
    (diracOperator_square D)
  simpa [LinearMap.comp_apply] using h

end InfoGeometry.Canonical.ZornDifferentialFormsLaplacianBridge
