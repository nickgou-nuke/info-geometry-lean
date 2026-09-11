import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.KK.RealSplitKreinUnboundedCycle
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.KK.DiracFredholmModule

Canonical naming layer for the real split-Krein Dirac/Fredholm surfaces.

This file does not introduce a new KK ontology. It records the intended
interpretation of the existing bounded and unbounded real split-Krein carriers:

- the bounded Kasparov-style seed is the real split-Krein Dirac/Fredholm module,
- the unbounded primitive seed is the real split-Krein Dirac module,
- the internal square-minus-one axis is always the derived operator
  `K := J.comp eps`.

Policy note: any surviving `complex_i` terminology elsewhere in the repository
is legacy compatibility language only. The canonical internal phase axis for the
Dirac/Fredholm layer is `K = J.comp eps`.
-/

namespace InfoGeometry.KK

open InfoGeometry.Krein

/-- Canonical name for the bounded real split-Krein Dirac/Fredholm module. -/
@[rep_depth krein]
abbrev RealSplitKreinDiracFredholmModule := RealSplitKreinKasparovCycle

/-- Canonical name for the unbounded real split-Krein Dirac module. -/
@[rep_depth krein]
abbrev RealSplitKreinDiracModule := RealSplitKreinUnboundedCycle

namespace RealSplitKreinKasparovCycle

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/-- The bounded Dirac/Fredholm module phase axis is the derived split-`Cl(1,1)` axis. -/
@[rep_depth krein, simp] theorem K_eq_J_comp_eps
    (X : RealSplitKreinDiracFredholmModule A B H) :
    X.K = X.cl11.J.comp X.cl11.eps := rfl

/-- The bounded Dirac/Fredholm module phase axis squares to `-Id`. -/
@[rep_depth krein] theorem K_sq
    (X : RealSplitKreinDiracFredholmModule A B H) :
    X.K.comp X.K = -(ContinuousLinearMap.id ℝ H) :=
  X.cl11.K_sq

end RealSplitKreinKasparovCycle

namespace RealSplitKreinUnboundedCycle

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/-- The unbounded Dirac module phase axis is the derived split-`Cl(1,1)` axis. -/
@[rep_depth krein, simp] theorem K_eq_J_comp_eps
    (X : RealSplitKreinDiracModule A B H) :
    X.K = X.cl11.J.comp X.cl11.eps := rfl

end RealSplitKreinUnboundedCycle

end InfoGeometry.KK
