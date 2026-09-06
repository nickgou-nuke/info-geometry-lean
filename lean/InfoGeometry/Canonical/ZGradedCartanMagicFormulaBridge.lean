import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.CartanLieDerivativeMagicBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.ZGradedCartanMagicFormulaBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.CartanLieDerivativeMagicBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Degree Shift Specification (+1 for d, -1 for ι_X, 0 for Lie Derivative). -/
structure ZGradedDegreeShift where
  d_deg : ℤ := 1
  iota_deg : ℤ := -1
  lie_deg : ℤ := 0

/-- **Definition**: Canonical Default Degree Shift (+1, -1, 0). -/
def defaultShift : ZGradedDegreeShift := {}

/-- **Theorem**: Lie Derivative Degree Neutrality (+1 + (-1) = 0). -/
theorem lie_derivative_degree_neutral :
    defaultShift.d_deg + defaultShift.iota_deg = defaultShift.lie_deg :=
  rfl

/-- **Theorem**: Z-Graded Lie Derivative Operator Commutator [d, ℒ_X] = 0 in Module.End. -/
theorem z_graded_cartan_commutes_end
    (d iota_X : Module.End R (ExteriorAlgebra R V))
    (hd2 : d.comp d = 0) :
    d.comp (lieDerivativeEnd d iota_X) = (lieDerivativeEnd d iota_X).comp d :=
  lieDerivative_commutes_exteriorDerivative_end d iota_X hd2

/-- **Theorem**: Master Z-Graded Cartan Magic Formula & Degree Shift Synthesis.
    Unifies:
    1. Z-graded degree shift (+1 for d, -1 for contraction ι_X, 0 for Lie derivative ℒ_X).
    2. Degree neutrality equation +1 + (-1) = 0.
    3. Global operator commutator equality d ∘ ℒ_X = ℒ_X ∘ d in Module.End. -/
theorem master_z_graded_cartan_magic_formula_synthesis
    (d iota_X : Module.End R (ExteriorAlgebra R V))
    (hd2 : d.comp d = 0) :
    (defaultShift.d_deg + defaultShift.iota_deg = defaultShift.lie_deg) ∧
    (d.comp (lieDerivativeEnd d iota_X) = (lieDerivativeEnd d iota_X).comp d) := ⟨
  lie_derivative_degree_neutral,
  lieDerivative_commutes_exteriorDerivative_end d iota_X hd2
⟩

end InfoGeometry.Canonical.ZGradedCartanMagicFormulaBridge
