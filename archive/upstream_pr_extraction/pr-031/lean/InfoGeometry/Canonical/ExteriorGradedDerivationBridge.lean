import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

noncomputable section

namespace InfoGeometry.Canonical.ExteriorGradedDerivationBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Graded Exterior Derivation Predicate IsGradedDerivation d for d(x·y) = dx·y + (-1)^k x·dy. -/
def IsGradedDerivation (d : Module.End R (ExteriorAlgebra R V)) : Prop :=
  ∀ (k : ℕ) (x y : ExteriorAlgebra R V),
    IsHomogeneousExteriorDegree k x →
    d (x * y) = d x * y + ((-1 : R) ^ k) • (x * d y)

/-- **Structure**: Complete Exterior Differential Data Package. -/
structure ExteriorDifferentialData (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  d : Module.End R (ExteriorAlgebra R V)
  gradedLeibniz : IsGradedDerivation d
  sq_zero : d.comp d = 0

/-- **Theorem**: Odd-Degree 1-Form Leibniz Derivation Rule d(A·y) = dA·y - A·dy (with (-1)^1 = -1). -/
theorem one_form_leibniz
    (D : ExteriorDifferentialData R V)
    (A y : ExteriorAlgebra R V)
    (hA : IsHomogeneousExteriorDegree 1 A) :
    D.d (A * y) = D.d A * y - A * D.d y := by
  have h_leibniz := D.gradedLeibniz 1 A y hA
  rw [h_leibniz]
  have h_sign : ((-1 : R) ^ 1) = -1 := pow_one (-1)
  rw [h_sign, neg_one_smul, sub_eq_add_neg]

/-- **Theorem**: Even-Degree 2-Form Leibniz Derivation Rule d(F·y) = dF·y + F·dy (with (-1)^2 = +1). -/
theorem two_form_leibniz
    (D : ExteriorDifferentialData R V)
    (F y : ExteriorAlgebra R V)
    (hF : IsHomogeneousExteriorDegree 2 F) :
    D.d (F * y) = D.d F * y + F * D.d y := by
  have h_leibniz := D.gradedLeibniz 2 F y hF
  rw [h_leibniz]
  have h_sign : ((-1 : R) ^ 2) = 1 := by ring
  rw [h_sign, one_smul]

/-- **Theorem**: Even Curvature Square Leibniz Product Rule d(F·F) = dF·F + F·dF. -/
theorem two_form_square_leibniz
    (D : ExteriorDifferentialData R V)
    (F : ExteriorAlgebra R V)
    (hF : IsHomogeneousExteriorDegree 2 F) :
    D.d (F * F) = D.d F * F + F * D.d F :=
  two_form_leibniz D F F hF

/-- **Theorem**: Master Exterior Graded Derivation Synthesis.
    Unifies:
    1. Graded exterior derivation structure IsGradedDerivation d.
    2. Derivation of odd-degree 1-form Leibniz rule d(A·y) = dA·y - A·dy from (-1)^1 = -1.
    3. Derivation of even-degree 2-form Leibniz rule d(F·y) = dF·y + F·dy from (-1)^2 = +1.
    4. Proof closure for even curvature square product rule d(F·F) = dF·F + F·dF. -/
theorem master_exterior_graded_derivation_synthesis
    (D : ExteriorDifferentialData R V)
    (A F y : ExteriorAlgebra R V)
    (hA : IsHomogeneousExteriorDegree 1 A)
    (hF : IsHomogeneousExteriorDegree 2 F) :
    (D.d (A * y) = D.d A * y - A * D.d y) ∧
    (D.d (F * y) = D.d F * y + F * D.d y) ∧
    (D.d (F * F) = D.d F * F + F * D.d F) := ⟨
  one_form_leibniz D A y hA,
  two_form_leibniz D F y hF,
  two_form_square_leibniz D F hF
⟩

end InfoGeometry.Canonical.ExteriorGradedDerivationBridge
