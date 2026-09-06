import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge
import InfoGeometry.Canonical.GradedConnectionBianchiBridge
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

noncomputable section

namespace InfoGeometry.Canonical.EinsteinHilbertPalatiniActionBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open InfoGeometry.Canonical.GradedConnectionBianchiBridge

open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {d : ℕ}

/-- **Definition**: Torsion 2-Form T^a = d(e^a) + ∑_b ω^{ab} ∧ e^b for Tetrad e^a and Spin Connection ω^{ab}. -/
def torsionTwoForm
    (diff : Module.End R (ExteriorAlgebra R V))
    (e : Fin d → ExteriorAlgebra R V)
    (omega : Fin d → Fin d → ExteriorAlgebra R V)
    (a : Fin d) : ExteriorAlgebra R V :=
  diff (e a) + ∑ b, omega a b * e b

/-- **Definition**: Riemann Curvature 2-Form R^{ab} = d(ω^{ab}) + ∑_c ω^{ac} ∧ ω^{cb} for Spin Connection ω. -/
def riemannCurvatureTwoForm
    (diff : Module.End R (ExteriorAlgebra R V))
    (omega : Fin d → Fin d → ExteriorAlgebra R V)
    (a b : Fin d) : ExteriorAlgebra R V :=
  diff (omega a b) + ∑ c, omega a c * omega c b

/-- **Definition**: Anti-Symmetric Spin Connection Predicate ω^{ba} = -ω^{ab}. -/
def IsAntiSymmetricSpinConnection (omega : Fin d → Fin d → ExteriorAlgebra R V) : Prop :=
  ∀ a b, omega b a = -omega a b

/-- **Theorem**: Product Anti-Commutativity of Spin Connection 1-Forms ω^{bc} ∧ ω^{ca} = -ω^{ac} ∧ ω^{cb} Derived from Spin Connection Anti-Symmetry and 1-Form Degree Anti-Commutativity. -/
theorem spinConnection_product_antiSymmetric
    (omega : Fin d → Fin d → ExteriorAlgebra R V)
    (h_anti : IsAntiSymmetricSpinConnection omega)
    (hω : ∀ a b, IsHomogeneousExteriorDegree (R:=R) (V:=V) 1 (omega a b))
    (h_1form_anti : ∀ x y, IsHomogeneousExteriorDegree (R:=R) (V:=V) 1 x → IsHomogeneousExteriorDegree (R:=R) (V:=V) 1 y → x * y = -(y * x))
    (a b c : Fin d) :
    omega b c * omega c a = -(omega a c * omega c b) := by
  have h_bc : omega b c = -omega c b := h_anti c b
  have h_ca : omega c a = -omega a c := h_anti a c
  have h_swap := h_1form_anti (omega c b) (omega a c) (hω c b) (hω a c)
  rw [h_bc, h_ca, neg_mul_neg, h_swap]

/-- **Theorem**: Anti-Symmetry of Riemann Curvature 2-Form R^{ba} = -R^{ab} Derived Structurally from Spin Connection Anti-Symmetry and 1-Form Degree. -/
theorem riemannCurvature_antiSymmetric
    (diff : Module.End R (ExteriorAlgebra R V))
    (omega : Fin d → Fin d → ExteriorAlgebra R V)
    (h_anti : IsAntiSymmetricSpinConnection omega)
    (hω : ∀ a b, IsHomogeneousExteriorDegree (R:=R) (V:=V) 1 (omega a b))
    (h_1form_anti : ∀ x y, IsHomogeneousExteriorDegree (R:=R) (V:=V) 1 x → IsHomogeneousExteriorDegree (R:=R) (V:=V) 1 y → x * y = -(y * x))
    (a b : Fin d) :
    riemannCurvatureTwoForm diff omega b a = -riemannCurvatureTwoForm diff omega a b := by
  dsimp [riemannCurvatureTwoForm]
  have h_sum : ∑ c, omega b c * omega c a = -∑ c, omega a c * omega c b := by
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext c
    exact spinConnection_product_antiSymmetric omega h_anti hω h_1form_anti a b c
  have h_neg_ba : omega b a = -omega a b := h_anti a b
  have h1 : diff (omega b a) = -diff (omega a b) := by rw [h_neg_ba, map_neg]
  rw [neg_add, h1, h_sum]

/-- **Definition**: 4D Levi-Civita Permutation Symbol ε_{abcd} in Ring R. -/
def leviCivita4D (R : Type*) [CommRing R] (a b c d_idx : Fin 4) : R :=
  if a.val ≠ b.val ∧ a.val ≠ c.val ∧ a.val ≠ d_idx.val ∧ b.val ≠ c.val ∧ b.val ≠ d_idx.val ∧ c.val ≠ d_idx.val then 1 else 0

/-- **Definition**: Palatini Einstein-Hilbert Lagrangian 4-Form Density L_{Palatini} = ∑_{a,b,c,d} ε_{abcd} e^a ∧ e^b ∧ R^{cd}. -/
def palatiniLagrangianFourForm
    (diff : Module.End R (ExteriorAlgebra R V))
    (e : Fin 4 → ExteriorAlgebra R V)
    (omega : Fin 4 → Fin 4 → ExteriorAlgebra R V) : ExteriorAlgebra R V :=
  ∑ a, ∑ b, ∑ c, ∑ d_idx,
    (leviCivita4D R a b c d_idx • (e a * e b * riemannCurvatureTwoForm diff omega c d_idx))

end InfoGeometry.Canonical.EinsteinHilbertPalatiniActionBridge
