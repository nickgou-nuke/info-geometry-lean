import Mathlib
import InfoGeometry.Clifford.Cl55DyadicMoritaBridge
import InfoGeometry.Physics.MatrixTraceBimodulePairingNative

/-!
# Finite Cl(5,5) Krein bilinear readout

This owner formalizes only the finite kernel-checkable layer:

* a real `32 = 16 + 16` signature operator on the native spinor carrier;
* the associated Krein bra and rank-one density dyad;
* scalar operator readout by matrix trace;
* a symmetric anticommutator metric shadow;
* transport of both readouts through the already-proved
  `cl55SpinorAlgEquiv : Cl55 ≃ₐ[ℝ] Matrix (Fin 32) (Fin 32) ℝ`.

No theorem here identifies the coordinate readout with a spacetime manifold,
Einstein metric, Tomita--Takesaki modular conjugation, or gravitational field.
Those require separate analytic/geometric bridge data.
-/

noncomputable section

namespace InfoGeometry.Physics.EmergentSpacetimeBilinear

open Matrix
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SpinorRep

abbrev Spinor32 : Type := InfoGeometry.Clifford.Clifford55.Spinor32
abbrev Mat32 : Type := InfoGeometry.Clifford.Clifford55.Mat32

/-- Coordinate sign for the fixed `16 + 16` Krein splitting. -/
def kreinSign (i : Fin 32) : ℝ :=
  if (i : Nat) < 16 then 1 else -1

/-- Diagonal fundamental symmetry with `16` positive and `16` negative entries. -/
def kreinEta : Mat32 :=
  Matrix.diagonal kreinSign

@[simp] theorem kreinEta_diag (i : Fin 32) :
    kreinEta i i = kreinSign i := by
  simp [kreinEta]

/-- The coordinate Krein dual of a real spinor.  This identifies the algebraic
row functional with its coefficient vector in the standard basis. -/
def kreinBra (psi : Spinor32) : Spinor32 :=
  fun i => kreinSign i * psi i

/-- Rank-one Krein density dyad `|psi><psi|_eta`. -/
def kreinDensity (psi : Spinor32) : Mat32 :=
  ketBra psi (kreinBra psi)

@[simp] theorem kreinDensity_apply (psi : Spinor32) (i j : Fin 32) :
    kreinDensity psi i j = psi i * (kreinSign j * psi j) := by
  rfl

/-- Scalar state/operator readout `Tr(rho_eta(psi) A)`. -/
def spacetimeCoordinate (psi : Spinor32) (A : Mat32) : ℝ :=
  Matrix.trace (kreinDensity psi * A)

@[simp] theorem spacetimeCoordinate_zero_operator (psi : Spinor32) :
    spacetimeCoordinate psi 0 = 0 := by
  simp [spacetimeCoordinate]

/-- The finite metric shadow obtained from the symmetrized operator product. -/
def emergentMetric (psi : Spinor32) (A B : Mat32) : ℝ :=
  (1 / 2 : ℝ) *
    (spacetimeCoordinate psi (A * B) + spacetimeCoordinate psi (B * A))

/-- The anticommutator metric shadow is symmetric by construction. -/
theorem emergentMetric_symm (psi : Spinor32) (A B : Mat32) :
    emergentMetric psi A B = emergentMetric psi B A := by
  simp [emergentMetric, add_comm]

/-- The coordinate readout is exactly the native trace pairing of the Krein
density with the supplied operator. -/
theorem spacetimeCoordinate_eq_tracePairingNative (psi : Spinor32) (A : Mat32) :
    spacetimeCoordinate psi A = tracePairingNative (kreinDensity psi) A := by
  rfl

/-- Pull the scalar coordinate readout back to the native Clifford carrier. -/
def cliffordCoordinate (psi : Spinor32) (x : Cl55) : ℝ :=
  spacetimeCoordinate psi (cl55SpinorAlgEquiv x)

/-- Pull the symmetric anticommutator metric shadow back to `Cl(5,5)`. -/
def cliffordMetric (psi : Spinor32) (x y : Cl55) : ℝ :=
  emergentMetric psi (cl55SpinorAlgEquiv x) (cl55SpinorAlgEquiv y)

/-- Clifford-side metric symmetry. -/
theorem cliffordMetric_symm (psi : Spinor32) (x y : Cl55) :
    cliffordMetric psi x y = cliffordMetric psi y x := by
  exact emergentMetric_symm psi (cl55SpinorAlgEquiv x) (cl55SpinorAlgEquiv y)

/-- The Clifford pullback is the expectation of the native algebra product,
using multiplicativity of `cl55SpinorAlgEquiv`. -/
theorem cliffordMetric_eq_product_readout (psi : Spinor32) (x y : Cl55) :
    cliffordMetric psi x y =
      (1 / 2 : ℝ) *
        (cliffordCoordinate psi (x * y) + cliffordCoordinate psi (y * x)) := by
  simp [cliffordMetric, emergentMetric, cliffordCoordinate, map_mul]

/-- The finite readout depends only on the dyadic density and the operator image;
this is the exact bridge to the preceding Morita reconstruction owner. -/
theorem cliffordCoordinate_dyadic_readback (psi : Spinor32) (x : Cl55) :
    cliffordCoordinate psi x =
      Matrix.trace (kreinDensity psi * cl55SpinorAlgEquiv x) := by
  rfl

end InfoGeometry.Physics.EmergentSpacetimeBilinear

end noncomputable section

