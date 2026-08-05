/- 
InfoGeometry/Algebraic/CliffordSymmetryLift.lean

Orthogonal-to-Clifford symmetry lift for the split quadratic carrier.

This file does not introduce modular generators or Pin/Spin elements.
It only packages quadratic-form isometries and lifts them to Clifford
algebra automorphisms using Mathlib's `CliffordAlgebra.equivOfIsometry`.
-/

import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import InfoGeometry.Algebraic.SplitCliffordCarrier

noncomputable section

namespace InfoGeometry.Algebraic.SplitSignature

/--
A split quadratic symmetry is a quadratic-form isometry of the real split
carrier.

This is the correct input for a Clifford lift.
-/
abbrev SplitQuadraticSymmetry (n : ℕ) :=
  (splitQuadraticForm n).IsometryEquiv (splitQuadraticForm n)

namespace SplitQuadraticSymmetry

abbrev iso {n : ℕ} (S : SplitQuadraticSymmetry n) :=
  S

/-- Underlying linear equivalence of a split quadratic symmetry. -/
def toLinearEquiv {n : ℕ} (S : SplitQuadraticSymmetry n) :
    SplitModule n ≃ₗ[ℝ] SplitModule n :=
  S.iso

@[simp]
theorem toLinearEquiv_apply
    {n : ℕ} (S : SplitQuadraticSymmetry n) (v : SplitModule n) :
    S.toLinearEquiv v = S.iso v :=
  rfl

end SplitQuadraticSymmetry

/--
Clifford algebra automorphism induced by a split quadratic symmetry.

This is the canonical lift used by the split Clifford carrier.
-/
def splitCliffordLift (n : ℕ) (S : SplitQuadraticSymmetry n) :
    Cl_nn n ≃ₐ[ℝ] Cl_nn n :=
  CliffordAlgebra.equivOfIsometry S.iso

@[simp]
theorem splitCliffordLift_apply
    (n : ℕ) (S : SplitQuadraticSymmetry n) (x : Cl_nn n) :
    splitCliffordLift n S x = CliffordAlgebra.equivOfIsometry S.iso x :=
  rfl

/--
Any split quadratic symmetry yields a Clifford algebra automorphism.

This is the base gate for later rotor, Narain, and modular specializations.
-/
abbrev SplitCliffordSymmetry (n : ℕ) :=
  Cl_nn n ≃ₐ[ℝ] Cl_nn n

namespace SplitCliffordSymmetry

abbrev lift {n : ℕ} (S : SplitCliffordSymmetry n) :=
  S

end SplitCliffordSymmetry

/-- Canonical packaging of the Clifford lift as a symmetry object. -/
def canonicalCliffordSymmetry (n : ℕ) (S : SplitQuadraticSymmetry n) :
    SplitCliffordSymmetry n :=
  splitCliffordLift n S

end InfoGeometry.Algebraic.SplitSignature
