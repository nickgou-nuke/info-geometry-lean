import InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
import InfoGeometry.Canonical.CurvatureFromConnectionBianchiBridge

noncomputable section

/-!
# Finite Abelian Maxwell specialization

This owner records only the algebraic Maxwell layer supported by the existing
matrix-valued exterior derivative.  The field strength is `d A`; the
homogeneous equation is the nilpotence consequence `d (d A) = 0`.  A supplied
connection curvature reduces to this field strength when its quadratic term
vanishes.  No Hodge star, current, or analytic Maxwell equation is claimed.
-/

namespace InfoGeometry.Canonical.AbelianMaxwellExteriorBridge

open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.CurvatureFromConnectionBianchiBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- Abelian field strength of a matrix-valued potential. -/
def abelianFieldStrength
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    Matrix (Fin n) (Fin n) (ExteriorAlgebra R V) :=
  matrixExteriorDerivative d A

/-- The homogeneous Maxwell equation is the square-zero law for `d`. -/
theorem abelian_bianchi
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hd2 : ∀ x : ExteriorAlgebra R V, d (d x) = 0) :
    matrixExteriorDerivative d (abelianFieldStrength d A) = 0 := by
  ext i j
  exact hd2 (A i j)

/-- The Yang--Mills curvature reduces to the Abelian field strength when its
quadratic connection term vanishes. -/
theorem curvatureFromConnection_eq_abelianFieldStrength
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hAA : A * A = 0) :
    curvatureFromConnection d A = abelianFieldStrength d A := by
  simp [curvatureFromConnection, abelianFieldStrength, hAA]

/-- Gauge shifts by an exact potential leave the Abelian field strength
unchanged under the same square-zero hypothesis. -/
theorem abelianFieldStrength_gauge_shift
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (φ : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hd2 : ∀ x : ExteriorAlgebra R V, d (d x) = 0) :
    abelianFieldStrength d (A + matrixExteriorDerivative d φ) =
      abelianFieldStrength d A := by
  ext i j
  simp [abelianFieldStrength, matrixExteriorDerivative, hd2]

end InfoGeometry.Canonical.AbelianMaxwellExteriorBridge
