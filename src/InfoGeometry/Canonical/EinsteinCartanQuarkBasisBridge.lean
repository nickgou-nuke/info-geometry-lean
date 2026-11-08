import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.EinsteinCartanBianchiBridge
import InfoGeometry.Canonical.GunaydinGurseyQuarkBasisBridge

/-!
# Typed Zorn quark-basis readout for Einstein-Cartan forms

The repository's Zorn carrier is intentionally not given a module structure.
Accordingly, this bridge takes the target map into the tetrad vector space as
explicit data.  It then applies the canonical ExteriorAlgebra inclusion and
packages the eight basis states as an eight-component tetrad.
-/

namespace InfoGeometry.Canonical.EinsteinCartanQuarkBasis

open InfoGeometry.Canonical
open InfoGeometry.Canonical.GunaydinGursey
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The eight states in the Günaydin-Gürsey Zorn basis. -/
def quarkBasis (q : Fin 8) : ZornVectorMatrix R :=
  match q.1 with
  | 0 => uZero
  | 1 => uStarZero
  | 2 => u 0
  | 3 => u 1
  | 4 => u 2
  | 5 => uStar 0
  | 6 => uStar 1
  | _ => uStar 2

/-- Explicit target data for a typed Zorn-to-tetrad readout. -/
abbrev QuarkTetradMap := ZornVectorMatrix R → V

namespace QuarkTetradMap

abbrev toVector (Q : QuarkTetradMap (R := R) (V := V)) :
    ZornVectorMatrix R → V :=
  Q

end QuarkTetradMap

/-- The induced ExteriorAlgebra component map. -/
def exteriorComponent (Q : QuarkTetradMap (R := R) (V := V))
    (x : ZornVectorMatrix R) : ExteriorAlgebra R V :=
  ExteriorAlgebra.ι R (Q.toVector x)

/-- The eight Zorn basis states as an eight-component tetrad. -/
def tetrad (Q : QuarkTetradMap (R := R) (V := V)) :
    TetradVector 8 R V :=
  fun q => exteriorComponent Q (quarkBasis q)

@[simp] theorem exteriorComponent_apply
    (Q : QuarkTetradMap (R := R) (V := V)) (x : ZornVectorMatrix R) :
    exteriorComponent Q x = ExteriorAlgebra.ι R (Q.toVector x) := rfl

@[simp] theorem tetrad_apply
    (Q : QuarkTetradMap (R := R) (V := V)) (q : Fin 8) :
    tetrad Q q = ExteriorAlgebra.ι R (Q.toVector (quarkBasis q)) := rfl

end InfoGeometry.Canonical.EinsteinCartanQuarkBasis
