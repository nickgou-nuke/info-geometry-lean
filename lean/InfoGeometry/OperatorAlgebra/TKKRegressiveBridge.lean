import InfoGeometry.Core.JordanAssociator
import InfoGeometry.Algebra.KantorTripleFiveGrading
import InfoGeometry.OperatorAlgebra.TKKClosure
import Mathlib.Tactic

namespace InfoGeometry.Geometry.Ambitwistor

open InfoGeometry.Algebra.KantorTripleFiveGrading
open InfoGeometry.Core.JordanAssociator
open InfoGeometry.Core.JordanPeirceDecomposition

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- 
In the ambitwistor framework, incidence failure (i.e., non-zero regressive product)
is measured not by generic exterior products but by the structural defect in the 
Kantor Triple System, which is exactly the `K` operator (the obstruction to being Jordan).
-/
def incidenceDefect (T : KantorTripleSystem R V) (x y : V) : Module.End R V :=
  T.K x y

/--
The geometric interpretation is that incidence is achieved when the defect vanishes.
This happens iff the elements `x` and `y` form a commuting pair in the outer arguments 
of the Kantor triple product.
-/
def isIncident (T : KantorTripleSystem R V) (x y : V) : Prop :=
  incidenceDefect T x y = 0

/--
The regressive product of two elements `x` and `y` in this exceptional algebraic
model is identified with the action of the incidence defect on the base module.
-/
def regressiveProduct (T : KantorTripleSystem R V) (x y z : V) : V :=
  incidenceDefect T x y z

theorem regressiveProduct_skew (T : KantorTripleSystem R V) (x y z : V) :
    regressiveProduct T x y z = -regressiveProduct T y x z := by
  change (T.K x y) z = -(T.K y x) z
  rw [T.K_skew]
  rfl

theorem regressiveProduct_self (T : KantorTripleSystem R V) (x z : V) :
    regressiveProduct T x x z = 0 := by
  change (T.K x x) z = 0
  rw [T.K_self]
  rfl

variable {A : Type*} [Ring A] [Algebra ℝ A]

/--
For a special Jordan algebra embedded in an associative envelope `A`, 
the incidence defect between two elements (as measured by the Jordan associator)
vanishes when the elements commute in the ambient envelope.
-/
theorem incidence_defect_vanishes_of_commute (x y z : A) (h : x * z = z * x) :
    jordanMul (jordanMul x y) z - jordanMul x (jordanMul y z) = 0 := by
  exact sub_eq_zero.mpr (jordan_associator_eq_zero_of_commute x y z h)

end InfoGeometry.Geometry.Ambitwistor
