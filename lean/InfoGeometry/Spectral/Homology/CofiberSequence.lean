import InfoGeometry.Spectral.Homotopy.Cofiber
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Spectral.Homology.Basic
import InfoGeometry.Spectral.Cohomology.LongExact

/-!
# Homology data attached to a pointed cofiber sequence

The former Spectral project constructed a long exact sequence from a
topological cofiber.  Here the topological construction and the algebraic
sequence are kept as separate inputs.  This makes the interface reusable
for any future realization while keeping every current theorem honest.
-/

namespace InfoGeometry.Spectral.Homology.CofiberSequence

open InfoGeometry.Spectral.Homotopy.Suspension
open InfoGeometry.Spectral.Homotopy.Cofiber
open InfoGeometry.Spectral.Homology.Basic
open InfoGeometry.Spectral.Cohomology.LongExact

universe u

/-- A cofiber sequence together with its already-constructed long exact
homology sequence. -/
structure CofiberHomologyData (shift : ℤ) where
  X : PointedReadout
  Y : PointedReadout
  C : PointedReadout
  cofiber : CofiberSequence X Y C
  theory : HomologyTheory
  sequence : LongExactSequence shift

namespace CofiberHomologyData

variable {shift : ℤ} (D : CofiberHomologyData shift)

@[simp]
theorem composite_base (x : D.X.carrier) :
    D.cofiber.inclusion (D.cofiber.map x) = D.C.base :=
  D.cofiber.composite_base x

theorem homology_exact_at (n : ℤ)
    (y : D.sequence.carrier (n + shift))
    (hy : D.sequence.next (n + shift) y = 0) :
    ∃ x : D.sequence.carrier n,
      D.sequence.next n x = y :=
  D.sequence.exact_at n y hy

end CofiberHomologyData

end InfoGeometry.Spectral.Homology.CofiberSequence
