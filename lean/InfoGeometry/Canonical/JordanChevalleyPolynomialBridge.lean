import InfoGeometry.Meta.Architecture
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanChevalleyBridge

/-!
# InfoGeometry.Canonical.JordanChevalleyPolynomialBridge

Constructive polynomial interpolation for the Jordan-Chevalley split.

This bridge packages the semisimple part of a Jordan-Chevalley decomposition
as a polynomial in the Hamiltonian and records the symmetry-preservation
readout needed by downstream canonical modules.
-/

noncomputable section

namespace InfoGeometry.Canonical.JordanChevalleyPolynomialBridge

open scoped Polynomial
open Polynomial
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanChevalleyBridge

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/--
A constructive Jordan-Chevalley interpolation witness.

The semisimple component is explicitly realized as `Polynomial.aeval f p`
for a polynomial `p` chosen from the singleton-adjoin decomposition.
-/
structure JordanChevalleyInterpolation (f : Module.End K V) where
  split : JordanChevalleySplit f
  poly : K[X]
  semisimple_eq : Polynomial.aeval f poly = split.semisimple

/-- The semisimple component read from a polynomial interpolation witness. -/
def semisimplePart {f : Module.End K V} (P : JordanChevalleyInterpolation f) :
    Module.End K V :=
  Polynomial.aeval f P.poly

/-- The nilpotent component read from a polynomial interpolation witness. -/
def nilpotentPart {f : Module.End K V} (P : JordanChevalleyInterpolation f) :
    Module.End K V :=
  f - semisimplePart P

/-!
`jordanChevalleyInterpolation` is a real witness, not a `Nonempty` endpoint:
it chooses a Jordan-Chevalley split and the polynomial whose evaluation at `f`
is the semisimple component.
-/
def jordanChevalleyInterpolation (f : Module.End K V) [PerfectField K] :
    JordanChevalleyInterpolation f := by
  let B : JordanChevalleySplit f :=
    JordanChevalleySplit.split (f := f)
  let hPoly := Algebra.adjoin_mem_exists_aeval (R := K) (x := f) B.semisimpleMem
  let p : K[X] := Classical.choose hPoly
  have hp : Polynomial.aeval f p = B.semisimple := Classical.choose_spec hPoly
  exact ⟨B, p, hp⟩

/-- The canonical interpolation witness reads its semisimple part as `p(f)`. -/
theorem jordanChevalleyInterpolation_semisimple_eq
    (f : Module.End K V) [PerfectField K] :
    Polynomial.aeval f (jordanChevalleyInterpolation f).poly =
      (jordanChevalleyInterpolation f).split.semisimple :=
  (jordanChevalleyInterpolation f).semisimple_eq

omit [FiniteDimensional K V] in
/-- The semisimple interpolation commutes with every symmetry commuting with the Hamiltonian. -/
theorem semisimplePart_commute {f g : Module.End K V}
    (P : JordanChevalleyInterpolation f) (hfg : Commute f g) :
    Commute (semisimplePart P) g := by
  simpa [semisimplePart] using
    (commute_of_mem_adjoin_singleton (f := f) (g := g) hfg
      (Polynomial.aeval_mem_adjoin_singleton (R := K) (p := P.poly) f))

omit [FiniteDimensional K V] in
/-- The nilpotent interpolation commutes with every symmetry commuting with the Hamiltonian. -/
theorem nilpotentPart_commute {f g : Module.End K V}
    (P : JordanChevalleyInterpolation f) (hfg : Commute f g) :
    Commute (nilpotentPart P) g := by
  simpa [nilpotentPart] using Commute.sub_left hfg (semisimplePart_commute (P := P) hfg)

omit [FiniteDimensional K V] in
/-- The polynomial interpolation preserves both the scale and defect symmetries. -/
theorem preserves_symmetries {f g : Module.End K V}
    (P : JordanChevalleyInterpolation f) (hfg : Commute f g) :
    Commute (semisimplePart P) g ∧ Commute (nilpotentPart P) g := by
  constructor
  · exact semisimplePart_commute (P := P) hfg
  · exact nilpotentPart_commute (P := P) hfg

omit [FiniteDimensional K V] in
/-- Supersymmetry readback for the nilpotent defect sector. -/
theorem unbroken_susy_in_jordan_blocks {f g : Module.End K V}
    (P : JordanChevalleyInterpolation f)
    (hSUSY : Commute f g) :
    Commute (nilpotentPart P) g :=
  (preserves_symmetries (P := P) hSUSY).right

end InfoGeometry.Canonical.JordanChevalleyPolynomialBridge
