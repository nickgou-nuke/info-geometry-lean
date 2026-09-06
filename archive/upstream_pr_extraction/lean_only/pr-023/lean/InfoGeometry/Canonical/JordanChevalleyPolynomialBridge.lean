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

/--
Every Jordan-Chevalley split admits a polynomial interpolation witness.
This packages the semisimple part as `p(f)` using the singleton-adjoin theorem.
-/
theorem interpolation_exists (f : Module.End K V) [PerfectField K] :
    Nonempty (JordanChevalleyInterpolation f) := by
  rcases JordanChevalleySplit.split_exists (f := f) with ⟨B⟩
  rcases Algebra.adjoin_mem_exists_aeval (R := K) (x := f) B.semisimpleMem with ⟨p, hp⟩
  exact ⟨⟨B, p, hp⟩⟩

/-- The semisimple interpolation commutes with every symmetry commuting with the Hamiltonian. -/
theorem semisimplePart_commute {f g : Module.End K V}
    (P : JordanChevalleyInterpolation f) (hfg : Commute f g) :
    Commute (semisimplePart P) g := by
  simpa [semisimplePart] using
    (commute_of_mem_adjoin_singleton (f := f) (g := g) hfg
      (by simpa using
        (Polynomial.aeval_mem_adjoin_singleton (R := K) (p := P.poly) f)))

/-- The nilpotent interpolation commutes with every symmetry commuting with the Hamiltonian. -/
theorem nilpotentPart_commute {f g : Module.End K V}
    (P : JordanChevalleyInterpolation f) (hfg : Commute f g) :
    Commute (nilpotentPart P) g := by
  simpa [nilpotentPart] using Commute.sub_left hfg (semisimplePart_commute (P := P) hfg)

/-- The polynomial interpolation preserves both the scale and defect symmetries. -/
theorem preserves_symmetries {f g : Module.End K V}
    (P : JordanChevalleyInterpolation f) (hfg : Commute f g) :
    Commute (semisimplePart P) g ∧ Commute (nilpotentPart P) g := by
  constructor
  · exact semisimplePart_commute (P := P) hfg
  · exact nilpotentPart_commute (P := P) hfg

/-- Supersymmetry readback for the nilpotent defect sector. -/
theorem unbroken_susy_in_jordan_blocks {f g : Module.End K V}
    (P : JordanChevalleyInterpolation f)
    (hSUSY : Commute f g) :
    Commute (nilpotentPart P) g :=
  (preserves_symmetries (P := P) hSUSY).right

end InfoGeometry.Canonical.JordanChevalleyPolynomialBridge
