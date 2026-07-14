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

namespace JordanChevalleyPolynomialBridge

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

/-- Jordan-Chevalley interpolation exists as an explicit existential theorem. -/
theorem exists_jordanChevalleyInterpolation
    (f : Module.End K V) [PerfectField K] :
    ∃ P : JordanChevalleyInterpolation f,
      Polynomial.aeval f P.poly = P.split.semisimple ∧
      IsSemisimpleEnd P.split.semisimple ∧
      IsNilpotentEnd P.split.nilpotent ∧
      Commute P.split.semisimple P.split.nilpotent ∧
      f = P.split.semisimple + P.split.nilpotent := by
  rcases JordanChevalleySplit.exists_split (f := f) with
    ⟨B, hss, hnil, hcomm, _hs, _hn, hsum⟩
  rcases Algebra.adjoin_mem_exists_aeval (R := K) (x := f) B.semisimpleMem with
    ⟨p, hp⟩
  exact ⟨⟨B, p, hp⟩, hp, hss, hnil, hcomm, hsum⟩

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

end JordanChevalleyPolynomialBridge
