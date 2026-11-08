import InfoGeometry.Clifford.SolderingCl11MatrixBridge
import InfoGeometry.Krein.Clifford

/-!
# Soldering `Cl(1,1)` roots in the doubled-real Krein representation

The soldering owner identifies two Clifford elements with the real matrix
CAR roots. `Cl11Matrix` identifies its quadratic form with `splitQ11`, and
Mathlib's isometry equivalence transports the Clifford algebra to the native
split-form carrier. This file composes that transport with the repository's
operator representation on `HilbertDoubled`; the latter retains the doubled
real Krein structure.
-/

noncomputable section

namespace InfoGeometry.Clifford.SolderingKreinRepresentationBridge

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.SolderingCl11MatrixBridge
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The quaternion-defined `Cl(1,1)` algebra acts on the repository's
doubled-real Krein space by transport through the equality of quadratic forms. -/
def cl11KreinRep : CliffordAlgebra q11 →ₐ[ℝ]
    (HilbertDoubled E →L[ℝ] HilbertDoubled E) :=
  (cl11RepHilbert (E := E)).comp q11ToSplitClifford.toAlgHom

/-- The transport sends every `q11` generator to the same-coordinate generator
of the native `splitQ11` carrier before applying the Krein representation. -/
@[simp] theorem cl11KreinRep_ι (v : Vec11) :
    cl11KreinRep (E := E) (CliffordAlgebra.ι q11 v) =
      cl11RepHilbert (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v) := by
  simp [cl11KreinRep]

/-- The raising soldering root acts square-zero on the doubled-real Krein
space, by transporting the already-proved Clifford CAR root. -/
theorem cl11KreinRep_rootPlus_sq :
    cl11KreinRep (E := E) rootPlusCl11 * cl11KreinRep (E := E) rootPlusCl11 = 0 := by
  have h := congrArg (cl11KreinRep (E := E)) rootPlusCl11_sq_zero
  simpa only [map_mul, map_zero] using h

/-- The lowering soldering root acts square-zero on the doubled-real Krein
space, by transporting the already-proved Clifford CAR root. -/
theorem cl11KreinRep_rootMinus_sq :
    cl11KreinRep (E := E) rootMinusCl11 * cl11KreinRep (E := E) rootMinusCl11 = 0 := by
  have h := congrArg (cl11KreinRep (E := E)) rootMinusCl11_sq_zero
  simpa only [map_mul, map_zero] using h

/-- The two soldering roots satisfy CAR as bounded operators on the doubled-real
Krein space. -/
theorem cl11KreinRep_root_anticommutator :
    cl11KreinRep (E := E) rootPlusCl11 * cl11KreinRep (E := E) rootMinusCl11 +
      cl11KreinRep (E := E) rootMinusCl11 * cl11KreinRep (E := E) rootPlusCl11 = 1 := by
  have h := congrArg (cl11KreinRep (E := E)) rootCl11_anticommutator
  simpa only [map_add, map_mul, map_one] using h

end InfoGeometry.Clifford.SolderingKreinRepresentationBridge

end
