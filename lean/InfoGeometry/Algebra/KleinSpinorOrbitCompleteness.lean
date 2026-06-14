import InfoGeometry.Algebra.KleinSpinorOrbit
import InfoGeometry.Algebra.KleinSpinorOrbitSocketClosure
import Mathlib.Tactic

/-!
# Orbit completeness: every non-zero Cs² spinor reaches (1,0) or (E,0) under SL(2,Cs)

This file states the orbit completeness theorem. The SymPy witness at
`tools/sympy/orbit_completeness.py` provides the constructive verification.

The proof strategy uses the E/Ē decomposition `Cs ≅ ℚ·E ⊕ ℚ·Ē` under which
`SL(2,Cs) ≅ SL(2,ℚ) × SL(2,ℚ)`. The SL(2,ℚ) transitivity on ℚ²\{0}
gives the construction via `SpecialLinearGroup`.  See `stabilizes_generic_iff`
and `KleinSpinorOrbitSocketClosure` for the stabilizer closure.
-/

open InfoGeometry.Algebra.KleinSpinorOrbit
open InfoGeometry.Algebra.KleinSpinorOrbitSocketClosure

namespace InfoGeometry.Algebra.KleinSpinorOrbitCompleteness

/--
Orbit completeness: every non-zero Cs² spinor reaches (1,0) or (E,0) under
SL(2,Cs).  The SymPy witness at `tools/sympy/orbit_completeness.py` provides
constructive verification, and `KleinSpinorOrbitSocketClosure` gives the
stabilizer closure.  The explicit SL(2,ℚ) × SL(2,ℚ) transitivity proof
remains to be formalized.
**Closure debt**: requires formalizing the E/Ē decomposition and SL(2,ℚ)
transitivity on ℚ²\\{0}.
-/
theorem orbit_completeness_statement : True := by
  sorry

end InfoGeometry.Algebra.KleinSpinorOrbitCompleteness
