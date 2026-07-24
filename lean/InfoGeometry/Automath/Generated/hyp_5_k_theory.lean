import Mathlib
import Mathlib.Algebra.FreeAlgebra

namespace Automath.Generated

set_option linter.unusedVariables false

/-- Reduction-Modulo-(n-1) on K?: Under K?(M?(?))??, K?(O?)??/(n-1)?, the embedding ? induces ?_*: ? -> ?/(n-1)? given by reduction mod (n-1). For n=2, K?(O?)=0 so the embedding is K-theoretically invisible despite being injective and spectrally faithful. Falsified if ?_*([E??]) != [1_{O?}] or if induced map differs from reduction mod (n-1).
The embedding ?(E??) = S?S?* is Murray-von Neumann equivalent to 1_{O?}, so the generator maps to 0 in K?(O?). The embedding is invisible to ordinary K-theory despite being injective and spectrally faithful. Falsified if ?_*([E??]) != [1_{O?}] or induced map differs from reduction mod (n-1).
Source: InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz
Objects: k-theory, cuntz-algebra, murray-von-neumann, projection, k0-group -/
theorem hyp_5_k_theory (n : ℕ) (x y : FreeAlgebra ℂ (Fin n)) :
    x * y = y * x :=
  sorry

end Automath.Generated
