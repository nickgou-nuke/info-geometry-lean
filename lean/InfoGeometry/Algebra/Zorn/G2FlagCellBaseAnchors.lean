import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Base indices of the exported flag cells

This owner records only the finite partition anchors.  It deliberately does
not identify the corresponding Lean representatives with GAP representatives
or assert a quotient equality.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagCellBaseAnchors

open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

def flagCellBaseIndex : Fin 12 → Fin 189
  | 0 => 0
  | 1 => 24
  | 2 => 3
  | 3 => 9
  | 4 => 6
  | 5 => 15
  | 6 => 1
  | 7 => 16
  | 8 => 7
  | 9 => 10
  | 10 => 4
  | 11 => 25

set_option maxRecDepth 100000 in
theorem flagCellBaseIndex_mem (k : Fin 12) :
    flagCellBaseIndex k ∈ flagCells k := by
  fin_cases k <;> decide

end InfoGeometry.Algebra.Zorn.G2FlagCellBaseAnchors
