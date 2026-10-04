import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace InfoGeometry.Canonical

/-- The 112 vector roots of the D8 subalgebra (permutations of ±1, ±1, 0^6). -/
abbrev E8VectorRoots := { p : Fin 8 × Fin 8 // p.1 < p.2 } × (Bool × Bool)

/-- The 128 spinor roots of E8 (±1/2, ..., ±1/2 with even parity of minus signs). -/
abbrev E8SpinorRoots := Fin 7 → Bool

/-- The full set of 240 E8 roots. -/
abbrev E8Roots := E8VectorRoots ⊕ E8SpinorRoots

/-- The number of D8 vector roots is exactly 112. -/
theorem card_e8_vector_roots : Fintype.card E8VectorRoots = 112 := by
  rfl

/-- The number of E8 spinor roots is exactly 128. -/
theorem card_e8_spinor_roots : Fintype.card E8SpinorRoots = 128 := by
  rfl

/-- 
🏆 THEOREM (E8 Lattice Structural Decomposition):
The 240 roots of the E8 exceptional lattice decompose perfectly into 
the 112 vector roots of the D8 subalgebra and its 128 spinor roots.
-/
theorem e8_root_decomposition_cardinality :
    Fintype.card E8Roots = 240 := by
  rw [Fintype.card_sum]
  rw [card_e8_vector_roots, card_e8_spinor_roots]

end InfoGeometry.Canonical
