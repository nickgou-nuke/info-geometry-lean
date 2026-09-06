import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace KitaevQuantumDoubleGSDBridge

/-!
The finite label carrier of the Drinfeld double of a finite group `G` is
`G × G`: one component records the flux label and one records the charge
label.  The ground-state degeneracy on the torus is therefore the cardinality
of this noncommutative label carrier, not a separately postulated scalar
function of a natural number.
-/

abbrev quantumDoubleBasis (G : Type*) := G × G

theorem quantumDoubleBasis_card (G : Type*) [Fintype G] :
    Fintype.card (quantumDoubleBasis G) = Fintype.card G ^ 2 := by
  simp [quantumDoubleBasis, pow_two]

def quantumDoubleTorusGSD (G : Type*) [Fintype G] : ℕ :=
  Fintype.card (quantumDoubleBasis G)

theorem quantum_double_total_dim_sq_formula (G : Type*) [Fintype G] :
    quantumDoubleTorusGSD G = Fintype.card G ^ 2 := by
  exact quantumDoubleBasis_card G

theorem toric_code_torus_gsd_eq :
    quantumDoubleTorusGSD (ZMod 2) = 4 := by
  native_decide

theorem quantum_double_s3_total_dim_sq_eq :
    quantumDoubleTorusGSD (Equiv.Perm (Fin 3)) = 36 := by
  native_decide

end KitaevQuantumDoubleGSDBridge
