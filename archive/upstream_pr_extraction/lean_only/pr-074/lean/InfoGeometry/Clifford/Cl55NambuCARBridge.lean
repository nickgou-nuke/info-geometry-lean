import Mathlib.Tactic
import InfoGeometry.Clifford.Cl55CARSpinAutomorphism

/-!
# Native `Cl(5,5)` Nambu--Gor'kov CAR

This file packages the already-proved five Witt CAR pairs into a single
particle/hole-indexed field.  It does not introduce a new Clifford carrier,
BdG Hamiltonian, or supercharge vocabulary.
-/

namespace InfoGeometry.Clifford.Clifford55

abbrev NambuIndex55 := Fin 2

noncomputable def nambuField55 (i : Fin 5) : NambuIndex55 → Cl55
  | 0 => annihilation55 i
  | 1 => creation55 i

def nambuTauXEntry55 (α β : NambuIndex55) : ℝ :=
  if α ≠ β then 1 else 0

@[simp] theorem nambuTauXEntry55_zero_zero :
    nambuTauXEntry55 0 0 = 0 := by
  simp [nambuTauXEntry55]

@[simp] theorem nambuTauXEntry55_zero_one :
    nambuTauXEntry55 0 1 = 1 := by
  simp [nambuTauXEntry55]

@[simp] theorem nambuTauXEntry55_one_zero :
    nambuTauXEntry55 1 0 = 1 := by
  simp [nambuTauXEntry55]

@[simp] theorem nambuTauXEntry55_one_one :
    nambuTauXEntry55 1 1 = 0 := by
  simp [nambuTauXEntry55]

theorem nambuField55_CAR_tauX
    (i j : Fin 5) (α β : NambuIndex55) :
    nambuField55 i α * nambuField55 j β +
        nambuField55 j β * nambuField55 i α =
      (if i = j then
        nambuTauXEntry55 α β • (1 : Cl55)
       else 0) := by
  fin_cases α <;> fin_cases β
  · simp [nambuField55, nambuTauXEntry55,
      annihilation55_anticommutator]
  · simpa [nambuField55, nambuTauXEntry55] using
      (annihilation55_creation55_anticommutator_eq i j)
  · simpa [nambuField55, nambuTauXEntry55, add_comm, eq_comm] using
      (annihilation55_creation55_anticommutator_eq j i)
  · simp [nambuField55, nambuTauXEntry55,
      creation55_anticommutator]

end InfoGeometry.Clifford.Clifford55
