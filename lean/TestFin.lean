import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

def fin3ToFin8 (j : Fin 3) : Fin 8 :=
  ⟨j.val + 2, by omega⟩

#eval fin3ToFin8 (0 : Fin 3)
#eval fin3ToFin8 (1 : Fin 3)
#eval fin3ToFin8 (2 : Fin 3)
