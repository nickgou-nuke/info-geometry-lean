import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

def fin3ToFin8 (j : Fin 3) : Fin 8 :=
  Fin.mk (j + 2) (by
    cases j with
    | mk j hj =>
      cases j with
      | zero => norm_num
      | succ j => cases j with
        | zero => norm_num
        | succ j =>
          simp at hj
          norm_num)

#eval fin3ToFin8 (0 : Fin 3)
#eval fin3ToFin8 (1 : Fin 3)
#eval fin3ToFin8 (2 : Fin 3)
