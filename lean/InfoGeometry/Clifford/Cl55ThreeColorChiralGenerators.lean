import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure

/-!
# The three-colour chiral readout inside `Cl(5,5)`

This is a direct restriction of the existing five CAR pairs to the first
three colour indices.  It introduces no new carrier and makes no claim that
these Clifford generators are already identified with the split-octonion
soldering operators.
-/

namespace InfoGeometry.Clifford.Clifford55

noncomputable section

def chiralPlus55 (i : Fin 3) : Cl55 :=
  creation55 (Fin.castAdd 2 i)

def chiralMinus55 (i : Fin 3) : Cl55 :=
  annihilation55 (Fin.castAdd 2 i)

@[simp] theorem chiralPlus55_sq (i : Fin 3) :
    chiralPlus55 i * chiralPlus55 i = 0 := by
  simp [chiralPlus55]

@[simp] theorem chiralMinus55_sq (i : Fin 3) :
    chiralMinus55 i * chiralMinus55 i = 0 := by
  simp [chiralMinus55]

theorem chiralPlus55_mem_grade_one (i : Fin 3) :
    chiralPlus55 i ∈ cl55GradeSubmodule 1 := by
  exact creation55_mem_grade_one (Fin.castAdd 2 i)

theorem chiralMinus55_mem_grade_neg_one (i : Fin 3) :
    chiralMinus55 i ∈ cl55GradeSubmodule (-1) := by
  exact annihilation55_mem_grade_neg_one (Fin.castAdd 2 i)

theorem chiralPlus55_product_mem_grade_two (i j : Fin 3) :
    chiralPlus55 i * chiralPlus55 j ∈ cl55GradeSubmodule 2 := by
  exact creation55_mul_creation55_mem_grade_two
    (Fin.castAdd 2 i) (Fin.castAdd 2 j)

theorem chiralMinus55_product_mem_grade_neg_two (i j : Fin 3) :
    chiralMinus55 i * chiralMinus55 j ∈ cl55GradeSubmodule (-2) := by
  exact annihilation55_mul_annihilation55_mem_grade_neg_two
    (Fin.castAdd 2 i) (Fin.castAdd 2 j)

theorem chiralPlus55_minus55_product_mem_grade_zero (i j : Fin 3) :
    chiralPlus55 i * chiralMinus55 j ∈ cl55GradeSubmodule 0 := by
  exact creation55_mul_annihilation55_mem_grade_zero
    (Fin.castAdd 2 i) (Fin.castAdd 2 j)

theorem chiralMinus55_plus55_product_mem_grade_zero (i j : Fin 3) :
    chiralMinus55 i * chiralPlus55 j ∈ cl55GradeSubmodule 0 := by
  exact annihilation55_mul_creation55_mem_grade_zero
    (Fin.castAdd 2 i) (Fin.castAdd 2 j)

theorem chiralPlus55_anticommutator (i j : Fin 3) :
    chiralPlus55 i * chiralPlus55 j +
        chiralPlus55 j * chiralPlus55 i = 0 := by
  exact creation55_anticommutator (Fin.castAdd 2 i) (Fin.castAdd 2 j)

theorem chiralMinus55_anticommutator (i j : Fin 3) :
    chiralMinus55 i * chiralMinus55 j +
        chiralMinus55 j * chiralMinus55 i = 0 := by
  exact annihilation55_anticommutator (Fin.castAdd 2 i) (Fin.castAdd 2 j)

theorem chiralMinus55_plus55_anticommutator (i j : Fin 3) :
    chiralMinus55 i * chiralPlus55 j +
        chiralPlus55 j * chiralMinus55 i =
      if i = j then 1 else 0 := by
  have hcast : Fin.castAdd 2 i = Fin.castAdd 2 j ↔ i = j := by
    constructor
    · intro h
      exact (Fin.castAdd_injective 3 2) h
    · intro h
      simpa [h]
  simpa [chiralMinus55, chiralPlus55, hcast] using
      (annihilation55_creation55_anticommutator_eq
      (Fin.castAdd 2 i) (Fin.castAdd 2 j))

theorem chiralPlus55_minus55_anticommutator (i j : Fin 3) :
    chiralPlus55 i * chiralMinus55 j +
        chiralMinus55 j * chiralPlus55 i =
      if i = j then 1 else 0 := by
  simpa [add_comm, eq_comm] using chiralMinus55_plus55_anticommutator j i

theorem chiralPlus55_minus55_commutator_mem_grade_zero (i j : Fin 3) :
    chiralPlus55 i * chiralMinus55 j -
        chiralMinus55 j * chiralPlus55 i ∈ cl55GradeSubmodule 0 := by
  exact cl55_mixed_commutator_mem_grade_zero
    (chiralPlus55_mem_grade_one i) (chiralMinus55_mem_grade_neg_one j)

theorem chiralMinus55_plus55_commutator_mem_grade_zero (i j : Fin 3) :
    chiralMinus55 i * chiralPlus55 j -
        chiralPlus55 j * chiralMinus55 i ∈ cl55GradeSubmodule 0 := by
  have h := cl55_mixed_commutator_mem_grade_zero
    (chiralPlus55_mem_grade_one j) (chiralMinus55_mem_grade_neg_one i)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (Submodule.neg_mem (cl55GradeSubmodule 0) h)

theorem chiralPlus55_commutator_mem_grade_two
    (i j : Fin 3) :
    chiralPlus55 i * chiralPlus55 j -
        chiralPlus55 j * chiralPlus55 i ∈ cl55GradeSubmodule 2 := by
  exact cl55_pos_one_pos_one_commutator_mem_grade_two
    (chiralPlus55_mem_grade_one i) (chiralPlus55_mem_grade_one j)

theorem chiralMinus55_commutator_mem_grade_neg_two
    (i j : Fin 3) :
    chiralMinus55 i * chiralMinus55 j -
        chiralMinus55 j * chiralMinus55 i ∈
      cl55GradeSubmodule (-2) := by
  exact cl55_neg_one_neg_one_commutator_mem_grade_neg_two
    (chiralMinus55_mem_grade_neg_one i)
    (chiralMinus55_mem_grade_neg_one j)

theorem chiralPlus55_spin_transport
    (g : Spin55) (i : Fin 3) :
    spinCliffordRingEquiv g (chiralPlus55 i) ∈
      spinTransportedCl55GradeSubmodule g 1 := by
  exact spinTransported_creation55_mem_grade_one g (Fin.castAdd 2 i)

theorem chiralMinus55_spin_transport
    (g : Spin55) (i : Fin 3) :
    spinCliffordRingEquiv g (chiralMinus55 i) ∈
      spinTransportedCl55GradeSubmodule g (-1) := by
  exact spinTransported_annihilation55_mem_grade_neg_one g (Fin.castAdd 2 i)

end

end InfoGeometry.Clifford.Clifford55
