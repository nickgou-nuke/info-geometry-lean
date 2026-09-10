import InfoGeometry.Canonical.CelikCantorCl2UniversalHom
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The standard rank-one Witt/Fock basis

The Pauli matrices `V` and `J` give the standard matrix-unit annihilator and
creator.  This owner records the finite CAR and vacuum/occupied projection
packet, together with its pullback through the already proved Clifford
equivalence.  No K-theory or multi-site tensor claim is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikCantorWittBasis

open InfoGeometry.Canonical.CelikCantorClifford
open InfoGeometry.Canonical.CelikCantorCl2UniversalHom

abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

noncomputable def annihilator : Mat2C :=
  (1 / 2 : ℂ) • (V - Complex.I • J)

noncomputable def creator : Mat2C :=
  (1 / 2 : ℂ) • (V + Complex.I • J)

@[simp] theorem annihilator_matrix :
    annihilator = !![(0 : ℂ), 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [annihilator, V, J, Matrix.smul_apply] <;> norm_num

@[simp] theorem creator_matrix :
    creator = !![(0 : ℂ), 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [creator, V, J, Matrix.smul_apply] <;> norm_num

@[simp] theorem annihilator_sq : annihilator * annihilator = 0 := by
  rw [annihilator_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem creator_sq : creator * creator = 0 := by
  rw [creator_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem car_relation :
    annihilator * creator + creator * annihilator = 1 := by
  rw [annihilator_matrix, creator_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem star_annihilator : star annihilator = creator := by
  rw [annihilator_matrix, creator_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp] theorem star_creator : star creator = annihilator := by
  rw [creator_matrix, annihilator_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

noncomputable def vacuumProjection : Mat2C := annihilator * creator

noncomputable def occupiedProjection : Mat2C := creator * annihilator

@[simp] theorem vacuumProjection_matrix :
    vacuumProjection = !![(1 : ℂ), 0; 0, 0] := by
  rw [vacuumProjection, annihilator_matrix, creator_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem occupiedProjection_matrix :
    occupiedProjection = !![(0 : ℂ), 0; 0, 1] := by
  rw [occupiedProjection, annihilator_matrix, creator_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem vacuumProjection_idempotent :
    vacuumProjection * vacuumProjection = vacuumProjection := by
  rw [vacuumProjection_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem occupiedProjection_idempotent :
    occupiedProjection * occupiedProjection = occupiedProjection := by
  rw [occupiedProjection_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem vacuum_occupied_orthogonal :
    vacuumProjection * occupiedProjection = 0 := by
  rw [vacuumProjection_matrix, occupiedProjection_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem occupied_vacuum_orthogonal :
    occupiedProjection * vacuumProjection = 0 := by
  rw [occupiedProjection_matrix, vacuumProjection_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem vacuum_add_occupied :
    vacuumProjection + occupiedProjection = 1 := by
  rw [vacuumProjection_matrix, occupiedProjection_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem vacuumProjection_pauli_formula :
    vacuumProjection = (1 / 2 : ℂ) • ((1 : Mat2C) + U) := by
  rw [vacuumProjection_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, Matrix.smul_apply] <;> norm_num

theorem occupiedProjection_pauli_formula :
    occupiedProjection = (1 / 2 : ℂ) • ((1 : Mat2C) - U) := by
  rw [occupiedProjection_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, Matrix.smul_apply] <;> norm_num

theorem parity_from_projections :
    vacuumProjection - occupiedProjection = U := by
  rw [vacuumProjection_matrix, occupiedProjection_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U]

noncomputable def cliffordAnnihilator : CliffordAlgebra q2 :=
  celikCl2AlgebraEquiv.symm annihilator

noncomputable def cliffordCreator : CliffordAlgebra q2 :=
  celikCl2AlgebraEquiv.symm creator

@[simp] theorem cliffordAnnihilator_readout :
    celikCl2AlgebraEquiv cliffordAnnihilator = annihilator := by
  simp [cliffordAnnihilator]

@[simp] theorem cliffordCreator_readout :
    celikCl2AlgebraEquiv cliffordCreator = creator := by
  simp [cliffordCreator]

theorem cliffordAnnihilator_formula :
    cliffordAnnihilator =
      (1 / 2 : ℂ) •
        (CliffordAlgebra.ι q2 (0, 1) +
          CliffordAlgebra.ι q2 (1, 0) * CliffordAlgebra.ι q2 (0, 1)) := by
  apply celikCl2AlgebraEquiv.injective
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cliffordAnnihilator, annihilator, U, V, J, Matrix.smul_apply,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
      norm_num

theorem cliffordCreator_formula :
    cliffordCreator =
      (1 / 2 : ℂ) •
        (CliffordAlgebra.ι q2 (0, 1) -
          CliffordAlgebra.ι q2 (1, 0) * CliffordAlgebra.ι q2 (0, 1)) := by
  apply celikCl2AlgebraEquiv.injective
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cliffordCreator, creator, U, V, J, Matrix.smul_apply,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
      norm_num

end InfoGeometry.Canonical.CelikCantorWittBasis
