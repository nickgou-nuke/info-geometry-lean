import InfoGeometry.Quantum.ChoiCompletePositivity

/-!
# Modular Choi compatibility owner

The native finite Choi certificate lives in `InfoGeometry.Quantum.Choi`.
This file provides the historical modular API without duplicating its proofs.
-/

noncomputable section

namespace InfoGeometry.Modular.Choi

open InfoGeometry.Quantum.Choi
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

abbrev MatrixMap := InfoGeometry.Quantum.Choi.MatrixMap (n := n)

abbrev stdBasis := InfoGeometry.Quantum.Choi.matrixUnit (n := n)

abbrev choiMatrix := InfoGeometry.Quantum.Choi.choiMatrix (n := n)

abbrev krausTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Mat) (X : Mat) : Mat := V * X * star V

def krausChannel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  InfoGeometry.Quantum.Choi.krausMap V

theorem choi_matrix_positive_semidefinite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) : (choiMatrix (krausChannel V)).PosSemidef := by
  rw [show choiMatrix (krausChannel V) = krausChoi V by
    simpa [krausChannel] using (choiMatrix_krausMap_eq_krausChoi V)]
  exact krausChoi_posSemidef V

theorem krausChannel_choi_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) :
    (choiMatrix (krausChannel V)).PosSemidef := by
  exact choi_matrix_positive_semidefinite V

end InfoGeometry.Modular.Choi

end noncomputable section
