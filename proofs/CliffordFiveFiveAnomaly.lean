import proofs.Clifford55AnomalyOSP

/-!
# Clifford `(5,5)` anomaly compatibility layer

This integrates the useful external `CliffordFiveFiveAnomaly` arithmetic by
routing it through the active `Clifford55AnomalyOSP` module.  Claims are finite
algebraic checks only: dimension arithmetic, split anomaly cancellation,
and the concrete `osp(1|2)` atom already proved in the active file.
-/

noncomputable section

namespace CliffordFiveFiveAnomaly

/-- Genuine index equivalence behind `M₂ ⊗ M₁₆ ≃ M₃₂`: row/column indices multiply. -/
def matrixIndexEquiv : Fin 2 × Fin 16 ≃ Fin 32 :=
  finProdFinEquiv.trans (finCongr (by norm_num))

/-- Matrix-entry index equivalence induced by `M₂ ⊗ M₁₆` flattening. -/
def matrixEntryIndexEquiv : (Fin 2 × Fin 16) × (Fin 2 × Fin 16) ≃ Fin 32 × Fin 32 :=
  Equiv.prodCongr matrixIndexEquiv matrixIndexEquiv

/-- Pull a `32×32` matrix back to its `2×16` by `2×16` block-indexed form. -/
def unflattenMatrix (A : Matrix (Fin 32) (Fin 32) ℝ) :
    Matrix (Fin 2 × Fin 16) (Fin 2 × Fin 16) ℝ :=
  fun i j => A (matrixIndexEquiv i) (matrixIndexEquiv j)

/-- Flatten a block-indexed matrix to an ordinary `32×32` matrix. -/
def flattenMatrix (A : Matrix (Fin 2 × Fin 16) (Fin 2 × Fin 16) ℝ) :
    Matrix (Fin 32) (Fin 32) ℝ :=
  fun i j => A (matrixIndexEquiv.symm i) (matrixIndexEquiv.symm j)

/-- Flattening and unflattening are inverse on `32×32` matrices. -/
theorem flatten_unflatten (A : Matrix (Fin 32) (Fin 32) ℝ) :
    flattenMatrix (unflattenMatrix A) = A := by
  ext i j
  simp [flattenMatrix, unflattenMatrix]

/-- Unflattening and flattening are inverse on block-indexed matrices. -/
theorem unflatten_flatten (A : Matrix (Fin 2 × Fin 16) (Fin 2 × Fin 16) ℝ) :
    unflattenMatrix (flattenMatrix A) = A := by
  ext i j
  simp [flattenMatrix, unflattenMatrix]

/-- Concrete matrix-space equivalence underlying the dimension factorization. -/
def matrixBlockEquiv :
    Matrix (Fin 2 × Fin 16) (Fin 2 × Fin 16) ℝ ≃ Matrix (Fin 32) (Fin 32) ℝ where
  toFun := flattenMatrix
  invFun := unflattenMatrix
  left_inv := unflatten_flatten
  right_inv := flatten_unflatten

/-- Dimension factorization for the split Clifford arithmetic. -/
theorem clifford_tensor_factorization : (4 : ℕ) * 256 = 1024 := by
  exact Clifford55AnomalyOSP.matrix_dim_factor

/-- Split signature cancellation when the supplied integers are exactly `(5,5)`. -/
theorem split_anomaly_cancellation (p q : ℤ) (h_split : p = 5 ∧ q = 5) :
    p - q = 0 := by
  rcases h_split with ⟨hp, hq⟩
  simp [hp, hq]

/-- In any additive-cancellative matrix ring, `{G,G}=2T` implies `G²=T`. -/
theorem osp_spatial_supersymmetry
    {n : Type*} [Fintype n] [DecidableEq n] (G T : Matrix n n ℝ)
    (h_anticomm : G * G + G * G = T + T) :
    G * G = T := by
  ext i j
  have h_eq : (G * G + G * G) i j = (T + T) i j := by rw [h_anticomm]
  have h_eq' : (G * G) i j + (G * G) i j = T i j + T i j := by simpa using h_eq
  linarith

/-- Concrete active atom: the external `osp` idea has a checked `2×2` model. -/
theorem concrete_osp_atom :
    Clifford55AnomalyOSP.Gatom * Clifford55AnomalyOSP.Gatom = Clifford55AnomalyOSP.Tatom ∧
    Clifford55AnomalyOSP.Gatom * Clifford55AnomalyOSP.Gatom +
        Clifford55AnomalyOSP.Gatom * Clifford55AnomalyOSP.Gatom =
      (2 : ℂ) • Clifford55AnomalyOSP.Tatom := by
  exact ⟨Clifford55AnomalyOSP.Gatom_sq, Clifford55AnomalyOSP.osp_atom_anticommutator⟩

/-- Consolidated finite `Cl(5,5)` anomaly arithmetic. -/
theorem clifford_five_five_anomaly_arithmetic :
    (4 : ℕ) * 256 = 1024 ∧ Clifford55AnomalyOSP.anomalyIndex 5 5 = 0 ∧
    Clifford55AnomalyOSP.Trip * Clifford55AnomalyOSP.Trip * Clifford55AnomalyOSP.Trip =
      Clifford55AnomalyOSP.Trip := by
  constructor
  · exact clifford_tensor_factorization
  constructor
  · exact Clifford55AnomalyOSP.anomalyIndex_55_zero
  · exact Clifford55AnomalyOSP.Trip_tripotent

#check clifford_tensor_factorization
#check split_anomaly_cancellation
#check osp_spatial_supersymmetry
#check concrete_osp_atom
#check clifford_five_five_anomaly_arithmetic

end CliffordFiveFiveAnomaly
