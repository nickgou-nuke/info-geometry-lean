import InfoGeometry.MaxEnt.Finite

open scoped BigOperators

/-!
# Finite Diagonal Thermal Model (Matrix Realization)

A concrete finite-dimensional thermal layer using diagonal matrices over `ℝ`:

- Hamiltonian `H = diag(Eᵢ)`
- Gibbs density `ρ_β = diag(exp(-β Eᵢ)/Z(β))`
- thermal functional `ω_β(A) = ⟨ρ_β, A⟩` on diagonal observables
- a diagonal (commutative) KMS-like identity

This is a clean intermediate step before a full noncommutative matrix-exponential KMS file.
-/

namespace InfoGeometry.Thermal

section DiagonalObs

variable {n : ℕ}

/-- Diagonal observables, represented by their diagonal coefficients. -/
structure DiagonalObservable (n : ℕ) where
  coeff : Fin n → ℝ

namespace DiagonalObservable

instance : CoeFun (DiagonalObservable n) (fun _ => Fin n → ℝ) := ⟨fun A => A.coeff⟩

instance : Zero (DiagonalObservable n) := ⟨⟨fun _ => 0⟩⟩
instance : One (DiagonalObservable n) := ⟨⟨fun _ => 1⟩⟩
instance : Add (DiagonalObservable n) := ⟨fun A B => ⟨fun i => A i + B i⟩⟩
instance : Neg (DiagonalObservable n) := ⟨fun A => ⟨fun i => -A i⟩⟩
instance : Sub (DiagonalObservable n) := ⟨fun A B => ⟨fun i => A i - B i⟩⟩
instance : Mul (DiagonalObservable n) := ⟨fun A B => ⟨fun i => A i * B i⟩⟩
instance : SMul ℝ (DiagonalObservable n) := ⟨fun a A => ⟨fun i => a * A i⟩⟩

@[simp] lemma zero_apply (i : Fin n) : (0 : DiagonalObservable n) i = 0 := rfl
@[simp] lemma one_apply (i : Fin n) : (1 : DiagonalObservable n) i = 1 := rfl
@[simp] lemma add_apply (A B : DiagonalObservable n) (i : Fin n) : (A + B) i = A i + B i := rfl
@[simp] lemma sub_apply (A B : DiagonalObservable n) (i : Fin n) : (A - B) i = A i - B i := rfl
@[simp] lemma neg_apply (A : DiagonalObservable n) (i : Fin n) : (-A) i = -A i := rfl
@[simp] lemma mul_apply (A B : DiagonalObservable n) (i : Fin n) : (A * B) i = A i * B i := rfl
@[simp] lemma smul_apply (a : ℝ) (A : DiagonalObservable n) (i : Fin n) : (a • A) i = a * A i := rfl

/-- Matrix realization as a diagonal matrix. -/
noncomputable def toMatrix (A : DiagonalObservable n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => A i)

@[simp] lemma toMatrix_apply_diag (A : DiagonalObservable n) (i : Fin n) :
    A.toMatrix i i = A i := by
  simp [toMatrix]

@[simp] lemma toMatrix_apply_offdiag (A : DiagonalObservable n) {i j : Fin n} (h : i ≠ j) :
    A.toMatrix i j = 0 := by
  simp [toMatrix, h]

end DiagonalObservable
end DiagonalObs

section FiniteThermal

variable {n : ℕ} [Nonempty (Fin n)]

open DiagonalObservable

/-- A finite diagonal Hamiltonian, encoded by energy levels `Eᵢ`. -/
structure Hamiltonian (n : ℕ) where
  energy : Fin n → ℝ

namespace Hamiltonian

/-- Matrix form `H = diag(Eᵢ)`. -/
noncomputable def toMatrix (H : Hamiltonian n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal H.energy

omit [Nonempty (Fin n)] in
@[simp] lemma toMatrix_apply_diag (H : Hamiltonian n) (i : Fin n) :
    H.toMatrix i i = H.energy i := by
  simp [toMatrix]

/-- Gibbs weights `pᵢ(β) = exp(-β Eᵢ)/Z(β)`. -/
noncomputable def gibbsWeight (H : Hamiltonian n) (β : ℝ) : Fin n → ℝ :=
  InfoGeometry.MaxEnt.gibbs H.energy β

/-- Partition function `Z(β)`. -/
noncomputable def partition (H : Hamiltonian n) (β : ℝ) : ℝ :=
  InfoGeometry.MaxEnt.partition H.energy β

/-- Log-partition `log Z(β)`. -/
noncomputable def logPartition (H : Hamiltonian n) (β : ℝ) : ℝ :=
  InfoGeometry.MaxEnt.logPartition H.energy β

lemma partition_pos (H : Hamiltonian n) (β : ℝ) : 0 < H.partition β := by
  simpa [partition] using InfoGeometry.MaxEnt.partition_pos (f := H.energy) (lam := β)

lemma partition_ne_zero (H : Hamiltonian n) (β : ℝ) : H.partition β ≠ 0 :=
  (H.partition_pos β).ne'

lemma gibbsWeight_pos (H : Hamiltonian n) (β : ℝ) (i : Fin n) :
    0 < H.gibbsWeight β i := by
  simpa [gibbsWeight] using InfoGeometry.MaxEnt.gibbs_pos (f := H.energy) (lam := β) i

lemma gibbsWeight_nonneg (H : Hamiltonian n) (β : ℝ) (i : Fin n) :
    0 ≤ H.gibbsWeight β i :=
  (H.gibbsWeight_pos β i).le

lemma gibbsWeight_sum_one (H : Hamiltonian n) (β : ℝ) :
    ∑ i, H.gibbsWeight β i = 1 := by
  simpa [gibbsWeight] using InfoGeometry.MaxEnt.gibbs_sum_one (f := H.energy) (lam := β)

/-- Diagonal log-density coefficients:
`log pᵢ = -β Eᵢ - log Z(β)`. -/
noncomputable def logDensityCoeff (H : Hamiltonian n) (β : ℝ) : Fin n → ℝ :=
  fun i => -β * H.energy i - H.logPartition β

/-- Diagonal "modular Hamiltonian"/log-density observable. -/
noncomputable def logDensityObs (H : Hamiltonian n) (β : ℝ) : DiagonalObservable n :=
  ⟨H.logDensityCoeff β⟩

lemma gibbsWeight_eq_exp_logDensity (H : Hamiltonian n) (β : ℝ) (i : Fin n) :
    H.gibbsWeight β i = Real.exp (H.logDensityCoeff β i) := by
  unfold gibbsWeight logDensityCoeff logPartition
  simpa using
    (InfoGeometry.MaxEnt.gibbs_eq_exp_sub_logPartition (f := H.energy) (lam := β) (i := i))

/-- Gibbs density matrix `ρ_β = diag(pᵢ(β))`. -/
noncomputable def densityMatrix (H : Hamiltonian n) (β : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (H.gibbsWeight β)

omit [Nonempty (Fin n)] in
@[simp] lemma densityMatrix_apply_diag (H : Hamiltonian n) (β : ℝ) (i : Fin n) :
    H.densityMatrix β i i = H.gibbsWeight β i := by
  simp [densityMatrix]

omit [Nonempty (Fin n)] in
@[simp] lemma densityMatrix_apply_offdiag (H : Hamiltonian n) (β : ℝ) {i j : Fin n} (h : i ≠ j) :
    H.densityMatrix β i j = 0 := by
  simp [densityMatrix, h]

/-- Diagonal mass for `n×n` matrices (sum of diagonal entries). -/
noncomputable def diagonalMass (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, M i i

@[simp] lemma diagonalMass_densityMatrix (H : Hamiltonian n) (β : ℝ) :
    diagonalMass (n := n) (H.densityMatrix β) = 1 := by
  simp [diagonalMass, densityMatrix, gibbsWeight_sum_one]

/-- Thermal expectation functional on diagonal observables:
`ω_β(A) = ⟨ρ_β, A⟩ = ∑ᵢ pᵢ Aᵢ`. -/
noncomputable def thermalState (H : Hamiltonian n) (β : ℝ) (A : DiagonalObservable n) : ℝ :=
  ∑ i, H.gibbsWeight β i * A i

@[simp] lemma thermalState_one (H : Hamiltonian n) (β : ℝ) :
    H.thermalState β (1 : DiagonalObservable n) = 1 := by
  simpa [thermalState] using H.gibbsWeight_sum_one β

lemma thermalState_nonneg
    (H : Hamiltonian n) (β : ℝ) (A : DiagonalObservable n)
    (hA : ∀ i, 0 ≤ A i) :
    0 ≤ H.thermalState β A := by
  unfold thermalState
  exact Finset.sum_nonneg (by
    intro i hi
    exact mul_nonneg (H.gibbsWeight_nonneg β i) (hA i))

/-- Energy observable as a diagonal operator. -/
noncomputable def energyObs (H : Hamiltonian n) : DiagonalObservable n :=
  ⟨H.energy⟩

/-- Internal energy `U(β) = E_{ρ_β}[H]`. -/
noncomputable def internalEnergy (H : Hamiltonian n) (β : ℝ) : ℝ :=
  H.thermalState β H.energyObs

omit [Nonempty (Fin n)] in
lemma internalEnergy_eq_gibbsExpectation (H : Hamiltonian n) (β : ℝ) :
    H.internalEnergy β = InfoGeometry.MaxEnt.gibbsExpectation H.energy β := by
  rfl

/-- On the diagonal (commutative) subalgebra, modular conjugation is trivial. -/
def modularShift (_H : Hamiltonian n) (_β : ℝ) (A : DiagonalObservable n) : DiagonalObservable n := A

omit [Nonempty (Fin n)] in
@[simp] lemma modularShift_apply (H : Hamiltonian n) (β : ℝ) (A : DiagonalObservable n) (i : Fin n) :
    H.modularShift β A i = A i := rfl

omit [Nonempty (Fin n)] in
@[simp] lemma modularShift_zero (H : Hamiltonian n) (A : DiagonalObservable n) :
    H.modularShift 0 A = A := rfl

omit [Nonempty (Fin n)] in
@[simp] lemma modularShift_add (H : Hamiltonian n) (s t : ℝ) (A : DiagonalObservable n) :
    H.modularShift (s + t) A = H.modularShift s (H.modularShift t A) := rfl

omit [Nonempty (Fin n)] in
@[simp] lemma modularShift_mul (H : Hamiltonian n) (t : ℝ)
    (A B : DiagonalObservable n) :
    H.modularShift t (A * B) = H.modularShift t A * H.modularShift t B := rfl

omit [Nonempty (Fin n)] in
lemma thermalState_modularShift_invariant
    (H : Hamiltonian n) (β t : ℝ) (A : DiagonalObservable n) :
    H.thermalState β (H.modularShift t A) = H.thermalState β A := by
  simp [thermalState, modularShift]

/-- Diagonal KMS-like identity for the Gibbs functional. -/
def SatisfiesDiagonalKMS (H : Hamiltonian n) (β : ℝ) : Prop :=
  ∀ A B : DiagonalObservable n,
    H.thermalState β (A * H.modularShift β B)
      = H.thermalState β (B * A)

omit [Nonempty (Fin n)] in
theorem satisfiesDiagonalKMS (H : Hamiltonian n) (β : ℝ) :
    SatisfiesDiagonalKMS (n := n) H β := by
  unfold SatisfiesDiagonalKMS
  intro A B
  unfold thermalState modularShift
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_comm]

omit [Nonempty (Fin n)] in
/-- Matrix-level version of a diagonal observable expectation:
`diagMass(ρ_β diag(A)) = ω_β(A)`. -/
lemma thermalState_eq_diagonalMass_density_mul_diag
    (H : Hamiltonian n) (β : ℝ) (A : DiagonalObservable n) :
    H.thermalState β A = diagonalMass (n := n) (Matrix.diagonal (H.gibbsWeight β) * A.toMatrix) := by
  unfold thermalState diagonalMass DiagonalObservable.toMatrix
  simp

end Hamiltonian
end FiniteThermal

end InfoGeometry.Thermal
