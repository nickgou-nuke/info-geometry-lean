import InfoGeometry.Physics.ChiralCausalCone

/-!
# Cl(1,1) atom to chiral CAR basis bridge

This file welds the split Clifford `Cl(1,1)` atom to the concrete chiral
Pauli/CAR basis.  The bridge is deliberately finite and matrix-level: the two
split Clifford generators are represented by

`γ₊ = σ⁺ + σ⁻`, `γ₋ = σ⁺ - σ⁻`,

so `γ₊² = +1`, `γ₋² = -1`, and `γ₊γ₋ = -γ₋γ₊`.  Conversely the chiral CAR
operators are recovered by the light-cone formulas

`σ⁺ = 1/2 (γ₊ + γ₋)`, `σ⁻ = 1/2 (γ₊ - γ₋)`.

No analytic or universal-completion claim is made here; this is the finite
`M₂(ℂ)` Clifford/CAR atom used by the downstream TL and braid proofs.
-/

noncomputable section

namespace InfoGeometry.Physics.Cl11ChiralCARBridge

open Matrix
open InfoGeometry.Physics.ChiralCausalCone
open InfoGeometry.Physics.CPTAtom

/-- Matrix model of the positive split Clifford generator. -/
def gammaPosM : M2C := σPlus + σMinus

/-- Matrix model of the negative split Clifford generator. -/
def gammaNegM : M2C := σPlus - σMinus

/-- The positive split generator squares to `+1`. -/
@[simp] theorem gammaPosM_sq : gammaPosM * gammaPosM = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaPosM, σPlus, σMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The negative split generator squares to `-1`. -/
@[simp] theorem gammaNegM_sq : gammaNegM * gammaNegM = -(1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaNegM, σPlus, σMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix split generators anticommute. -/
theorem gammaPosM_mul_gammaNegM : gammaPosM * gammaNegM = -(gammaNegM * gammaPosM) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaPosM, gammaNegM, σPlus, σMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Clifford anticommutator of the split generators vanishes. -/
theorem gammaPosM_anticomm_gammaNegM :
    gammaPosM * gammaNegM + gammaNegM * gammaPosM = (0 : M2C) := by
  rw [gammaPosM_mul_gammaNegM]
  simp

/-! ## Identification with the concrete real CPT atom -/

@[simp] theorem gammaPosM_eq_complexifyCl11_eps :
    gammaPosM = complexifyCl11 CPTAtom.eps := by
  rw [complexifyCl11_eps]
  rfl

@[simp] theorem complexifyCl11_J_eq_neg_gammaNegM :
    complexifyCl11 CPTAtom.J = -gammaNegM := by
  rw [complexifyCl11_J]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaNegM, σPlus, σMinus, Matrix.neg_apply, Matrix.sub_apply]

@[simp] theorem gammaNegM_eq_neg_complexifyCl11_J :
    gammaNegM = -complexifyCl11 CPTAtom.J := by
  rw [complexifyCl11_J_eq_neg_gammaNegM]
  simp

@[simp] theorem complexifyCl11_CPT_eq_sigma3c :
    complexifyCl11 CPTAtom.CPT = σ3c :=
  complexifyCl11_CPT

/-- The chiral annihilation/CAR raising operator is the light-cone half-sum. -/
theorem sigmaPlus_from_cl11_matrix :
    σPlus = (1 / 2 : ℂ) • (gammaPosM + gammaNegM) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaPosM, gammaNegM, σPlus, σMinus, Matrix.smul_apply] <;> norm_num

/-- The chiral creation/CAR lowering operator is the light-cone half-difference. -/
theorem sigmaMinus_from_cl11_matrix :
    σMinus = (1 / 2 : ℂ) • (gammaPosM - gammaNegM) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaPosM, gammaNegM, σPlus, σMinus, Matrix.smul_apply] <;> norm_num

/-- The concrete CAR annihilator from `SplitCliffordAlgebras` is the same
light-cone half-sum of the matrix `Cl(1,1)` generators. -/
theorem carAnn_from_cl11_matrix :
    SplitClifford.carAnn = (1 / 2 : ℂ) • (gammaPosM + gammaNegM) := by
  rw [← σPlus_eq_carAnn, sigmaPlus_from_cl11_matrix]

/-- The concrete CAR creator from `SplitCliffordAlgebras` is the same light-cone
half-difference of the matrix `Cl(1,1)` generators. -/
theorem carCre_from_cl11_matrix :
    SplitClifford.carCre = (1 / 2 : ℂ) • (gammaPosM - gammaNegM) := by
  rw [← σMinus_eq_carCre, sigmaMinus_from_cl11_matrix]

/-- The chiral CAR pair is exactly the CAR pair recovered from the finite
matrix `Cl(1,1)` light-cone split. -/
def cl11ChiralCARPair : SplitClifford.CARPair M2C where
  ann := (1 / 2 : ℂ) • (gammaPosM + gammaNegM)
  cre := (1 / 2 : ℂ) • (gammaPosM - gammaNegM)
  ann_sq := by
    rw [← sigmaPlus_from_cl11_matrix]
    exact σPlus_sq
  cre_sq := by
    rw [← sigmaMinus_from_cl11_matrix]
    exact σMinus_sq
  anti := by
    rw [← sigmaPlus_from_cl11_matrix, ← sigmaMinus_from_cl11_matrix]
    simpa [SplitClifford.antiComm] using anti_σPlus_σMinus

/-- Projection of the bridge back to the already-used chiral CAR annihilator. -/
@[simp] theorem cl11ChiralCARPair_ann : cl11ChiralCARPair.ann = σPlus := by
  dsimp [cl11ChiralCARPair]
  exact sigmaPlus_from_cl11_matrix.symm

/-- Projection of the bridge back to the already-used chiral CAR creator. -/
@[simp] theorem cl11ChiralCARPair_cre : cl11ChiralCARPair.cre = σMinus := by
  dsimp [cl11ChiralCARPair]
  exact sigmaMinus_from_cl11_matrix.symm

/-- Capstone: the `Cl(1,1)` matrix atom recovers the chiral CAR basis. -/
theorem cl11_atom_recovers_chiral_CAR_basis :
    gammaPosM * gammaPosM = (1 : M2C) ∧
    gammaNegM * gammaNegM = -(1 : M2C) ∧
    gammaPosM * gammaNegM = -(gammaNegM * gammaPosM) ∧
    σPlus = (1 / 2 : ℂ) • (gammaPosM + gammaNegM) ∧
    σMinus = (1 / 2 : ℂ) • (gammaPosM - gammaNegM) ∧
    cl11ChiralCARPair.ann = σPlus ∧
    cl11ChiralCARPair.cre = σMinus := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gammaPosM_sq
  · exact gammaNegM_sq
  · exact gammaPosM_mul_gammaNegM
  · exact sigmaPlus_from_cl11_matrix
  · exact sigmaMinus_from_cl11_matrix
  · exact cl11ChiralCARPair_ann
  · exact cl11ChiralCARPair_cre

/-- Capstone weld: the concrete real `CPTAtom` complexifies to the same finite
`Cl(1,1)`/CAR bridge used by the chiral TL and braid layers. -/
theorem cpt_atom_matches_cl11_chiral_CAR_bridge :
    gammaPosM = complexifyCl11 CPTAtom.eps ∧
    gammaNegM = -complexifyCl11 CPTAtom.J ∧
    complexifyCl11 CPTAtom.CPT = σ3c ∧
    σPlus = (1/2 : ℂ) • (complexifyCl11 CPTAtom.eps - complexifyCl11 CPTAtom.J) ∧
    σMinus = (1/2 : ℂ) • (complexifyCl11 CPTAtom.eps + complexifyCl11 CPTAtom.J) ∧
    σPlus = SplitClifford.carAnn ∧
    σMinus = SplitClifford.carCre := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gammaPosM_eq_complexifyCl11_eps
  · exact gammaNegM_eq_neg_complexifyCl11_J
  · exact complexifyCl11_CPT
  · exact σPlus_from_cl11
  · exact σMinus_from_cl11
  · exact σPlus_eq_carAnn
  · exact σMinus_eq_carCre


end InfoGeometry.Physics.Cl11ChiralCARBridge
