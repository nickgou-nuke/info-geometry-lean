import InfoGeometry.Canonical.CelikCantorWittBasis
import InfoGeometry.Quantum.QutritPrimitiveWeyl

/-!
# Finite two-sheet / three-colour Weyl packet

This owner combines the already existing rank-one Witt matrices with the
canonical qutrit Weyl pair.  The tensor carrier is indexed by
`Fin 2 × Fin 3`; this is the native matrix form of the six-state space and
does not introduce a second tensor or colour carrier.

Only the commuting sheet--colour realization is bundled here.  In particular
no orientation-reversing colour reflection, semidirect-product claim, or group
order theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikCantorSheetColourWeyl

open InfoGeometry.Canonical.CelikCantorClifford
open InfoGeometry.Canonical.CelikCantorWittBasis
open InfoGeometry.Quantum.QutritBraidIncidenceBridge
open scoped Kronecker

local notation "ζ₃" => InfoGeometry.Topology.Parafermion.omega

abbrev SheetMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev ColourMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev SheetColourMatrix := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ

@[simp] theorem sheetColour_state_count :
    Fintype.card (Fin 2 × Fin 3) = 6 := by
  simp

/-! ## Reusable tensor normalization -/

abbrev tensor {m n : Type*} (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    Matrix (m × n) (m × n) ℂ := Matrix.kronecker A B

theorem tensor_mul {m n : Type*} [Fintype m] [Fintype n]
    (A C : Matrix m m ℂ) (B D : Matrix n n ℂ) :
    tensor A B * tensor C D = tensor (A * C) (B * D) := by
  exact (Matrix.mul_kronecker_mul A C B D).symm

@[simp] theorem tensor_one_one {m n : Type*} [DecidableEq m] [DecidableEq n] :
    tensor (1 : Matrix m m ℂ) (1 : Matrix n n ℂ) = 1 := by
  simp [tensor]

@[simp] theorem tensor_one_mul {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (B D : Matrix n n ℂ) :
    tensor (1 : Matrix m m ℂ) B * tensor (1 : Matrix m m ℂ) D =
      tensor (1 : Matrix m m ℂ) (B * D) := by
  rw [tensor_mul]
  simp

@[simp] theorem tensor_mul_one {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A C : Matrix m m ℂ) :
    tensor A (1 : Matrix n n ℂ) * tensor C (1 : Matrix n n ℂ) =
      tensor (A * C) (1 : Matrix n n ℂ) := by
  rw [tensor_mul]
  simp

/-! ## The sheet packet -/

def sheetPlus : SheetMatrix := vacuumProjection
def sheetMinus : SheetMatrix := occupiedProjection
def sheetParity : SheetMatrix := U
def sheetFlip : SheetMatrix := V

@[simp] theorem sheetPlus_add_sheetMinus :
    sheetPlus + sheetMinus = 1 := by
  simpa [sheetPlus, sheetMinus] using vacuum_add_occupied

@[simp] theorem sheetPlus_mul_sheetMinus :
    sheetPlus * sheetMinus = 0 := by
  simpa [sheetPlus, sheetMinus] using vacuum_occupied_orthogonal

@[simp] theorem sheetMinus_mul_sheetPlus :
    sheetMinus * sheetPlus = 0 := by
  simpa [sheetPlus, sheetMinus] using occupied_vacuum_orthogonal

@[simp] theorem sheetParity_sq : sheetParity * sheetParity = (1 : SheetMatrix) := by
  simpa [sheetParity] using U_sq

@[simp] theorem sheetFlip_sq : sheetFlip * sheetFlip = (1 : SheetMatrix) := by
  simpa [sheetFlip] using V_sq

theorem sheetFlip_conj_parity :
    sheetFlip * sheetParity * sheetFlip = -(sheetParity : SheetMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetParity, V, U, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetFlip_conj_plus :
    sheetFlip * sheetPlus * sheetFlip = sheetMinus := by
  rw [sheetPlus, sheetMinus, sheetFlip, V]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-! ## The colour packet -/

abbrev colourShift : ColourMatrix := qutritGeneralizedPauliX
abbrev colourClock : ColourMatrix := qutritPrimitiveClock

@[simp] theorem colourShift_cube :
    colourShift * colourShift * colourShift = (1 : ColourMatrix) := by
  simpa [colourShift] using qutritGeneralizedPauliX_cube_identity

@[simp] theorem colourClock_cube :
    colourClock * colourClock * colourClock = (1 : ColourMatrix) := by
  simpa only [colourClock, pow_three, mul_assoc] using qutritPrimitiveClock_cube

theorem colourClock_mul_shift :
    colourClock * colourShift = ζ₃ • (colourShift * colourClock) := by
  simpa [colourClock, colourShift] using qutritPrimitiveClock_mul_X

@[simp] theorem omega_mul_omega_mul_omega :
    ζ₃ * ζ₃ * ζ₃ = (1 : ℂ) := by
  calc
    ζ₃ * ζ₃ * ζ₃ = ζ₃ ^ 3 := by ring
    _ = 1 := InfoGeometry.Topology.Parafermion.omega_cube_eq_one

@[simp] theorem omega_sq_cubed :
    (ζ₃ * ζ₃) ^ 3 = (1 : ℂ) := by
  rw [← pow_two]
  rw [← pow_mul, show 2 * 3 = 3 * 2 by ring, pow_mul,
    InfoGeometry.Topology.Parafermion.omega_cube_eq_one]
  norm_num

@[simp] theorem omega_mul_omega_sq :
    ζ₃ * (ζ₃ * ζ₃) = (1 : ℂ) := by
  calc
    ζ₃ * (ζ₃ * ζ₃) = ζ₃ ^ 3 := by ring
    _ = 1 := InfoGeometry.Topology.Parafermion.omega_cube_eq_one

@[simp] theorem omega_sq_mul_omega :
    (ζ₃ * ζ₃) * ζ₃ = (1 : ℂ) := by
  calc
    (ζ₃ * ζ₃) * ζ₃ = ζ₃ ^ 3 := by ring
    _ = 1 := InfoGeometry.Topology.Parafermion.omega_cube_eq_one

@[simp] theorem colourRoot_square_cube :
    (ζ₃ ^ 2) ^ 3 = (1 : ℂ) := by
  rw [← pow_mul, show 2 * 3 = 3 * 2 by ring, pow_mul,
    InfoGeometry.Topology.Parafermion.omega_cube_eq_one]
  norm_num

/-! ## The commuting six-state realization -/

def sheetLift (A : SheetMatrix) : SheetColourMatrix := tensor A (1 : ColourMatrix)
def colourLift (B : ColourMatrix) : SheetColourMatrix := tensor (1 : SheetMatrix) B

abbrev liftedParity : SheetColourMatrix := sheetLift sheetParity
abbrev liftedSheetFlip : SheetColourMatrix := sheetLift sheetFlip
abbrev liftedSheetPlus : SheetColourMatrix := sheetLift sheetPlus
abbrev liftedSheetMinus : SheetColourMatrix := sheetLift sheetMinus
abbrev liftedColourShift : SheetColourMatrix := colourLift colourShift
abbrev liftedColourClock : SheetColourMatrix := colourLift colourClock

@[simp] theorem liftedParity_sq :
    liftedParity * liftedParity = (1 : SheetColourMatrix) := by
  rw [liftedParity, sheetLift, tensor_mul]
  simp [sheetParity_sq]

@[simp] theorem liftedSheetFlip_sq :
    liftedSheetFlip * liftedSheetFlip = (1 : SheetColourMatrix) := by
  rw [liftedSheetFlip, sheetLift, tensor_mul]
  simp [sheetFlip_sq]

theorem liftedSheetFlip_conj_parity :
    liftedSheetFlip * liftedParity * liftedSheetFlip = -liftedParity := by
  rw [liftedSheetFlip, liftedParity]
  simp only [sheetLift]
  rw [
    tensor_mul, tensor_mul]
  rw [sheetFlip_conj_parity]
  ext i j
  simp [tensor, Matrix.kroneckerMap_apply]

theorem liftedSheetFlip_conj_plus :
    liftedSheetFlip * liftedSheetPlus * liftedSheetFlip = liftedSheetMinus := by
  rw [liftedSheetFlip, liftedSheetPlus, liftedSheetMinus]
  simp only [sheetLift]
  rw [
    tensor_mul, tensor_mul]
  simp [sheetFlip_conj_plus]

@[simp] theorem liftedColourShift_cube :
    liftedColourShift * liftedColourShift * liftedColourShift =
      (1 : SheetColourMatrix) := by
  rw [liftedColourShift, colourLift, tensor_mul, tensor_mul]
  simp [colourShift_cube]

@[simp] theorem liftedColourClock_cube :
    liftedColourClock * liftedColourClock * liftedColourClock =
      (1 : SheetColourMatrix) := by
  rw [liftedColourClock, colourLift, tensor_mul, tensor_mul]
  simp [colourClock_cube]

theorem liftedColourClock_mul_shift :
    liftedColourClock * liftedColourShift =
      ζ₃ • (liftedColourShift * liftedColourClock) := by
  change ((1 : SheetMatrix) ⊗ₖ colourClock) * ((1 : SheetMatrix) ⊗ₖ colourShift) =
    ζ₃ • (((1 : SheetMatrix) ⊗ₖ colourShift) * ((1 : SheetMatrix) ⊗ₖ colourClock))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    colourClock_mul_shift, Matrix.kronecker_smul]

theorem liftedParity_comm_colourShift :
    liftedParity * liftedColourShift = liftedColourShift * liftedParity := by
  rw [liftedParity, liftedColourShift, sheetLift, colourLift,
    tensor_mul, tensor_mul]
  simp

theorem liftedParity_comm_colourClock :
    liftedParity * liftedColourClock = liftedColourClock * liftedParity := by
  rw [liftedParity, liftedColourClock, sheetLift, colourLift,
    tensor_mul, tensor_mul]
  simp

theorem liftedSheetFlip_comm_colourShift :
    liftedSheetFlip * liftedColourShift = liftedColourShift * liftedSheetFlip := by
  rw [liftedSheetFlip, liftedColourShift, sheetLift, colourLift,
    tensor_mul, tensor_mul]
  simp

theorem liftedSheetFlip_comm_colourClock :
    liftedSheetFlip * liftedColourClock = liftedColourClock * liftedSheetFlip := by
  rw [liftedSheetFlip, liftedColourClock, sheetLift, colourLift,
    tensor_mul, tensor_mul]
  simp

theorem commuting_sheet_colour_packet :
    liftedParity * liftedParity = 1 ∧
      liftedSheetFlip * liftedSheetFlip = 1 ∧
      liftedColourShift * liftedColourShift * liftedColourShift = 1 ∧
      liftedColourClock * liftedColourClock * liftedColourClock = 1 ∧
      liftedColourClock * liftedColourShift =
        ζ₃ • (liftedColourShift * liftedColourClock) ∧
      liftedParity * liftedColourShift = liftedColourShift * liftedParity ∧
      liftedParity * liftedColourClock = liftedColourClock * liftedParity ∧
      liftedSheetFlip * liftedColourShift = liftedColourShift * liftedSheetFlip ∧
      liftedSheetFlip * liftedColourClock = liftedColourClock * liftedSheetFlip := by
  exact ⟨liftedParity_sq, liftedSheetFlip_sq, liftedColourShift_cube,
    liftedColourClock_cube, liftedColourClock_mul_shift,
    liftedParity_comm_colourShift, liftedParity_comm_colourClock,
    liftedSheetFlip_comm_colourShift, liftedSheetFlip_comm_colourClock⟩

end InfoGeometry.Canonical.CelikCantorSheetColourWeyl
