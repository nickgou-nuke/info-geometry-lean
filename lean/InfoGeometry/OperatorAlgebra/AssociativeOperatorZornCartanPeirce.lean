import InfoGeometry.Physics.OperatorZornMatrixAlgebra

/-!
# Cartan and Peirce calculus for the associative operator-Zorn shell

`InfoGeometry.Physics.OperatorZornMatrix A` is the transported associative
algebra `Matrix (Fin 2) (Fin 2) A`.  This file installs the intrinsic sheet
idempotents, the Cartan grading involution, the four Peirce corners, and the
sheet exchange.  These are ordinary ring theorems over a possibly
noncommutative coefficient ring.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

open InfoGeometry.Physics
open InfoGeometry.Physics.OperatorZornMatrix

variable {A : Type*} [Ring A] [StarRing A]

abbrev ZornBlock (A : Type*) [Ring A] [StarRing A] :=
  InfoGeometry.Physics.OperatorZornMatrix A

@[ext] theorem zornBlock_ext {X Y : ZornBlock A}
    (hplus : X.n_plus_op = Y.n_plus_op)
    (hminus : X.n_minus_op = Y.n_minus_op)
    (hsp : X.sigma_plus_op = Y.sigma_plus_op)
    (hsm : X.sigma_minus_op = Y.sigma_minus_op) : X = Y := by
  cases X
  cases Y
  simp_all

/-- Positive diagonal Peirce idempotent. -/
def ePlus : ZornBlock A :=
  ⟨1, 0, 0, 0⟩

/-- Negative diagonal Peirce idempotent. -/
def eMinus : ZornBlock A :=
  ⟨0, 1, 0, 0⟩

/-- Cartan grading element `Gamma = diag(1,-1)`. -/
def grading : ZornBlock A :=
  ⟨1, -1, 0, 0⟩

/-- Sheet-exchange element. -/
def sheetExchange : ZornBlock A :=
  ⟨0, 0, 1, 1⟩

@[simp] theorem ePlus_sq :
    ePlus (A := A) * ePlus = ePlus := by
  apply zornBlock_ext <;> simp [ePlus]

@[simp] theorem eMinus_sq :
    eMinus (A := A) * eMinus = eMinus := by
  apply zornBlock_ext <;> simp [eMinus]

@[simp] theorem ePlus_mul_eMinus :
    ePlus (A := A) * eMinus = 0 := by
  apply zornBlock_ext <;> simp [ePlus, eMinus]

@[simp] theorem eMinus_mul_ePlus :
    eMinus (A := A) * ePlus = 0 := by
  apply zornBlock_ext <;> simp [ePlus, eMinus]

@[simp] theorem ePlus_add_eMinus :
    ePlus (A := A) + eMinus = 1 := by
  apply (equivMatrix (A := A)).injective
  rw [toMatrix_add, toMatrix_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ePlus, eMinus, toMatrix]

@[simp] theorem grading_sq :
    grading (A := A) * grading = 1 := by
  apply zornBlock_ext <;> simp [grading]

@[simp] theorem sheetExchange_sq :
    sheetExchange (A := A) * sheetExchange = 1 := by
  apply zornBlock_ext <;> simp [sheetExchange]

/-- Inner Cartan involution of the two-sheet block algebra. -/
def cartanInvolution (X : ZornBlock A) : ZornBlock A :=
  grading * X * grading

/-- Coordinate action: diagonal entries are even; off-diagonal entries are
odd. -/
theorem cartanInvolution_coordinates (X : ZornBlock A) :
    cartanInvolution X =
      (⟨X.n_plus_op, X.n_minus_op,
        -X.sigma_plus_op, -X.sigma_minus_op⟩ : ZornBlock A) := by
  apply zornBlock_ext <;> simp [cartanInvolution, grading]

@[simp] theorem cartanInvolution_involutive (X : ZornBlock A) :
    cartanInvolution (cartanInvolution X) = X := by
  rw [cartanInvolution_coordinates, cartanInvolution_coordinates]
  cases X
  simp

/-- The Cartan involution is multiplicative. -/
theorem cartanInvolution_mul (X Y : ZornBlock A) :
    cartanInvolution (X * Y) =
      cartanInvolution X * cartanInvolution Y := by
  unfold cartanInvolution
  noncomm_ring [grading_sq (A := A)]

/-- Matrix commutator in the associative shell. -/
def commutator (X Y : ZornBlock A) : ZornBlock A :=
  X * Y - Y * X

/-- The Cartan involution preserves commutators. -/
theorem cartanInvolution_commutator (X Y : ZornBlock A) :
    cartanInvolution (commutator X Y) =
      commutator (cartanInvolution X) (cartanInvolution Y) := by
  unfold commutator cartanInvolution
  rw [mul_sub, sub_mul]
  rw [cartanInvolution_mul, cartanInvolution_mul]

/-- Even Cartan sector. -/
def IsEven (X : ZornBlock A) : Prop :=
  cartanInvolution X = X

/-- Odd Cartan sector. -/
def IsOdd (X : ZornBlock A) : Prop :=
  cartanInvolution X = -X

/-- Even-even commutators remain even. -/
theorem commutator_even_even {X Y : ZornBlock A}
    (hX : IsEven X) (hY : IsEven Y) :
    IsEven (commutator X Y) := by
  unfold IsEven at hX hY ⊢
  rw [cartanInvolution_commutator, hX, hY]

/-- Even-odd commutators are odd. -/
theorem commutator_even_odd {X Y : ZornBlock A}
    (hX : IsEven X) (hY : IsOdd Y) :
    IsOdd (commutator X Y) := by
  unfold IsEven at hX
  unfold IsOdd at hY ⊢
  rw [cartanInvolution_commutator, hX, hY]
  unfold commutator
  noncomm_ring

/-- Odd-even commutators are odd. -/
theorem commutator_odd_even {X Y : ZornBlock A}
    (hX : IsOdd X) (hY : IsEven Y) :
    IsOdd (commutator X Y) := by
  unfold IsOdd at hX ⊢
  unfold IsEven at hY
  rw [cartanInvolution_commutator, hX, hY]
  unfold commutator
  noncomm_ring

/-- Odd-odd commutators return to the even sector. -/
theorem commutator_odd_odd {X Y : ZornBlock A}
    (hX : IsOdd X) (hY : IsOdd Y) :
    IsEven (commutator X Y) := by
  unfold IsOdd at hX hY
  unfold IsEven
  rw [cartanInvolution_commutator, hX, hY]
  unfold commutator
  noncomm_ring

/-- Diagonal projection. -/
def diagonalPart (X : ZornBlock A) : ZornBlock A :=
  ⟨X.n_plus_op, X.n_minus_op, 0, 0⟩

/-- Off-diagonal projection. -/
def offDiagonalPart (X : ZornBlock A) : ZornBlock A :=
  ⟨0, 0, X.sigma_plus_op, X.sigma_minus_op⟩

/-- Exact even/odd reconstruction. -/
theorem diagonalPart_add_offDiagonalPart (X : ZornBlock A) :
    diagonalPart X + offDiagonalPart X = X := by
  apply (equivMatrix (A := A)).injective
  rw [toMatrix_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalPart, offDiagonalPart, toMatrix]

@[simp] theorem cartanInvolution_diagonalPart (X : ZornBlock A) :
    cartanInvolution (diagonalPart X) = diagonalPart X := by
  rw [cartanInvolution_coordinates]
  rfl

@[simp] theorem cartanInvolution_offDiagonalPart (X : ZornBlock A) :
    cartanInvolution (offDiagonalPart X) = -offDiagonalPart X := by
  apply zornBlock_ext <;>
    simp [cartanInvolution_coordinates, offDiagonalPart]

/-- Four Peirce corners. -/
def cornerPP (X : ZornBlock A) : ZornBlock A :=
  ePlus * X * ePlus

def cornerPM (X : ZornBlock A) : ZornBlock A :=
  ePlus * X * eMinus

def cornerMP (X : ZornBlock A) : ZornBlock A :=
  eMinus * X * ePlus

def cornerMM (X : ZornBlock A) : ZornBlock A :=
  eMinus * X * eMinus

@[simp] theorem cornerPP_coordinates (X : ZornBlock A) :
    cornerPP X = (⟨X.n_plus_op, 0, 0, 0⟩ : ZornBlock A) := by
  apply zornBlock_ext <;> simp [cornerPP, ePlus]

@[simp] theorem cornerPM_coordinates (X : ZornBlock A) :
    cornerPM X = (⟨0, 0, X.sigma_plus_op, 0⟩ : ZornBlock A) := by
  apply zornBlock_ext <;> simp [cornerPM, ePlus, eMinus]

@[simp] theorem cornerMP_coordinates (X : ZornBlock A) :
    cornerMP X = (⟨0, 0, 0, X.sigma_minus_op⟩ : ZornBlock A) := by
  apply zornBlock_ext <;> simp [cornerMP, ePlus, eMinus]

@[simp] theorem cornerMM_coordinates (X : ZornBlock A) :
    cornerMM X = (⟨0, X.n_minus_op, 0, 0⟩ : ZornBlock A) := by
  apply zornBlock_ext <;> simp [cornerMM, eMinus]

/-- Full Peirce decomposition of every associative operator-Zorn block. -/
theorem four_corner_decomposition (X : ZornBlock A) :
    cornerPP X + cornerPM X + cornerMP X + cornerMM X = X := by
  apply (equivMatrix (A := A)).injective
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cornerPP_coordinates, cornerPM_coordinates,
      cornerMP_coordinates, cornerMM_coordinates, toMatrix]

/-- Sheet exchange swaps all four matrix coordinates. -/
theorem sheetExchange_conjugates (X : ZornBlock A) :
    sheetExchange * X * sheetExchange =
      (⟨X.n_minus_op, X.n_plus_op,
        X.sigma_minus_op, X.sigma_plus_op⟩ : ZornBlock A) := by
  apply zornBlock_ext <;> simp [sheetExchange]

@[simp] theorem sheetExchange_conjugates_ePlus :
    sheetExchange (A := A) * ePlus * sheetExchange = eMinus := by
  rw [sheetExchange_conjugates]
  rfl

@[simp] theorem sheetExchange_conjugates_eMinus :
    sheetExchange (A := A) * eMinus * sheetExchange = ePlus := by
  rw [sheetExchange_conjugates]
  rfl

end InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
