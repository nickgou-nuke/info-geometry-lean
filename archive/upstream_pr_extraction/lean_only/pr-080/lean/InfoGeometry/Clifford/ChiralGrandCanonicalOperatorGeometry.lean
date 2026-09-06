import InfoGeometry.Clifford.ChiralLorentzFockQuadratic

/-!
# Grand-canonical geometry in the native noncommutative CAR operator algebra

This file keeps the CAR algebra fixed and changes only the operator generator.
The two sheet number operators are genuine quadratic operators in the native
split `Cl(4,4)` Clifford algebra.  No diagonal or commutative replacement is
used.
-/

noncomputable section

namespace InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford.ChiralLorentzCARLift
open InfoGeometry.Clifford.ChiralLorentzFockQuadratic

abbrev Operator := Cl44

/-- A two-sheet matrix with native Clifford operators as entries. -/
abbrev SheetOperatorMatrix := Matrix (Fin 2) (Fin 2) Operator

/-- A two-sheet operator column.  This is the noncommutative projective carrier;
we do not divide by an operator-valued denominator. -/
abbrev SheetOperatorPair := Fin 2 → Operator

def sheetOperatorAction (G : SheetOperatorMatrix) (ψ : SheetOperatorPair) :
    SheetOperatorPair := G.mulVec ψ

theorem sheetOperatorAction_mul (G H : SheetOperatorMatrix)
    (ψ : SheetOperatorPair) :
    sheetOperatorAction (G * H) ψ =
      sheetOperatorAction G (sheetOperatorAction H ψ) := by
  exact (Matrix.mulVec_mulVec ψ G H).symm

theorem sheetOperatorAction_one (ψ : SheetOperatorPair) :
    sheetOperatorAction (1 : SheetOperatorMatrix) ψ = ψ := by
  exact Matrix.one_mulVec ψ

theorem sheetOperatorAction_add (G H : SheetOperatorMatrix)
    (ψ : SheetOperatorPair) :
    sheetOperatorAction (G + H) ψ =
      sheetOperatorAction G ψ + sheetOperatorAction H ψ := by
  ext i
  simp [sheetOperatorAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  noncomm_ring

def sheetOperatorUnitAction (G : SheetOperatorMatrixˣ)
    (ψ : SheetOperatorPair) : SheetOperatorPair :=
  sheetOperatorAction (G : SheetOperatorMatrix) ψ

theorem sheetOperatorUnitAction_inverse (G : SheetOperatorMatrixˣ)
    (ψ : SheetOperatorPair) :
    sheetOperatorUnitAction G⁻¹ (sheetOperatorUnitAction G ψ) = ψ := by
  unfold sheetOperatorUnitAction
  rw [← sheetOperatorAction_mul]
  have h : (↑(G⁻¹) : SheetOperatorMatrix) *
      (↑G : SheetOperatorMatrix) = 1 := Units.inv_mul G
  rw [h]
  exact sheetOperatorAction_one ψ

theorem sheetOperatorUnitAction_mul (G H : SheetOperatorMatrixˣ)
    (ψ : SheetOperatorPair) :
    sheetOperatorUnitAction (G * H) ψ =
      sheetOperatorUnitAction G (sheetOperatorUnitAction H ψ) := by
  unfold sheetOperatorUnitAction
  exact sheetOperatorAction_mul (G : SheetOperatorMatrix)
    (H : SheetOperatorMatrix) ψ

/-- Inner automorphism of the two-sheet operator algebra. -/
def sheetAdjoint (U : SheetOperatorMatrixˣ) (A : SheetOperatorMatrix) :
    SheetOperatorMatrix :=
  (U : SheetOperatorMatrix) * A * (↑(U⁻¹) : SheetOperatorMatrix)

theorem sheetAdjoint_one (A : SheetOperatorMatrix) :
    sheetAdjoint (1 : SheetOperatorMatrixˣ) A = A := by
  simp [sheetAdjoint]

theorem sheetAdjoint_one_of (U : SheetOperatorMatrixˣ) :
    sheetAdjoint U (1 : SheetOperatorMatrix) = 1 := by
  unfold sheetAdjoint
  rw [mul_one, Units.mul_inv]

theorem sheetAdjoint_mul (U : SheetOperatorMatrixˣ)
    (A B : SheetOperatorMatrix) :
    sheetAdjoint U (A * B) = sheetAdjoint U A * sheetAdjoint U B := by
  simp only [sheetAdjoint, ← mul_assoc]
  rw [mul_assoc ((U : SheetOperatorMatrix) * A)
      (↑(U⁻¹) : SheetOperatorMatrix) (U : SheetOperatorMatrix)]
  rw [show (↑(U⁻¹) : SheetOperatorMatrix) * (U : SheetOperatorMatrix) = 1
      from Units.inv_mul U]
  rw [mul_one]

theorem sheetAdjoint_comp (U V : SheetOperatorMatrixˣ)
    (A : SheetOperatorMatrix) :
    sheetAdjoint (U * V) A =
      sheetAdjoint U (sheetAdjoint V A) := by
  simp only [sheetAdjoint, Units.val_mul]
  noncomm_ring

theorem sheetAdjoint_add (U : SheetOperatorMatrixˣ)
    (A B : SheetOperatorMatrix) :
    sheetAdjoint U (A + B) = sheetAdjoint U A + sheetAdjoint U B := by
  unfold sheetAdjoint
  rw [mul_add, add_mul]

theorem sheetAdjoint_smul (U : SheetOperatorMatrixˣ)
    (r : ℝ) (A : SheetOperatorMatrix) :
    sheetAdjoint U (r • A) = r • sheetAdjoint U A := by
  unfold sheetAdjoint
  simp only [Algebra.smul_def]
  have hU : algebraMap ℝ SheetOperatorMatrix r * (U : SheetOperatorMatrix) =
      (U : SheetOperatorMatrix) * algebraMap ℝ SheetOperatorMatrix r :=
    Algebra.commutes r (U : SheetOperatorMatrix)
  have hUi : algebraMap ℝ SheetOperatorMatrix r *
      (↑(U⁻¹) : SheetOperatorMatrix) =
      (↑(U⁻¹) : SheetOperatorMatrix) * algebraMap ℝ SheetOperatorMatrix r :=
    Algebra.commutes r (↑(U⁻¹) : SheetOperatorMatrix)
  calc
    (U : SheetOperatorMatrix) *
          (algebraMap ℝ SheetOperatorMatrix r * A) *
            (↑(U⁻¹) : SheetOperatorMatrix) =
        ((U : SheetOperatorMatrix) * algebraMap ℝ SheetOperatorMatrix r) * A *
          (↑(U⁻¹) : SheetOperatorMatrix) := by
            simp only [mul_assoc]
    _ = (algebraMap ℝ SheetOperatorMatrix r * (U : SheetOperatorMatrix)) * A *
          (↑(U⁻¹) : SheetOperatorMatrix) := by rw [← hU]
    _ = algebraMap ℝ SheetOperatorMatrix r *
          ((U : SheetOperatorMatrix) * A * (↑(U⁻¹) : SheetOperatorMatrix)) := by
            simp only [mul_assoc]

theorem sheetAdjoint_sub (U : SheetOperatorMatrixˣ)
    (A B : SheetOperatorMatrix) :
    sheetAdjoint U (A - B) = sheetAdjoint U A - sheetAdjoint U B := by
  unfold sheetAdjoint
  rw [mul_sub, sub_mul]

/-- The sheet inner action is a genuine ring automorphism of the native
two-sheet operator algebra. -/
def sheetAdjointRingEquiv (U : SheetOperatorMatrixˣ) :
    SheetOperatorMatrix ≃+* SheetOperatorMatrix where
  toFun := sheetAdjoint U
  invFun := sheetAdjoint U⁻¹
  left_inv := by
    intro A
    change (↑(U⁻¹) : SheetOperatorMatrix) *
        ((U : SheetOperatorMatrix) * A * (↑(U⁻¹) : SheetOperatorMatrix)) *
          (U : SheetOperatorMatrix) = A
    calc
      (↑(U⁻¹) : SheetOperatorMatrix) *
          ((U : SheetOperatorMatrix) * A * (↑(U⁻¹) : SheetOperatorMatrix)) *
            (U : SheetOperatorMatrix) =
          ((↑(U⁻¹) : SheetOperatorMatrix) * (U : SheetOperatorMatrix)) * A *
            ((↑(U⁻¹) : SheetOperatorMatrix) * (U : SheetOperatorMatrix)) := by
              noncomm_ring
      _ = A := by
            rw [Units.inv_mul U]
            simp
  right_inv := by
    intro A
    change (U : SheetOperatorMatrix) *
        ((↑(U⁻¹) : SheetOperatorMatrix) * A * (U : SheetOperatorMatrix)) *
          (↑(U⁻¹) : SheetOperatorMatrix) = A
    calc
      (U : SheetOperatorMatrix) *
          ((↑(U⁻¹) : SheetOperatorMatrix) * A * (U : SheetOperatorMatrix)) *
            (↑(U⁻¹) : SheetOperatorMatrix) =
          ((U : SheetOperatorMatrix) * (↑(U⁻¹) : SheetOperatorMatrix)) * A *
            ((U : SheetOperatorMatrix) * (↑(U⁻¹) : SheetOperatorMatrix)) := by
              noncomm_ring
      _ = A := by
            rw [Units.mul_inv U]
            simp
  map_add' := sheetAdjoint_add U
  map_mul' := sheetAdjoint_mul U

@[simp] theorem sheetAdjointRingEquiv_apply
    (U : SheetOperatorMatrixˣ) (A : SheetOperatorMatrix) :
    sheetAdjointRingEquiv U A = sheetAdjoint U A := rfl

theorem sheetAdjointRingEquiv_mul (U V : SheetOperatorMatrixˣ) :
    sheetAdjointRingEquiv (U * V) =
      (sheetAdjointRingEquiv V).trans (sheetAdjointRingEquiv U) := by
  apply RingEquiv.ext
  intro A
  simpa [sheetAdjointRingEquiv] using sheetAdjoint_comp U V A

/-- Native parity and sheet-exchange matrices with Clifford-operator entries. -/
def sheetParity : SheetOperatorMatrix :=
  !![(1 : Operator), 0; 0, -1]

def sheetExchange : SheetOperatorMatrix :=
  !![(0 : Operator), 1; 1, 0]

theorem sheetParity_sq : sheetParity * sheetParity = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetParity_pow_two_mul (n : ℕ) :
    sheetParity ^ (2 * n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, pow_add, ih, pow_two, sheetParity_sq, one_mul]

theorem sheetParity_pow_two_mul_add_one (n : ℕ) :
    sheetParity ^ (2 * n + 1) = sheetParity := by
  rw [pow_succ, sheetParity_pow_two_mul, one_mul]

theorem sheetExchange_sq : sheetExchange * sheetExchange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetExchange, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two parity projectors on the native sheet operator carrier. -/
def sheetProjectorPlus : SheetOperatorMatrix :=
  (1 / 2 : ℝ) • ((1 : SheetOperatorMatrix) + sheetParity)

def sheetProjectorMinus : SheetOperatorMatrix :=
  (1 / 2 : ℝ) • ((1 : SheetOperatorMatrix) - sheetParity)

theorem sheetProjectorPlus_sq :
    sheetProjectorPlus * sheetProjectorPlus = sheetProjectorPlus := by
  unfold sheetProjectorPlus
  rw [smul_mul_assoc, mul_smul_comm]
  rw [smul_smul]
  norm_num
  simp only [one_mul, mul_one, add_mul, mul_add]
  rw [sheetParity_sq]
  module

theorem sheetProjectorMinus_sq :
    sheetProjectorMinus * sheetProjectorMinus = sheetProjectorMinus := by
  unfold sheetProjectorMinus
  rw [smul_mul_assoc, mul_smul_comm]
  rw [smul_smul]
  norm_num
  simp only [one_mul, mul_one, sub_mul, mul_sub]
  rw [sheetParity_sq]
  module

theorem sheetProjectors_add :
    sheetProjectorPlus + sheetProjectorMinus = 1 := by
  unfold sheetProjectorPlus sheetProjectorMinus
  module

theorem sheetProjectors_mul :
    sheetProjectorPlus * sheetProjectorMinus = 0 := by
  unfold sheetProjectorPlus sheetProjectorMinus
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num
  simp only [one_mul, mul_one, add_mul, mul_sub]
  rw [sheetParity_sq]
  module

theorem sheetProjectors_mul_reverse :
    sheetProjectorMinus * sheetProjectorPlus = 0 := by
  unfold sheetProjectorPlus sheetProjectorMinus
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num
  simp only [one_mul, mul_one, sub_mul, mul_add]
  rw [sheetParity_sq]
  module

theorem sheetParity_mul_projectorPlus :
    sheetParity * sheetProjectorPlus = sheetProjectorPlus := by
  unfold sheetProjectorPlus
  rw [mul_smul_comm]
  simp only [mul_add, sheetParity_sq, mul_one]
  module

theorem sheetParity_mul_projectorMinus :
    sheetParity * sheetProjectorMinus = -sheetProjectorMinus := by
  unfold sheetProjectorMinus
  rw [mul_smul_comm]
  simp only [mul_sub, sheetParity_sq, mul_one]
  module

theorem sheetProjectorPlus_mul_sheetParity :
    sheetProjectorPlus * sheetParity = sheetProjectorPlus := by
  unfold sheetProjectorPlus
  rw [smul_mul_assoc]
  simp only [add_mul, sheetParity_sq, one_mul]
  module

theorem sheetProjectorMinus_mul_sheetParity :
    sheetProjectorMinus * sheetParity = -sheetProjectorMinus := by
  unfold sheetProjectorMinus
  rw [smul_mul_assoc]
  simp only [sub_mul, sheetParity_sq, one_mul]
  module

theorem sheetProjector_decomposition (A : SheetOperatorMatrix) :
    A = sheetProjectorPlus * A * sheetProjectorPlus +
        sheetProjectorPlus * A * sheetProjectorMinus +
        sheetProjectorMinus * A * sheetProjectorPlus +
        sheetProjectorMinus * A * sheetProjectorMinus := by
  have hsum : sheetProjectorPlus + sheetProjectorMinus =
      (1 : SheetOperatorMatrix) := sheetProjectors_add
  calc
    A = (sheetProjectorPlus + sheetProjectorMinus) * A *
          (sheetProjectorPlus + sheetProjectorMinus) := by
            rw [hsum, one_mul, mul_one]
    _ = sheetProjectorPlus * A * sheetProjectorPlus +
          sheetProjectorPlus * A * sheetProjectorMinus +
          sheetProjectorMinus * A * sheetProjectorPlus +
          sheetProjectorMinus * A * sheetProjectorMinus := by
            noncomm_ring

theorem sheetParity_exchange_anticomm :
    sheetParity * sheetExchange + sheetExchange * sheetParity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, sheetExchange]

def sheetEvenPart (A : SheetOperatorMatrix) : SheetOperatorMatrix :=
  A + sheetParity * A * sheetParity

def sheetOddPart (A : SheetOperatorMatrix) : SheetOperatorMatrix :=
  A - sheetParity * A * sheetParity

theorem sheetEvenPart_add_oddPart (A : SheetOperatorMatrix) :
    sheetEvenPart A + sheetOddPart A = (2 : ℤ) • A := by
  unfold sheetEvenPart sheetOddPart
  module

theorem sheetParity_mul_evenPart_eq_evenPart_mul_sheetParity
    (A : SheetOperatorMatrix) :
    sheetParity * sheetEvenPart A =
      sheetEvenPart A * sheetParity := by
  unfold sheetEvenPart
  calc
    sheetParity * (A + sheetParity * A * sheetParity) =
        sheetParity * A + A * sheetParity := by
          rw [mul_add]
          congr 1
          rw [← mul_assoc, ← mul_assoc sheetParity sheetParity A,
            sheetParity_sq, one_mul]
    _ = (A + sheetParity * A * sheetParity) * sheetParity := by
      rw [add_mul]
      have h : sheetParity * A * sheetParity * sheetParity =
          sheetParity * A := by
        rw [mul_assoc (sheetParity * A) sheetParity sheetParity,
          sheetParity_sq, mul_one]
      rw [h, add_comm]

theorem sheetParity_mul_oddPart_eq_neg_oddPart_mul_sheetParity
    (A : SheetOperatorMatrix) :
    sheetParity * sheetOddPart A =
      -(sheetOddPart A * sheetParity) := by
  unfold sheetOddPart
  calc
    sheetParity * (A - sheetParity * A * sheetParity) =
        sheetParity * A - A * sheetParity := by
          rw [mul_sub]
          congr 1
          rw [← mul_assoc, ← mul_assoc sheetParity sheetParity A,
            sheetParity_sq, one_mul]
    _ = -((A - sheetParity * A * sheetParity) * sheetParity) := by
      rw [sub_mul]
      have h : sheetParity * A * sheetParity * sheetParity =
          sheetParity * A := by
        rw [mul_assoc (sheetParity * A) sheetParity sheetParity,
          sheetParity_sq, mul_one]
      rw [h, neg_sub]

theorem sheetEvenPart_eq_of_commute (A : SheetOperatorMatrix)
    (hcomm : sheetParity * A = A * sheetParity) :
    sheetEvenPart A = (2 : ℝ) • A := by
  unfold sheetEvenPart
  rw [hcomm, mul_assoc A sheetParity sheetParity,
    sheetParity_sq, mul_one, two_smul]

theorem sheetOddPart_eq_zero_of_commute (A : SheetOperatorMatrix)
    (hcomm : sheetParity * A = A * sheetParity) :
    sheetOddPart A = 0 := by
  unfold sheetOddPart
  rw [hcomm, mul_assoc A sheetParity sheetParity,
    sheetParity_sq, mul_one, sub_self]

/-- A native sheet-off-diagonal supercharge with operator-valued entries. -/
def sheetSupercharge (qPlus qMinus : Operator) : SheetOperatorMatrix :=
  !![(0 : Operator), qPlus; qMinus, 0]

theorem sheetSupercharge_is_odd (qPlus qMinus : Operator) :
    sheetParity * sheetSupercharge qPlus qMinus +
        sheetSupercharge qPlus qMinus * sheetParity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, sheetSupercharge]

theorem sheetSupercharge_anticommutator_block
    (qPlus qMinus rPlus rMinus : Operator) :
    sheetSupercharge qPlus qMinus * sheetSupercharge rPlus rMinus +
        sheetSupercharge rPlus rMinus * sheetSupercharge qPlus qMinus =
      !![qPlus * rMinus + rPlus * qMinus, 0;
        0, qMinus * rPlus + rMinus * qPlus] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetSupercharge]

/-- The same native operator acts on both sheet diagonal blocks. -/
def sheetScalar (z : Operator) : SheetOperatorMatrix :=
  !![z, 0; 0, z]

theorem sheetSupercharge_anticommutator_eq_sheetScalar
    (qPlus qMinus rPlus rMinus z : Operator)
    (hPlus : qPlus * rMinus + rPlus * qMinus = z)
    (hMinus : qMinus * rPlus + rMinus * qPlus = z) :
    sheetSupercharge qPlus qMinus * sheetSupercharge rPlus rMinus +
        sheetSupercharge rPlus rMinus * sheetSupercharge qPlus qMinus =
      sheetScalar z := by
  rw [sheetSupercharge_anticommutator_block]
  simp [sheetScalar, hPlus, hMinus]

theorem sheetScalar_commutes
    (z : Operator) (hz : ∀ x : Operator, z * x = x * z)
    (A : SheetOperatorMatrix) :
    sheetScalar z * A = A * sheetScalar z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetScalar, Matrix.mul_apply, Fin.sum_univ_two, hz]

theorem sheetSupercharge_anticommutator_is_central
    (qPlus qMinus rPlus rMinus z : Operator)
    (hPlus : qPlus * rMinus + rPlus * qMinus = z)
    (hMinus : qMinus * rPlus + rMinus * qPlus = z)
    (hz : ∀ x : Operator, z * x = x * z) (A : SheetOperatorMatrix) :
    (sheetSupercharge qPlus qMinus * sheetSupercharge rPlus rMinus +
        sheetSupercharge rPlus rMinus * sheetSupercharge qPlus qMinus) * A =
      A * (sheetSupercharge qPlus qMinus * sheetSupercharge rPlus rMinus +
        sheetSupercharge rPlus rMinus * sheetSupercharge qPlus qMinus) := by
  rw [sheetSupercharge_anticommutator_eq_sheetScalar
    qPlus qMinus rPlus rMinus z hPlus hMinus]
  exact sheetScalar_commutes z hz A

theorem sheetSupercharge_anticommutator_is_even
    (Q R : SheetOperatorMatrix)
    (hQ : sheetParity * Q + Q * sheetParity = 0)
    (hR : sheetParity * R + R * sheetParity = 0) :
    sheetParity * (Q * R + R * Q) =
      (Q * R + R * Q) * sheetParity := by
  have hQ' : sheetParity * Q = -(Q * sheetParity) :=
    eq_neg_of_add_eq_zero_left hQ
  have hR' : sheetParity * R = -(R * sheetParity) :=
    eq_neg_of_add_eq_zero_left hR
  calc
    sheetParity * (Q * R + R * Q) =
        sheetParity * (Q * R) + sheetParity * (R * Q) := by
          rw [mul_add]
    _ =
        (sheetParity * Q) * R + (sheetParity * R) * Q := by
          noncomm_ring
    _ = (-(Q * sheetParity)) * R +
        (-(R * sheetParity)) * Q := by rw [hQ', hR']
    _ = (Q * R + R * Q) * sheetParity := by
          have hR'' : -(sheetParity * R) = R * sheetParity := by
            rw [hR']
            simp
          have hQ'' : -(sheetParity * Q) = Q * sheetParity := by
            rw [hQ']
            simp
          calc
            (-(Q * sheetParity)) * R + (-(R * sheetParity)) * Q =
                Q * (-(sheetParity * R)) +
                  R * (-(sheetParity * Q)) := by noncomm_ring
            _ = Q * (R * sheetParity) + R * (Q * sheetParity) := by
                  rw [hR'', hQ'']
            _ = (Q * R + R * Q) * sheetParity := by
                  rw [add_mul]
                  simp only [mul_assoc]

theorem sheetAdjoint_fixed_sheetParity (U : SheetOperatorMatrixˣ)
    (hU : (U : SheetOperatorMatrix) * sheetParity =
      sheetParity * (U : SheetOperatorMatrix)) :
    sheetAdjoint U sheetParity = sheetParity := by
  unfold sheetAdjoint
  rw [hU]
  rw [mul_assoc, Units.mul_inv]
  simp

theorem sheetAdjoint_fixed_sheetProjectorPlus
    (U : SheetOperatorMatrixˣ)
    (hU : (U : SheetOperatorMatrix) * sheetParity =
      sheetParity * (U : SheetOperatorMatrix)) :
    sheetAdjoint U sheetProjectorPlus = sheetProjectorPlus := by
  unfold sheetProjectorPlus
  rw [sheetAdjoint_smul, sheetAdjoint_add,
    sheetAdjoint_one_of, sheetAdjoint_fixed_sheetParity U hU]

theorem sheetAdjoint_fixed_sheetProjectorMinus
    (U : SheetOperatorMatrixˣ)
    (hU : (U : SheetOperatorMatrix) * sheetParity =
      sheetParity * (U : SheetOperatorMatrix)) :
    sheetAdjoint U sheetProjectorMinus = sheetProjectorMinus := by
  unfold sheetProjectorMinus
  rw [sheetAdjoint_smul, sheetAdjoint_sub,
    sheetAdjoint_one_of, sheetAdjoint_fixed_sheetParity U hU]

theorem sheetAdjoint_preserves_evenPart (U : SheetOperatorMatrixˣ)
    (A : SheetOperatorMatrix)
    (hU : (U : SheetOperatorMatrix) * sheetParity =
      sheetParity * (U : SheetOperatorMatrix)) :
    sheetEvenPart (sheetAdjoint U A) =
      sheetAdjoint U (sheetEvenPart A) := by
  unfold sheetEvenPart
  calc
    sheetAdjoint U A + sheetParity * sheetAdjoint U A * sheetParity =
        sheetAdjoint U A + sheetAdjoint U sheetParity *
          sheetAdjoint U A * sheetAdjoint U sheetParity := by
            rw [sheetAdjoint_fixed_sheetParity U hU]
    _ = sheetAdjoint U A + sheetAdjoint U
          (sheetParity * A * sheetParity) := by
            rw [sheetAdjoint_mul, sheetAdjoint_mul,
              sheetAdjoint_fixed_sheetParity U hU]
    _ = sheetAdjoint U (A + sheetParity * A * sheetParity) := by
            rw [sheetAdjoint_add]

theorem sheetAdjoint_preserves_odd
    (U : SheetOperatorMatrixˣ) (Q : SheetOperatorMatrix)
    (hU : (U : SheetOperatorMatrix) * sheetParity =
      sheetParity * (U : SheetOperatorMatrix))
    (hQ : sheetParity * Q + Q * sheetParity = 0) :
    sheetParity * sheetAdjoint U Q +
        sheetAdjoint U Q * sheetParity = 0 := by
  calc
    sheetParity * sheetAdjoint U Q + sheetAdjoint U Q * sheetParity =
        sheetAdjoint U sheetParity * sheetAdjoint U Q +
          sheetAdjoint U Q * sheetAdjoint U sheetParity := by
            rw [sheetAdjoint_fixed_sheetParity U hU]
    _ = sheetAdjoint U (sheetParity * Q + Q * sheetParity) := by
          symm
          rw [sheetAdjoint_add, sheetAdjoint_mul, sheetAdjoint_mul]
    _ = sheetAdjoint U 0 := by rw [hQ]
    _ = 0 := by simp only [sheetAdjoint, mul_zero, zero_mul]

/-- Number operator on the positive sheet mode. -/
def sheetNumberPlus : Operator := wittNumberOperator 0

/-- Number operator on the negative sheet mode. -/
def sheetNumberMinus : Operator := wittNumberOperator 1

/-- Number operators embedded into their respective sheet blocks. -/
def sheetNumberMatrixPlus : SheetOperatorMatrix :=
  !![sheetNumberPlus, 0; 0, 0]

def sheetNumberMatrixMinus : SheetOperatorMatrix :=
  !![0, 0; 0, sheetNumberMinus]

def sheetTotalNumberMatrix : SheetOperatorMatrix :=
  sheetNumberMatrixPlus + sheetNumberMatrixMinus

def sheetChiralChargeMatrix : SheetOperatorMatrix :=
  sheetNumberMatrixPlus - sheetNumberMatrixMinus

theorem sheetProjectorPlus_mul_sheetNumberMatrixPlus :
    sheetProjectorPlus * sheetNumberMatrixPlus =
      sheetNumberMatrixPlus := by
  unfold sheetProjectorPlus sheetNumberMatrixPlus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    simp only [Algebra.smul_def, mul_one]
    rw [← map_add]
    norm_num

theorem sheetProjectorMinus_mul_sheetNumberMatrixPlus :
    sheetProjectorMinus * sheetNumberMatrixPlus = 0 := by
  unfold sheetProjectorMinus sheetNumberMatrixPlus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetProjectorMinus_mul_sheetNumberMatrixMinus :
    sheetProjectorMinus * sheetNumberMatrixMinus =
      sheetNumberMatrixMinus := by
  unfold sheetProjectorMinus sheetNumberMatrixMinus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    simp only [Algebra.smul_def]
    rw [← mul_assoc]
    have htwo : (1 + 1 : Operator) = algebraMap ℝ Operator (2 : ℝ) := by
      norm_num [map_ofNat]
    rw [htwo, ← map_mul]
    norm_num

theorem sheetProjectorPlus_mul_sheetNumberMatrixMinus :
    sheetProjectorPlus * sheetNumberMatrixMinus = 0 := by
  unfold sheetProjectorPlus sheetNumberMatrixMinus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetNumberMatrixPlus_parity_commutes :
    sheetParity * sheetNumberMatrixPlus =
      sheetNumberMatrixPlus * sheetParity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, sheetNumberMatrixPlus]

theorem sheetNumberMatrixMinus_parity_commutes :
    sheetParity * sheetNumberMatrixMinus =
      sheetNumberMatrixMinus * sheetParity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, sheetNumberMatrixMinus]

theorem sheetTotalNumberMatrix_parity_commutes :
    sheetParity * sheetTotalNumberMatrix =
      sheetTotalNumberMatrix * sheetParity := by
  unfold sheetTotalNumberMatrix
  rw [mul_add, add_mul, sheetNumberMatrixPlus_parity_commutes,
    sheetNumberMatrixMinus_parity_commutes]

theorem sheetChiralChargeMatrix_parity_commutes :
    sheetParity * sheetChiralChargeMatrix =
      sheetChiralChargeMatrix * sheetParity := by
  unfold sheetChiralChargeMatrix
  rw [mul_sub, sub_mul, sheetNumberMatrixPlus_parity_commutes,
    sheetNumberMatrixMinus_parity_commutes]

def sheetGrandCanonicalGeneratorMatrix
    (H : SheetOperatorMatrix) (μ μχ : ℝ) : SheetOperatorMatrix :=
  H - μ • sheetTotalNumberMatrix - μχ • sheetChiralChargeMatrix

theorem sheetGrandCanonicalGeneratorMatrix_parity_commutes
    (H : SheetOperatorMatrix)
    (hH : sheetParity * H = H * sheetParity)
    (μ μχ : ℝ) :
    sheetParity * sheetGrandCanonicalGeneratorMatrix H μ μχ =
      sheetGrandCanonicalGeneratorMatrix H μ μχ * sheetParity := by
  unfold sheetGrandCanonicalGeneratorMatrix
  rw [mul_sub, sub_mul, mul_sub, sub_mul]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [sheetTotalNumberMatrix_parity_commutes,
    sheetChiralChargeMatrix_parity_commutes]
  rw [hH]

theorem sheetChemicalPotential_split (μplus μminus : ℝ) :
    ((μplus + μminus) / 2) • sheetTotalNumberMatrix +
        ((μplus - μminus) / 2) • sheetChiralChargeMatrix =
      μplus • sheetNumberMatrixPlus + μminus • sheetNumberMatrixMinus := by
  unfold sheetTotalNumberMatrix sheetChiralChargeMatrix
  module

theorem sheetGrandCanonicalGeneratorMatrix_sheet_form
    (H : SheetOperatorMatrix) (μplus μminus : ℝ) :
    sheetGrandCanonicalGeneratorMatrix H
        ((μplus + μminus) / 2) ((μplus - μminus) / 2) =
      H - μplus • sheetNumberMatrixPlus -
        μminus • sheetNumberMatrixMinus := by
  unfold sheetGrandCanonicalGeneratorMatrix
  rw [sub_sub, sub_sub, sheetChemicalPotential_split]

/-- Total occupation operator of the two selected sheet modes. -/
def totalNumber : Operator := sheetNumberPlus + sheetNumberMinus

/-- Chiral charge: positive-sheet occupation minus negative-sheet occupation. -/
def chiralCharge : Operator := sheetNumberPlus - sheetNumberMinus

/-- Grand-canonical operator with total and chiral chemical potentials. -/
def grandCanonicalGenerator (H : Operator) (μ μχ : ℝ) : Operator :=
  H - μ • totalNumber - μχ • chiralCharge

/-- Free two-sheet Hamiltonian built from the native quadratic number operators. -/
def freeSheetHamiltonian (Eplus Eminus : ℝ) : Operator :=
  Eplus • sheetNumberPlus + Eminus • sheetNumberMinus

/-- Grand-canonical free generator in the two native sheet sectors. -/
def freeGrandCanonicalGenerator
    (Eplus Eminus μplus μminus : ℝ) : Operator :=
  grandCanonicalGenerator (freeSheetHamiltonian Eplus Eminus)
    ((μplus + μminus) / 2) ((μplus - μminus) / 2)

theorem freeSheetHamiltonian_commutator_annihilation_plus
    (Eplus Eminus : ℝ) :
    algebraCommutator (freeSheetHamiltonian Eplus Eminus) (a 0) =
      -(Eplus • a 0) := by
  have hplus : algebraCommutator (sheetNumberPlus) (a 0) = -(a 0) := by
    simpa [sheetNumberPlus] using
      (quadraticWittGenerator_commutator_annihilation 0 0 0)
  have hminus : algebraCommutator (sheetNumberMinus) (a 0) = 0 := by
    simpa [sheetNumberMinus] using
      (quadraticWittGenerator_commutator_annihilation 1 1 0)
  have hplus' : sheetNumberPlus * a 0 - a 0 * sheetNumberPlus = -(a 0) := hplus
  have hminus' : sheetNumberMinus * a 0 - a 0 * sheetNumberMinus = 0 := hminus
  unfold freeSheetHamiltonian algebraCommutator
  calc
    (Eplus • sheetNumberPlus + Eminus • sheetNumberMinus) * a 0 -
          a 0 * (Eplus • sheetNumberPlus + Eminus • sheetNumberMinus) =
        ((Eplus • sheetNumberPlus) * a 0 -
            a 0 * (Eplus • sheetNumberPlus)) +
          ((Eminus • sheetNumberMinus) * a 0 -
            a 0 * (Eminus • sheetNumberMinus)) := by noncomm_ring
    _ = Eplus • (sheetNumberPlus * a 0 - a 0 * sheetNumberPlus) +
          Eminus • (sheetNumberMinus * a 0 - a 0 * sheetNumberMinus) := by
            rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
              mul_smul_comm]
            module
    _ = -(Eplus • a 0) := by
          rw [hplus', hminus']
          simp

theorem freeSheetHamiltonian_commutator_annihilation_minus
    (Eplus Eminus : ℝ) :
    algebraCommutator (freeSheetHamiltonian Eplus Eminus) (a 1) =
      -(Eminus • a 1) := by
  have hplus : algebraCommutator (sheetNumberPlus) (a 1) = 0 := by
    simpa [sheetNumberPlus] using
      (quadraticWittGenerator_commutator_annihilation 0 0 1)
  have hminus : algebraCommutator (sheetNumberMinus) (a 1) = -(a 1) := by
    simpa [sheetNumberMinus] using
      (quadraticWittGenerator_commutator_annihilation 1 1 1)
  have hplus' : sheetNumberPlus * a 1 - a 1 * sheetNumberPlus = 0 := hplus
  have hminus' : sheetNumberMinus * a 1 - a 1 * sheetNumberMinus = -(a 1) := hminus
  unfold freeSheetHamiltonian algebraCommutator
  calc
    (Eplus • sheetNumberPlus + Eminus • sheetNumberMinus) * a 1 -
          a 1 * (Eplus • sheetNumberPlus + Eminus • sheetNumberMinus) =
        ((Eplus • sheetNumberPlus) * a 1 -
            a 1 * (Eplus • sheetNumberPlus)) +
          ((Eminus • sheetNumberMinus) * a 1 -
            a 1 * (Eminus • sheetNumberMinus)) := by noncomm_ring
    _ = Eplus • (sheetNumberPlus * a 1 - a 1 * sheetNumberPlus) +
          Eminus • (sheetNumberMinus * a 1 - a 1 * sheetNumberMinus) := by
            rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
              mul_smul_comm]
            module
    _ = -(Eminus • a 1) := by
          rw [hplus', hminus']
          simp

theorem freeSheetHamiltonian_commutator_creation_plus
    (Eplus Eminus : ℝ) :
    algebraCommutator (freeSheetHamiltonian Eplus Eminus) (adag 0) =
      Eplus • adag 0 := by
  have hplus : algebraCommutator (sheetNumberPlus) (adag 0) = adag 0 := by
    simpa [sheetNumberPlus] using
      (quadraticWittGenerator_commutator_creation 0 0 0)
  have hminus : algebraCommutator (sheetNumberMinus) (adag 0) = 0 := by
    simpa [sheetNumberMinus] using
      (quadraticWittGenerator_commutator_creation 1 1 0)
  have hplus' : sheetNumberPlus * adag 0 - adag 0 * sheetNumberPlus = adag 0 := hplus
  have hminus' : sheetNumberMinus * adag 0 - adag 0 * sheetNumberMinus = 0 := hminus
  unfold freeSheetHamiltonian algebraCommutator
  calc
    (Eplus • sheetNumberPlus + Eminus • sheetNumberMinus) * adag 0 -
          adag 0 * (Eplus • sheetNumberPlus + Eminus • sheetNumberMinus) =
        ((Eplus • sheetNumberPlus) * adag 0 -
            adag 0 * (Eplus • sheetNumberPlus)) +
          ((Eminus • sheetNumberMinus) * adag 0 -
            adag 0 * (Eminus • sheetNumberMinus) ) := by noncomm_ring
    _ = Eplus • (sheetNumberPlus * adag 0 - adag 0 * sheetNumberPlus) +
          Eminus • (sheetNumberMinus * adag 0 - adag 0 * sheetNumberMinus) := by
            rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
              mul_smul_comm]
            module
    _ = Eplus • adag 0 := by
          rw [hplus', hminus']
          simp

theorem freeSheetHamiltonian_commutator_creation_minus
    (Eplus Eminus : ℝ) :
    algebraCommutator (freeSheetHamiltonian Eplus Eminus) (adag 1) =
      Eminus • adag 1 := by
  have hplus : algebraCommutator (sheetNumberPlus) (adag 1) = 0 := by
    simpa [sheetNumberPlus] using
      (quadraticWittGenerator_commutator_creation 0 0 1)
  have hminus : algebraCommutator (sheetNumberMinus) (adag 1) = adag 1 := by
    simpa [sheetNumberMinus] using
      (quadraticWittGenerator_commutator_creation 1 1 1)
  have hplus' : sheetNumberPlus * adag 1 - adag 1 * sheetNumberPlus = 0 := hplus
  have hminus' : sheetNumberMinus * adag 1 - adag 1 * sheetNumberMinus = adag 1 := hminus
  unfold freeSheetHamiltonian algebraCommutator
  calc
    (Eplus • sheetNumberPlus + Eminus • sheetNumberMinus) * adag 1 -
          adag 1 * (Eplus • sheetNumberPlus + Eminus • sheetNumberMinus) =
        ((Eplus • sheetNumberPlus) * adag 1 -
            adag 1 * (Eplus • sheetNumberPlus)) +
          ((Eminus • sheetNumberMinus) * adag 1 -
            adag 1 * (Eminus • sheetNumberMinus)) := by noncomm_ring
    _ = Eplus • (sheetNumberPlus * adag 1 - adag 1 * sheetNumberPlus) +
          Eminus • (sheetNumberMinus * adag 1 - adag 1 * sheetNumberMinus) := by
            rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
              mul_smul_comm]
            module
    _ = Eminus • adag 1 := by
          rw [hplus', hminus']
          simp

/-- The central even operator produced by a same-sheet CAR supercharge pair. -/
def centralSupercharge (i : Fin 4) : Operator :=
  a i * adag i + adag i * a i

theorem centralSupercharge_eq_one (i : Fin 4) :
    centralSupercharge i = 1 := by
  exact witt_CAR_eq i

theorem centralSupercharge_commutator (i : Fin 4) (X : Operator) :
    algebraCommutator (centralSupercharge i) X = 0 := by
  rw [centralSupercharge_eq_one]
  simp [algebraCommutator]

theorem totalNumber_commutator_chiralCharge :
    algebraCommutator totalNumber chiralCharge = 0 := by
  have h00 : algebraCommutator (wittNumberOperator 0)
      (wittNumberOperator 0) = 0 := by
    simpa using (quadraticWittGenerator_commutator_genuine 0 0 0 0)
  have h01 : algebraCommutator (wittNumberOperator 0)
      (wittNumberOperator 1) = 0 := by
    simpa using (quadraticWittGenerator_commutator_genuine 0 0 1 1)
  have h10 : algebraCommutator (wittNumberOperator 1)
      (wittNumberOperator 0) = 0 := by
    simpa using (quadraticWittGenerator_commutator_genuine 1 1 0 0)
  have h11 : algebraCommutator (wittNumberOperator 1)
      (wittNumberOperator 1) = 0 := by
    simpa using (quadraticWittGenerator_commutator_genuine 1 1 1 1)
  unfold totalNumber chiralCharge algebraCommutator
  calc
    (wittNumberOperator 0 + wittNumberOperator 1) *
          (wittNumberOperator 0 - wittNumberOperator 1) -
        (wittNumberOperator 0 - wittNumberOperator 1) *
          (wittNumberOperator 0 + wittNumberOperator 1) =
      (wittNumberOperator 0 * wittNumberOperator 0 -
          wittNumberOperator 0 * wittNumberOperator 0) -
        (wittNumberOperator 0 * wittNumberOperator 1 -
          wittNumberOperator 1 * wittNumberOperator 0) +
        (wittNumberOperator 1 * wittNumberOperator 0 -
          wittNumberOperator 0 * wittNumberOperator 1) -
        (wittNumberOperator 1 * wittNumberOperator 1 -
          wittNumberOperator 1 * wittNumberOperator 1) := by
            noncomm_ring
    _ = 0 := by
      rw [show wittNumberOperator 0 * wittNumberOperator 0 -
          wittNumberOperator 0 * wittNumberOperator 0 =
          algebraCommutator (wittNumberOperator 0)
            (wittNumberOperator 0) by rfl]
      rw [show wittNumberOperator 0 * wittNumberOperator 1 -
          wittNumberOperator 1 * wittNumberOperator 0 =
          algebraCommutator (wittNumberOperator 0)
            (wittNumberOperator 1) by rfl]
      rw [show wittNumberOperator 1 * wittNumberOperator 0 -
          wittNumberOperator 0 * wittNumberOperator 1 =
          algebraCommutator (wittNumberOperator 1)
            (wittNumberOperator 0) by rfl]
      rw [show wittNumberOperator 1 * wittNumberOperator 1 -
          wittNumberOperator 1 * wittNumberOperator 1 =
          algebraCommutator (wittNumberOperator 1)
            (wittNumberOperator 1) by rfl]
      rw [h00, h01, h10, h11]
      abel

theorem chiralCharge_commutator_totalNumber :
    algebraCommutator chiralCharge totalNumber = 0 := by
  have h : totalNumber * chiralCharge = chiralCharge * totalNumber :=
    sub_eq_zero.mp totalNumber_commutator_chiralCharge
  unfold algebraCommutator
  rw [h]
  exact sub_self _

theorem totalNumber_commutator_of_grandCanonicalGenerator
    (H : Operator) (μ μχ : ℝ)
    (hH : algebraCommutator H totalNumber = 0) :
    algebraCommutator (grandCanonicalGenerator H μ μχ) totalNumber = 0 := by
  unfold grandCanonicalGenerator algebraCommutator
  have hμ : (μ • totalNumber) * totalNumber =
      μ • (totalNumber * totalNumber) := by
    rw [smul_mul_assoc]
  have hμ' : totalNumber * (μ • totalNumber) =
      μ • (totalNumber * totalNumber) := by
    rw [mul_smul_comm]
  have hμχ : (μχ • chiralCharge) * totalNumber =
      μχ • (chiralCharge * totalNumber) := by
    rw [smul_mul_assoc]
  have hμχ' : totalNumber * (μχ • chiralCharge) =
      μχ • (totalNumber * chiralCharge) := by
    rw [mul_smul_comm]
  simp only [sub_mul, mul_sub]
  rw [hμ, hμ', hμχ, hμχ']
  have hH' : H * totalNumber - totalNumber * H = 0 := hH
  have hχ : chiralCharge * totalNumber = totalNumber * chiralCharge :=
    sub_eq_zero.mp chiralCharge_commutator_totalNumber
  calc
    H * totalNumber - μ • (totalNumber * totalNumber) -
          μχ • (chiralCharge * totalNumber) -
        (totalNumber * H - μ • (totalNumber * totalNumber) -
          μχ • (totalNumber * chiralCharge)) =
        (H * totalNumber - totalNumber * H) -
          μ • (totalNumber * totalNumber) +
          μ • (totalNumber * totalNumber) -
          μχ • (chiralCharge * totalNumber) +
          μχ • (totalNumber * chiralCharge) := by abel
    _ = 0 := by rw [hH', hχ]; module

theorem chemicalPotential_split (μplus μminus : ℝ) :
    ((μplus + μminus) / 2) • totalNumber +
        ((μplus - μminus) / 2) • chiralCharge =
      μplus • sheetNumberPlus + μminus • sheetNumberMinus := by
  dsimp [totalNumber, chiralCharge]
  module

theorem grandCanonicalGenerator_sheet_form (H : Operator) (μplus μminus : ℝ) :
    grandCanonicalGenerator H ((μplus + μminus) / 2)
        ((μplus - μminus) / 2) =
      H - μplus • sheetNumberPlus - μminus • sheetNumberMinus := by
  unfold grandCanonicalGenerator
  rw [sub_sub, sub_sub, chemicalPotential_split]

theorem freeGrandCanonicalGenerator_eq_effectiveHamiltonian
    (Eplus Eminus μplus μminus : ℝ) :
    freeGrandCanonicalGenerator Eplus Eminus μplus μminus =
      freeSheetHamiltonian (Eplus - μplus) (Eminus - μminus) := by
  unfold freeGrandCanonicalGenerator
  rw [grandCanonicalGenerator_sheet_form]
  unfold freeSheetHamiltonian
  module

theorem freeGrandCanonicalGenerator_commutator_annihilation_plus
    (Eplus Eminus μplus μminus : ℝ) :
    algebraCommutator
        (freeGrandCanonicalGenerator Eplus Eminus μplus μminus) (a 0) =
      -((Eplus - μplus) • a 0) := by
  rw [freeGrandCanonicalGenerator_eq_effectiveHamiltonian]
  exact freeSheetHamiltonian_commutator_annihilation_plus
    (Eplus - μplus) (Eminus - μminus)

theorem freeGrandCanonicalGenerator_commutator_annihilation_minus
    (Eplus Eminus μplus μminus : ℝ) :
    algebraCommutator
        (freeGrandCanonicalGenerator Eplus Eminus μplus μminus) (a 1) =
      -((Eminus - μminus) • a 1) := by
  rw [freeGrandCanonicalGenerator_eq_effectiveHamiltonian]
  exact freeSheetHamiltonian_commutator_annihilation_minus
    (Eplus - μplus) (Eminus - μminus)

theorem freeGrandCanonicalGenerator_commutator_creation_plus
    (Eplus Eminus μplus μminus : ℝ) :
    algebraCommutator
        (freeGrandCanonicalGenerator Eplus Eminus μplus μminus) (adag 0) =
      (Eplus - μplus) • adag 0 := by
  rw [freeGrandCanonicalGenerator_eq_effectiveHamiltonian]
  exact freeSheetHamiltonian_commutator_creation_plus
    (Eplus - μplus) (Eminus - μminus)

theorem freeGrandCanonicalGenerator_commutator_creation_minus
    (Eplus Eminus μplus μminus : ℝ) :
    algebraCommutator
        (freeGrandCanonicalGenerator Eplus Eminus μplus μminus) (adag 1) =
      (Eminus - μminus) • adag 1 := by
  rw [freeGrandCanonicalGenerator_eq_effectiveHamiltonian]
  exact freeSheetHamiltonian_commutator_creation_minus
    (Eplus - μplus) (Eminus - μminus)

theorem chiralCharge_conserved_of_commutator (H : Operator)
    (hH : algebraCommutator H chiralCharge = 0) :
    algebraCommutator (grandCanonicalGenerator H 0 0) chiralCharge = 0 := by
  simpa [grandCanonicalGenerator] using hH

theorem grandCanonicalGenerator_commutator_chiralCharge (H : Operator)
    (μ μχ : ℝ) (hH : algebraCommutator H chiralCharge = 0)
    (hN : algebraCommutator totalNumber chiralCharge = 0) :
    algebraCommutator (grandCanonicalGenerator H μ μχ) chiralCharge = 0 := by
  unfold grandCanonicalGenerator algebraCommutator
  have hμ : (μ • totalNumber) * chiralCharge =
      μ • (totalNumber * chiralCharge) := by
    rw [smul_mul_assoc]
  have hμ' : chiralCharge * (μ • totalNumber) =
      μ • (chiralCharge * totalNumber) := by
    rw [mul_smul_comm]
  have hμχ : (μχ • chiralCharge) * chiralCharge =
      μχ • (chiralCharge * chiralCharge) := by
    rw [smul_mul_assoc]
  have hμχ' : chiralCharge * (μχ • chiralCharge) =
      μχ • (chiralCharge * chiralCharge) := by
    rw [mul_smul_comm]
  simp only [sub_mul, mul_sub]
  rw [hμ, hμχ, hμ', hμχ']
  have hH' : H * chiralCharge - chiralCharge * H = 0 := hH
  have hN' : totalNumber * chiralCharge =
      chiralCharge * totalNumber := sub_eq_zero.mp hN
  calc
    H * chiralCharge - μ • (totalNumber * chiralCharge) -
          μχ • (chiralCharge * chiralCharge) -
          (chiralCharge * H - μ • (chiralCharge * totalNumber) -
            μχ • (chiralCharge * chiralCharge)) =
        (H * chiralCharge - chiralCharge * H) -
          μ • (totalNumber * chiralCharge) +
          μ • (chiralCharge * totalNumber) -
          μχ • (chiralCharge * chiralCharge) +
          μχ • (chiralCharge * chiralCharge) := by abel
    _ = 0 := by rw [hH', hN']; module

theorem grandCanonicalGenerator_commutator_chiralCharge_conserved
    (H : Operator) (μ μχ : ℝ)
    (hH : algebraCommutator H chiralCharge = 0) :
    algebraCommutator (grandCanonicalGenerator H μ μχ) chiralCharge = 0 :=
  grandCanonicalGenerator_commutator_chiralCharge H μ μχ hH
    totalNumber_commutator_chiralCharge

/-- The modular generator is a scalar multiple of the native grand-canonical
operator; this records the algebraic part of modular flow without assuming an
analytic exponential or a KMS state. -/
def grandCanonicalModularGenerator (H : Operator) (beta μ μχ : ℝ) : Operator :=
  beta • grandCanonicalGenerator H μ μχ

theorem grandCanonicalModularGenerator_commutator_chiralCharge
    (H : Operator) (beta μ μχ : ℝ)
    (hH : algebraCommutator H chiralCharge = 0) :
    algebraCommutator
        (grandCanonicalModularGenerator H beta μ μχ) chiralCharge = 0 := by
  unfold grandCanonicalModularGenerator
  have hG : algebraCommutator
      (grandCanonicalGenerator H μ μχ) chiralCharge = 0 :=
    grandCanonicalGenerator_commutator_chiralCharge_conserved H μ μχ hH
  unfold algebraCommutator at hG ⊢
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [← smul_sub, hG, smul_zero]

/-- The fixed CAR relation on the positive sheet is unchanged by the
grand-canonical choice of generator. -/
theorem sheetPlus_CAR :
    a 0 * adag 0 + adag 0 * a 0 = 1 :=
  witt_CAR_eq 0

/-- The fixed CAR relation on the negative sheet is unchanged by the
grand-canonical choice of generator. -/
theorem sheetMinus_CAR :
    a 1 * adag 1 + adag 1 * a 1 = 1 :=
  witt_CAR_eq 1

/-- Inner operator transport preserves the CAR product and anticommutator. -/
theorem unit_transport_CAR (u : Operatorˣ) (x y : Operator)
    (hxy : x * y + y * x = 1) :
    unitConjugation u x * unitConjugation u y +
        unitConjugation u y * unitConjugation u x = 1 := by
  rw [← unitConjugation_mul, ← unitConjugation_mul, ← unitConjugation_add,
    hxy, unitConjugation_one]

end InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry
