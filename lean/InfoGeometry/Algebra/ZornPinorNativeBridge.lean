import InfoGeometry.Algebra.ZornMatrix

/-!
# Native Zorn realization of the Pin-minus and split ladder carriers

The informal three-vector presentation is not a second algebra.  This file
expresses its generators in the repository-owned nonassociative Zorn carrier:
`U i` and `V i` are the two off-diagonal root directions and `E11`, `E22` are
the two Peirce idempotents.  All identities below involve at most two factors,
so no associativity is assumed.
-/

namespace InfoGeometry.Algebra.ZornMatrix

noncomputable section

variable {R : Type*} [CommRing R]

/-- The two chiral ladder generators in the native Zorn carrier. -/
def pinorRaise (i : Fin 3) : ZornMatrix R := U i

def pinorLower (i : Fin 3) : ZornMatrix R := V i

/-- The split and Pin-minus combinations of one root direction. -/
def splitPinor (i : Fin 3) : ZornMatrix R := U i + V i

def pinMinusPinor (i : Fin 3) : ZornMatrix R := U i - V i

@[simp] theorem pinorRaise_sq_zero (i : Fin 3) :
    pinorRaise (R := R) i * pinorRaise i = 0 := by
  exact U_mul_self_zero i

@[simp] theorem pinorLower_sq_zero (i : Fin 3) :
    pinorLower (R := R) i * pinorLower i = 0 := by
  exact V_mul_self_zero i

theorem pinor_car (i j : Fin 3) :
      pinorRaise (R := R) i * pinorLower j +
        pinorLower j * pinorRaise i =
      if i = j then I else 0 := by
  exact U_V_anticommutator i j

@[simp] theorem pinor_car_same (i : Fin 3) :
    pinorRaise (R := R) i * pinorLower i +
        pinorLower i * pinorRaise i = I := by
  simpa using pinor_car (R := R) i i

theorem pinor_car_of_ne {i j : Fin 3} (hij : i ≠ j) :
    pinorRaise (R := R) i * pinorLower j +
        pinorLower j * pinorRaise i = (0 : ZornMatrix R) := by
  simpa [hij] using pinor_car (R := R) i j

@[simp] theorem raise_lower_same (i : Fin 3) :
    pinorRaise (R := R) i * pinorLower i = E11 := by
  exact U_mul_V_self i

@[simp] theorem lower_raise_same (i : Fin 3) :
    pinorLower (R := R) i * pinorRaise i = E22 := by
  exact V_mul_U_self i

@[simp] theorem splitPinor_sq (i : Fin 3) :
    splitPinor (R := R) i * splitPinor i = I := by
  fin_cases i <;> apply ZornMatrix.ext <;>
    simp [splitPinor, U, V, I, Vec3.basis, mul, Vec3.dot, Vec3.cross,
      Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem pinMinusPinor_sq (i : Fin 3) :
    pinMinusPinor (R := R) i * pinMinusPinor i = smul (-1 : R) I := by
  fin_cases i <;> apply ZornMatrix.ext <;>
    simp [pinMinusPinor, U, V, I, Vec3.basis, ZornMatrix.smul, mul,
      Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

theorem splitPinor_eq_raise_add_lower (i : Fin 3) :
    splitPinor (R := R) i = pinorRaise i + pinorLower i := rfl

theorem pinMinusPinor_eq_raise_sub_lower (i : Fin 3) :
    pinMinusPinor (R := R) i = pinorRaise i - pinorLower i := rfl

@[simp] theorem plus_projection_raise (i : Fin 3) :
    E11 * pinorRaise (R := R) i = pinorRaise i := by
  exact E11_mul_U i

@[simp] theorem lower_projection_plus (i : Fin 3) :
    pinorLower (R := R) i * E11 = pinorLower i := by
  exact V_mul_E11 i

@[simp] theorem raise_projection_minus (i : Fin 3) :
    pinorRaise (R := R) i * E22 = pinorRaise i := by
  exact U_mul_E22 i

@[simp] theorem minus_projection_lower (i : Fin 3) :
    E22 * pinorLower (R := R) i = pinorLower i := by
  exact E22_mul_V i

/-- The Pin-minus generator in the notation used by the source specification. -/
def gamma (i : Fin 3) : ZornMatrix R := pinMinusPinor i

theorem gamma_anticomm_general (i j : Fin 3) :
    gamma (R := R) i * gamma j + gamma j * gamma i =
      smul (- (2 : R) * Vec3.dot (Vec3.basis i) (Vec3.basis j)) I := by
  fin_cases i <;> fin_cases j <;> apply ZornMatrix.ext <;>
    simp [gamma, pinMinusPinor, U, V, I, Vec3.basis, ZornMatrix.smul,
      mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul] <;> ring

theorem gamma_anticomm_of_orthogonal {i j : Fin 3}
    (hij : Vec3.dot (Vec3.basis (R := R) i) (Vec3.basis (R := R) j) = (0 : R)) :
    gamma (R := R) i * gamma j + gamma j * gamma i = 0 := by
  rw [gamma_anticomm_general i j]
  have hcoef : - (2 : R) * Vec3.dot (Vec3.basis (R := R) i)
      (Vec3.basis (R := R) j) = 0 := by rw [hij]; ring
  rw [hcoef]
  simp [ZornMatrix.smul, zero, I, Vec3.smul]

/- The negative and split polarizations are orthogonal as Clifford
    directions.  This is a two-factor identity, so it does not use ambient
    associativity of the Zorn product. -/
theorem gamma_splitPinor_anticomm (i j : Fin 3) :
    gamma (R := R) i * splitPinor j +
        splitPinor j * gamma i = (0 : ZornMatrix R) := by
  fin_cases i <;> fin_cases j <;>
    apply ZornMatrix.ext <;>
    simp [gamma, splitPinor, pinMinusPinor, U, V,
      mul, zero, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub,
      Vec3.smul]

/-! ## Bivector readout -/

/-- The product of two Pin-minus generators is the native bivector carrier. -/
def bivector (i j : Fin 3) : ZornMatrix R := gamma i * gamma j

@[simp] theorem bivector_sq_of_ne {i j : Fin 3} (hij : i ≠ j) :
    bivector (R := R) i j * bivector i j = smul (-1 : R) I := by
  fin_cases i <;> fin_cases j <;>
    simp_all [bivector, gamma, pinMinusPinor, U, V, I, ZornMatrix.smul,
      mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul] <;>
    ring

/-- The native Zorn orientation fixes the sign of the first quaternion product. -/
theorem gamma_mul_gamma_zero_one :
    gamma (R := R) 0 * gamma 1 = smul (-1 : R) (gamma 2) := by
  apply ZornMatrix.ext <;>
    simp [gamma, pinMinusPinor, U, V, I, ZornMatrix.smul, mul,
      Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-- The native orientation of the three-dimensional Pin-minus carrier gives
    the corresponding cyclic bivector product.  This is stated with the
    parenthesisation displayed: no associativity of the Zorn product is
    being used as an ambient algebra law. -/
theorem bivector_cycle_zero_one_two :
    bivector (R := R) 0 1 * bivector 1 2 =
      smul (-1 : R) (bivector 0 2) := by
  apply ZornMatrix.ext <;>
    simp [bivector, gamma, pinMinusPinor, U, V, I, ZornMatrix.smul, mul,
      Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-- Bivectors sharing one orthogonal generator anticommute in the native
    orientation. -/
theorem bivector_anticomm_shared :
    bivector (R := R) 0 1 * bivector 1 2 +
        bivector 1 2 * bivector 0 1 = (0 : ZornMatrix R) := by
  apply ZornMatrix.ext <;>
    simp [bivector, gamma, pinMinusPinor, U, V, I, ZornMatrix.smul, zero, mul,
      Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-! ## Quaternion-unit readout

The native orientation has `γ₀ γ₁ = -γ₂`.  We therefore choose the third
unit with that sign built into its definition.  These declarations only
record the finite multiplication table; no group structure is placed on the
ambient nonassociative Zorn carrier.
-/

def qI : ZornMatrix R := gamma 0

def qJ : ZornMatrix R := gamma 1

def qK : ZornMatrix R := smul (-1 : R) (gamma 2)

@[simp] theorem qI_sq : qI (R := R) * qI = smul (-1 : R) I := by
  simpa [qI, gamma] using (pinMinusPinor_sq (R := R) 0)

@[simp] theorem qJ_sq : qJ (R := R) * qJ = smul (-1 : R) I := by
  simpa [qJ, gamma] using (pinMinusPinor_sq (R := R) 1)

@[simp] theorem qK_sq : qK (R := R) * qK = smul (-1 : R) I := by
  apply ZornMatrix.ext <;>
    simp [qK, gamma, pinMinusPinor, U, V, I, ZornMatrix.smul, mul,
      Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

theorem qI_mul_qJ : qI (R := R) * qJ = qK := by
  simpa [qI, qJ, qK] using (gamma_mul_gamma_zero_one (R := R))

theorem qJ_mul_qK : qJ (R := R) * qK = qI := by
  apply ZornMatrix.ext <;>
    simp [qI, qJ, qK, gamma, pinMinusPinor, U, V, I, ZornMatrix.smul, mul,
      Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

theorem qK_mul_qI : qK (R := R) * qI = qJ := by
  apply ZornMatrix.ext <;>
    simp [qI, qJ, qK, gamma, pinMinusPinor, U, V, I, ZornMatrix.smul, mul,
      Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

theorem qJ_mul_qI : qJ (R := R) * qI = smul (-1 : R) qK := by
  apply ZornMatrix.ext <;>
    simp [qI, qJ, qK, gamma, pinMinusPinor, U, V, I, ZornMatrix.smul, mul,
      Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

theorem qK_mul_qJ : qK (R := R) * qJ = smul (-1 : R) qI := by
  apply ZornMatrix.ext <;>
    simp [qI, qJ, qK, gamma, pinMinusPinor, U, V, I, ZornMatrix.smul, mul,
      Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

theorem qI_mul_qK : qI (R := R) * qK = smul (-1 : R) qJ := by
  apply ZornMatrix.ext <;>
    simp [qI, qJ, qK, gamma, pinMinusPinor, U, V, I, ZornMatrix.smul, mul,
      Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

theorem qI_anticomm_qJ :
    qI (R := R) * qJ + qJ * qI = (0 : ZornMatrix R) := by
  rw [qI_mul_qJ, qJ_mul_qI]
  apply ZornMatrix.ext <;>
    simp [qI, qJ, qK, gamma, pinMinusPinor, U, V, ZornMatrix.smul,
      Vec3.smul, Vec3.add, zero] <;> ring

theorem qJ_anticomm_qK :
    qJ (R := R) * qK + qK * qJ = (0 : ZornMatrix R) := by
  rw [qJ_mul_qK, qK_mul_qJ]
  apply ZornMatrix.ext <;>
    simp [qI, qJ, qK, gamma, pinMinusPinor, U, V, ZornMatrix.smul,
      Vec3.smul, Vec3.add, zero] <;> ring

theorem qK_anticomm_qI :
    qK (R := R) * qI + qI * qK = (0 : ZornMatrix R) := by
  rw [qK_mul_qI, qI_mul_qK]
  apply ZornMatrix.ext <;>
    simp [qI, qJ, qK, gamma, pinMinusPinor, U, V, ZornMatrix.smul,
      Vec3.smul, Vec3.add, zero] <;> ring

end

end InfoGeometry.Algebra.ZornMatrix
