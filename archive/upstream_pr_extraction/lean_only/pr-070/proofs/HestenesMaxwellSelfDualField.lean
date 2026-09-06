import proofs.HestenesBivectorSelfDuality

/-!
# Maxwell bivectors in the associative Pauli realization

The exact bivector carrier itself is not an algebra.  Multiplication is
therefore performed in `M₂(ℂ)`, the already certified associative image of
`Cl⁺(1,3)`.  This owner proves the Riemann--Silberstein square and separates
its scalar and pseudoscalar invariants.
-/

noncomputable section
namespace HestenesMaxwellSelfDualField

open HestenesEvenPauliEquiv
open TwoSheetThreeColorWeyl

abbrev RealSpatial := Fin 3 → ℝ
abbrev PauliMatrix := Matrix (Fin 2) (Fin 2) ℂ

def spatialNormSq (v : RealSpatial) : ℝ := ∑ k, v k ^ 2
def spatialDot (u v : RealSpatial) : ℝ := ∑ k, u k * v k

def pauliVector (v : RealSpatial) : PauliMatrix :=
  (v 0 : ℂ) • pauli1 + (v 1 : ℂ) • pauli2 + (v 2 : ℂ) • pauli3

/-- The Riemann--Silberstein/Hestenes field `E + iB` in the Pauli algebra. -/
def maxwellField (E B : RealSpatial) : PauliMatrix :=
  pauliVector E + Complex.I • pauliVector B

def scalarInvariant (E B : RealSpatial) : ℝ :=
  spatialNormSq E - spatialNormSq B

def pseudoscalarInvariant (E B : RealSpatial) : ℝ :=
  2 * spatialDot E B

theorem pauliVector_sq (v : RealSpatial) :
    pauliVector v * pauliVector v =
      (spatialNormSq v : ℂ) • (1 : PauliMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVector, spatialNormSq, pauli1, pauli2, pauli3,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.smul_apply] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem pauliVector_anticommutator (u v : RealSpatial) :
    pauliVector u * pauliVector v + pauliVector v * pauliVector u =
      ((2 * spatialDot u v : ℝ) : ℂ) • (1 : PauliMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVector, spatialDot, pauli1, pauli2, pauli3,
      Fin.sum_univ_three, Matrix.smul_apply, Matrix.add_apply] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- The two Lorentz invariants are the real and pseudoscalar coefficients of `F²`. -/
theorem maxwellField_sq (E B : RealSpatial) :
    maxwellField E B * maxwellField E B =
      ((scalarInvariant E B : ℝ) : ℂ) • (1 : PauliMatrix) +
        (Complex.I * (pseudoscalarInvariant E B : ℝ)) •
          (1 : PauliMatrix) := by
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    simp
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show 4 = 2 + 2 by omega, pow_add, Complex.I_sq]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [maxwellField, pauliVector, scalarInvariant, pseudoscalarInvariant,
      spatialNormSq, spatialDot, pauli1, pauli2, pauli3,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.smul_apply, Matrix.add_apply] <;>
    ring_nf <;> simp only [Complex.I_sq, hI3, hI4] <;> ring

theorem maxwell_null_iff (E B : RealSpatial) :
    maxwellField E B * maxwellField E B = 0 ↔
      scalarInvariant E B = 0 ∧ pseudoscalarInvariant E B = 0 := by
  rw [maxwellField_sq]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [Matrix.smul_apply, Matrix.add_apply] at h00
    constructor
    · simpa using congrArg Complex.re h00
    · have him := congrArg Complex.im h00
      simpa using him
  · rintro ⟨hS, hP⟩
    simp [hS, hP]

theorem maxwell_invariant_packet (E B : RealSpatial) :
    maxwellField E B * maxwellField E B =
      ((spatialNormSq E - spatialNormSq B : ℝ) : ℂ) •
          (1 : PauliMatrix) +
        (Complex.I * (2 * spatialDot E B : ℝ)) •
          (1 : PauliMatrix) := by
  simpa [scalarInvariant, pseudoscalarInvariant] using maxwellField_sq E B

end HestenesMaxwellSelfDualField
end noncomputable section
