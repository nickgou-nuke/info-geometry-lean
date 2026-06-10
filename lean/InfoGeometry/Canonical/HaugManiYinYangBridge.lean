import InfoGeometry.Krein.TomitaMatrixAtom

/-!
# Haug-Mani Real Doubled Bridge, finite owner surface

This module formalizes the finite algebraic corridor behind the informal
"symmetric sign / no primitive imaginary scalar" reading:

* two real involutions `J` and `eps`;
* the derived real phase axis `K = J * eps`;
* `K^2 = -1`;
* real scalar readback `a + bK`;
* the ordinary complex multiplication table reproduced by real `2 × 2`
  matrices.

#### BUCKET 1: CLOSED FINITE THEOREMS
All theorem statements below are concrete matrix identities over `ℝ`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
No claim is made that imaginary numbers are unnecessary in physics, that a
new number system is superior, that quantum mechanics is reconstructed, or
that any Riemann Hypothesis consequence follows from this representation.
-/

namespace InfoGeometry.Canonical.HaugManiYinYangBridge

open InfoGeometry.Krein.TomitaMatrixAtom

/-- Concrete real `2 × 2` carrier for the doubled sign/phase atom. -/
abbrev RealDoubledMatrix := M2R

/-- Positive/physical sector idempotent. -/
abbrev physicalSector : RealDoubledMatrix := Pplus

/-- Negative/ghost sector idempotent. -/
abbrev ghostSector : RealDoubledMatrix := Pminus

/-- The sheet-mixing involution. -/
abbrev mixedSector : RealDoubledMatrix := J

/-- Derived real phase axis, replacing primitive scalar `i` in this finite model. -/
def phaseAxis : RealDoubledMatrix := J * eps

/-- Real doubled scalar readback: `a + b i` is represented as `a * I + b * K`. -/
def realDoubledScalar (a b : ℝ) : RealDoubledMatrix :=
  a • (1 : RealDoubledMatrix) + b • phaseAxis

@[simp]
theorem physicalSector_idempotent :
    physicalSector * physicalSector = physicalSector :=
  Pplus_idempotent

@[simp]
theorem ghostSector_idempotent :
    ghostSector * ghostSector = ghostSector :=
  Pminus_idempotent

@[simp]
theorem physical_ghost_orthogonal :
    physicalSector * ghostSector = 0 :=
  Pplus_mul_Pminus

@[simp]
theorem ghost_physical_orthogonal :
    ghostSector * physicalSector = 0 :=
  Pminus_mul_Pplus

@[simp]
theorem physical_add_ghost :
    physicalSector + ghostSector = (1 : RealDoubledMatrix) :=
  Pplus_add_Pminus

/-- The mixed sector swaps positive and negative projectors by conjugation. -/
theorem mixedSector_conj_physical :
    mixedSector * physicalSector * mixedSector = ghostSector := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mixedSector, physicalSector, ghostSector, J, Pplus, Pminus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The mixed sector swaps negative and positive projectors by conjugation. -/
theorem mixedSector_conj_ghost :
    mixedSector * ghostSector * mixedSector = physicalSector := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mixedSector, physicalSector, ghostSector, J, Pplus, Pminus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem phaseAxis_eq_J_mul_eps :
    phaseAxis = J * eps := rfl

/-- The phase axis squares to `-1`, so the complex unit is derived from real data. -/
theorem phaseAxis_sq :
    phaseAxis * phaseAxis = -(1 : RealDoubledMatrix) := by
  simpa [phaseAxis] using J_eps_sq

/-- Modular/sheet reflection flips the derived phase axis. -/
theorem mixedSector_conj_phaseAxis :
    mixedSector * phaseAxis * mixedSector = -phaseAxis := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mixedSector, phaseAxis, J, eps, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem realDoubledScalar_zero :
    realDoubledScalar 0 0 = 0 := by
  simp [realDoubledScalar]

@[simp]
theorem realDoubledScalar_one :
    realDoubledScalar 1 0 = (1 : RealDoubledMatrix) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realDoubledScalar, phaseAxis, J, eps, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem realDoubledScalar_I :
    realDoubledScalar 0 1 = phaseAxis := by
  simp [realDoubledScalar]

/-- The embedded finite scalar `i` squares to `-1`. -/
theorem realDoubledScalar_I_sq :
    realDoubledScalar 0 1 * realDoubledScalar 0 1 =
      -(1 : RealDoubledMatrix) := by
  simpa using phaseAxis_sq

/--
The real doubled scalar product reproduces ordinary complex multiplication:
`(a + bK)(c + dK) = (ac - bd) + (ad + bc)K`.
-/
theorem realDoubledScalar_mul
    (a b c d : ℝ) :
    realDoubledScalar a b * realDoubledScalar c d =
      realDoubledScalar (a * c - b * d) (a * d + b * c) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [realDoubledScalar, phaseAxis, J, eps, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf

/-- Sheet reflection is complex conjugation in the real doubled readback. -/
theorem mixedSector_conj_realDoubledScalar
    (a b : ℝ) :
    mixedSector * realDoubledScalar a b * mixedSector =
      realDoubledScalar a (-b) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [realDoubledScalar, phaseAxis, mixedSector, J, eps,
      Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
      Matrix.vecCons, Fin.sum_univ_two] <;>
    ring_nf

@[simp]
theorem realDoubledScalar_apply_zero_zero (a b : ℝ) :
    realDoubledScalar a b 0 0 = a := by
  norm_num [realDoubledScalar, phaseAxis, J, eps]

@[simp]
theorem realDoubledScalar_apply_one_zero (a b : ℝ) :
    realDoubledScalar a b 1 0 = b := by
  norm_num [realDoubledScalar, phaseAxis, J, eps]

/-- The real doubled readback is injective in its two real coefficients. -/
theorem realDoubledScalar_injective
    {a b c d : ℝ}
    (h : realDoubledScalar a b = realDoubledScalar c d) :
    a = c ∧ b = d := by
  constructor
  · simpa using congrFun (congrFun h 0) 0
  · simpa using congrFun (congrFun h 1) 0

/--
Finite capstone: the sign sectors split the carrier, the mixed sector swaps
them, and the derived real phase axis behaves as the scalar imaginary unit.
-/
theorem haug_mani_real_doubled_capstone :
    physicalSector * physicalSector = physicalSector ∧
    ghostSector * ghostSector = ghostSector ∧
    physicalSector * ghostSector = 0 ∧
    ghostSector * physicalSector = 0 ∧
    physicalSector + ghostSector = (1 : RealDoubledMatrix) ∧
    mixedSector * physicalSector * mixedSector = ghostSector ∧
    mixedSector * ghostSector * mixedSector = physicalSector ∧
    phaseAxis = J * eps ∧
    phaseAxis * phaseAxis = -(1 : RealDoubledMatrix) ∧
    mixedSector * phaseAxis * mixedSector = -phaseAxis :=
  ⟨physicalSector_idempotent, ghostSector_idempotent,
    physical_ghost_orthogonal, ghost_physical_orthogonal,
    physical_add_ghost, mixedSector_conj_physical, mixedSector_conj_ghost,
    phaseAxis_eq_J_mul_eps, phaseAxis_sq, mixedSector_conj_phaseAxis⟩

end InfoGeometry.Canonical.HaugManiYinYangBridge
