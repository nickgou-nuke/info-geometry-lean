import InfoGeometry.Canonical.SplitCliffordCantorFock
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Local `Cl(1,1)` hop and parity packet

This owner bundles the already-proved one-mode CAR matrices into the
involutive Boolean hop `X = a + a†` and its anticommuting parity operator.
It makes no claim about a global boundary mirror, a Fock completion, or a
statistics interpretation.
-/

namespace InfoGeometry.Canonical.CantorLocalCl11HopParity

open InfoGeometry.Canonical.SplitCliffordCantorFock

def localHopOperator : M2R :=
  a_op + aDag_op

def localVacuumProjection : M2R :=
  a_op * aDag_op

def localOccupiedProjection : M2R :=
  aDag_op * a_op

def localParityOperator : M2R :=
  localVacuumProjection - localOccupiedProjection

def localPhaseOperator : M2R :=
  localHopOperator * localParityOperator

@[simp] theorem localVacuumProjection_add_localOccupiedProjection :
    localVacuumProjection + localOccupiedProjection = (1 : M2R) := by
  simpa [localVacuumProjection, localOccupiedProjection] using local_car_identity

theorem localVacuumProjection_sq :
    localVacuumProjection * localVacuumProjection = localVacuumProjection := by
  unfold localVacuumProjection
  have hswap : aDag_op * a_op =
      (1 : M2R) - a_op * aDag_op := by
    calc
      aDag_op * a_op =
          (a_op * aDag_op + aDag_op * a_op) - a_op * aDag_op := by
            noncomm_ring
      _ = 1 - a_op * aDag_op := by rw [local_car_identity]
  calc
    (a_op * aDag_op) * (a_op * aDag_op) =
        a_op * (aDag_op * a_op) * aDag_op := by noncomm_ring
    _ = a_op * (1 - a_op * aDag_op) * aDag_op := by rw [hswap]
    _ = a_op * aDag_op - (a_op * a_op) * (aDag_op * aDag_op) := by
      noncomm_ring
    _ = a_op * aDag_op := by rw [a_op_sq_zero, aDag_op_sq_zero]; simp

theorem localOccupiedProjection_sq :
    localOccupiedProjection * localOccupiedProjection = localOccupiedProjection := by
  unfold localOccupiedProjection
  have hswap : a_op * aDag_op =
      (1 : M2R) - aDag_op * a_op := by
    calc
      a_op * aDag_op =
          (a_op * aDag_op + aDag_op * a_op) - aDag_op * a_op := by
            noncomm_ring
      _ = 1 - aDag_op * a_op := by rw [local_car_identity]
  calc
    (aDag_op * a_op) * (aDag_op * a_op) =
        aDag_op * (a_op * aDag_op) * a_op := by noncomm_ring
    _ = aDag_op * (1 - aDag_op * a_op) * a_op := by rw [hswap]
    _ = aDag_op * a_op - (aDag_op * aDag_op) * (a_op * a_op) := by
      noncomm_ring
    _ = aDag_op * a_op := by rw [a_op_sq_zero, aDag_op_sq_zero]; simp

theorem localVacuumProjection_mul_localOccupiedProjection :
    localVacuumProjection * localOccupiedProjection = 0 := by
  unfold localVacuumProjection localOccupiedProjection
  calc
    (a_op * aDag_op) * (aDag_op * a_op) =
        a_op * (aDag_op * aDag_op) * a_op := by noncomm_ring
    _ = 0 := by rw [aDag_op_sq_zero]; simp

theorem localOccupiedProjection_mul_localVacuumProjection :
    localOccupiedProjection * localVacuumProjection = 0 := by
  unfold localOccupiedProjection localVacuumProjection
  calc
    (aDag_op * a_op) * (a_op * aDag_op) =
        aDag_op * (a_op * a_op) * aDag_op := by noncomm_ring
    _ = 0 := by rw [a_op_sq_zero]; simp

theorem localHopOperator_sq :
    localHopOperator * localHopOperator = (1 : M2R) := by
  unfold localHopOperator
  calc
    (a_op + aDag_op) * (a_op + aDag_op) =
        a_op * a_op + (a_op * aDag_op + aDag_op * a_op) +
          aDag_op * aDag_op := by noncomm_ring
    _ = 1 := by
      rw [a_op_sq_zero, aDag_op_sq_zero, local_car_identity]
      simp

theorem localParityOperator_sq :
    localParityOperator * localParityOperator = (1 : M2R) := by
  unfold localParityOperator
  calc
    (localVacuumProjection - localOccupiedProjection) *
        (localVacuumProjection - localOccupiedProjection) =
      localVacuumProjection * localVacuumProjection -
        (localVacuumProjection * localOccupiedProjection +
          localOccupiedProjection * localVacuumProjection) +
        localOccupiedProjection * localOccupiedProjection := by
          noncomm_ring
    _ = localVacuumProjection + localOccupiedProjection := by
      rw [localVacuumProjection_sq, localOccupiedProjection_sq,
        localVacuumProjection_mul_localOccupiedProjection,
        localOccupiedProjection_mul_localVacuumProjection]
      simp
    _ = 1 := localVacuumProjection_add_localOccupiedProjection

noncomputable def localPlusProjection : M2R :=
  (1 / 2 : ℝ) • ((1 : M2R) + localParityOperator)

noncomputable def localMinusProjection : M2R :=
  (1 / 2 : ℝ) • ((1 : M2R) - localParityOperator)

theorem localPlusProjection_eq_localVacuumProjection :
    localPlusProjection = localVacuumProjection := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localPlusProjection, localParityOperator,
      localVacuumProjection, localOccupiedProjection, a_op, aDag_op,
      Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply]

theorem localMinusProjection_eq_localOccupiedProjection :
    localMinusProjection = localOccupiedProjection := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localMinusProjection, localParityOperator,
      localVacuumProjection, localOccupiedProjection, a_op, aDag_op,
      Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply]

theorem localPlusProjection_sq :
    localPlusProjection * localPlusProjection = localPlusProjection := by
  rw [localPlusProjection_eq_localVacuumProjection]
  exact localVacuumProjection_sq

theorem localMinusProjection_sq :
    localMinusProjection * localMinusProjection = localMinusProjection := by
  rw [localMinusProjection_eq_localOccupiedProjection]
  exact localOccupiedProjection_sq

theorem localPlusProjection_mul_localMinusProjection :
    localPlusProjection * localMinusProjection = 0 := by
  rw [localPlusProjection_eq_localVacuumProjection,
    localMinusProjection_eq_localOccupiedProjection]
  exact localVacuumProjection_mul_localOccupiedProjection

theorem localMinusProjection_mul_localPlusProjection :
    localMinusProjection * localPlusProjection = 0 := by
  rw [localPlusProjection_eq_localVacuumProjection,
    localMinusProjection_eq_localOccupiedProjection]
  exact localOccupiedProjection_mul_localVacuumProjection

@[simp] theorem localPlusProjection_add_localMinusProjection :
    localPlusProjection + localMinusProjection = (1 : M2R) := by
  rw [localPlusProjection_eq_localVacuumProjection,
    localMinusProjection_eq_localOccupiedProjection]
  exact localVacuumProjection_add_localOccupiedProjection

theorem localPlusProjection_sub_localMinusProjection :
    localPlusProjection - localMinusProjection = localParityOperator := by
  rw [localPlusProjection_eq_localVacuumProjection,
    localMinusProjection_eq_localOccupiedProjection]
  rfl

theorem localPlusProjection_mul_annihilation :
    localPlusProjection * a_op = a_op * localMinusProjection := by
  rw [localPlusProjection_eq_localVacuumProjection,
    localMinusProjection_eq_localOccupiedProjection]
  unfold localVacuumProjection localOccupiedProjection
  noncomm_ring

theorem localMinusProjection_mul_creation :
    localMinusProjection * aDag_op = aDag_op * localPlusProjection := by
  rw [localPlusProjection_eq_localVacuumProjection,
    localMinusProjection_eq_localOccupiedProjection]
  unfold localVacuumProjection localOccupiedProjection
  noncomm_ring

theorem annihilation_eq_localPlusProjection_mul_annihilation_mul_localMinusProjection :
    a_op = localPlusProjection * a_op * localMinusProjection := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localPlusProjection, localMinusProjection,
      localParityOperator, localVacuumProjection,
      localOccupiedProjection, a_op, aDag_op,
      Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem creation_eq_localMinusProjection_mul_creation_mul_localPlusProjection :
    aDag_op = localMinusProjection * aDag_op * localPlusProjection := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localPlusProjection, localMinusProjection,
      localParityOperator, localVacuumProjection,
      localOccupiedProjection, a_op, aDag_op,
      Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]

def localNumberOperator : M2R := aDag_op * a_op

def localHoleOperator : M2R := a_op * aDag_op

@[simp] theorem localNumberOperator_eq_localOccupiedProjection :
    localNumberOperator = localOccupiedProjection := rfl

@[simp] theorem localHoleOperator_eq_localVacuumProjection :
    localHoleOperator = localVacuumProjection := rfl

theorem localParityOperator_eq_hole_sub_number :
    localParityOperator = localHoleOperator - localNumberOperator := by
  rfl

theorem localParityOperator_eq_one_sub_two_number :
    localParityOperator = (1 : M2R) - 2 • localNumberOperator := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localParityOperator, localNumberOperator,
      localVacuumProjection, localOccupiedProjection,
      a_op, aDag_op, Matrix.one_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem localPlusProjection_eq_localHoleOperator :
    localPlusProjection = localHoleOperator := by
  exact localPlusProjection_eq_localVacuumProjection.trans
    localHoleOperator_eq_localVacuumProjection.symm

theorem localMinusProjection_eq_localNumberOperator :
    localMinusProjection = localNumberOperator := by
  exact localMinusProjection_eq_localOccupiedProjection.trans
    localNumberOperator_eq_localOccupiedProjection.symm

theorem localAnnihilation_same_sheet_corners_zero :
    localPlusProjection * a_op * localPlusProjection = 0 ∧
      localMinusProjection * a_op * localMinusProjection = 0 := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [localPlusProjection, localMinusProjection,
        localParityOperator, localVacuumProjection,
        localOccupiedProjection, a_op, aDag_op,
        Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem localCreation_same_sheet_corners_zero :
    localPlusProjection * aDag_op * localPlusProjection = 0 ∧
      localMinusProjection * aDag_op * localMinusProjection = 0 := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [localPlusProjection, localMinusProjection,
        localParityOperator, localVacuumProjection,
        localOccupiedProjection, a_op, aDag_op,
        Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem localAnnihilation_corner :
    a_op = localPlusProjection * a_op * localMinusProjection :=
  annihilation_eq_localPlusProjection_mul_annihilation_mul_localMinusProjection

theorem localCreation_corner :
    aDag_op = localMinusProjection * aDag_op * localPlusProjection :=
  creation_eq_localMinusProjection_mul_creation_mul_localPlusProjection

theorem localHop_anticommutes_localParity :
    localHopOperator * localParityOperator =
      -(localParityOperator * localHopOperator) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localHopOperator, localParityOperator,
      localVacuumProjection, localOccupiedProjection, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localPhaseOperator_sq :
    localPhaseOperator * localPhaseOperator = -(1 : M2R) := by
  unfold localPhaseOperator
  have hanti : localParityOperator * localHopOperator =
      -(localHopOperator * localParityOperator) := by
    rw [localHop_anticommutes_localParity]
    simp
  calc
    (localHopOperator * localParityOperator) *
        (localHopOperator * localParityOperator) =
      localHopOperator * (localParityOperator * localHopOperator) *
        localParityOperator := by noncomm_ring
    _ = localHopOperator * (-(localHopOperator * localParityOperator)) *
        localParityOperator := by rw [hanti]
    _ = -(localHopOperator * localHopOperator) *
        (localParityOperator * localParityOperator) := by noncomm_ring
    _ = -1 := by
      rw [localHopOperator_sq, localParityOperator_sq]
      simp

theorem localHop_mul_localPhaseOperator :
    localHopOperator * localPhaseOperator = localParityOperator := by
  unfold localPhaseOperator
  rw [← Matrix.mul_assoc, localHopOperator_sq]
  simp

theorem localPhaseOperator_mul_localHop :
    localPhaseOperator * localHopOperator = -localParityOperator := by
  unfold localPhaseOperator
  rw [localHop_anticommutes_localParity]
  rw [neg_mul, Matrix.mul_assoc, localHopOperator_sq]
  simp

theorem localHop_false :
    localHopOperator * cantorState false = cantorState true := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localHopOperator, cantorState, state_false, state_true,
      a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

theorem localHop_true :
    localHopOperator * cantorState true = cantorState false := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localHopOperator, cantorState, state_false, state_true,
      a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

theorem localParity_false :
    localParityOperator * cantorState false = cantorState false := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localParityOperator, localVacuumProjection,
      localOccupiedProjection, cantorState, state_false, state_true,
      a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

theorem localParity_true :
    localParityOperator * cantorState true = -cantorState true := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localParityOperator, localVacuumProjection,
      localOccupiedProjection, cantorState, state_false, state_true,
      a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

theorem localPhase_false :
    localPhaseOperator * cantorState false = cantorState true := by
  unfold localPhaseOperator
  rw [Matrix.mul_assoc, localParity_false, localHop_false]

theorem localPhase_true :
    localPhaseOperator * cantorState true = -cantorState false := by
  unfold localPhaseOperator
  rw [Matrix.mul_assoc, localParity_true]
  calc
    localHopOperator * -cantorState true =
        -(localHopOperator * cantorState true) := by simp
    _ = -cantorState false := by rw [localHop_true]

end InfoGeometry.Canonical.CantorLocalCl11HopParity
