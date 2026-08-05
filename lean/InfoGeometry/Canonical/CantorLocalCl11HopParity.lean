import InfoGeometry.Canonical.SplitCliffordCantorFock

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
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localVacuumProjection, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localOccupiedProjection_sq :
    localOccupiedProjection * localOccupiedProjection = localOccupiedProjection := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localOccupiedProjection, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localVacuumProjection_mul_localOccupiedProjection :
    localVacuumProjection * localOccupiedProjection = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localVacuumProjection, localOccupiedProjection, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localOccupiedProjection_mul_localVacuumProjection :
    localOccupiedProjection * localVacuumProjection = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localVacuumProjection, localOccupiedProjection, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localHopOperator_sq :
    localHopOperator * localHopOperator = (1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localHopOperator, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localParityOperator_sq :
    localParityOperator * localParityOperator = (1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localParityOperator, localVacuumProjection,
      localOccupiedProjection, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localHop_anticommutes_localParity :
    localHopOperator * localParityOperator =
      -(localParityOperator * localHopOperator) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localHopOperator, localParityOperator,
      localVacuumProjection, localOccupiedProjection, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localPhaseOperator_sq :
    localPhaseOperator * localPhaseOperator = -(1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localPhaseOperator, localHopOperator, localParityOperator,
      localVacuumProjection, localOccupiedProjection, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

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

end InfoGeometry.Canonical.CantorLocalCl11HopParity
