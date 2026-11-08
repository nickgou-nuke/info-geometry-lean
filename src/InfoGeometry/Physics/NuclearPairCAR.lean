import InfoGeometry.Physics.NuclearQuasiparticleCARBridge

namespace InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR

variable {Index AlgebraType : Type*} [DecidableEq Index] [Ring AlgebraType]
variable (car : QuasiparticleCAR Index AlgebraType)

theorem pair_commutator_normal_order
    (first second third fourth : Index) :
    comm (car.a second * car.a first) (car.adag third * car.adag fourth) =
      (if first = third then 1 else 0 : AlgebraType) *
          (if second = fourth then 1 else 0) -
        (if second = third then 1 else 0) *
          (if first = fourth then 1 else 0) -
        (if first = third then 1 else 0) * car.adag fourth * car.a second +
        (if second = third then 1 else 0) * car.adag fourth * car.a first +
        (if first = fourth then 1 else 0) * car.adag third * car.a second -
        (if second = fourth then 1 else 0) * car.adag third * car.a first := by
  have normalOrder (annihilator creator : Index) :
      car.a annihilator * car.adag creator =
        (if annihilator = creator then 1 else 0) -
          car.adag creator * car.a annihilator := by
    exact eq_sub_of_add_eq (car.anticomm_a_adag annihilator creator)
  calc
    _ = car.a second *
          (car.a first * car.adag third + car.adag third * car.a first) *
            car.adag fourth -
        (car.a second * car.adag third + car.adag third * car.a second) *
          car.a first * car.adag fourth +
        car.adag third * car.a second *
          (car.a first * car.adag fourth + car.adag fourth * car.a first) -
        car.adag third *
          (car.a second * car.adag fourth + car.adag fourth * car.a second) *
            car.a first := by
      unfold comm
      noncomm_ring
    _ = _ := by
      rw [car.anticomm_a_adag, car.anticomm_a_adag,
        car.anticomm_a_adag, car.anticomm_a_adag]
      split_ifs <;> simp only [mul_one, one_mul, mul_zero, zero_mul]
      all_goals
        try rw [normalOrder second fourth]
        try rw [normalOrder first fourth]
        try split_ifs
        all_goals noncomm_ring

theorem pair_commutator_same (first second : Index) (distinct : first ≠ second) :
    comm (car.a second * car.a first) (car.adag first * car.adag second) =
      1 - car.numberOp first - car.numberOp second := by
  rw [car.pair_commutator_normal_order]
  simp [distinct, Ne.symm distinct, numberOp]
  abel

section LinearCombinations

variable [Algebra ℝ AlgebraType]

theorem bogoliubov_anticommutator (first second : Index) (particle hole : ℝ) :
    (particle • car.a first + hole • car.adag second) *
        (particle • car.adag first + hole • car.a second) +
      (particle • car.adag first + hole • car.a second) *
        (particle • car.a first + hole • car.adag second) =
      (particle ^ 2 + hole ^ 2) • (1 : AlgebraType) := by
  calc
    _ = particle ^ 2 •
          (car.a first * car.adag first + car.adag first * car.a first) +
        hole ^ 2 •
          (car.a second * car.adag second + car.adag second * car.a second) +
        (particle * hole) •
          (car.a first * car.a second + car.a second * car.a first) +
        (particle * hole) •
          (car.adag second * car.adag first + car.adag first * car.adag second) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        smul_smul, smul_add]
      module
    _ = _ := by
      rw [car.anticomm_a_adag, car.anticomm_a_adag,
        car.anticomm_a_a, car.anticomm_adag_adag]
      simp [add_smul]

theorem pair_mode_commutator (first second : Index) (distinct : first ≠ second)
    (forward backward : ℝ) :
    comm
        (forward • (car.a second * car.a first) -
          backward • (car.adag first * car.adag second))
        (forward • (car.adag first * car.adag second) -
          backward • (car.a second * car.a first)) =
      (forward ^ 2 - backward ^ 2) •
        (1 - car.numberOp first - car.numberOp second) := by
  calc
    _ = (forward ^ 2 - backward ^ 2) •
        comm (car.a second * car.a first) (car.adag first * car.adag second) := by
      unfold comm
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        smul_smul, sub_smul, smul_sub]
      module
    _ = _ := by rw [car.pair_commutator_same first second distinct]

theorem normalized_pair_mode_correction
    (first second : Index) (distinct : first ≠ second)
    (forward backward : ℝ) (normalized : forward ^ 2 - backward ^ 2 = 1) :
    comm
        (forward • (car.a second * car.a first) -
          backward • (car.adag first * car.adag second))
        (forward • (car.adag first * car.adag second) -
          backward • (car.a second * car.a first)) - 1 =
      -(car.numberOp first + car.numberOp second) := by
  rw [car.pair_mode_commutator first second distinct, normalized, one_smul]
  abel

end LinearCombinations

end InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR
