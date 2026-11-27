/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

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

/-- Elementary one-body fermion scattering / pair-density operator
$B_{\alpha\beta} = a_\alpha^\dagger a_\beta$. -/
def scatteringOp (α β : Index) : AlgebraType :=
  car.adag α * car.a β

@[simp] theorem scatteringOp_diag (α : Index) :
    car.scatteringOp α α = car.numberOp α := rfl

/-- Exact commutator of a one-body scattering operator `a_α† a_β` with a two-quasiparticle
creation operator `a_γ† a_δ†`. -/
theorem comm_scatteringOp_pairCreation (α β γ δ : Index) :
    comm (car.scatteringOp α β) (car.adag γ * car.adag δ) =
      (if β = γ then 1 else 0 : AlgebraType) * (car.adag α * car.adag δ) -
        (if β = δ then 1 else 0) * (car.adag α * car.adag γ) := by
  have ha_adag (i j : Index) :
      car.a i * car.adag j = (if i = j then 1 else 0) - car.adag j * car.a i :=
    eq_sub_of_add_eq (car.anticomm_a_adag i j)
  have hadag (i j : Index) : car.adag i * car.adag j = -(car.adag j * car.adag i) :=
    eq_neg_of_add_eq_zero_left (car.anticomm_adag_adag i j)
  dsimp [comm, scatteringOp]
  calc
    (car.adag α * car.a β) * (car.adag γ * car.adag δ) -
        (car.adag γ * car.adag δ) * (car.adag α * car.a β)
      = car.adag α * ((car.a β * car.adag γ) * car.adag δ) -
          (car.adag γ * (car.adag δ * car.adag α)) * car.a β := by noncomm_ring
    _ = car.adag α * (((if β = γ then 1 else 0) - car.adag γ * car.a β) * car.adag δ) -
          (car.adag γ * (-(car.adag α * car.adag δ))) * car.a β := by
        rw [ha_adag β γ, hadag δ α]
    _ = (if β = γ then 1 else 0 : AlgebraType) * (car.adag α * car.adag δ) -
          (car.adag α * car.adag γ) * (car.a β * car.adag δ) +
          (car.adag γ * car.adag α) * car.adag δ * car.a β := by
        split_ifs <;> noncomm_ring
    _ = (if β = γ then 1 else 0 : AlgebraType) * (car.adag α * car.adag δ) -
          (car.adag α * car.adag γ) * ((if β = δ then 1 else 0) - car.adag δ * car.a β) -
          (car.adag α * car.adag γ) * car.adag δ * car.a β := by
        rw [ha_adag β δ, hadag γ α]
        split_ifs <;> noncomm_ring
    _ = (if β = γ then 1 else 0 : AlgebraType) * (car.adag α * car.adag δ) -
          (if β = δ then 1 else 0) * (car.adag α * car.adag γ) := by
        split_ifs <;> noncomm_ring

/-- Exact commutator of a two-quasiparticle annihilation operator `a_β a_α` with a one-body
scattering operator `a_γ† a_δ`. -/
theorem comm_pairAnnihilation_scatteringOp (α β γ δ : Index) :
    comm (car.a β * car.a α) (car.scatteringOp γ δ) =
      (if α = γ then 1 else 0 : AlgebraType) * (car.a β * car.a δ) -
        (if β = γ then 1 else 0) * (car.a α * car.a δ) := by
  have ha_adag (i j : Index) :
      car.a i * car.adag j = (if i = j then 1 else 0) - car.adag j * car.a i :=
    eq_sub_of_add_eq (car.anticomm_a_adag i j)
  have haa (i j : Index) : car.a i * car.a j = -(car.a j * car.a i) :=
    eq_neg_of_add_eq_zero_left (car.anticomm_a_a i j)
  dsimp [comm, scatteringOp]
  calc
    (car.a β * car.a α) * (car.adag γ * car.a δ) -
        (car.adag γ * car.a δ) * (car.a β * car.a α)
      = car.a β * (car.a α * car.adag γ) * car.a δ -
          car.adag γ * ((car.a δ * car.a β) * car.a α) := by noncomm_ring
    _ = car.a β * ((if α = γ then 1 else 0) - car.adag γ * car.a α) * car.a δ -
          car.adag γ * ((-(car.a β * car.a δ)) * car.a α) := by
        rw [ha_adag α γ, haa δ β]
    _ = (if α = γ then 1 else 0 : AlgebraType) * (car.a β * car.a δ) -
          (car.a β * car.adag γ) * (car.a α * car.a δ) +
          car.adag γ * car.a β * (car.a δ * car.a α) := by
        split_ifs <;> noncomm_ring
    _ = (if α = γ then 1 else 0 : AlgebraType) * (car.a β * car.a δ) -
          ((if β = γ then 1 else 0) - car.adag γ * car.a β) * (car.a α * car.a δ) -
          car.adag γ * car.a β * (car.a α * car.a δ) := by
        rw [ha_adag β γ, haa δ α]
        split_ifs <;> noncomm_ring
    _ = (if α = γ then 1 else 0 : AlgebraType) * (car.a β * car.a δ) -
          (if β = γ then 1 else 0) * (car.a α * car.a δ) := by
        split_ifs <;> noncomm_ring

/-- Exact `gl(N)` commutator of two one-body fermion scattering operators. -/
theorem comm_scatteringOp_scatteringOp (α β γ δ : Index) :
    comm (car.scatteringOp α β) (car.scatteringOp γ δ) =
      (if β = γ then 1 else 0 : AlgebraType) * car.scatteringOp α δ -
        (if α = δ then 1 else 0) * car.scatteringOp γ β := by
  have ha_adag (i j : Index) :
      car.a i * car.adag j = (if i = j then 1 else 0) - car.adag j * car.a i :=
    eq_sub_of_add_eq (car.anticomm_a_adag i j)
  have hadag (i j : Index) : car.adag i * car.adag j = -(car.adag j * car.adag i) :=
    eq_neg_of_add_eq_zero_left (car.anticomm_adag_adag i j)
  have haa (i j : Index) : car.a i * car.a j = -(car.a j * car.a i) :=
    eq_neg_of_add_eq_zero_left (car.anticomm_a_a i j)
  dsimp [comm, scatteringOp]
  calc
    (car.adag α * car.a β) * (car.adag γ * car.a δ) -
        (car.adag γ * car.a δ) * (car.adag α * car.a β)
      = car.adag α * (car.a β * car.adag γ) * car.a δ -
          car.adag γ * (car.a δ * car.adag α) * car.a β := by noncomm_ring
    _ = car.adag α * ((if β = γ then 1 else 0) - car.adag γ * car.a β) * car.a δ -
          car.adag γ * ((if δ = α then 1 else 0) - car.adag α * car.a δ) * car.a β := by
        rw [ha_adag β γ, ha_adag δ α]
    _ = (if β = γ then 1 else 0 : AlgebraType) * (car.adag α * car.a δ) -
          (if α = δ then 1 else 0) * (car.adag γ * car.a β) -
          (car.adag α * car.adag γ) * (car.a β * car.a δ) +
          (car.adag γ * car.adag α) * (car.a δ * car.a β) := by
        have heq : (δ = α) = (α = δ) := propext eq_comm
        simp only [heq]
        split_ifs <;> noncomm_ring
    _ = (if β = γ then 1 else 0 : AlgebraType) * (car.adag α * car.a δ) -
          (if α = δ then 1 else 0) * (car.adag γ * car.a β) := by
        rw [hadag α γ, haa β δ]
        noncomm_ring

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
