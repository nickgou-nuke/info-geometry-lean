/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Physics.NuclearPairCAR
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

noncomputable section

namespace InfoGeometry.Physics.SolovievPhononCorrections

open scoped BigOperators
open NuclearQuasiparticleCAR
open NuclearQuasiparticleCAR.QuasiparticleCAR

variable {Index AlgebraType : Type*} [DecidableEq Index] [Ring AlgebraType]
variable [Algebra ℂ AlgebraType]

def phononCreation (car : QuasiparticleCAR Index AlgebraType)
    (first second : Index) (forward backward : ℂ) : AlgebraType :=
  forward • (car.adag first * car.adag second) -
    backward • (car.a second * car.a first)

def phononAnnihilation (car : QuasiparticleCAR Index AlgebraType)
    (first second : Index) (forward backward : ℂ) : AlgebraType :=
  starRingEnd ℂ forward • (car.a second * car.a first) -
    starRingEnd ℂ backward • (car.adag first * car.adag second)

theorem phonon_commutator (car : QuasiparticleCAR Index AlgebraType)
    (first second : Index) (distinct : first ≠ second) (forward backward : ℂ) :
    comm (phononAnnihilation car first second forward backward)
        (phononCreation car first second forward backward) =
      ((Complex.normSq forward - Complex.normSq backward : ℝ) : ℂ) •
        (1 - car.numberOp first - car.numberOp second) := by
  calc
    _ = (starRingEnd ℂ forward * forward - starRingEnd ℂ backward * backward) •
        comm (car.a second * car.a first) (car.adag first * car.adag second) := by
      unfold phononAnnihilation phononCreation NuclearQuasiparticleCAR.QuasiparticleCAR.comm
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        smul_smul, sub_smul, smul_sub]
      module
    _ = _ := by
      rw [car.pair_commutator_same first second distinct,
        Complex.ofReal_sub, Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_conj_mul_self]

theorem normalized_phonon_defect (car : QuasiparticleCAR Index AlgebraType)
    (first second : Index) (distinct : first ≠ second) (forward backward : ℂ)
    (normalized : Complex.normSq forward - Complex.normSq backward = 1) :
    comm (phononAnnihilation car first second forward backward)
        (phononCreation car first second forward backward) - 1 =
      -(car.numberOp first + car.numberOp second) := by
  rw [phonon_commutator car first second distinct, normalized]
  simp only [Complex.ofReal_one, one_smul]
  abel

def circularAmplitude (amplitude sign : ℝ) : ℂ :=
  ((amplitude / (2 * Real.sqrt 2) : ℝ) : ℂ) * (1 + Complex.I * (sign : ℂ))

theorem circularAmplitude_normSq (amplitude sign : ℝ) (sign_sq : sign ^ 2 = 1) :
    Complex.normSq (circularAmplitude amplitude sign) = amplitude ^ 2 / 4 := by
  have root_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have phase_norm : Complex.normSq (1 + Complex.I * (sign : ℂ)) = 2 := by
    simp [Complex.normSq_apply]
    nlinarith [sign_sq]
  unfold circularAmplitude
  rw [Complex.normSq_mul, Complex.normSq_ofReal, phase_norm]
  rw [← sq]
  rw [div_pow, mul_pow, root_sq]
  ring

theorem circular_phonon_commutator (car : QuasiparticleCAR Index AlgebraType)
    (first second : Index) (distinct : first ≠ second)
    (forward backward sign : ℝ) (sign_sq : sign ^ 2 = 1) :
    comm
        (phononAnnihilation car first second
          (circularAmplitude forward sign) (circularAmplitude backward (-sign)))
        (phononCreation car first second
          (circularAmplitude forward sign) (circularAmplitude backward (-sign))) =
      (((forward ^ 2 - backward ^ 2) / 4 : ℝ) : ℂ) •
        (1 - car.numberOp first - car.numberOp second) := by
  rw [phonon_commutator car first second distinct,
    circularAmplitude_normSq forward sign sign_sq,
    circularAmplitude_normSq backward (-sign) (by simpa using sign_sq)]
  congr 2
  ring

section Vacuum

variable {State : Type*} [AddCommGroup State] [Module ℂ State]

theorem normalized_phonon_on_vacuum
    (car : QuasiparticleCAR Index (Module.End ℂ State))
    (first second : Index) (distinct : first ≠ second)
    (forward backward : ℂ)
    (normalized : Complex.normSq forward - Complex.normSq backward = 1)
    (vacuum : State) (first_empty : car.a first vacuum = 0)
    (second_empty : car.a second vacuum = 0) :
    comm (phononAnnihilation car first second forward backward)
        (phononCreation car first second forward backward) vacuum = vacuum := by
  rw [phonon_commutator car first second distinct, normalized]
  simp [numberOp, Module.End.mul_apply, first_empty, second_empty]

end Vacuum

/-- Single-pair Tamm--Dancoff phonon creation (`backward = 0` specialization of
`phononCreation`). -/
def tdaSinglePairCreation (car : QuasiparticleCAR Index AlgebraType)
    (first second : Index) (amp : ℂ) : AlgebraType :=
  phononCreation car first second amp 0

/-- Single-pair Tamm--Dancoff phonon annihilation (`backward = 0` specialization of
`phononAnnihilation`). -/
def tdaSinglePairAnnihilation (car : QuasiparticleCAR Index AlgebraType)
    (first second : Index) (amp : ℂ) : AlgebraType :=
  phononAnnihilation car first second amp 0

/-- Tamm--Dancoff (`backward = 0`) single-pair commutator: pure forward Pauli-blocking
law with no backward ground-state correlation subtraction. -/
theorem tdaSinglePair_commutator (car : QuasiparticleCAR Index AlgebraType)
    (first second : Index) (distinct : first ≠ second) (amp : ℂ) :
    comm (tdaSinglePairAnnihilation car first second amp)
        (tdaSinglePairCreation car first second amp) =
      ((Complex.normSq amp : ℝ) : ℂ) • (1 - car.numberOp first - car.numberOp second) := by
  simpa [tdaSinglePairAnnihilation, tdaSinglePairCreation] using
    phonon_commutator car first second distinct amp 0

/-- **Single-Pair Pauli Obstruction Generates the `sl₂` Seniority / Quasispin Eigenvalue `-2`**:
commuting the Pauli-blocking phonon commutator `[Q, Q†] = 1 - N_i - N_j` (when `|amp|² = 1`)
with `Q†` yields the exact grade-`+2` quasispin raising relation `[[Q, Q†], Q†] = -2 Q†`. -/
theorem tdaSinglePair_double_commutator_quasispin
    (car : QuasiparticleCAR Index AlgebraType)
    (first second : Index) (distinct : first ≠ second)
    (amp : ℂ) (hnorm : Complex.normSq amp = 1) :
    comm (comm (tdaSinglePairAnnihilation car first second amp)
        (tdaSinglePairCreation car first second amp))
      (tdaSinglePairCreation car first second amp) =
      (-2 : ℂ) • tdaSinglePairCreation car first second amp := by
  rw [tdaSinglePair_commutator car first second distinct amp, hnorm]
  simp only [Complex.ofReal_one, one_smul]
  dsimp [tdaSinglePairCreation, phononCreation]
  rw [zero_smul, sub_zero]
  have h1 : comm (1 : AlgebraType) (car.adag first * car.adag second) = 0 := by
    simp [QuasiparticleCAR.comm]
  have hni :
      comm (car.numberOp first) (car.adag first * car.adag second) =
        car.adag first * car.adag second := by
    rw [← car.scatteringOp_diag first, car.comm_scatteringOp_pairCreation]
    simp [distinct]
  have hnj :
      comm (car.numberOp second) (car.adag first * car.adag second) =
        car.adag first * car.adag second := by
    rw [← car.scatteringOp_diag second, car.comm_scatteringOp_pairCreation]
    simp [Ne.symm distinct, car.adag_mul_adag_comm first second]
  have hlin :
      comm (1 - car.numberOp first - car.numberOp second)
          (amp • (car.adag first * car.adag second)) =
        amp • (comm (1 : AlgebraType) (car.adag first * car.adag second) -
          comm (car.numberOp first) (car.adag first * car.adag second) -
          comm (car.numberOp second) (car.adag first * car.adag second)) := by
    simp only [QuasiparticleCAR.comm, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
    module
  rw [hlin, h1, hni, hnj]
  simp only [zero_sub, sub_eq_add_neg, smul_add, smul_neg]
  module

/-- Induced antisymmetrized amplitude matrix from commuting `B(ϕ)` with `X†(ψ)`. -/
def tdScatteringTransform {Idx : Type*} [Fintype Idx]
    (ϕ ψ : Idx → Idx → ℂ) (α δ : Idx) : ℂ :=
  ∑ β : Idx, (ϕ α β * ψ β δ - ϕ δ β * ψ β α)

theorem tdScatteringTransform_antisymm {Idx : Type*} [Fintype Idx]
    (ϕ ψ : Idx → Idx → ℂ) (α δ : Idx) :
    tdScatteringTransform ϕ ψ δ α = -tdScatteringTransform ϕ ψ α δ := by
  dsimp [tdScatteringTransform]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

section TammDancoffMultiMode

variable [Fintype Index]

/-- Multi-mode Tamm--Dancoff two-quasiparticle phonon creation operator
`X†(φ) = (1/2) ∑_{α, β} φ α β • (a_α† a_β†)`. For antisymmetric `φ β α = -φ α β`,
the factor `1/2` prevents double counting over `α < β`. -/
def tdPhononCreation (car : QuasiparticleCAR Index AlgebraType)
    (φ : Index → Index → ℂ) : AlgebraType :=
  (1 / 2 : ℂ) • ∑ α : Index, ∑ β : Index, φ α β • (car.adag α * car.adag β)

/-- Multi-mode Tamm--Dancoff two-quasiparticle phonon annihilation operator
`X(ψ) = (1/2) ∑_{α, β} conj(ψ α β) • (a_β a_α)`. -/
def tdPhononAnnihilation (car : QuasiparticleCAR Index AlgebraType)
    (ψ : Index → Index → ℂ) : AlgebraType :=
  (1 / 2 : ℂ) • ∑ α : Index, ∑ β : Index,
    starRingEnd ℂ (ψ α β) • (car.a β * car.a α)

/-- Linear combination of one-body fermion scattering operators
`B(ϕ) = ∑_{α, β} ϕ α β • a_α† a_β`. -/
def scatteringCombination (car : QuasiparticleCAR Index AlgebraType)
    (ϕ : Index → Index → ℂ) : AlgebraType :=
  ∑ α : Index, ∑ β : Index, ϕ α β • car.scatteringOp α β

omit [Algebra ℂ AlgebraType] in
private theorem comm_sum_left {ι : Type*} (s : Finset ι) (f : ι → AlgebraType)
    (y : AlgebraType) :
    comm (∑ i ∈ s, f i) y = ∑ i ∈ s, comm (f i) y := by
  simp only [QuasiparticleCAR.comm, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

omit [Algebra ℂ AlgebraType] in
private theorem comm_sum_right {ι : Type*} (s : Finset ι) (x : AlgebraType)
    (g : ι → AlgebraType) :
    comm x (∑ i ∈ s, g i) = ∑ i ∈ s, comm x (g i) := by
  simp only [QuasiparticleCAR.comm, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

private theorem comm_smul_left (c : ℂ) (x y : AlgebraType) :
    comm (c • x) y = c • comm x y := by
  simp only [QuasiparticleCAR.comm, smul_mul_assoc, mul_smul_comm, smul_sub]

private theorem comm_smul_right (c : ℂ) (x y : AlgebraType) :
    comm x (c • y) = c • comm x y := by
  simp only [QuasiparticleCAR.comm, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- **Multi-mode Tamm--Dancoff Phonon Commutator** (`2203.03780v3.pdf` §2.1 Eq. 6a):
for antisymmetric two-quasiparticle amplitudes `ψ β α = -ψ α β` and `φ β α = -φ α β`,
`[X(ψ), X†(φ)] = (1/2 ∑_{α,β} ψ̄_{αβ} φ_{αβ}) · 1 - ∑_{α,β,γ} ψ̄_{αβ} φ_{αγ} a_γ† a_β`. -/
theorem tdPhonon_commutator_exact (car : QuasiparticleCAR Index AlgebraType)
    (ψ φ : Index → Index → ℂ)
    (hψ : ∀ α β, ψ β α = -ψ α β) (hφ : ∀ α β, φ β α = -φ α β) :
    comm (tdPhononAnnihilation car ψ) (tdPhononCreation car φ) =
      ((1 / 2 : ℂ) * ∑ α : Index, ∑ β : Index, starRingEnd ℂ (ψ α β) * φ α β) •
          (1 : AlgebraType) -
        ∑ α : Index, ∑ β : Index, ∑ γ : Index,
          (starRingEnd ℂ (ψ α β) * φ α γ) • car.scatteringOp γ β := by
  let c : Index → Index → ℂ := fun α β => starRingEnd ℂ (ψ α β)
  have hc : ∀ α β, c β α = -c α β := fun α β => by
    dsimp [c]; rw [hψ α β, map_neg]
  have hexpand :
      comm (tdPhononAnnihilation car ψ) (tdPhononCreation car φ) =
        ((1 / 2 : ℂ) * (1 / 2 : ℂ)) •
          ∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
            (c α β * φ γ δ) • comm (car.a β * car.a α) (car.adag γ * car.adag δ) := by
    dsimp [tdPhononAnnihilation, tdPhononCreation, c]
    rw [comm_smul_left, comm_smul_right, smul_smul]
    congr 1
    rw [comm_sum_left]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [comm_sum_left]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [comm_smul_left, comm_sum_right, Finset.smul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [comm_sum_right, Finset.smul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [comm_smul_right, smul_smul]
  have h1 :
      (∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
        (c α β * φ γ δ) •
          ((if α = γ then 1 else 0 : AlgebraType) * (if β = δ then 1 else 0))) =
        (∑ α : Index, ∑ β : Index, c α β * φ α β) • (1 : AlgebraType) := by
    trans ∑ α : Index, ∑ β : Index, (c α β * φ α β) • (1 : AlgebraType)
    · refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      trans ∑ γ : Index, ∑ δ : Index,
          (if α = γ then (if β = δ then (c α β * φ γ δ) • (1 : AlgebraType) else 0) else 0)
      · refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
        split_ifs <;> simp
      · trans ∑ γ : Index, (if α = γ then (c α β * φ γ β) • (1 : AlgebraType) else 0)
        · refine Finset.sum_congr rfl fun γ _ => ?_
          split_ifs <;> simp
        · simp
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.sum_smul]
  have h2 :
      (∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
        (c α β * φ γ δ) •
          ((if β = γ then 1 else 0 : AlgebraType) * (if α = δ then 1 else 0))) =
        -(∑ α : Index, ∑ β : Index, c α β * φ α β) • (1 : AlgebraType) := by
    trans ∑ α : Index, ∑ β : Index, (c α β * φ β α) • (1 : AlgebraType)
    · refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      trans ∑ γ : Index, ∑ δ : Index,
          (if β = γ then (if α = δ then (c α β * φ γ δ) • (1 : AlgebraType) else 0) else 0)
      · refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
        split_ifs <;> simp
      · trans ∑ γ : Index, (if β = γ then (c α β * φ γ α) • (1 : AlgebraType) else 0)
        · refine Finset.sum_congr rfl fun γ _ => ?_
          split_ifs <;> simp
        · simp
    · rw [neg_smul, Finset.sum_smul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.sum_smul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [hφ α β, mul_neg, neg_smul]
  have h3 :
      (∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
        (c α β * φ γ δ) • ((if α = γ then 1 else 0 : AlgebraType) * car.adag δ * car.a β)) =
        ∑ α : Index, ∑ β : Index, ∑ γ : Index,
          (c α β * φ α γ) • car.scatteringOp γ β := by
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    trans ∑ γ : Index, ∑ δ : Index,
        (if α = γ then (c α β * φ γ δ) • car.scatteringOp δ β else 0)
    · refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
      split_ifs <;> simp [scatteringOp]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun γ _ => ?_
      simp
  have h4 :
      (∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
        (c α β * φ γ δ) • ((if β = γ then 1 else 0 : AlgebraType) * car.adag δ * car.a α)) =
        -(∑ α : Index, ∑ β : Index, ∑ γ : Index,
          (c α β * φ α γ) • car.scatteringOp γ β) := by
    calc
      _ = ∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
            (if β = γ then (c α β * φ γ δ) • car.scatteringOp δ α else 0) := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
            Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
          split_ifs <;> simp [scatteringOp]
      _ = ∑ α : Index, ∑ β : Index, ∑ δ : Index,
            (c α β * φ β δ) • car.scatteringOp δ α := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun δ _ => ?_
          simp
      _ = ∑ β : Index, ∑ α : Index, ∑ δ : Index,
            (c α β * φ β δ) • car.scatteringOp δ α := Finset.sum_comm
      _ = -(∑ α : Index, ∑ β : Index, ∑ γ : Index,
            (c α β * φ α γ) • car.scatteringOp γ β) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [hc α β, neg_mul, neg_smul]
  have h5 :
      (∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
        (c α β * φ γ δ) • ((if α = δ then 1 else 0 : AlgebraType) * car.adag γ * car.a β)) =
        -(∑ α : Index, ∑ β : Index, ∑ γ : Index,
          (c α β * φ α γ) • car.scatteringOp γ β) := by
    calc
      _ = ∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
            (if α = δ then (c α β * φ γ δ) • car.scatteringOp γ β else 0) := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
            Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
          split_ifs <;> simp [scatteringOp]
      _ = ∑ α : Index, ∑ β : Index, ∑ γ : Index,
            (c α β * φ γ α) • car.scatteringOp γ β := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
            Finset.sum_congr rfl fun γ _ => ?_
          simp
      _ = -(∑ α : Index, ∑ β : Index, ∑ γ : Index,
            (c α β * φ α γ) • car.scatteringOp γ β) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [hφ α γ, mul_neg, neg_smul]
  have h6 :
      (∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
        (c α β * φ γ δ) • ((if β = δ then 1 else 0 : AlgebraType) * car.adag γ * car.a α)) =
        ∑ α : Index, ∑ β : Index, ∑ γ : Index,
          (c α β * φ α γ) • car.scatteringOp γ β := by
    calc
      _ = ∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
            (if β = δ then (c α β * φ γ δ) • car.scatteringOp γ α else 0) := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
            Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
          split_ifs <;> simp [scatteringOp]
      _ = ∑ α : Index, ∑ β : Index, ∑ γ : Index,
            (c α β * φ γ β) • car.scatteringOp γ α := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
            Finset.sum_congr rfl fun γ _ => ?_
          simp
      _ = ∑ β : Index, ∑ α : Index, ∑ γ : Index,
            (c α β * φ γ β) • car.scatteringOp γ α := Finset.sum_comm
      _ = ∑ α : Index, ∑ β : Index, ∑ γ : Index,
            (c α β * φ α γ) • car.scatteringOp γ β := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
            Finset.sum_congr rfl fun γ _ => ?_
          rw [hc α β, hφ α γ, neg_mul, mul_neg, neg_neg]
  have hinner :
      (∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
        (c α β * φ γ δ) • comm (car.a β * car.a α) (car.adag γ * car.adag δ)) =
        (2 • (∑ α : Index, ∑ β : Index, c α β * φ α β)) • (1 : AlgebraType) -
          (4 : ℂ) • ∑ α : Index, ∑ β : Index, ∑ γ : Index,
            (c α β * φ α γ) • car.scatteringOp γ β := by
    simp only [car.pair_commutator_normal_order, smul_sub, smul_add,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [h1, h2, h3, h4, h5, h6]
    module
  rw [hexpand, hinner, smul_sub, smul_smul, smul_smul]
  have hc4 : (1 / 2 : ℂ) * (1 / 2) * 4 = 1 := by norm_num
  rw [hc4, one_smul]
  congr 1
  congr 1
  simp only [c, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **Multi-mode Scattering--Phonon Commutator** (`2203.03780v3.pdf` §2.1 Eq. 6b):
`[B(ϕ), X†(ψ)] = X†(tdScatteringTransform ϕ ψ)`. -/
theorem comm_scatteringCombination_tdPhononCreation
    (car : QuasiparticleCAR Index AlgebraType)
    (ϕ ψ : Index → Index → ℂ) (hψ : ∀ α β, ψ β α = -ψ α β) :
    comm (scatteringCombination car ϕ) (tdPhononCreation car ψ) =
      tdPhononCreation car (tdScatteringTransform ϕ ψ) := by
  have hexpand :
      comm (scatteringCombination car ϕ) (tdPhononCreation car ψ) =
        (1 / 2 : ℂ) • ∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
          (ϕ α β * ψ γ δ) • comm (car.scatteringOp α β) (car.adag γ * car.adag δ) := by
    dsimp [scatteringCombination, tdPhononCreation]
    rw [comm_smul_right]
    congr 1
    rw [comm_sum_left]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [comm_sum_left]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [comm_smul_left, comm_sum_right, Finset.smul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [comm_sum_right, Finset.smul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [comm_smul_right, smul_smul]
  let S : AlgebraType :=
    ∑ α : Index, ∑ δ : Index, (∑ β : Index, ϕ α β * ψ β δ) • (car.adag α * car.adag δ)
  have hS_lhs :
      (∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
        (ϕ α β * ψ γ δ) • comm (car.scatteringOp α β) (car.adag γ * car.adag δ)) =
        (2 : ℂ) • S := by
    have ht1 :
        (∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
          (ϕ α β * ψ γ δ) •
            ((if β = γ then 1 else 0 : AlgebraType) * (car.adag α * car.adag δ))) = S := by
      dsimp [S]
      calc
        _ = ∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
              (if β = γ then (ϕ α β * ψ γ δ) • (car.adag α * car.adag δ) else 0) := by
            refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
              Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
            split_ifs <;> simp
        _ = ∑ α : Index, ∑ β : Index, ∑ δ : Index,
              (ϕ α β * ψ β δ) • (car.adag α * car.adag δ) := by
            refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun δ _ => ?_
            simp
        _ = ∑ α : Index, ∑ δ : Index, ∑ β : Index,
              (ϕ α β * ψ β δ) • (car.adag α * car.adag δ) := by
            refine Finset.sum_congr rfl fun α _ => Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun δ _ => ?_
            rw [← Finset.sum_smul]
    have ht2 :
        (∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
          (ϕ α β * ψ γ δ) •
            ((if β = δ then 1 else 0 : AlgebraType) * (car.adag α * car.adag γ))) = -S := by
      dsimp [S]
      calc
        _ = ∑ α : Index, ∑ β : Index, ∑ γ : Index, ∑ δ : Index,
              (if β = δ then (ϕ α β * ψ γ δ) • (car.adag α * car.adag γ) else 0) := by
            refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
              Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
            split_ifs <;> simp
        _ = ∑ α : Index, ∑ β : Index, ∑ γ : Index,
              (ϕ α β * ψ γ β) • (car.adag α * car.adag γ) := by
            refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
              Finset.sum_congr rfl fun γ _ => ?_
            simp
        _ = -∑ α : Index, ∑ β : Index, ∑ γ : Index,
              (ϕ α β * ψ β γ) • (car.adag α * car.adag γ) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun α _ => ?_
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun β _ => ?_
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun γ _ => ?_
            rw [hψ β γ, mul_neg, neg_smul]
        _ = -∑ α : Index, ∑ γ : Index, ∑ β : Index,
              (ϕ α β * ψ β γ) • (car.adag α * car.adag γ) := by
            congr 1; refine Finset.sum_congr rfl fun α _ => Finset.sum_comm
        _ = -S := by
            congr 1
            refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
            rw [← Finset.sum_smul]
    simp_rw [car.comm_scatteringOp_pairCreation, smul_sub, Finset.sum_sub_distrib, ht1, ht2]
    module
  have hS_rhs :
      (∑ α : Index, ∑ δ : Index,
        tdScatteringTransform ϕ ψ α δ • (car.adag α * car.adag δ)) = (2 : ℂ) • S := by
    have hswap :
        (∑ α : Index, ∑ δ : Index,
          (-(∑ β : Index, ϕ δ β * ψ β α)) • (car.adag α * car.adag δ)) = S := by
      calc
        _ = ∑ δ : Index, ∑ α : Index,
              (-(∑ β : Index, ϕ δ β * ψ β α)) • (car.adag α * car.adag δ) := Finset.sum_comm
        _ = ∑ α : Index, ∑ δ : Index,
              (∑ β : Index, ϕ α β * ψ β δ) • (car.adag α * car.adag δ) := by
            refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun α _ => ?_
            rw [car.adag_mul_adag_comm δ α, smul_neg, neg_smul, neg_neg]
    dsimp [tdScatteringTransform, S]
    simp_rw [Finset.sum_sub_distrib, sub_smul]
    have hsplit :
        (∑ α : Index, ∑ δ : Index,
          ((∑ β : Index, ϕ α β * ψ β δ) • (car.adag α * car.adag δ) -
            (∑ β : Index, ϕ δ β * ψ β α) • (car.adag α * car.adag δ))) =
        (∑ α : Index, ∑ δ : Index,
          (∑ β : Index, ϕ α β * ψ β δ) • (car.adag α * car.adag δ)) +
        (∑ α : Index, ∑ δ : Index,
          (-(∑ β : Index, ϕ δ β * ψ β α)) • (car.adag α * car.adag δ)) := by
      simp_rw [sub_eq_add_neg, neg_smul, Finset.sum_add_distrib]
    rw [hsplit, hswap]
    module
  rw [hexpand, hS_lhs]
  dsimp [tdPhononCreation]
  rw [hS_rhs]

/-- One-body Pauli-blocking obstruction matrix `Γ_{γβ} = ∑_α conj(ψ_{αβ}) φ_{αγ}`
generated by commuting multi-mode Tamm--Dancoff phonons `[X(ψ), X†(φ)]`. -/
def tdPauliObstructionMatrix (ψ φ : Index → Index → ℂ) (γ β : Index) : ℂ :=
  ∑ α : Index, starRingEnd ℂ (ψ α β) * φ α γ

/-- The noncommutative Pauli-blocking obstruction `comm [X(ψ), X†(φ)] - c · 1` is
identically the negated one-body fermion scattering operator `-B(tdPauliObstructionMatrix ψ φ)`. -/
theorem tdPhonon_pauliObstruction_eq_neg_scattering
    (car : QuasiparticleCAR Index AlgebraType)
    (ψ φ : Index → Index → ℂ)
    (hψ : ∀ α β, ψ β α = -ψ α β) (hφ : ∀ α β, φ β α = -φ α β) :
    comm (tdPhononAnnihilation car ψ) (tdPhononCreation car φ) -
        ((1 / 2 : ℂ) * ∑ α : Index, ∑ β : Index, starRingEnd ℂ (ψ α β) * φ α β) •
          (1 : AlgebraType) =
      -scatteringCombination car (tdPauliObstructionMatrix ψ φ) := by
  rw [tdPhonon_commutator_exact car ψ φ hψ hφ, sub_sub_cancel_left]
  congr 1
  calc
    (∑ α : Index, ∑ β : Index, ∑ γ : Index,
        (starRingEnd ℂ (ψ α β) * φ α γ) • car.scatteringOp γ β)
      = ∑ α : Index, ∑ γ : Index, ∑ β : Index,
          (starRingEnd ℂ (ψ α β) * φ α γ) • car.scatteringOp γ β := by
        refine Finset.sum_congr rfl fun α _ => Finset.sum_comm
    _ = ∑ γ : Index, ∑ α : Index, ∑ β : Index,
          (starRingEnd ℂ (ψ α β) * φ α γ) • car.scatteringOp γ β := Finset.sum_comm
    _ = ∑ γ : Index, ∑ β : Index, ∑ α : Index,
          (starRingEnd ℂ (ψ α β) * φ α γ) • car.scatteringOp γ β := by
        refine Finset.sum_congr rfl fun γ _ => Finset.sum_comm
    _ = scatteringCombination car (tdPauliObstructionMatrix ψ φ) := by
        dsimp [scatteringCombination, tdPauliObstructionMatrix]
        refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun β _ => ?_
        rw [Finset.sum_smul]

/-- **Emergence of the Kantor / Jordan Triple Product from Pauli Blocking**:
commuting the Pauli-blocked Tamm--Dancoff commutator `[X(ψ), X†(φ)]` with a third
phonon creation `X†(χ)` closes back onto the grade-`+2` pair space with amplitude
`-tdScatteringTransform (tdPauliObstructionMatrix ψ φ) χ`. -/
theorem tdPhonon_double_commutator_exact
    (car : QuasiparticleCAR Index AlgebraType)
    (ψ φ χ : Index → Index → ℂ)
    (hψ : ∀ α β, ψ β α = -ψ α β) (hφ : ∀ α β, φ β α = -φ α β)
    (hχ : ∀ α β, χ β α = -χ α β) :
    comm (comm (tdPhononAnnihilation car ψ) (tdPhononCreation car φ))
        (tdPhononCreation car χ) =
      -tdPhononCreation car (tdScatteringTransform (tdPauliObstructionMatrix ψ φ) χ) := by
  let scalarNorm : ℂ :=
    (1 / 2 : ℂ) * ∑ α : Index, ∑ β : Index, starRingEnd ℂ (ψ α β) * φ α β
  have hsplit :
      comm (tdPhononAnnihilation car ψ) (tdPhononCreation car φ) =
        scalarNorm • (1 : AlgebraType) -
          scatteringCombination car (tdPauliObstructionMatrix ψ φ) := by
    calc
      comm (tdPhononAnnihilation car ψ) (tdPhononCreation car φ)
        = (comm (tdPhononAnnihilation car ψ) (tdPhononCreation car φ) -
            scalarNorm • (1 : AlgebraType)) + scalarNorm • (1 : AlgebraType) := by abel
      _ = -scatteringCombination car (tdPauliObstructionMatrix ψ φ) +
            scalarNorm • (1 : AlgebraType) := by
          rw [tdPhonon_pauliObstruction_eq_neg_scattering car ψ φ hψ hφ]
      _ = scalarNorm • (1 : AlgebraType) -
            scatteringCombination car (tdPauliObstructionMatrix ψ φ) := by abel
  have h1 : comm (scalarNorm • (1 : AlgebraType)) (tdPhononCreation car χ) = 0 := by
    simp [QuasiparticleCAR.comm]
  have hsub :
      comm (scalarNorm • (1 : AlgebraType) -
            scatteringCombination car (tdPauliObstructionMatrix ψ φ))
          (tdPhononCreation car χ) =
        comm (scalarNorm • (1 : AlgebraType)) (tdPhononCreation car χ) -
          comm (scatteringCombination car (tdPauliObstructionMatrix ψ φ))
            (tdPhononCreation car χ) := by
    simp only [QuasiparticleCAR.comm, sub_mul, mul_sub]
    abel
  rw [hsplit, hsub, h1, zero_sub,
    comm_scatteringCombination_tdPhononCreation car (tdPauliObstructionMatrix ψ φ) χ hχ]

section Vacuum

variable {State : Type*} [AddCommGroup State] [Module ℂ State]

/-- On the quasiparticle vacuum (`a_i |0⟩ = 0` for all `i`), every one-body
scattering operator annihilates `|0⟩` and the multi-mode Tamm--Dancoff phonon
commutator reduces purely to the c-number inner product. -/
theorem tdPhonon_commutator_on_vacuum
    (car : QuasiparticleCAR Index (Module.End ℂ State))
    (ψ φ : Index → Index → ℂ)
    (hψ : ∀ α β, ψ β α = -ψ α β) (hφ : ∀ α β, φ β α = -φ α β)
    (vacuum : State) (hvac : ∀ i : Index, car.a i vacuum = 0) :
    comm (tdPhononAnnihilation car ψ) (tdPhononCreation car φ) vacuum =
      ((1 / 2 : ℂ) * ∑ α : Index, ∑ β : Index, starRingEnd ℂ (ψ α β) * φ α β) •
        vacuum := by
  rw [tdPhonon_commutator_exact car ψ φ hψ hφ]
  have hscatt :
      (∑ α : Index, ∑ β : Index, ∑ γ : Index,
        (starRingEnd ℂ (ψ α β) * φ α γ) • car.scatteringOp γ β) vacuum = 0 := by
    simp [scatteringOp, LinearMap.sum_apply, Module.End.mul_apply, hvac]
  simp [hscatt]

end Vacuum

end TammDancoffMultiMode

namespace ProofDependency

inductive Archetype
  | carRelations
  | fermionicBogoliubov
  | pairNormalOrder
  | phononCorrection
  | circularCoefficients
  | vacuumReadout
  deriving DecidableEq

open Archetype

instance : Fintype Archetype where
  elems := {carRelations, fermionicBogoliubov, pairNormalOrder, phononCorrection, circularCoefficients, vacuumReadout}
  complete := by rintro (_ | _ | _ | _ | _ | _) <;> decide

def prerequisites : Archetype → Finset Archetype
  | carRelations => {carRelations}
  | fermionicBogoliubov => {carRelations, fermionicBogoliubov}
  | pairNormalOrder => {carRelations, pairNormalOrder}
  | phononCorrection => {carRelations, pairNormalOrder, phononCorrection}
  | circularCoefficients =>
      {carRelations, pairNormalOrder, phononCorrection, circularCoefficients}
  | vacuumReadout => {carRelations, pairNormalOrder, phononCorrection, vacuumReadout}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem correction_prerequisites :
    carRelations < pairNormalOrder ∧ pairNormalOrder < phononCorrection ∧
      phononCorrection < circularCoefficients ∧ phononCorrection < vacuumReadout := by
  simp only [lt_iff_le_not_ge]
  decide

theorem circular_and_vacuum_incomparable :
    ¬ circularCoefficients ≤ vacuumReadout ∧ ¬ vacuumReadout ≤ circularCoefficients := by
  decide

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def solovievPhononArchetypeOperator (P A C X : B) : Archetype → B
  | .carRelations => invS P
  | .fermionicBogoliubov => conePlus P A
  | .pairNormalOrder => coneMinus P C
  | .phononCorrection => genPhi P A C
  | .circularCoefficients => genJ P A C
  | .vacuumReadout => evenGrade P X + oddGrade P X

theorem solovievPhononArchetype_operator_identities
    {P : B} (hP : P * P = P) (A C X : B) :
    solovievPhononArchetypeOperator P A C X .carRelations *
      solovievPhononArchetypeOperator P A C X .carRelations = (1 : B) ∧
    solovievPhononArchetypeOperator P A C X .fermionicBogoliubov *
      solovievPhononArchetypeOperator P A C X .fermionicBogoliubov = 0 ∧
    solovievPhononArchetypeOperator P A C X .pairNormalOrder *
      solovievPhononArchetypeOperator P A C X .pairNormalOrder = 0 ∧
    solovievPhononArchetypeOperator P A C X .phononCorrection *
      solovievPhononArchetypeOperator P A C X .phononCorrection +
      solovievPhononArchetypeOperator P A C X .circularCoefficients *
        solovievPhononArchetypeOperator P A C X .circularCoefficients = 0 ∧
    solovievPhononArchetypeOperator P A C X .vacuumReadout = X := by
  dsimp only [solovievPhononArchetypeOperator]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

end ProofDependency

end InfoGeometry.Physics.SolovievPhononCorrections
