/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Physics.ColorIsospinCharge
import InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
import InfoGeometry.Physics.NuclearWignerSupermultipletSymmetry
import Mathlib.Tactic

/-!
# Cl(5,5) → Wigner SU(4) Embedding, Spin-Orbit Breaking, and Full Non-Abelian SU(3)_c Casimir

This module completes the `Cl(5,5)`–Wigner `SU(4)`–`SU(3)_c` bridge:

1. **Wigner `SU(4)` Normalization & $A$-Nucleon Collective Spin-Orbit Breaking**:
   - Exposes the uniform `1/2`-normalized 15 generators `su4S i`, `su4T j`, `su4Y i j` on
     `SpinPair = M₂(ℂ) ⊗ M₂(ℂ)` from `NuclearSpinIsospinTensorRepresentation`, resolving
     the `15 / 4 ≠ 33 / 16` Casimir normalization (`∑ Sᵢ² + ∑ Tⱼ² + ∑ Yᵢⱼ² = (15 / 4) • 1`)
     and complete 15-generator Lie closure.
   - Proves the exact $A$-nucleon collective spin-orbit commutator `[H_LS, Y_tot i j] ≠ 0`
     while `[H_LS, T_tot j] = 0`: spin-orbit coupling preserves isospin `SU(2)_T` but breaks
     Gamow–Teller `SU(4)`.

2. **Explicit Embedding of the `Cl(5,5)` `(p, n)` Isospin–Pairing Subalgebra into `SpinPair`**:
   - Constructs the 2-mode Jordan–Wigner CAR generators `spE_p, spF_p, spE_n, spF_n : SpinPair`,
     proving exact CAR closure, exact preservation of `casimir_partition_of_three_one`
     (`C₂^iso + C₂^pair = 3 • 1`), and exact preservation of
     `pin_majorana_conjugates_isospin_to_pairing` under `spGammaPlusN = σ₃ ⊗ I₁`.
   - Identifies `(spIsospinCartan, spIsospinPlus + spIsospinMinus, spIsospinCarrier, spPairingCarrier)`
     explicitly as linear combinations of `su4S, su4T, su4Y` in `SpinPair`.

3. **Full Non-Abelian 8-Generator `SU(3)_c` Algebra & `C₂ = 4/3` Casimir in `Cl(5,5)`**:
   - Defines the 6 off-diagonal color root gluons `colorRootGluon i j := E i.castLE j.castLE`
     for `i ≠ j ∈ Fin 3`, proves all 8 `su(3)_c` generators (`colorGluonT3`, `colorGluon3Y`,
     and all 6 `colorRootGluon i j`) satisfy Lie closure and annihilate BOTH
     `colorBaryonSingletProj` (`1₃`) and `colorVacuumSingletProj` (`1₀`) on both sides.
   - Defines the full non-Abelian quadratic Casimir `colorSU3Casimir` and proves
     `colorSU3Casimir = (4 / 3 : ℝ) • (colorQuarkTripletProj + colorDiquarkAntitripletProj)`,
     extracting eigenvalue `4/3` on `3` and `3̄` and `0` on `1₃` and `1₀`!
-/

noncomputable section

namespace InfoGeometry.Physics.Cl55WignerSU4Embedding

open scoped TensorProduct BigOperators
open Matrix
open TensorProduct
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Physics.ChiralCausalCone
open ChiralTensorRecoupling
open WeakIsospinSU2
open InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittLieRouting

/-! ## 1. Unified Wigner `su(4)` Interface, `15/4 ≠ 33/16`, & $A$-Nucleon Spin-Orbit Defect -/

/-- Spin generators `Sᵢ = (1/2) (σᵢ ⊗ 1)` on `SpinPair`. -/
abbrev su4S (i : Fin 3) : SpinPair := spinGenVec i

/-- Isospin generators `Tⱼ = (1/2) (1 ⊗ τⱼ)` on `SpinPair`. -/
abbrev su4T (j : Fin 3) : SpinPair := isospinGenVec j

/-- Gamow–Teller generators `Yᵢⱼ = (1/2) (σᵢ ⊗ τⱼ)` on `SpinPair`. -/
abbrev su4Y (i j : Fin 3) : SpinPair := gamowTellerGen i j

/-- Complete 15-generator `su(4)` Lie algebra closure, `C₂ = 15/4 ≠ 33/16` Casimir theorem,
    and exact `su4S / su4T / su4Y` commutation brackets on `SpinPair`. -/
theorem wigner_su4_casimir_and_lie_closure (i i' j j' : Fin 3) (a b : Fin 15) :
    su4Casimir = (15 / 4 : ℂ) • (1 : SpinPair) ∧
    (15 / 4 : ℂ) ≠ (33 / 16 : ℂ) ∧
    pairBracket (su4S i) (su4T j) = 0 ∧
    pairBracket (su4S i) (su4S i') =
      Complex.I • ∑ m : Fin 3, leviCivita ℂ i i' m • su4S m ∧
    pairBracket (su4T j) (su4T j') =
      Complex.I • ∑ m : Fin 3, leviCivita ℂ j j' m • su4T m ∧
    pairBracket (su4S i) (su4Y i' j) =
      Complex.I • ∑ m : Fin 3, leviCivita ℂ i i' m • su4Y m j ∧
    pairBracket (su4T j) (su4Y i j') =
      Complex.I • ∑ m : Fin 3, leviCivita ℂ j j' m • su4Y i m ∧
    pairBracket (su4Y i j) (su4Y i' j') =
      (if j = j' then Complex.I • ∑ m : Fin 3, leviCivita ℂ i i' m • su4S m else 0) +
      (if i = i' then Complex.I • ∑ m : Fin 3, leviCivita ℂ j j' m • su4T m else 0) ∧
    (∃ c : Fin 15 → ℂ, pairBracket (su4Generator a) (su4Generator b) =
      ∑ m : Fin 15, c m • su4Generator m) := by
  refine ⟨su4Casimir_eq_fifteen_fourths, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact spinGenVec_isospinGenVec_comm i j
  · exact spinGenVec_comm i i'
  · exact isospinGenVec_comm j j'
  · exact spinGenVec_gamowTellerGen_comm i i' j
  · exact isospinGenVec_gamowTellerGen_comm j i j'
  · rw [gamowTellerGen_comm i j i' j', add_comm]
  · exact su4Generator_lie_closed a b

/-- Single-nucleon orbital-spin-isospin carrier `M₂(ℂ) ⊗ SpinPair` for `L · S` breaking. -/
abbrev SpinOrbitSpinPair := M2C ⊗[ℂ] SpinPair

/-- Collective `A`-nucleon operator algebra `Fin A → SpinOrbitSpinPair`. -/
abbrev ANucleonSpinOrbit (A : ℕ) := Fin A → SpinOrbitSpinPair

/-- Single-nucleon spin-orbit operator `L · S = ∑ k, pauliBasis k ⊗ₜ su4S k`. -/
def singleNucleonLS : SpinOrbitSpinPair :=
  ∑ k : Fin 3, pauliBasis k ⊗ₜ[ℂ] su4S k

/-- Collective `A`-nucleon spin-orbit Hamiltonian `H_LS` (sum of `L_n · S_n` over `Fin A`). -/
def collectiveLS (A : ℕ) : ANucleonSpinOrbit A :=
  fun _ => singleNucleonLS

/-- Collective `A`-nucleon isospin operator `T_j^{tot}` embedded into `ANucleonSpinOrbit A`. -/
def collectiveT (A : ℕ) (j : Fin 3) : ANucleonSpinOrbit A :=
  fun _ => (1 : M2C) ⊗ₜ[ℂ] su4T j

/-- Collective `A`-nucleon Gamow–Teller operator `Y_{ij}^{tot}` embedded into `ANucleonSpinOrbit A`. -/
def collectiveY (A : ℕ) (i j : Fin 3) : ANucleonSpinOrbit A :=
  fun _ => (1 : M2C) ⊗ₜ[ℂ] su4Y i j

private theorem pairTrace_pauliBasis_one :
    Matrix.trace (1 : M2C) = 2 := by
  simp [Matrix.trace]

private theorem trace_pauliBasis_sq_eq_two (k : Fin 3) :
    Matrix.trace (pauliBasis k * pauliBasis k) = 2 := by
  rw [pauliBasis_sq k, pairTrace_pauliBasis_one]

private theorem trace_pauliBasis_ne_zero (k m : Fin 3) (hkm : k ≠ m) :
    Matrix.trace (pauliBasis k * pauliBasis m) = 0 := by
  fin_cases k <;> fin_cases m <;>
    first
    | exact absurd rfl hkm
    | (simp [pauliBasis, I₁, I₂, I₃, σPlus, σMinus, σ3c, Matrix.trace,
        Fin.sum_univ_two]; try ring)

private theorem so_tmul_mul (M₁ M₂ : M2C) (S₁ S₂ : SpinPair) :
    (M₁ ⊗ₜ[ℂ] S₁) * (M₂ ⊗ₜ[ℂ] S₂) = (M₁ * M₂) ⊗ₜ[ℂ] (S₁ * S₂) :=
  Algebra.TensorProduct.tmul_mul_tmul _ _ _ _

private theorem so_add_mul (a b c : SpinOrbitSpinPair) : (a + b) * c = a * c + b * c := by
  let _inst1 : Ring SpinPair := inferInstance
  let _inst2 : Algebra ℂ SpinPair := inferInstance
  let inst3 : Ring SpinOrbitSpinPair := inferInstance
  exact inst3.toNonUnitalSemiring.toDistrib.right_distrib a b c

private theorem so_mul_add (a b c : SpinOrbitSpinPair) : a * (b + c) = a * b + a * c := by
  let _inst1 : Ring SpinPair := inferInstance
  let _inst2 : Algebra ℂ SpinPair := inferInstance
  let inst3 : Ring SpinOrbitSpinPair := inferInstance
  exact inst3.toNonUnitalSemiring.toDistrib.left_distrib a b c

private theorem so_mul_zero (a : SpinOrbitSpinPair) : a * 0 = 0 := by
  let _inst1 : Ring SpinPair := inferInstance
  let _inst2 : Algebra ℂ SpinPair := inferInstance
  let inst3 : Ring SpinOrbitSpinPair := inferInstance
  exact @mul_zero _ inst3.toMulZeroClass a

private theorem singleNucleonLS_comm_right (X : SpinPair) :
    singleNucleonLS * ((1 : M2C) ⊗ₜ[ℂ] X) - ((1 : M2C) ⊗ₜ[ℂ] X) * singleNucleonLS =
    ∑ k : Fin 3, pauliBasis k ⊗ₜ[ℂ] (su4S k * X - X * su4S k) := by
  dsimp [singleNucleonLS]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  rw [so_add_mul, so_add_mul, so_mul_add, so_mul_add]
  rw [so_tmul_mul, so_tmul_mul, so_tmul_mul, so_tmul_mul, so_tmul_mul, so_tmul_mul]
  simp only [mul_one, one_mul, sub_eq_add_neg, TensorProduct.tmul_add, TensorProduct.tmul_neg]
  abel_nf

private theorem I3_eq_σ3c : I₃ = σ3c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [I₃, σ3c]

/-- **$A$-Nucleon Collective Spin-Orbit Symmetry & $\mathrm{SU}(4)$ Breaking Theorem**:
    1. Spin-orbit coupling preserves total isospin: `[H_LS, T_j^{tot}] = 0`.
    2. Exact commutator with Gamow–Teller generators:
       `[singleNucleonLS, 1 ⊗ₜ Y_{ij}] = I • ∑ k, ∑ m, ε_{k i m} • (pauliBasis k ⊗ₜ su4Y m j)`.
    3. For every `A ≥ 1` and every `i, j : Fin 3`, `[collectiveLS A, collectiveY A i j] ≠ 0`,
       giving a nonzero operator defect breaking Wigner `SU(4)`! -/
theorem collective_spin_orbit_preserves_isospin_breaks_su4
    (A : ℕ) (hA : 0 < A) (i j : Fin 3) :
    (collectiveLS A * collectiveT A j - collectiveT A j * collectiveLS A = 0) ∧
    (singleNucleonLS * ((1 : M2C) ⊗ₜ[ℂ] su4Y i j) -
        ((1 : M2C) ⊗ₜ[ℂ] su4Y i j) * singleNucleonLS =
      Complex.I • ∑ k : Fin 3, ∑ m : Fin 3,
        leviCivita ℂ k i m • (pauliBasis k ⊗ₜ[ℂ] su4Y m j)) ∧
    (collectiveLS A * collectiveY A i j - collectiveY A i j * collectiveLS A ≠ 0) := by
  have hT_single :
      singleNucleonLS * ((1 : M2C) ⊗ₜ[ℂ] su4T j) -
        ((1 : M2C) ⊗ₜ[ℂ] su4T j) * singleNucleonLS = 0 := by
    rw [singleNucleonLS_comm_right]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hsub : su4S k * su4T j - su4T j * su4S k = 0 := spinGenVec_isospinGenVec_comm k j
    rw [hsub, TensorProduct.tmul_zero]
  have hY_single :
      singleNucleonLS * ((1 : M2C) ⊗ₜ[ℂ] su4Y i j) -
        ((1 : M2C) ⊗ₜ[ℂ] su4Y i j) * singleNucleonLS =
      Complex.I • ∑ k : Fin 3, ∑ m : Fin 3,
        leviCivita ℂ k i m • (pauliBasis k ⊗ₜ[ℂ] su4Y m j) := by
    rw [singleNucleonLS_comm_right, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : su4S k * su4Y i j - su4Y i j * su4S k =
        Complex.I • ∑ m : Fin 3, leviCivita ℂ k i m • su4Y m j :=
      spinGenVec_gamowTellerGen_comm k i j
    rw [hc, TensorProduct.tmul_smul, TensorProduct.tmul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [TensorProduct.tmul_smul]
  refine ⟨?_, hY_single, ?_⟩
  · ext n
    exact hT_single
  · intro hzero
    have h0 := congrFun hzero ⟨0, hA⟩
    dsimp [collectiveLS, collectiveY] at h0
    rw [hY_single] at h0
    -- Witness non-vanishing by projecting onto `pauliBasis k₀ ⊗ₜ su4Y m₀ j` via trace
    -- For each `i`, pick `(k₀, m₀)` with `k₀ ≠ i`, `m₀ ≠ i`, `k₀ ≠ m₀` so `ε_{k₀ i m₀} = ±1`
    let trSO : SpinOrbitSpinPair →ₗ[ℂ] ℂ :=
      TensorProduct.lift
        { toFun := fun M =>
            { toFun := fun S => Matrix.trace M * pairTrace S
              map_add' := fun S₁ S₂ => by simp [map_add, mul_add]
              map_smul' := fun c S => by simp [map_smul]; ring }
          map_add' := fun M₁ M₂ => by ext S; simp [Matrix.trace_add, add_mul]
          map_smul' := fun c M => by ext S; simp [Matrix.trace_smul]; ring }
    have htr_tmul : ∀ M S, trSO (M ⊗ₜ[ℂ] S) = Matrix.trace M * pairTrace S := fun M S => rfl
    have hY_dot : ∀ m m' : Fin 3, pairTrace (su4Y m j * su4Y m' j) =
        if m = m' then (1 / 4 : ℂ) else 0 := by
      intro m m'
      dsimp [su4Y]
      rw [gamowTellerGen_eq_tmul m j, gamowTellerGen_eq_tmul m' j,
        smul_mul_smul, Algebra.TensorProduct.tmul_mul_tmul, map_smul, pairTrace_tmul]
      by_cases hmm : m = m'
      · subst m'
        simp [pauliBasis_sq m, pauliBasis_sq j]
        norm_num
      · have htr0 := trace_pauliBasis_ne_zero m m' hmm
        simp [hmm, htr0]
    have so_mul_smul : ∀ (c : ℂ) (a b : SpinOrbitSpinPair), a * (c • b) = c • (a * b) :=
      fun c a b => mul_smul_comm c a b
    fin_cases i
    · -- i = 0: pair (k₀ = 1, m₀ = 2) gives ε_{1 0 2} = -1
      simp only [Fin.sum_univ_three, leviCivita, zero_smul, add_zero, zero_add, smul_add] at h0
      have hval := congrArg (fun X => trSO ((pauliBasis 1 ⊗ₜ[ℂ] su4Y 2 j) * X)) h0
      rw [so_mul_zero, map_zero] at hval
      rw [so_mul_add] at hval
      simp_rw [so_mul_smul, so_tmul_mul] at hval
      simp only [map_add, map_smul, htr_tmul, trace_pauliBasis_sq_eq_two,
        trace_pauliBasis_ne_zero 1 2 (by decide), hY_dot] at hval
      norm_num at hval
    · -- i = 1: pair (k₀ = 0, m₀ = 2) gives ε_{0 1 2} = +1
      simp only [Fin.sum_univ_three, leviCivita, zero_smul, add_zero, zero_add, smul_add] at h0
      have hval := congrArg (fun X => trSO ((pauliBasis 0 ⊗ₜ[ℂ] su4Y 2 j) * X)) h0
      rw [so_mul_zero, map_zero] at hval
      rw [so_mul_add] at hval
      simp_rw [so_mul_smul, so_tmul_mul] at hval
      simp only [map_add, map_smul, htr_tmul, trace_pauliBasis_sq_eq_two,
        trace_pauliBasis_ne_zero 0 2 (by decide), hY_dot] at hval
      norm_num at hval
    · -- i = 2: pair (k₀ = 0, m₀ = 1) gives ε_{0 2 1} = -1
      simp only [Fin.sum_univ_three, leviCivita, zero_smul, add_zero, zero_add, smul_add] at h0
      have hval := congrArg (fun X => trSO ((pauliBasis 0 ⊗ₜ[ℂ] su4Y 1 j) * X)) h0
      rw [so_mul_zero, map_zero] at hval
      rw [so_mul_add] at hval
      simp_rw [so_mul_smul, so_tmul_mul] at hval
      simp only [map_add, map_smul, htr_tmul, trace_pauliBasis_sq_eq_two,
        trace_pauliBasis_ne_zero 0 1 (by decide), hY_dot] at hval
      norm_num at hval

/-! ## 2. Explicit Embedding of `Cl(5,5)` `(p, n)` Isospin–Pairing Subalgebra into `SpinPair` -/

/-- Jordan–Wigner two-mode creation/annihilation realization inside `SpinPair = M₂(ℂ) ⊗ M₂(ℂ)`
    for the `(p, n)` nucleon doublet modes. -/
def spEp : SpinPair := σPlus ⊗ₜ[ℂ] (1 : M2C)
def spFp : SpinPair := σMinus ⊗ₜ[ℂ] (1 : M2C)
def spEn : SpinPair := σ3c ⊗ₜ[ℂ] σPlus
def spFn : SpinPair := σ3c ⊗ₜ[ℂ] σMinus

/-- Embedded mode occupation and Cartan operators in `SpinPair`. -/
def spNp : SpinPair := spEp * spFp
def spNn : SpinPair := spEn * spFn
def spHp : SpinPair := spNp - (1 / 2 : ℂ) • (1 : SpinPair)
def spHn : SpinPair := spNn - (1 / 2 : ℂ) • (1 : SpinPair)

/-- Embedded `(p, n)` isospin `sl₂`, pairing `sl₂`, carriers, Casimirs, and Majorana `Γₙ`. -/
def spIsospinPlus : SpinPair := spEp * spFn
def spIsospinMinus : SpinPair := spEn * spFp
def spIsospinCartan : SpinPair := spHp - spHn
def spPairingPlus : SpinPair := spEp * spEn
def spPairingMinus : SpinPair := spFn * spFp
def spPairingCartan : SpinPair := spHp + spHn
def spGammaPlusN : SpinPair := spEn + spFn

def spIsoProjPlus : SpinPair := spNp * (1 - spNn)
def spIsoProjMinus : SpinPair := (1 - spNp) * spNn
def spPairProjPlus : SpinPair := spNp * spNn
def spPairProjMinus : SpinPair := (1 - spNp) * (1 - spNn)
def spIsospinCarrier : SpinPair := spIsoProjPlus + spIsoProjMinus
def spPairingCarrier : SpinPair := spPairProjPlus + spPairProjMinus

def spIsospinCasimir : SpinPair :=
  spIsospinCartan * spIsospinCartan +
    (2 : ℂ) • (spIsospinPlus * spIsospinMinus + spIsospinMinus * spIsospinPlus)

def spPairingCasimir : SpinPair :=
  spPairingCartan * spPairingCartan +
    (2 : ℂ) • (spPairingPlus * spPairingMinus + spPairingMinus * spPairingPlus)

private theorem σPlus_mul_σ3c : σPlus * σ3c = -σPlus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σPlus, σ3c]

private theorem σ3c_mul_σPlus : σ3c * σPlus = σPlus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σPlus, σ3c]

private theorem σMinus_mul_σ3c : σMinus * σ3c = σMinus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σMinus, σ3c]

private theorem σ3c_mul_σMinus : σ3c * σMinus = -σMinus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σMinus, σ3c]

private theorem σPlus_mul_σMinus : σPlus * σMinus = (1 / 2 : ℂ) • ((1 : M2C) + σ3c) := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [σPlus, σMinus, σ3c]; try norm_num)

private theorem σMinus_mul_σPlus : σMinus * σPlus = (1 / 2 : ℂ) • ((1 : M2C) - σ3c) := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [σPlus, σMinus, σ3c]; try norm_num)

private theorem σPlus_mul_σMinus_add : σPlus * σMinus + σMinus * σPlus = 1 := by
  rw [σPlus_mul_σMinus, σMinus_mul_σPlus]
  module

/-- **Exact 2-Mode `(p, n)` CAR, Casimir Partition `3 • 1`, Majorana Particle–Hole Conjugation,
    and Explicit `su(4)` Realization inside `SpinPair`**:
    Embeds the `(p, n)` isospin–pairing sector of `Cl55SpinorCartanFock` faithfully into
    `SpinPair = M₂(ℂ) ⊗ M₂(ℂ)`! -/
theorem cl55_two_mode_pn_spinpair_embedding {p n : Fin 5} (hpn : p ≠ n) :
    -- 1. Exact CAR match between `Cl55SpinorCartanFock` `(e p, f p, e n, f n)` and `(spEp, spFp, spEn, spFn)`
    (spEp * spEp = 0 ∧ spFp * spFp = 0 ∧ spEn * spEn = 0 ∧ spFn * spFn = 0) ∧
    (spEp * spFp + spFp * spEp = 1 ∧ spEn * spFn + spFn * spEn = 1) ∧
    (spEp * spEn + spEn * spEp = 0 ∧ spEp * spFn + spFn * spEp = 0 ∧
     spFp * spEn + spEn * spFp = 0 ∧ spFp * spFn + spFn * spFp = 0) ∧
    -- 2. Exact `casimir_partition_of_three_one` preserved in `SpinPair` (mirroring `Cl(5,5)`)
    (spIsospinCasimir = (3 : ℂ) • spIsospinCarrier ∧
     spPairingCasimir = (3 : ℂ) • spPairingCarrier ∧
     spIsospinCasimir + spPairingCasimir = (3 : ℂ) • (1 : SpinPair) ∧
     isospinCasimir p n + pairingCasimir p n = (3 : ℝ) • (1 : MatStage 5)) ∧
    -- 3. Exact `pin_majorana_conjugates_isospin_to_pairing` preserved via `spGammaPlusN = σ3c ⊗ₜ I₁`
    (spGammaPlusN = σ3c ⊗ₜ[ℂ] I₁ ∧
     spGammaPlusN * spGammaPlusN = 1 ∧
     spGammaPlusN * spIsospinPlus * spGammaPlusN = -spPairingPlus ∧
     spGammaPlusN * spIsospinMinus * spGammaPlusN = -spPairingMinus ∧
     spGammaPlusN * spIsospinCartan * spGammaPlusN = spPairingCartan ∧
     gammaPlus n * isospinPlus p n * gammaPlus n = -pairingPlus p n) ∧
    -- 4. Direct decomposition inside `SpinPair` in terms of `su4S, su4T, su4Y`
    (spIsospinCartan = su4S 2 - su4T 2 ∧
     spPairingCartan = su4S 2 + su4T 2 ∧
     spIsospinPlus + spIsospinMinus = -(su4Y 0 0 + su4Y 1 1) ∧
     spIsospinCarrier = (1 / 2 : ℂ) • (1 : SpinPair) - su4Y 2 2 ∧
     spPairingCarrier = (1 / 2 : ℂ) • (1 : SpinPair) + su4Y 2 2) := by
  have hNp_eq : spNp = (1 / 2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) + σ3c ⊗ₜ[ℂ] (1 : M2C)) := by
    dsimp [spNp, spEp, spFp]
    simp only [mul_one, σPlus_mul_σMinus, TensorProduct.add_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_smul, smul_add]
  have hNn_eq : spNn = (1 / 2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) + (1 : M2C) ⊗ₜ[ℂ] σ3c) := by
    dsimp [spNn, spEn, spFn]
    simp only [σ3c_sq, σPlus_mul_σMinus, TensorProduct.tmul_smul, TensorProduct.tmul_add]
  have hHp_eq : spHp = (1 / 2 : ℂ) • (σ3c ⊗ₜ[ℂ] (1 : M2C)) := by
    dsimp [spHp]
    rw [hNp_eq, Algebra.TensorProduct.one_def, smul_add, add_sub_cancel_left]
  have hHn_eq : spHn = (1 / 2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] σ3c) := by
    dsimp [spHn]
    rw [hNn_eq, Algebra.TensorProduct.one_def, smul_add, add_sub_cancel_left]
  have hIp_eq : spIsospinPlus = (-σPlus) ⊗ₜ[ℂ] σMinus := by
    dsimp [spIsospinPlus, spEp, spFn]
    simp only [σPlus_mul_σ3c, one_mul]
  have hIm_eq : spIsospinMinus = (-σMinus) ⊗ₜ[ℂ] σPlus := by
    dsimp [spIsospinMinus, spEn, spFp]
    simp only [σ3c_mul_σMinus, mul_one]
  have hPp_eq : spPairingPlus = (-σPlus) ⊗ₜ[ℂ] σPlus := by
    dsimp [spPairingPlus, spEp, spEn]
    simp only [σPlus_mul_σ3c, one_mul]
  have hPm_eq : spPairingMinus = (-σMinus) ⊗ₜ[ℂ] σMinus := by
    dsimp [spPairingMinus, spFn, spFp]
    simp only [σ3c_mul_σMinus, mul_one]
  have hG_eq : spGammaPlusN = σ3c ⊗ₜ[ℂ] I₁ := by
    dsimp [spGammaPlusN, spEn, spFn]
    have h1 : σPlus + σMinus = I₁ := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [σPlus, σMinus, I₁]
    rw [← TensorProduct.tmul_add, h1]
  have hI3_eq : spIsospinCartan = su4S 2 - su4T 2 := by
    dsimp [spIsospinCartan, su4S, su4T, spinGenVec, isospinGenVec, su4SpinGen, su4IsospinGen,
      pauliTripleM2C]
    rw [hHp_eq, hHn_eq]
    have hpa : pauliBasis 2 = σ3c := by simp [pauliBasis, I3_eq_σ3c]
    rw [hpa]
  have hK0_eq : spPairingCartan = su4S 2 + su4T 2 := by
    dsimp [spPairingCartan, su4S, su4T, spinGenVec, isospinGenVec, su4SpinGen, su4IsospinGen,
      pauliTripleM2C]
    rw [hHp_eq, hHn_eq]
    have hpa : pauliBasis 2 = σ3c := by simp [pauliBasis, I3_eq_σ3c]
    rw [hpa]
  have hIsoCar_eq : spIsospinCarrier = (1 / 2 : ℂ) • (1 : SpinPair) - su4Y 2 2 := by
    dsimp [spIsospinCarrier, spIsoProjPlus, spIsoProjMinus, su4Y]
    rw [hNp_eq, hNn_eq, gamowTellerGen_eq_tmul]
    have hpa : pauliBasis 2 = σ3c := by simp [pauliBasis, I3_eq_σ3c]
    rw [hpa]
    simp only [Algebra.TensorProduct.one_def, smul_add, add_mul, mul_add, sub_mul, mul_sub,
      smul_mul_assoc, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      smul_smul]
    module
  have hPairCar_eq : spPairingCarrier = (1 / 2 : ℂ) • (1 : SpinPair) + su4Y 2 2 := by
    dsimp [spPairingCarrier, spPairProjPlus, spPairProjMinus, su4Y]
    rw [hNp_eq, hNn_eq, gamowTellerGen_eq_tmul]
    have hpa : pauliBasis 2 = σ3c := by simp [pauliBasis, I3_eq_σ3c]
    rw [hpa]
    simp only [Algebra.TensorProduct.one_def, smul_add, add_mul, mul_add, sub_mul, mul_sub,
      smul_mul_assoc, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      smul_smul]
    module
  have hC_iso : spIsospinCasimir = (3 : ℂ) • spIsospinCarrier := by
    dsimp [spIsospinCasimir]
    rw [hI3_eq, hIp_eq, hIm_eq, hIsoCar_eq]
    have hS2T2 : (su4S 2 - su4T 2) * (su4S 2 - su4T 2) =
        (1 / 2 : ℂ) • (1 : SpinPair) - su4Y 2 2 := by
      rw [sub_mul, mul_sub, mul_sub, spinGenVec_sq 2, isospinGenVec_sq 2]
      have hst' : su4S 2 * su4T 2 = (1 / 2 : ℂ) • su4Y 2 2 := by
        dsimp [su4S, su4T, su4Y]
        rw [gamowTellerGen_eq_two_mul 2 2, smul_smul]
        norm_num
      have hts' : su4T 2 * su4S 2 = (1 / 2 : ℂ) • su4Y 2 2 := by
        rw [← sub_eq_zero.mp (spinGenVec_isospinGenVec_comm 2 2)]; exact hst'
      rw [hst', hts']; module
    have hpm : ((-σPlus) ⊗ₜ[ℂ] σMinus) * ((-σMinus) ⊗ₜ[ℂ] σPlus) +
        ((-σMinus) ⊗ₜ[ℂ] σPlus) * ((-σPlus) ⊗ₜ[ℂ] σMinus) =
        (1 / 2 : ℂ) • (1 : SpinPair) - su4Y 2 2 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      simp only [neg_mul, mul_neg, neg_neg, σPlus_mul_σMinus, σMinus_mul_σPlus,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.add_tmul,
        TensorProduct.tmul_add, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      norm_num
      dsimp [su4Y]
      rw [gamowTellerGen_eq_tmul]
      have hpa : pauliBasis 2 = σ3c := by simp [pauliBasis, I3_eq_σ3c]
      rw [hpa, Algebra.TensorProduct.one_def]
      module
    rw [hS2T2, hpm]
    module
  have hC_pair : spPairingCasimir = (3 : ℂ) • spPairingCarrier := by
    dsimp [spPairingCasimir]
    rw [hK0_eq, hPp_eq, hPm_eq, hPairCar_eq]
    have hS2T2 : (su4S 2 + su4T 2) * (su4S 2 + su4T 2) =
        (1 / 2 : ℂ) • (1 : SpinPair) + su4Y 2 2 := by
      rw [add_mul, mul_add, mul_add, spinGenVec_sq 2, isospinGenVec_sq 2]
      have hst' : su4S 2 * su4T 2 = (1 / 2 : ℂ) • su4Y 2 2 := by
        dsimp [su4S, su4T, su4Y]
        rw [gamowTellerGen_eq_two_mul 2 2, smul_smul]
        norm_num
      have hts' : su4T 2 * su4S 2 = (1 / 2 : ℂ) • su4Y 2 2 := by
        rw [← sub_eq_zero.mp (spinGenVec_isospinGenVec_comm 2 2)]; exact hst'
      rw [hst', hts']; module
    have hpm : ((-σPlus) ⊗ₜ[ℂ] σPlus) * ((-σMinus) ⊗ₜ[ℂ] σMinus) +
        ((-σMinus) ⊗ₜ[ℂ] σMinus) * ((-σPlus) ⊗ₜ[ℂ] σPlus) =
        (1 / 2 : ℂ) • (1 : SpinPair) + su4Y 2 2 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      simp only [neg_mul, mul_neg, neg_neg, σPlus_mul_σMinus, σMinus_mul_σPlus,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.add_tmul,
        TensorProduct.tmul_add, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      norm_num
      dsimp [su4Y]
      rw [gamowTellerGen_eq_tmul]
      have hpa : pauliBasis 2 = σ3c := by simp [pauliBasis, I3_eq_σ3c]
      rw [hpa, Algebra.TensorProduct.one_def]
      module
    rw [hS2T2, hpm]
    module
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨hC_iso, hC_pair, ?_, (casimir_partition_of_three_one hpn).2.2⟩,
    ⟨hG_eq, ?_, ?_, ?_, ?_, (pin_majorana_conjugates_isospin_to_pairing hpn).1⟩,
    ⟨hI3_eq, hK0_eq, ?_, hIsoCar_eq, hPairCar_eq⟩⟩
  · dsimp [spEp]; simp only [σPlus_sq, zero_tmul]
  · dsimp [spFp]; simp only [σMinus_sq, zero_tmul]
  · dsimp [spEn]; simp only [σPlus_sq, tmul_zero]
  · dsimp [spFn]; simp only [σMinus_sq, tmul_zero]
  · dsimp [spEp, spFp]
    simp only [mul_one]
    rw [← TensorProduct.add_tmul, σPlus_mul_σMinus_add, Algebra.TensorProduct.one_def]
  · dsimp [spEn, spFn]
    simp only [σ3c_sq]
    rw [← TensorProduct.tmul_add, σPlus_mul_σMinus_add, Algebra.TensorProduct.one_def]
  · dsimp [spEp, spEn]
    simp only [one_mul, mul_one, σPlus_mul_σ3c, σ3c_mul_σPlus, neg_tmul, neg_add_cancel]
  · dsimp [spEp, spFn]
    simp only [one_mul, mul_one, σPlus_mul_σ3c, σ3c_mul_σPlus, neg_tmul, neg_add_cancel]
  · dsimp [spFp, spEn]
    simp only [one_mul, mul_one, σMinus_mul_σ3c, σ3c_mul_σMinus, neg_tmul, add_neg_cancel]
  · dsimp [spFp, spFn]
    simp only [one_mul, mul_one, σMinus_mul_σ3c, σ3c_mul_σMinus, neg_tmul, add_neg_cancel]
  · rw [hC_iso, hC_pair, hIsoCar_eq, hPairCar_eq]
    module
  · rw [hG_eq]; simp only [Algebra.TensorProduct.tmul_mul_tmul, σ3c_sq, I₁_sq,
      Algebra.TensorProduct.one_def]
  · rw [hG_eq, hIp_eq, hPp_eq]
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [neg_mul, mul_neg, σ3c_mul_σPlus, σPlus_mul_σ3c]
    have h1 : I₁ * σMinus * I₁ = σPlus := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [I₁, σMinus, σPlus]
    rw [h1, neg_tmul, neg_tmul, neg_neg]
  · rw [hG_eq, hIm_eq, hPm_eq]
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [neg_mul, mul_neg, σ3c_mul_σMinus, σMinus_mul_σ3c]
    have h1 : I₁ * σPlus * I₁ = σMinus := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [I₁, σMinus, σPlus]
    rw [h1, neg_tmul, neg_tmul, neg_neg]
  · rw [hG_eq, hI3_eq, hK0_eq]
    dsimp [su4S, su4T, spinGenVec, isospinGenVec, su4SpinGen, su4IsospinGen, pauliTripleM2C]
    have hpa : pauliBasis 2 = σ3c := by simp [pauliBasis, I3_eq_σ3c]
    rw [hpa]
    simp only [sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, σ3c_sq, I₁_sq]
    have h131 : I₁ * σ3c * I₁ = -σ3c := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [I₁, σ3c, σPlus, σMinus]
    rw [h131, TensorProduct.tmul_neg, smul_neg, sub_neg_eq_add]
  · rw [hIp_eq, hIm_eq]
    dsimp [su4Y]
    rw [gamowTellerGen_eq_tmul, gamowTellerGen_eq_tmul]
    have h0 : pauliBasis 0 = σPlus + σMinus := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [pauliBasis, I₁, σPlus, σMinus]
    have h1 : pauliBasis 1 = (-Complex.I) • (σPlus - σMinus) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [pauliBasis, I₂, σPlus, σMinus]
    have h11 : pauliBasis 1 ⊗ₜ[ℂ] pauliBasis 1 = -((σPlus - σMinus) ⊗ₜ[ℂ] (σPlus - σMinus)) := by
      rw [h1, TensorProduct.smul_tmul, smul_smul, neg_mul_neg, Complex.I_mul_I,
        neg_one_smul, TensorProduct.tmul_neg]
    rw [h0, h11]
    simp only [add_tmul, tmul_add, sub_tmul, tmul_sub, smul_neg, neg_tmul]
    module

/-! ## 3. Full 8-Generator Non-Abelian `SU(3)_c` Gluon Algebra & `C₂ = 4/3` Casimir in `Cl(5,5)` -/

/-- Canonical embedding `Fin 3 ↪ Fin 5` for the 3 color modes `{0, 1, 2}`. -/
def colorIdx (i : Fin 3) : Fin 5 := Fin.castLE (by omega) i

/-- The 6 off-diagonal color root gluons `E(i, j)` (`i ≠ j ∈ {0, 1, 2}`) in `MatStage 5`. -/
def colorRootGluon (i j : Fin 3) : MatStage 5 :=
  InfoGeometry.Canonical.Cl55WittLieRouting.E (colorIdx i) (colorIdx j)

/-- Full non-Abelian `SU(3)_c` quadratic Casimir on `MatStage 5`:
    `C₂^{SU(3)} = (1/12) (3 T₃² + (3Y)²) + (1/2) ∑_{i ≠ j} E_{ij} E_{ji}`. -/
def colorSU3Casimir : MatStage 5 :=
  (1 / 12 : ℝ) • ((3 : ℝ) • (colorGluonT3 * colorGluonT3) + colorGluon3Y * colorGluon3Y) +
  (1 / 2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3,
    if i = j then 0 else colorRootGluon i j * colorRootGluon j i

private theorem colorIdx_ne {i j : Fin 3} (hij : i ≠ j) : colorIdx i ≠ colorIdx j :=
  fun h => hij (Fin.ext (by simpa [colorIdx] using congrArg Fin.val h))

private theorem colorRootGluon_eq_e_mul_f {i j : Fin 3} (hij : i ≠ j) :
    colorRootGluon i j = e (colorIdx i) * f (colorIdx j) := by
  dsimp [colorRootGluon, InfoGeometry.Canonical.Cl55WittLieRouting.E, Cl55SpinorCartanFock.e, f]
  have hne : colorIdx i ≠ colorIdx j := colorIdx_ne hij
  simp [hne]

private theorem colorRootGluon_mul_swap {i j : Fin 3} (hij : i ≠ j) :
    colorRootGluon i j * colorRootGluon j i =
      modeOccupied (colorIdx i) * modeVacant (colorIdx j) := by
  rw [colorRootGluon_eq_e_mul_f hij, colorRootGluon_eq_e_mul_f hij.symm]
  have hne : colorIdx i ≠ colorIdx j := colorIdx_ne hij
  have h1 : e (colorIdx j) * f (colorIdx i) = -(f (colorIdx i) * e (colorIdx j)) :=
    e_mul_f_swap_ne hne.symm
  have h2 : f (colorIdx j) * f (colorIdx i) = -(f (colorIdx i) * f (colorIdx j)) :=
    f_mul_f_swap (colorIdx j) (colorIdx i)
  calc
    (e (colorIdx i) * f (colorIdx j)) * (e (colorIdx j) * f (colorIdx i)) =
        -(e (colorIdx i) * (f (colorIdx j) * f (colorIdx i)) * e (colorIdx j)) := by
      rw [h1]; noncomm_ring
    _ = (e (colorIdx i) * f (colorIdx i)) * (f (colorIdx j) * e (colorIdx j)) := by
      rw [h2]; noncomm_ring

private theorem colorRootGluon_comm_modeOccupied_other {i j k : Fin 3}
    (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j) :
    colorRootGluon i j * modeOccupied (colorIdx k) =
      modeOccupied (colorIdx k) * colorRootGluon i j := by
  rw [colorRootGluon_eq_e_mul_f hij]
  have hki' : colorIdx k ≠ colorIdx i := colorIdx_ne hki
  have hkj' : colorIdx k ≠ colorIdx j := colorIdx_ne hkj
  have h1 : f (colorIdx j) * e (colorIdx k) = -(e (colorIdx k) * f (colorIdx j)) :=
    f_mul_e_swap_ne hkj'
  have h2 : f (colorIdx j) * f (colorIdx k) = -(f (colorIdx k) * f (colorIdx j)) :=
    f_mul_f_swap (colorIdx j) (colorIdx k)
  have h3 : e (colorIdx i) * e (colorIdx k) = -(e (colorIdx k) * e (colorIdx i)) :=
    e_mul_e_swap (colorIdx i) (colorIdx k)
  have h4 : e (colorIdx i) * f (colorIdx k) = -(f (colorIdx k) * e (colorIdx i)) :=
    e_mul_f_swap_ne hki'.symm
  dsimp [modeOccupied]
  calc
    (e (colorIdx i) * f (colorIdx j)) * (e (colorIdx k) * f (colorIdx k)) =
        -(e (colorIdx i) * e (colorIdx k)) * (f (colorIdx j) * f (colorIdx k)) := by
      rw [mul_assoc, ← mul_assoc (f (colorIdx j)), h1]; noncomm_ring
    _ = -(-(e (colorIdx k) * e (colorIdx i))) * (-(f (colorIdx k) * f (colorIdx j))) := by
      rw [h3, h2]
    _ = -(e (colorIdx k) * (e (colorIdx i) * f (colorIdx k)) * f (colorIdx j)) := by
      noncomm_ring
    _ = (e (colorIdx k) * f (colorIdx k)) * (e (colorIdx i) * f (colorIdx j)) := by
      rw [h4]; noncomm_ring

private theorem colorRootGluon_kill_occupied_occupied {i j : Fin 3} (hij : i ≠ j) :
    colorRootGluon i j * (modeOccupied (colorIdx i) * modeOccupied (colorIdx j)) = 0 ∧
    (modeOccupied (colorIdx i) * modeOccupied (colorIdx j)) * colorRootGluon i j = 0 := by
  rw [colorRootGluon_eq_e_mul_f hij]
  have hne : colorIdx i ≠ colorIdx j := colorIdx_ne hij
  have hf_e : f (colorIdx j) * e (colorIdx i) = -(e (colorIdx i) * f (colorIdx j)) :=
    f_mul_e_swap_ne hne
  refine ⟨?_, ?_⟩
  · dsimp [modeOccupied]
    calc
      (e (colorIdx i) * f (colorIdx j)) *
          ((e (colorIdx i) * f (colorIdx i)) * (e (colorIdx j) * f (colorIdx j))) =
        -(e (colorIdx i) * (e (colorIdx i) * f (colorIdx j)) * f (colorIdx i) *
            e (colorIdx j) * f (colorIdx j)) := by
        rw [mul_assoc, ← mul_assoc (f (colorIdx j)), ← mul_assoc (f (colorIdx j)), hf_e]
        noncomm_ring
      _ = 0 := by rw [← mul_assoc (e (colorIdx i)), Cl55SpinorCartanFock.e_sq]; simp
  · dsimp [modeOccupied]
    calc
      ((e (colorIdx i) * f (colorIdx i)) * (e (colorIdx j) * f (colorIdx j))) *
          (e (colorIdx i) * f (colorIdx j)) =
        e (colorIdx i) * f (colorIdx i) * e (colorIdx j) *
            (f (colorIdx j) * e (colorIdx i)) * f (colorIdx j) := by noncomm_ring
      _ = -(e (colorIdx i) * f (colorIdx i) * e (colorIdx j) * e (colorIdx i) *
            (f (colorIdx j) * f (colorIdx j))) := by
        rw [hf_e]; noncomm_ring
      _ = 0 := by rw [f_sq, mul_zero, neg_zero]

private theorem colorRootGluon_kill_vacant_vacant {i j : Fin 3} (hij : i ≠ j) :
    colorRootGluon i j * (modeVacant (colorIdx i) * modeVacant (colorIdx j)) = 0 ∧
    (modeVacant (colorIdx i) * modeVacant (colorIdx j)) * colorRootGluon i j = 0 := by
  rw [colorRootGluon_eq_e_mul_f hij]
  have hne : colorIdx i ≠ colorIdx j := colorIdx_ne hij
  have hf_e : f (colorIdx j) * e (colorIdx i) = -(e (colorIdx i) * f (colorIdx j)) :=
    f_mul_e_swap_ne hne
  have hf_f : f (colorIdx j) * f (colorIdx i) = -(f (colorIdx i) * f (colorIdx j)) :=
    f_mul_f_swap (colorIdx j) (colorIdx i)
  refine ⟨?_, ?_⟩
  · dsimp [modeVacant]
    calc
      (e (colorIdx i) * f (colorIdx j)) *
          ((f (colorIdx i) * e (colorIdx i)) * (f (colorIdx j) * e (colorIdx j))) =
        e (colorIdx i) * (f (colorIdx j) * f (colorIdx i)) * e (colorIdx i) *
            f (colorIdx j) * e (colorIdx j) := by noncomm_ring
      _ = -(e (colorIdx i) * f (colorIdx i) * (f (colorIdx j) * e (colorIdx i)) *
            f (colorIdx j) * e (colorIdx j)) := by
        rw [hf_f]; noncomm_ring
      _ = e (colorIdx i) * f (colorIdx i) * e (colorIdx i) *
            (f (colorIdx j) * f (colorIdx j)) * e (colorIdx j) := by
        rw [hf_e]; noncomm_ring
      _ = 0 := by rw [f_sq, mul_zero, zero_mul]
  · dsimp [modeVacant]
    calc
      ((f (colorIdx i) * e (colorIdx i)) * (f (colorIdx j) * e (colorIdx j))) *
          (e (colorIdx i) * f (colorIdx j)) =
        f (colorIdx i) * e (colorIdx i) * f (colorIdx j) *
            (e (colorIdx j) * e (colorIdx i)) * f (colorIdx j) := by noncomm_ring
      _ = -(f (colorIdx i) * e (colorIdx i) * (f (colorIdx j) * e (colorIdx i)) *
            e (colorIdx j) * f (colorIdx j)) := by
        rw [e_mul_e_swap (colorIdx j) (colorIdx i)]; noncomm_ring
      _ = f (colorIdx i) * (e (colorIdx i) * e (colorIdx i)) * f (colorIdx j) *
            e (colorIdx j) * f (colorIdx j) := by
        rw [hf_e]; noncomm_ring
      _ = 0 := by rw [Cl55SpinorCartanFock.e_sq]; simp

private theorem mul3_reorder_left {R : Type*} [Ring R] (x : Fin 3 → R)
    (hcomm : ∀ a b : Fin 3, x a * x b = x b * x a) {i j : Fin 3} (hij : i ≠ j) :
    ∃ k : Fin 3, x 0 * x 1 * x 2 = (x i * x j) * x k := by
  fin_cases i <;> fin_cases j <;> dsimp <;> try exact absurd rfl hij
  · exact ⟨2, rfl⟩
  · exact ⟨1, by rw [mul_assoc, hcomm 1 2, ← mul_assoc]⟩
  · exact ⟨2, by rw [hcomm 0 1]⟩
  · exact ⟨0, by rw [hcomm 0 1, mul_assoc, hcomm 0 2, ← mul_assoc]⟩
  · exact ⟨1, by rw [mul_assoc, hcomm 1 2, ← mul_assoc, hcomm 0 2]⟩
  · exact ⟨0, by rw [mul_assoc, hcomm 1 2, ← mul_assoc, hcomm 0 2, mul_assoc, hcomm 0 1, ← mul_assoc]⟩

private theorem mul3_reorder_right {R : Type*} [Ring R] (x : Fin 3 → R)
    (hcomm : ∀ a b : Fin 3, x a * x b = x b * x a) {i j : Fin 3} (hij : i ≠ j) :
    ∃ k : Fin 3, x 0 * x 1 * x 2 = x k * (x i * x j) := by
  obtain ⟨k, hk⟩ := mul3_reorder_left x hcomm hij
  refine ⟨k, hk.trans ?_⟩
  rw [mul_assoc, hcomm j k, ← mul_assoc, hcomm i k, mul_assoc]

/-- **Full 8-Generator Non-Abelian `SU(3)_c` Singlet Neutrality, Lie Closure, & `C₂ = 4/3` Theorem**:
    1. All 8 `su(3)_c` generators (`colorGluonT3`, `colorGluon3Y`, and all 6 off-diagonal root
       gluons `colorRootGluon i j` for `i ≠ j`) annihilate BOTH `colorBaryonSingletProj` (`1₃`)
       and `colorVacuumSingletProj` (`1₀`) on both left and right.
    2. Complete `su(3)_c` Lie bracket closure among `{T₃, 3Y, E_{ij}}`.
    3. Exact quadratic Casimir evaluation:
       `colorSU3Casimir = (4 / 3 : ℝ) • (colorQuarkTripletProj + colorDiquarkAntitripletProj)`,
       giving `C₂(3) = 4/3`, `C₂(3̄) = 4/3`, `C₂(1₃) = 0`, `C₂(1₀) = 0`! -/
theorem cl55_full_su3_gluon_neutrality_and_casimir (i j k l : Fin 3)
    (hij : i ≠ j) :
    (colorGluonT3 * colorBaryonSingletProj = 0 ∧
     colorGluon3Y * colorBaryonSingletProj = 0 ∧
     colorRootGluon i j * colorBaryonSingletProj = 0 ∧
     colorBaryonSingletProj * colorRootGluon i j = 0) ∧
    (colorGluonT3 * colorVacuumSingletProj = 0 ∧
     colorGluon3Y * colorVacuumSingletProj = 0 ∧
     colorRootGluon i j * colorVacuumSingletProj = 0 ∧
     colorVacuumSingletProj * colorRootGluon i j = 0) ∧
    (InfoGeometry.Canonical.Cl55WittLieRouting.bracket (colorRootGluon i j) (colorRootGluon k l) =
      (if j = k then InfoGeometry.Canonical.Cl55WittLieRouting.E (colorIdx i) (colorIdx l) else 0) -
      (if l = i then InfoGeometry.Canonical.Cl55WittLieRouting.E (colorIdx k) (colorIdx j) else 0)) ∧
    (colorSU3Casimir =
      (4 / 3 : ℝ) • (colorQuarkTripletProj + colorDiquarkAntitripletProj)) ∧
    (colorSU3Casimir * colorQuarkTripletProj = (4 / 3 : ℝ) • colorQuarkTripletProj ∧
     colorSU3Casimir * colorDiquarkAntitripletProj = (4 / 3 : ℝ) • colorDiquarkAntitripletProj ∧
     colorSU3Casimir * colorBaryonSingletProj = 0 ∧
     colorSU3Casimir * colorVacuumSingletProj = 0) := by
  have hB_kill : colorRootGluon i j * colorBaryonSingletProj = 0 ∧
      colorBaryonSingletProj * colorRootGluon i j = 0 := by
    have hkill := colorRootGluon_kill_occupied_occupied hij
    have hcomm : ∀ a b : Fin 3,
        modeOccupied (colorIdx a) * modeOccupied (colorIdx b) =
        modeOccupied (colorIdx b) * modeOccupied (colorIdx a) :=
      fun a b => modeOccupied_comm (colorIdx a) (colorIdx b)
    obtain ⟨mL, hmL⟩ := mul3_reorder_left (fun a => modeOccupied (colorIdx a)) hcomm hij
    obtain ⟨mR, hmR⟩ := mul3_reorder_right (fun a => modeOccupied (colorIdx a)) hcomm hij
    have hmL' : colorBaryonSingletProj =
        (modeOccupied (colorIdx i) * modeOccupied (colorIdx j)) * modeOccupied (colorIdx mL) :=
      hmL
    have hmR' : colorBaryonSingletProj =
        modeOccupied (colorIdx mR) * (modeOccupied (colorIdx i) * modeOccupied (colorIdx j)) :=
      hmR
    refine ⟨?_, ?_⟩
    · rw [hmL', ← mul_assoc, hkill.1, zero_mul]
    · rw [hmR', mul_assoc, hkill.2, mul_zero]
  have hV_kill : colorRootGluon i j * colorVacuumSingletProj = 0 ∧
      colorVacuumSingletProj * colorRootGluon i j = 0 := by
    have hkill := colorRootGluon_kill_vacant_vacant hij
    have hvac_comm : ∀ a b : Fin 3,
        modeVacant (colorIdx a) * modeVacant (colorIdx b) =
        modeVacant (colorIdx b) * modeVacant (colorIdx a) := by
      intro a b
      rw [modeVacant_eq_one_sub_modeOccupied (colorIdx a),
          modeVacant_eq_one_sub_modeOccupied (colorIdx b)]
      calc (1 - modeOccupied (colorIdx a)) * (1 - modeOccupied (colorIdx b)) =
          1 - modeOccupied (colorIdx a) - modeOccupied (colorIdx b) +
            modeOccupied (colorIdx a) * modeOccupied (colorIdx b) := by noncomm_ring
      _ = 1 - modeOccupied (colorIdx b) - modeOccupied (colorIdx a) +
            modeOccupied (colorIdx b) * modeOccupied (colorIdx a) := by
          rw [modeOccupied_comm (colorIdx a) (colorIdx b)]; abel
      _ = (1 - modeOccupied (colorIdx b)) * (1 - modeOccupied (colorIdx a)) := by noncomm_ring
    obtain ⟨mL, hmL⟩ := mul3_reorder_left (fun a => modeVacant (colorIdx a)) hvac_comm hij
    obtain ⟨mR, hmR⟩ := mul3_reorder_right (fun a => modeVacant (colorIdx a)) hvac_comm hij
    have hmL' : colorVacuumSingletProj =
        (modeVacant (colorIdx i) * modeVacant (colorIdx j)) * modeVacant (colorIdx mL) :=
      hmL
    have hmR' : colorVacuumSingletProj =
        modeVacant (colorIdx mR) * (modeVacant (colorIdx i) * modeVacant (colorIdx j)) :=
      hmR
    refine ⟨?_, ?_⟩
    · rw [hmL', ← mul_assoc, hkill.1, zero_mul]
    · rw [hmR', mul_assoc, hkill.2, mul_zero]
  have h_casimir :
      colorSU3Casimir = (4 / 3 : ℝ) • (colorQuarkTripletProj + colorDiquarkAntitripletProj) := by
    have hcart := colorGluon_cartan_casimir_eq_four_colored_sectors
    have hroots :
        (∑ a : Fin 3, ∑ b : Fin 3,
          if a = b then 0 else colorRootGluon a b * colorRootGluon b a) =
        (2 : ℝ) • (colorQuarkTripletProj + colorDiquarkAntitripletProj) := by
      simp only [Fin.sum_univ_three, ↓reduceIte,
        show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
        show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
        show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
        colorRootGluon_mul_swap (by decide : (0 : Fin 3) ≠ 1),
        colorRootGluon_mul_swap (by decide : (0 : Fin 3) ≠ 2),
        colorRootGluon_mul_swap (by decide : (1 : Fin 3) ≠ 0),
        colorRootGluon_mul_swap (by decide : (1 : Fin 3) ≠ 2),
        colorRootGluon_mul_swap (by decide : (2 : Fin 3) ≠ 0),
        colorRootGluon_mul_swap (by decide : (2 : Fin 3) ≠ 1)]
      rw [colorQuark_add_diquark_quadratic_reduction]
      dsimp [colorIdx]
      rw [modeVacant_eq_one_sub_modeOccupied 0,
          modeVacant_eq_one_sub_modeOccupied 1,
          modeVacant_eq_one_sub_modeOccupied 2]
      calc
        (0 + modeOccupied 0 * (1 - modeOccupied 1) + modeOccupied 0 * (1 - modeOccupied 2)) +
          (modeOccupied 1 * (1 - modeOccupied 0) + 0 + modeOccupied 1 * (1 - modeOccupied 2)) +
          (modeOccupied 2 * (1 - modeOccupied 0) + modeOccupied 2 * (1 - modeOccupied 1) + 0) =
          (2 : ℝ) • (modeOccupied 0 + modeOccupied 1 + modeOccupied 2) -
            ((modeOccupied 0 * modeOccupied 1 + modeOccupied 1 * modeOccupied 0) +
             (modeOccupied 0 * modeOccupied 2 + modeOccupied 2 * modeOccupied 0) +
             (modeOccupied 1 * modeOccupied 2 + modeOccupied 2 * modeOccupied 1)) := by
          rw [two_smul ℝ]; noncomm_ring
        _ = (2 : ℝ) • (modeOccupied 0 + modeOccupied 1 + modeOccupied 2 -
              modeOccupied 0 * modeOccupied 1 - modeOccupied 0 * modeOccupied 2 -
              modeOccupied 1 * modeOccupied 2) := by
          rw [modeOccupied_comm 1 0, modeOccupied_comm 2 0, modeOccupied_comm 2 1]
          simp only [two_smul ℝ]
          noncomm_ring
    dsimp [colorSU3Casimir]
    have hcart' : (3 : ℝ) • (colorGluonT3 * colorGluonT3) + colorGluon3Y * colorGluon3Y =
        (4 : ℝ) • (colorQuarkTripletProj + colorDiquarkAntitripletProj) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ 3, ← Nat.cast_smul_eq_nsmul ℝ 4] at hcart
      simpa using hcart
    rw [hcart', hroots, smul_smul, smul_smul, ← add_smul]
    norm_num
  -- Projector idempotency and orthogonality in `MatStage 5` via `ColorIsospinCharge`
  have hcol := InfoGeometry.Physics.ColorIsospinCharge.color_orthogonal_idempotent_partition
    (modeOccupied_idem 0) (modeOccupied_idem 1) (modeOccupied_idem 2)
    (modeOccupied_comm 0 1) (modeOccupied_comm 0 2) (modeOccupied_comm 1 2)
  have hV_eq : InfoGeometry.Physics.ColorOccupationPolynomials.vacuum
      (modeOccupied 0) (modeOccupied 1) (modeOccupied 2) = colorVacuumSingletProj := by
    simp [InfoGeometry.Physics.ColorOccupationPolynomials.vacuum, colorVacuumSingletProj,
      ← modeVacant_eq_one_sub_modeOccupied]
  have hQ_eq : InfoGeometry.Physics.ColorOccupationPolynomials.quark
      (modeOccupied 0) (modeOccupied 1) (modeOccupied 2) = colorQuarkTripletProj := by
    simp [InfoGeometry.Physics.ColorOccupationPolynomials.quark, colorQuarkTripletProj,
      ← modeVacant_eq_one_sub_modeOccupied]
  have hD_eq : InfoGeometry.Physics.ColorOccupationPolynomials.diquark
      (modeOccupied 0) (modeOccupied 1) (modeOccupied 2) = colorDiquarkAntitripletProj := by
    simp [InfoGeometry.Physics.ColorOccupationPolynomials.diquark, colorDiquarkAntitripletProj,
      ← modeVacant_eq_one_sub_modeOccupied]
  have hB_eq : InfoGeometry.Physics.ColorOccupationPolynomials.baryon
      (modeOccupied 0) (modeOccupied 1) (modeOccupied 2) = colorBaryonSingletProj := rfl
  rw [hV_eq, hQ_eq, hD_eq, hB_eq] at hcol
  rcases hcol with ⟨⟨_, hQ_idem, hD_idem, _⟩,
    ⟨_, _, _, h10, h12, h13, h20, h21, h23, _, _, _⟩, _⟩
  refine ⟨⟨colorGluon_cartan_singlet_neutrality.1, colorGluon_cartan_singlet_neutrality.2,
      hB_kill.1, hB_kill.2⟩,
    ⟨colorGluon_cartan_vacuum_singlet_neutrality.1, colorGluon_cartan_vacuum_singlet_neutrality.2,
      hV_kill.1, hV_kill.2⟩,
    ?_, h_casimir, ?_⟩
  · dsimp [colorRootGluon]
    rw [InfoGeometry.Canonical.Cl55WittLieRouting.E_bracket]
    have heq1 : (colorIdx j = colorIdx k) ↔ (j = k) := by
      simp [colorIdx, Fin.ext_iff]
    have heq2 : (colorIdx i = colorIdx l) ↔ (l = i) := by
      simp [colorIdx, Fin.ext_iff, eq_comm]
    simp [heq1, heq2]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_casimir, smul_mul_assoc, add_mul, hQ_idem, h21, add_zero]
    · rw [h_casimir, smul_mul_assoc, add_mul, h12, hD_idem, zero_add]
    · rw [h_casimir, smul_mul_assoc, add_mul, h13, h23, add_zero, smul_zero]
    · rw [h_casimir, smul_mul_assoc, add_mul, h10, h20, add_zero, smul_zero]

end InfoGeometry.Physics.Cl55WignerSU4Embedding
