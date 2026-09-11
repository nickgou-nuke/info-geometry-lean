import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearBdGSolovievCompression

/-!
# A common CAR--phonon carrier and finite Soloviev compression

The carrier `ℕ → Fock4` combines the finite two-mode CAR representation with an
algebraic bosonic occupation ladder. Fermionic maps act pointwise in the
occupation coordinate; bosonic maps shift that coordinate. Thus exact CAR,
exact CCR, and cross-commutation hold in one associative endomorphism algebra.

Compressing the oscillator Hamiltonian to one fixed quasiparticle vector and
occupation levels `0,1` gives the finite Soloviev matrix exactly.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearCARPhononCommonCarrier

open InfoGeometry.Physics.NuclearTwoModeCARFiveGrade
open InfoGeometry.Physics.NuclearBdGSolovievCompression

abbrev CoupledCarrier := ℕ → Fock4
abbrev CoupledEnd := Module.End ℂ CoupledCarrier

/-! ## Pointwise fermionic operators -/

/-- Pointwise lift of a finite CAR operator. -/
def pointwiseLift (T : Op) : CoupledEnd where
  toFun f n := T (f n)
  map_add' f g := by
    funext n
    simp
  map_smul' c f := by
    funext n
    simp

@[simp] theorem pointwiseLift_apply
    (T : Op) (f : CoupledCarrier) (n : ℕ) :
    pointwiseLift T f n = T (f n) := rfl

@[simp] theorem pointwiseLift_zero : pointwiseLift 0 = 0 := by
  apply LinearMap.ext
  intro f
  funext n
  simp

@[simp] theorem pointwiseLift_one : pointwiseLift 1 = 1 := by
  apply LinearMap.ext
  intro f
  funext n
  rfl

@[simp] theorem pointwiseLift_add (T U : Op) :
    pointwiseLift (T + U) = pointwiseLift T + pointwiseLift U := by
  apply LinearMap.ext
  intro f
  funext n
  rfl

@[simp] theorem pointwiseLift_mul (T U : Op) :
    pointwiseLift (T * U) = pointwiseLift T * pointwiseLift U := by
  apply LinearMap.ext
  intro f
  funext n
  rfl

/-- The first CAR relation persists on the common carrier. -/
theorem common_CAR_one :
    pointwiseLift annihilationOne * pointwiseLift creationOne +
      pointwiseLift creationOne * pointwiseLift annihilationOne = 1 := by
  rw [← pointwiseLift_mul, ← pointwiseLift_mul,
    ← pointwiseLift_add, CAR_one, pointwiseLift_one]

/-- The second CAR relation persists on the common carrier. -/
theorem common_CAR_two :
    pointwiseLift annihilationTwo * pointwiseLift creationTwo +
      pointwiseLift creationTwo * pointwiseLift annihilationTwo = 1 := by
  rw [← pointwiseLift_mul, ← pointwiseLift_mul,
    ← pointwiseLift_add, CAR_two, pointwiseLift_one]

/-! ## Algebraic bosonic ladder -/

/-- Unnormalised creation shift. -/
def bosonCreation : CoupledEnd where
  toFun f n :=
    match n with
    | 0 => 0
    | k + 1 => f k
  map_add' f g := by
    funext n
    cases n <;> simp [Pi.add_apply]
  map_smul' c f := by
    funext n
    cases n <;> simp [Pi.smul_apply]

/-- Weighted annihilation shift. -/
def bosonAnnihilation : CoupledEnd where
  toFun f n := ((n + 1 : ℕ) : ℂ) • f (n + 1)
  map_add' f g := by
    funext n
    simp [smul_add]
  map_smul' c f := by
    funext n
    simp only [Pi.smul_apply, smul_smul]
    change (((n + 1 : ℕ) : ℂ) * c) • f (n + 1) =
      (c * ((n + 1 : ℕ) : ℂ)) • f (n + 1)
    rw [mul_comm]

@[simp] theorem bosonCreation_zero (f : CoupledCarrier) :
    bosonCreation f 0 = 0 := rfl

@[simp] theorem bosonCreation_succ (f : CoupledCarrier) (n : ℕ) :
    bosonCreation f (n + 1) = f n := rfl

@[simp] theorem bosonAnnihilation_apply
    (f : CoupledCarrier) (n : ℕ) :
    bosonAnnihilation f n = ((n + 1 : ℕ) : ℂ) • f (n + 1) := rfl

/-- Exact algebraic Heisenberg CCR. -/
theorem boson_CCR :
    bosonAnnihilation * bosonCreation -
      bosonCreation * bosonAnnihilation = 1 := by
  apply LinearMap.ext
  intro f
  funext n
  ext i
  cases n with
  | zero => simp [Module.End.mul_apply]
  | succ n =>
      simp [Module.End.mul_apply]
      ring

/-- Bosonic occupation operator. -/
def bosonNumber : CoupledEnd := bosonCreation * bosonAnnihilation

@[simp] theorem bosonNumber_apply (f : CoupledCarrier) (n : ℕ) :
    bosonNumber f n = (n : ℂ) • f n := by
  cases n with
  | zero => simp [bosonNumber, Module.End.mul_apply]
  | succ n => simp [bosonNumber, Module.End.mul_apply]

/-- Number weight of bosonic creation. -/
theorem bosonNumber_comm_creation :
    bosonNumber * bosonCreation - bosonCreation * bosonNumber =
      bosonCreation := by
  apply LinearMap.ext
  intro f
  funext n
  ext i
  cases n with
  | zero => simp [Module.End.mul_apply]
  | succ n =>
      simp [Module.End.mul_apply, bosonNumber_apply]
      ring

/-- Number weight of bosonic annihilation. -/
theorem bosonNumber_comm_annihilation :
    bosonNumber * bosonAnnihilation - bosonAnnihilation * bosonNumber =
      -bosonAnnihilation := by
  apply LinearMap.ext
  intro f
  funext n
  ext i
  simp [Module.End.mul_apply, bosonNumber_apply]
  ring

/-! ## CAR and CCR act on independent coordinates -/

/-- Every pointwise fermionic operator commutes with bosonic creation. -/
theorem pointwiseLift_commutes_bosonCreation (T : Op) :
    pointwiseLift T * bosonCreation =
      bosonCreation * pointwiseLift T := by
  apply LinearMap.ext
  intro f
  funext n
  cases n <;> simp [Module.End.mul_apply]

/-- Every pointwise fermionic operator commutes with bosonic annihilation. -/
theorem pointwiseLift_commutes_bosonAnnihilation (T : Op) :
    pointwiseLift T * bosonAnnihilation =
      bosonAnnihilation * pointwiseLift T := by
  apply LinearMap.ext
  intro f
  funext n
  simp [Module.End.mul_apply]

/-! ## Finite two-sector compression -/

/-- Fixed one-quasiparticle vector. -/
def quasiparticleVector : Fock4 := ![0, 1, 0, 0]

@[simp] theorem quasiparticleVector_zero : quasiparticleVector 0 = 0 := rfl
@[simp] theorem quasiparticleVector_one : quasiparticleVector 1 = 1 := rfl
@[simp] theorem quasiparticleVector_two : quasiparticleVector 2 = 0 := rfl
@[simp] theorem quasiparticleVector_three : quasiparticleVector 3 = 0 := rfl

/-- Embed two amplitudes into levels zero and one. -/
def twoSectorEmbed : EvenSector →ₗ[ℂ] CoupledCarrier where
  toFun φ n :=
    match n with
    | 0 => φ 0 • quasiparticleVector
    | k + 1 =>
        match k with
        | 0 => φ 1 • quasiparticleVector
        | _ + 1 => 0
  map_add' φ ψ := by
    funext n
    cases n with
    | zero => simp [add_smul]
    | succ n =>
        cases n <;> simp [add_smul]
  map_smul' c φ := by
    funext n
    cases n with
    | zero => simp [smul_smul]
    | succ n =>
        cases n <;> simp [smul_smul]

/-- Read the selected quasiparticle coefficient at levels zero and one. -/
def twoSectorProject : CoupledCarrier →ₗ[ℂ] EvenSector where
  toFun f := ![f 0 1, f 1 1]
  map_add' f g := by
    ext i
    fin_cases i <;> simp
  map_smul' c f := by
    ext i
    fin_cases i <;> simp

@[simp] theorem twoSectorEmbed_zero_level (φ : EvenSector) :
    twoSectorEmbed φ 0 = φ 0 • quasiparticleVector := rfl

@[simp] theorem twoSectorEmbed_one_level (φ : EvenSector) :
    twoSectorEmbed φ 1 = φ 1 • quasiparticleVector := rfl

@[simp] theorem twoSectorEmbed_high_level
    (φ : EvenSector) (n : ℕ) :
    twoSectorEmbed φ (n + 2) = 0 := by
  rfl

@[simp] theorem twoSectorProject_twoSectorEmbed :
    twoSectorProject.comp twoSectorEmbed = LinearMap.id := by
  apply LinearMap.ext
  intro φ
  ext i
  fin_cases i <;> simp [twoSectorProject]

/-- Algebraic quasiparticle--phonon oscillator Hamiltonian. -/
def oscillatorHamiltonian (Eqp ω V : ℂ) : CoupledEnd :=
  Eqp • 1 + ω • bosonNumber + V • (bosonCreation + bosonAnnihilation)

/-- Compression to the selected quasiparticle and levels `0,1`. -/
def compressedOscillatorHamiltonian
    (Eqp ω V : ℂ) : EvenEnd :=
  twoSectorProject.comp ((oscillatorHamiltonian Eqp ω V).comp twoSectorEmbed)

@[simp] theorem compressedOscillatorHamiltonian_apply
    (Eqp ω V : ℂ) (φ : EvenSector) :
    compressedOscillatorHamiltonian Eqp ω V φ =
      ![Eqp * φ 0 + V * φ 1,
        V * φ 0 + (Eqp + ω) * φ 1] := by
  ext i
  fin_cases i <;>
    simp [compressedOscillatorHamiltonian, oscillatorHamiltonian,
      Module.End.mul_apply, twoSectorProject, bosonNumber_apply] <;>
    ring

/-- Compression is exactly the finite Soloviev matrix action. -/
theorem compressedOscillatorHamiltonian_eq_soloviev
    (Eqp ω V : ℂ) (φ : EvenSector) :
    compressedOscillatorHamiltonian Eqp ω V φ =
      Matrix.mulVec (solovievBlock Eqp ω V) φ := by
  ext i
  fin_cases i <;>
    simp [compressedOscillatorHamiltonian_apply, solovievBlock,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

/-- Exact CAR, CCR, cross-commutation, and Soloviev compression coexist on one
associative carrier. -/
theorem nuclear_common_car_ccr_soloviev_packet
    (Eqp ω V : ℂ) :
    pointwiseLift annihilationOne * pointwiseLift creationOne +
        pointwiseLift creationOne * pointwiseLift annihilationOne = 1 ∧
      bosonAnnihilation * bosonCreation -
        bosonCreation * bosonAnnihilation = 1 ∧
      pointwiseLift creationOne * bosonCreation =
        bosonCreation * pointwiseLift creationOne ∧
      ∀ φ : EvenSector,
        compressedOscillatorHamiltonian Eqp ω V φ =
          Matrix.mulVec (solovievBlock Eqp ω V) φ := by
  exact ⟨common_CAR_one, boson_CCR,
    pointwiseLift_commutes_bosonCreation creationOne,
    compressedOscillatorHamiltonian_eq_soloviev Eqp ω V⟩

end InfoGeometry.Physics.NuclearCARPhononCommonCarrier
