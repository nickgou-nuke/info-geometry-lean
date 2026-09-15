import InfoGeometry.Physics.NuclearPairCAR

noncomputable section

namespace InfoGeometry.Physics.SolovievPhononCorrections

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

namespace ProofDependency

inductive Archetype
  | carRelations
  | fermionicBogoliubov
  | pairNormalOrder
  | phononCorrection
  | circularCoefficients
  | vacuumReadout
  deriving DecidableEq, Fintype

open Archetype

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

end ProofDependency

end InfoGeometry.Physics.SolovievPhononCorrections
