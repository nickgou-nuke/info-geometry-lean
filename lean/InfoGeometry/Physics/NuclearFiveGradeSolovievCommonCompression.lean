import Mathlib
import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
import InfoGeometry.Physics.SolovievQuasiparticlePhononEigenproblem

/-!
# Soloviev compression on the grade-preserving common carrier

The common representation carrier

`ℕ → (Fin 4 → NativeZorn)`

already supports the complete concrete two-mode five-grading, exact fermionic
CAR, exact phonon CCR, and the coefficientwise Zorn derivation action.  This
file selects one occupied quasiparticle basis vector at phonon levels zero and
one and proves that the compressed represented Hamiltonian is exactly the
finite Soloviev QPNM matrix.

Thus the five-grade representation and the Soloviev compression now live on
the same operator carrier.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression

open Matrix
open InfoGeometry.Algebra
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.SolovievQPNMEigenproblem

abbrev ModelVector := Fin 2 → ℝ

/-- Scalar copy of the native Zorn unit. -/
def scalarCoefficient (c : ℝ) : Coefficient where
  a := c
  v := fun _ => 0
  w := fun _ => 0
  b := c

/-- The selected quasiparticle mode is the `|10⟩` Jordan--Wigner basis vector. -/
def quasiparticleKet (c : ℝ) : FermionVector :=
  ![0, 0, scalarCoefficient c, 0]

@[simp] theorem quasiparticleKet_selected_a (c : ℝ) :
    (quasiparticleKet c 2).a = c := rfl

/-- Embed the zero- and one-phonon quasiparticle channels. -/
def modelEmbed : ModelVector →ₗ[ℝ] Carrier where
  toFun v
    | 0 => quasiparticleKet (v 0)
    | Nat.succ 0 => quasiparticleKet (v 1)
    | Nat.succ (Nat.succ _) => 0
  map_add' v w := by
    funext n i
    cases n with
    | zero =>
        fin_cases i <;> simp [quasiparticleKet, scalarCoefficient]
    | succ n =>
        cases n with
        | zero =>
            fin_cases i <;> simp [quasiparticleKet, scalarCoefficient]
        | succ n => simp
  map_smul' c v := by
    funext n i
    cases n with
    | zero =>
        fin_cases i <;> simp [quasiparticleKet, scalarCoefficient]
    | succ n =>
        cases n with
        | zero =>
            fin_cases i <;> simp [quasiparticleKet, scalarCoefficient]
        | succ n => simp

@[simp] theorem modelEmbed_zero_level (v : ModelVector) :
    modelEmbed v 0 = quasiparticleKet (v 0) := rfl

@[simp] theorem modelEmbed_one_level (v : ModelVector) :
    modelEmbed v 1 = quasiparticleKet (v 1) := rfl

@[simp] theorem modelEmbed_high_level (v : ModelVector) (n : ℕ) :
    modelEmbed v (n + 2) = 0 := by
  rfl

/-- Read the scalar coefficient of the selected quasiparticle basis vector. -/
def modelReadout : Carrier →ₗ[ℝ] ModelVector where
  toFun ψ := ![(ψ 0 2).a, (ψ 1 2).a]
  map_add' ψ φ := by
    ext i
    fin_cases i <;> simp
  map_smul' c ψ := by
    ext i
    fin_cases i <;> simp

@[simp] theorem modelReadout_modelEmbed (v : ModelVector) :
    modelReadout (modelEmbed v) = v := by
  ext i
  fin_cases i <;> rfl

/-- Model-space projection on the common carrier. -/
def modelProjection : Operator :=
  modelEmbed.comp modelReadout

@[simp] theorem modelProjection_modelEmbed (v : ModelVector) :
    modelProjection (modelEmbed v) = modelEmbed v := by
  change modelEmbed (modelReadout (modelEmbed v)) = modelEmbed v
  rw [modelReadout_modelEmbed]

/-- The common model projection is idempotent. -/
theorem modelProjection_idempotent :
    modelProjection * modelProjection = modelProjection := by
  apply LinearMap.ext
  intro ψ
  change modelEmbed
      (modelReadout (modelEmbed (modelReadout ψ))) =
    modelEmbed (modelReadout ψ)
  rw [modelReadout_modelEmbed]

/-- Explicit first-mode occupation matrix. -/
theorem number1_eq_diagonal :
    number1 =
      !![0, 0, 0, 0;
          0, 0, 0, 0;
          0, 0, 1, 0;
          0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [number1, a1, a1Dag, Matrix.mul_apply,
      Fin.sum_univ_four]

/-- Represented quasiparticle number. -/
def quasiparticleNumber : Operator :=
  representation number1

/-- Phonon number. -/
def phononNumber : Operator :=
  phononCreation * phononAnnihilation

/-- Full represented quasiparticle--phonon Hamiltonian. -/
def fullHamiltonian (Eqp omega V : ℝ) : Operator :=
  Eqp • quasiparticleNumber + omega • phononNumber +
    V • (phononCreation + phononAnnihilation)

/-- Compression of the represented Hamiltonian. -/
def compressedAction (Eqp omega V : ℝ) :
    ModelVector →ₗ[ℝ] ModelVector :=
  modelReadout.comp ((fullHamiltonian Eqp omega V).comp modelEmbed)

/-- Zero-phonon readout. -/
theorem compressedAction_zero
    (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] 0 = Eqp * C + V * D := by
  rw [show number1 =
      !![0, 0, 0, 0;
          0, 0, 0, 0;
          0, 0, 1, 0;
          0, 0, 0, 1] from number1_eq_diagonal]
  simp [compressedAction, fullHamiltonian, quasiparticleNumber,
    phononNumber, modelReadout, modelEmbed, quasiparticleKet,
    scalarCoefficient, representation, occupationLift, fermionAction,
    phononCreation, phononAnnihilation, Module.End.mul_apply,
    Fin.sum_univ_four]
  ring

/-- One-phonon readout. -/
theorem compressedAction_one
    (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] 1 =
      V * C + (Eqp + omega) * D := by
  rw [show number1 =
      !![0, 0, 0, 0;
          0, 0, 0, 0;
          0, 0, 1, 0;
          0, 0, 0, 1] from number1_eq_diagonal]
  simp [compressedAction, fullHamiltonian, quasiparticleNumber,
    phononNumber, modelReadout, modelEmbed, quasiparticleKet,
    scalarCoefficient, representation, occupationLift, fermionAction,
    phononCreation, phononAnnihilation, Module.End.mul_apply,
    Fin.sum_univ_four]
  ring

/-- Main same-carrier compression theorem. -/
theorem compressedAction_eq_qpnm_mulVec
    (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] =
      mulVec (qpnmMatrix Eqp omega V) ![C, D] := by
  ext i
  fin_cases i
  · rw [compressedAction_zero]
    simp [qpnmMatrix, mulVec, dotProduct, Fin.sum_univ_two]
  · rw [compressedAction_one]
    simp [qpnmMatrix, mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- Exact projected-Hamiltonian theorem on the represented common carrier. -/
theorem projected_fullHamiltonian_on_model
    (Eqp omega V C D : ℝ) :
    modelProjection
        (fullHamiltonian Eqp omega V
          (modelProjection (modelEmbed ![C, D]))) =
      modelEmbed (mulVec (qpnmMatrix Eqp omega V) ![C, D]) := by
  rw [modelProjection_modelEmbed]
  change modelEmbed (compressedAction Eqp omega V ![C, D]) = _
  rw [compressedAction_eq_qpnm_mulVec]

/-- Complete same-carrier closure packet. -/
theorem five_grade_soloviev_same_carrier_packet
    (Eqp omega V C D : ℝ) :
    modelProjection * modelProjection = modelProjection ∧
      RepresentedHasGrade 2 (representation pairCreation) ∧
      RepresentedHasGrade (-2) (representation pairAnnihilation) ∧
      modelProjection
          (fullHamiltonian Eqp omega V
            (modelProjection (modelEmbed ![C, D]))) =
        modelEmbed (mulVec (qpnmMatrix Eqp omega V) ![C, D]) := by
  exact ⟨modelProjection_idempotent,
    representation_preserves_grade pairCreation_grade,
    representation_preserves_grade pairAnnihilation_grade,
    projected_fullHamiltonian_on_model Eqp omega V C D⟩

end InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
