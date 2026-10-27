import InfoGeometry.Twistor.PerjesConventions
import InfoGeometry.Twistor.InfinityTwistor

/-!
# The kinematic twistor and its mixed-index operator

The symmetric contravariant tensor of Perjes (6.4) is distinct from the
alternating Plucker bivector and from the mixed-index moment operator.
The contravariant infinity tensor is a map from the dual, not an inverse
of the existing degenerate covariant infinity form.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwistorKinematicTensor

open Matrix
open scoped BigOperators
open PenroseIncidence PerjesConventions

abbrev TwistorIndex := Fin 2 ⊕ Fin 2
abbrev KinematicMatrix := Matrix TwistorIndex TwistorIndex ℂ

def twistorCoordinate (Z : Twistor4) : TwistorIndex → ℂ := Sum.elim Z.1 Z.2

@[simp] theorem twistorCoordinate_smul (c : ℂ) (Z : Twistor4) (a : TwistorIndex) :
    twistorCoordinate (c • Z) a = c * twistorCoordinate Z a := by
  cases a <;> rfl

@[simp] theorem twistorCoordinate_add (Z W : Twistor4) (a : TwistorIndex) :
    twistorCoordinate (Z + W) a = twistorCoordinate Z a + twistorCoordinate W a := by
  cases a <;> rfl

def upperBasis (i : Fin 2) : Twistor4 := (Pi.single i 1, 0)

/-- Upper infinity bivector contracted with an actual algebraic covector. -/
def infinitySharp : Module.Dual ℂ Twistor4 →ₗ[ℂ] Twistor4 where
  toFun f := f (upperBasis 1) • upperBasis 0 - f (upperBasis 0) • upperBasis 1
  map_add' f g := by simp [add_smul]; abel
  map_smul' c f := by simp [smul_sub, smul_smul]

theorem infinitySharp_alternating (f g : Module.Dual ℂ Twistor4) :
    f (infinitySharp g) = -g (infinitySharp f) := by
  simp [infinitySharp]
  ring

/-- Conjugation into the dual in the incidence frame. -/
def twistorCovector (Z : Twistor4) : Module.Dual ℂ Twistor4 where
  toFun W := incidenceHermitian Z W
  map_add' W V := by simp [incidenceHermitian, Fin.sum_univ_two]; ring
  map_smul' c W := by simp [incidenceHermitian, Fin.sum_univ_two, smul_eq_mul]; ring

def raisedConjugate (Z : Twistor4) : Twistor4 := infinitySharp (twistorCovector Z)

theorem raisedConjugate_explicit (Z : Twistor4) :
    raisedConjugate Z = (![star (Z.2 1), -star (Z.2 0)], 0) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [raisedConjugate, infinitySharp, twistorCovector, incidenceHermitian,
      upperBasis, Fin.sum_univ_two]

@[simp] theorem raisedConjugate_snd (Z : Twistor4) : (raisedConjugate Z).2 = 0 := by
  rw [raisedConjugate_explicit]

@[simp] theorem raisedConjugate_add (Z W : Twistor4) :
    raisedConjugate (Z + W) = raisedConjugate Z + raisedConjugate W := by
  simp only [raisedConjugate_explicit]
  apply Prod.ext <;> funext i <;> fin_cases i <;> simp [add_comm]

@[simp] theorem raisedConjugate_smul (c : ℂ) (Z : Twistor4) :
    raisedConjugate (c • Z) = star c • raisedConjugate Z := by
  simp only [raisedConjugate_explicit]
  apply Prod.ext <;> funext i <;> fin_cases i <;> simp [smul_eq_mul]

@[simp] theorem raisedConjugate_zero : raisedConjugate 0 = 0 := by
  simp [raisedConjugate_explicit]

@[simp] theorem raisedConjugate_raisedConjugate (Z : Twistor4) :
    raisedConjugate (raisedConjugate Z) = 0 := by
  simp [raisedConjugate_explicit]

theorem infinityTwistor_raisedConjugate (Z : Twistor4) :
    InfinityTwistor.infinityTwistor (raisedConjugate Z) = 0 := by
  exact (InfinityTwistor.infinityTwistor_radical _).2 (raisedConjugate_snd Z)

/-- Equation (6.4), with symmetrization expanded and no scalar proxy. -/
def kinematic (Z : Twistor4) : KinematicMatrix :=
  vecMulVec (twistorCoordinate Z) (twistorCoordinate (raisedConjugate Z)) +
    vecMulVec (twistorCoordinate (raisedConjugate Z)) (twistorCoordinate Z)

theorem kinematic_symmetric (Z : Twistor4) : (kinematic Z)ᵀ = kinematic Z := by
  ext a b
  simp [kinematic, vecMulVec]
  ring

theorem kinematic_smul (c : ℂ) (Z : Twistor4) :
    kinematic (c • Z) = (c * star c) • kinematic Z := by
  ext a b
  simp [kinematic, vecMulVec, raisedConjugate_smul, twistorCoordinate_smul,
    smul_eq_mul]
  ring

theorem kinematic_phase_invariant (c : ℂ) (hc : c * star c = 1) (Z : Twistor4) :
    kinematic (c • Z) = kinematic Z := by
  rw [kinematic_smul, hc, one_smul]

/-- Future-positive rank-one momentum in the declared spinor convention. -/
def momentum (Z : Twistor4) : ComplexSpacetime := vecMulVec Z.2 (star Z.2)

theorem momentum_hermitian (Z : Twistor4) : (momentum Z)ᴴ = momentum Z := by
  ext i j
  simp [momentum, vecMulVec, mul_comm]

theorem kinematic_lower_block_zero (Z : Twistor4) (i j : Fin 2) :
    kinematic Z (.inr i) (.inr j) = 0 := by
  simp [kinematic, vecMulVec, twistorCoordinate, raisedConjugate_explicit]

theorem kinematic_momentum_column_zero (Z : Twistor4) (i : Fin 2) :
    kinematic Z (.inr i) (.inl 0) = momentum Z i 1 := by
  simp [kinematic, momentum, vecMulVec, twistorCoordinate, raisedConjugate_explicit]

theorem kinematic_momentum_column_one (Z : Twistor4) (i : Fin 2) :
    kinematic Z (.inr i) (.inl 1) = -momentum Z i 0 := by
  simp [kinematic, momentum, vecMulVec, twistorCoordinate, raisedConjugate_explicit]

def angularSpinor (Z : Twistor4) : ComplexSpacetime :=
  (kinematic Z).submatrix Sum.inl Sum.inl

theorem angularSpinor_symmetric (Z : Twistor4) : (angularSpinor Z)ᵀ = angularSpinor Z := by
  ext i j
  exact congrFun (congrFun (kinematic_symmetric Z) (.inl i)) (.inl j)

theorem momentum_translation (X : ComplexSpacetime) (Z : Twistor4) :
    momentum (InfinityTwistor.translation X Z) = momentum Z := rfl

def conjugateCoordinate (Z : Twistor4) : TwistorIndex → ℂ :=
  Sum.elim (star Z.2) (star Z.1)

/-- A mixed-index operator; unlike `kinematic`, it composes as an endomorphism. -/
def momentOperator (Z : Twistor4) : KinematicMatrix :=
  vecMulVec (twistorCoordinate Z) (conjugateCoordinate Z)

theorem momentOperator_square (Z : Twistor4) :
    momentOperator Z * momentOperator Z = incidenceHermitian Z Z • momentOperator Z := by
  ext a b
  simp [momentOperator, vecMulVec, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, incidenceHermitian, twistorCoordinate, conjugateCoordinate,
    smul_eq_mul]
  ring

theorem null_momentOperator_square (Z : Twistor4) (hZ : incidenceHermitian Z Z = 0) :
    momentOperator Z * momentOperator Z = 0 := by
  rw [momentOperator_square, hZ, zero_smul]

/-- Genuine noncommutativity, even on two null rank-one moment operators. -/
theorem momentOperators_noncommuting :
    ∃ Z W : Twistor4,
      incidenceHermitian Z Z = 0 ∧ incidenceHermitian W W = 0 ∧
      momentOperator Z * momentOperator W ≠ momentOperator W * momentOperator Z := by
  let Z : Twistor4 := (![1, 0], 0)
  let W : Twistor4 := (0, ![1, 0])
  refine ⟨Z, W, by simp [Z, incidenceHermitian], by simp [W, incidenceHermitian], ?_⟩
  intro h
  have h00 := congrArg (fun M : KinematicMatrix => M (.inl 0) (.inl 0)) h
  norm_num [momentOperator, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    vecMulVec, twistorCoordinate, conjugateCoordinate, Z, W] at h00

end InfoGeometry.Twistor.TwistorKinematicTensor
