import InfoGeometry.Canonical.OperatorZornFourPotentialGauge
import InfoGeometry.Canonical.OperatorZornRealModule

namespace InfoGeometry.Canonical.OperatorZornFourPotentialGauge

open InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A]

abbrev FourCurrent (A : Type*) [Ring A] := Fin 4 → OperatorZornMatrix A

abbrev zornZero : OperatorZornMatrix A := 0

@[simp] theorem zornZero_n_plus : (zornZero : OperatorZornMatrix A).n_plus = 0 := rfl
@[simp] theorem zornZero_n_minus : (zornZero : OperatorZornMatrix A).n_minus = 0 := rfl
@[simp] theorem zornZero_sigma_plus (i : Fin 3) :
    (zornZero : OperatorZornMatrix A).sigma_plus i = 0 := rfl
@[simp] theorem zornZero_sigma_minus (i : Fin 3) :
    (zornZero : OperatorZornMatrix A).sigma_minus i = 0 := rfl

def adjointDivergenceMinkowski (p : Fin 4 → A) (Phi : FourPotential A)
    (nu : Fin 4) : OperatorZornMatrix A :=
  - adjointCovariant p Phi 0 (fieldStrength p Phi 0 nu) +
    adjointCovariant p Phi 1 (fieldStrength p Phi 1 nu) +
    adjointCovariant p Phi 2 (fieldStrength p Phi 2 nu) +
    adjointCovariant p Phi 3 (fieldStrength p Phi 3 nu)

def adjointDivergenceSplit (p : Fin 4 → A) (Phi : FourPotential A)
    (nu : Fin 4) : OperatorZornMatrix A :=
  adjointCovariant p Phi 0 (fieldStrength p Phi 0 nu) -
    adjointCovariant p Phi 1 (fieldStrength p Phi 1 nu) +
    adjointCovariant p Phi 2 (fieldStrength p Phi 2 nu) -
    adjointCovariant p Phi 3 (fieldStrength p Phi 3 nu)

def IsMaxwellZornSolution (p : Fin 4 → A) (Phi : FourPotential A)
    (J : FourCurrent A) : Prop :=
  ∀ nu, adjointDivergenceMinkowski p Phi nu = J nu

theorem fieldStrength_self_zero (p : Fin 4 → A) (Phi : FourPotential A)
    (mu : Fin 4) : fieldStrength p Phi mu mu = zornZero := by
  apply operatorZornMatrix_ext
  · dsimp [fieldStrength, bracket, coefficientBracket, zornZero]
    simp
  · dsimp [fieldStrength, bracket, coefficientBracket, zornZero]
    simp
  · funext i
    dsimp [fieldStrength, bracket, coefficientBracket, zornZero]
    simp
  · funext i
    dsimp [fieldStrength, bracket, coefficientBracket, zornZero]
    simp

theorem adjointCovariant_zero (p : Fin 4 → A) (Phi : FourPotential A)
    (mu : Fin 4) : adjointCovariant p Phi mu zornZero = zornZero := by
  apply operatorZornMatrix_ext
  · dsimp [adjointCovariant, bracket, coefficientBracket, zornZero]
    simp [operatorZornCoordinates, coefficientDeriv, coefficientBracket,
      NCZornElement.zornDot,
      NCZornElement.zornCross]
  · dsimp [adjointCovariant, bracket, coefficientBracket, zornZero]
    simp [operatorZornCoordinates, coefficientDeriv, coefficientBracket,
      NCZornElement.zornDot,
      NCZornElement.zornCross]
  · funext i
    dsimp [adjointCovariant, bracket, coefficientBracket, zornZero]
    simp [operatorZornCoordinates, coefficientDeriv, coefficientBracket,
      NCZornElement.zornDot,
      NCZornElement.zornCross, zornZero_n_plus, zornZero_n_minus,
      zornZero_sigma_plus, zornZero_sigma_minus]
  · funext i
    dsimp [adjointCovariant, bracket, coefficientBracket, zornZero]
    simp [operatorZornCoordinates, coefficientDeriv, coefficientBracket,
      NCZornElement.zornDot,
      NCZornElement.zornCross, zornZero_n_plus, zornZero_n_minus,
      zornZero_sigma_plus, zornZero_sigma_minus]

theorem adjointCovariant_neg (p : Fin 4 → A) (Phi : FourPotential A)
    (mu : Fin 4) (X : OperatorZornMatrix A) :
    adjointCovariant p Phi mu (-X) = -adjointCovariant p Phi mu X := by
  apply operatorZornMatrix_ext
  · dsimp [adjointCovariant, bracket, coefficientDeriv, coefficientBracket]
    simp [coefficientBracket, NCZornElement.zornDot, NCZornElement.zornCross]
    noncomm_ring
  · dsimp [adjointCovariant, bracket, coefficientDeriv, coefficientBracket]
    simp [coefficientBracket, NCZornElement.zornDot, NCZornElement.zornCross]
    noncomm_ring
  · funext i
    dsimp [adjointCovariant, bracket, coefficientDeriv, coefficientBracket]
    fin_cases i <;>
      simp [coefficientBracket, NCZornElement.zornDot, NCZornElement.zornCross] <;>
      noncomm_ring
  · funext i
    dsimp [adjointCovariant, bracket, coefficientDeriv, coefficientBracket]
    fin_cases i <;>
      simp [coefficientBracket, NCZornElement.zornDot, NCZornElement.zornCross] <;>
      noncomm_ring

theorem maxwellZorn_gauss (p : Fin 4 → A) (Phi : FourPotential A) :
    adjointDivergenceMinkowski p Phi 0 =
      adjointCovariant p Phi 1 (fieldStrength p Phi 1 0) +
      adjointCovariant p Phi 2 (fieldStrength p Phi 2 0) +
      adjointCovariant p Phi 3 (fieldStrength p Phi 3 0) := by
  unfold adjointDivergenceMinkowski
  rw [fieldStrength_self_zero, adjointCovariant_zero]
  simp

theorem maxwellZorn_ampere_x (p : Fin 4 → A) (Phi : FourPotential A) :
    adjointDivergenceMinkowski p Phi 1 =
      -adjointCovariant p Phi 0 (electric p Phi 0) -
        adjointCovariant p Phi 2 (magnetic p Phi 2) +
        adjointCovariant p Phi 3 (magnetic p Phi 1) := by
  unfold adjointDivergenceMinkowski electric magnetic
  rw [fieldStrength_self_zero, adjointCovariant_zero]
  rw [fieldStrength_swap p Phi 2 1, adjointCovariant_neg]
  simp

theorem maxwellZorn_ampere_y (p : Fin 4 → A) (Phi : FourPotential A) :
    adjointDivergenceMinkowski p Phi 2 =
      -adjointCovariant p Phi 0 (electric p Phi 1) +
        adjointCovariant p Phi 1 (magnetic p Phi 2) -
        adjointCovariant p Phi 3 (magnetic p Phi 0) := by
  unfold adjointDivergenceMinkowski electric magnetic
  rw [fieldStrength_self_zero, adjointCovariant_zero]
  rw [fieldStrength_swap p Phi 3 2, adjointCovariant_neg]
  simp

theorem maxwellZorn_ampere_z (p : Fin 4 → A) (Phi : FourPotential A) :
    adjointDivergenceMinkowski p Phi 3 =
      -adjointCovariant p Phi 0 (electric p Phi 2) -
        adjointCovariant p Phi 1 (magnetic p Phi 1) +
        adjointCovariant p Phi 2 (magnetic p Phi 0) := by
  unfold adjointDivergenceMinkowski electric magnetic
  rw [fieldStrength_self_zero, adjointCovariant_zero]
  rw [fieldStrength_swap p Phi 1 3, adjointCovariant_neg]
  simp

end InfoGeometry.Canonical.OperatorZornFourPotentialGauge
