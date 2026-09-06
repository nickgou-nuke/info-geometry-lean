import InfoGeometry.Canonical.OperatorZornFourPotentialGauge

/-! Chiral coordinate projections of the full operator-Zorn four-potential.

These are linear readouts of the existing eight coefficient channels.  They do
not install an associative product or identify the readouts with physical
gauge groups.
-/
namespace InfoGeometry.Canonical.OperatorZornChiralProjection

open InfoGeometry.Physics.NCG
open InfoGeometry.Canonical.OperatorZornFourPotentialGauge

variable {A : Type*} [Ring A]

abbrev Z := OperatorZornMatrix A

def projNPlus (X : Z) : Z :=
  operatorZornCoordinates X.n_plus 0 (fun _ => 0) (fun _ => 0)

def projNMinus (X : Z) : Z :=
  operatorZornCoordinates 0 X.n_minus (fun _ => 0) (fun _ => 0)

def projSigmaPlus (X : Z) : Z :=
  operatorZornCoordinates 0 0 X.sigma_plus (fun _ => 0)

def projSigmaMinus (X : Z) : Z :=
  operatorZornCoordinates 0 0 (fun _ => 0) X.sigma_minus

theorem proj_completeness (X : Z) :
    projNPlus X + projNMinus X + projSigmaPlus X + projSigmaMinus X = X := by
  apply operatorZornMatrix_ext
  · dsimp [projNPlus, projNMinus, projSigmaPlus, projSigmaMinus]
    simp only [zornAdd_nPlus, operatorZornCoordinates_n_plus]
    noncomm_ring
  · dsimp [projNPlus, projNMinus, projSigmaPlus, projSigmaMinus]
    simp only [zornAdd_nMinus, operatorZornCoordinates_n_minus]
    noncomm_ring
  · funext i
    dsimp [projNPlus, projNMinus, projSigmaPlus, projSigmaMinus]
    simp only [zornAdd_sigmaPlus_apply,
      operatorZornCoordinates_sigma_plus_apply]
    noncomm_ring
  · funext i
    dsimp [projNPlus, projNMinus, projSigmaPlus, projSigmaMinus]
    simp only [zornAdd_sigmaMinus_apply,
      operatorZornCoordinates_sigma_minus_apply]
    noncomm_ring

theorem projNPlus_idempotent (X : Z) :
    projNPlus (projNPlus X) = projNPlus X := by
  apply operatorZornMatrix_ext <;> (try funext i) <;>
    simp [projNPlus]

theorem projNMinus_idempotent (X : Z) :
    projNMinus (projNMinus X) = projNMinus X := by
  apply operatorZornMatrix_ext <;> (try funext i) <;>
    simp [projNMinus]

theorem projSigmaPlus_idempotent (X : Z) :
    projSigmaPlus (projSigmaPlus X) = projSigmaPlus X := by
  apply operatorZornMatrix_ext <;> (try funext i) <;>
    simp [projSigmaPlus]

theorem projSigmaMinus_idempotent (X : Z) :
    projSigmaMinus (projSigmaMinus X) = projSigmaMinus X := by
  apply operatorZornMatrix_ext <;> (try funext i) <;>
    simp [projSigmaMinus]

def AEM (Phi : FourPotential A) (mu : Fin 4) : A :=
  (Phi mu).n_plus + (Phi mu).n_minus

def AAxial (Phi : FourPotential A) (mu : Fin 4) : A :=
  (Phi mu).n_plus - (Phi mu).n_minus

theorem AEM_add_AAxial (Phi : FourPotential A) (mu : Fin 4) :
    AEM Phi mu + AAxial Phi mu =
      (Phi mu).n_plus + (Phi mu).n_plus := by
  dsimp [AEM, AAxial]
  noncomm_ring

theorem AEM_sub_AAxial (Phi : FourPotential A) (mu : Fin 4) :
    AEM Phi mu - AAxial Phi mu =
      (Phi mu).n_minus + (Phi mu).n_minus := by
  dsimp [AEM, AAxial]
  noncomm_ring

theorem fieldStrength_nPlus (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu : Fin 4) :
    (fieldStrength p Phi mu nu).n_plus =
      coefficientBracket (p mu) ((Phi nu).n_plus) -
      coefficientBracket (p nu) ((Phi mu).n_plus) +
      coefficientBracket ((Phi mu).n_plus) ((Phi nu).n_plus) +
      (NCZornElement.zornDot (Phi mu).sigma_plus (Phi nu).sigma_minus -
       NCZornElement.zornDot (Phi nu).sigma_plus (Phi mu).sigma_minus) := by
  dsimp [fieldStrength, bracket]
  simp only [zornAdd_nPlus, zornSub_nPlus, zornMul_nPlus,
    coefficientDeriv_nPlus, coefficientBracket]
  noncomm_ring

theorem fieldStrength_nMinus (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu : Fin 4) :
    (fieldStrength p Phi mu nu).n_minus =
      coefficientBracket (p mu) ((Phi nu).n_minus) -
      coefficientBracket (p nu) ((Phi mu).n_minus) +
      coefficientBracket ((Phi mu).n_minus) ((Phi nu).n_minus) +
      (NCZornElement.zornDot (Phi mu).sigma_minus (Phi nu).sigma_plus -
       NCZornElement.zornDot (Phi nu).sigma_minus (Phi mu).sigma_plus) := by
  dsimp [fieldStrength, bracket]
  simp only [zornAdd_nMinus, zornSub_nMinus, zornMul_nMinus,
    coefficientDeriv_nMinus, coefficientBracket]
  noncomm_ring

def lambdaEM (Lambda : Z) : A := Lambda.n_plus + Lambda.n_minus

def lambdaAxial (Lambda : Z) : A := Lambda.n_plus - Lambda.n_minus

def wTriplet (Lambda : Z) : Fin 3 → A :=
  fun i => Lambda.sigma_plus i + Lambda.sigma_minus i

def bTriplet (Lambda : Z) : Fin 3 → A :=
  fun i => Lambda.sigma_plus i - Lambda.sigma_minus i

def deltaPhi (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) : Z :=
  gaugeVariation p Phi Lambda mu

theorem deltaPhi_nPlus (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) :
    (deltaPhi p Phi Lambda mu).n_plus =
      coefficientBracket (p mu) Lambda.n_plus +
      coefficientBracket (Phi mu).n_plus Lambda.n_plus +
      (NCZornElement.zornDot (Phi mu).sigma_plus Lambda.sigma_minus -
       NCZornElement.zornDot Lambda.sigma_plus (Phi mu).sigma_minus) := by
  dsimp [deltaPhi, gaugeVariation, adjointCovariant, bracket]
  simp only [zornAdd_nPlus, zornMul_nPlus, coefficientDeriv_nPlus,
    coefficientBracket]
  noncomm_ring

theorem deltaPhi_nMinus (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) :
    (deltaPhi p Phi Lambda mu).n_minus =
      coefficientBracket (p mu) Lambda.n_minus +
      coefficientBracket (Phi mu).n_minus Lambda.n_minus +
      (NCZornElement.zornDot (Phi mu).sigma_minus Lambda.sigma_plus -
       NCZornElement.zornDot Lambda.sigma_minus (Phi mu).sigma_plus) := by
  dsimp [deltaPhi, gaugeVariation, adjointCovariant, bracket]
  simp only [zornAdd_nMinus, zornMul_nMinus, coefficientDeriv_nMinus,
    coefficientBracket]
  noncomm_ring

theorem deltaPhi_sigmaPlus_apply (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) (i : Fin 3) :
    (deltaPhi p Phi Lambda mu).sigma_plus i =
      coefficientBracket (p mu) (Lambda.sigma_plus i) +
      ((Phi mu).n_plus * Lambda.sigma_plus i +
       (Phi mu).sigma_plus i * Lambda.n_minus -
       Lambda.n_plus * (Phi mu).sigma_plus i -
       Lambda.sigma_plus i * (Phi mu).n_minus) -
      (NCZornElement.zornCross (Phi mu).sigma_minus Lambda.sigma_minus i -
       NCZornElement.zornCross Lambda.sigma_minus (Phi mu).sigma_minus i) := by
  dsimp [deltaPhi, gaugeVariation, adjointCovariant, bracket]
  simp only [zornAdd_sigmaPlus_apply, zornMul_sigmaPlus_apply,
    coefficientDeriv_sigmaPlus_apply, coefficientBracket]
  noncomm_ring

theorem deltaPhi_sigmaMinus_apply (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) (i : Fin 3) :
    (deltaPhi p Phi Lambda mu).sigma_minus i =
      coefficientBracket (p mu) (Lambda.sigma_minus i) +
      ((Phi mu).n_minus * Lambda.sigma_minus i +
       (Phi mu).sigma_minus i * Lambda.n_plus -
       Lambda.n_minus * (Phi mu).sigma_minus i -
       Lambda.sigma_minus i * (Phi mu).n_plus) +
      (NCZornElement.zornCross (Phi mu).sigma_plus Lambda.sigma_plus i -
       NCZornElement.zornCross Lambda.sigma_plus (Phi mu).sigma_plus i) := by
  dsimp [deltaPhi, gaugeVariation, adjointCovariant, bracket]
  simp only [zornAdd_sigmaMinus_apply, zornMul_sigmaMinus_apply,
    coefficientDeriv_sigmaMinus_apply, coefficientBracket]
  noncomm_ring

def deltaAEM (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) : A :=
  (deltaPhi p Phi Lambda mu).n_plus + (deltaPhi p Phi Lambda mu).n_minus

theorem deltaAEM_eq (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) :
    deltaAEM p Phi Lambda mu =
      coefficientBracket (p mu) (lambdaEM Lambda) +
      coefficientBracket (Phi mu).n_plus Lambda.n_plus +
      coefficientBracket (Phi mu).n_minus Lambda.n_minus +
      (NCZornElement.zornDot (Phi mu).sigma_plus Lambda.sigma_minus -
       NCZornElement.zornDot Lambda.sigma_plus (Phi mu).sigma_minus) +
      (NCZornElement.zornDot (Phi mu).sigma_minus Lambda.sigma_plus -
       NCZornElement.zornDot Lambda.sigma_minus (Phi mu).sigma_plus) := by
  dsimp [deltaAEM, lambdaEM]
  rw [deltaPhi_nPlus, deltaPhi_nMinus]
  simp only [coefficientBracket]
  noncomm_ring

def deltaW (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) : Fin 3 → A :=
  fun i => (deltaPhi p Phi Lambda mu).sigma_plus i +
    (deltaPhi p Phi Lambda mu).sigma_minus i

def deltaB (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) : Fin 3 → A :=
  fun i => (deltaPhi p Phi Lambda mu).sigma_plus i -
    (deltaPhi p Phi Lambda mu).sigma_minus i

theorem deltaW_apply (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) (i : Fin 3) :
    deltaW p Phi Lambda mu i =
      coefficientBracket (p mu) (wTriplet Lambda i) +
      ((Phi mu).n_plus * Lambda.sigma_plus i +
       (Phi mu).sigma_plus i * Lambda.n_minus -
       Lambda.n_plus * (Phi mu).sigma_plus i -
       Lambda.sigma_plus i * (Phi mu).n_minus) +
      ((Phi mu).n_minus * Lambda.sigma_minus i +
       (Phi mu).sigma_minus i * Lambda.n_plus -
       Lambda.n_minus * (Phi mu).sigma_minus i -
       Lambda.sigma_minus i * (Phi mu).n_plus) -
      (NCZornElement.zornCross (Phi mu).sigma_minus Lambda.sigma_minus i -
       NCZornElement.zornCross Lambda.sigma_minus (Phi mu).sigma_minus i) +
      (NCZornElement.zornCross (Phi mu).sigma_plus Lambda.sigma_plus i -
       NCZornElement.zornCross Lambda.sigma_plus (Phi mu).sigma_plus i) := by
  dsimp [deltaW, deltaPhi, gaugeVariation, adjointCovariant, bracket,
    wTriplet]
  simp only [zornAdd_sigmaPlus_apply, zornAdd_sigmaMinus_apply,
    zornMul_sigmaPlus_apply, zornMul_sigmaMinus_apply,
    coefficientDeriv_sigmaPlus_apply, coefficientDeriv_sigmaMinus_apply,
    coefficientBracket]
  noncomm_ring

theorem deltaB_apply (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) (i : Fin 3) :
    deltaB p Phi Lambda mu i =
      coefficientBracket (p mu) (bTriplet Lambda i) +
      ((Phi mu).n_plus * Lambda.sigma_plus i +
       (Phi mu).sigma_plus i * Lambda.n_minus -
       Lambda.n_plus * (Phi mu).sigma_plus i -
       Lambda.sigma_plus i * (Phi mu).n_minus) -
      ((Phi mu).n_minus * Lambda.sigma_minus i +
       (Phi mu).sigma_minus i * Lambda.n_plus -
       Lambda.n_minus * (Phi mu).sigma_minus i -
       Lambda.sigma_minus i * (Phi mu).n_plus) -
      (NCZornElement.zornCross (Phi mu).sigma_minus Lambda.sigma_minus i -
       NCZornElement.zornCross Lambda.sigma_minus (Phi mu).sigma_minus i) -
      (NCZornElement.zornCross (Phi mu).sigma_plus Lambda.sigma_plus i -
       NCZornElement.zornCross Lambda.sigma_plus (Phi mu).sigma_plus i) := by
  dsimp [deltaB, deltaPhi, gaugeVariation, adjointCovariant, bracket,
    bTriplet]
  simp only [zornSub_sigmaPlus_apply, zornSub_sigmaMinus_apply,
    zornMul_sigmaPlus_apply, zornMul_sigmaMinus_apply,
    coefficientDeriv_sigmaPlus_apply, coefficientDeriv_sigmaMinus_apply,
    coefficientBracket]
  noncomm_ring

theorem deltaAEM_pure_scalar (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4)
    (hsp : Lambda.sigma_plus = fun _ => 0)
    (hsm : Lambda.sigma_minus = fun _ => 0) :
    deltaAEM p Phi Lambda mu =
      coefficientBracket (p mu) (lambdaEM Lambda) +
      coefficientBracket (Phi mu).n_plus Lambda.n_plus +
      coefficientBracket (Phi mu).n_minus Lambda.n_minus := by
  rw [deltaAEM_eq]
  rw [hsp, hsm]
  simp only [NCZornElement.zornDot]
  noncomm_ring

theorem deltaAEM_pure_triplet (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4)
    (hnp : Lambda.n_plus = 0) (hnm : Lambda.n_minus = 0) :
    deltaAEM p Phi Lambda mu =
      (NCZornElement.zornDot (Phi mu).sigma_plus Lambda.sigma_minus -
       NCZornElement.zornDot Lambda.sigma_plus (Phi mu).sigma_minus) +
      (NCZornElement.zornDot (Phi mu).sigma_minus Lambda.sigma_plus -
       NCZornElement.zornDot Lambda.sigma_minus (Phi mu).sigma_plus) := by
  rw [deltaAEM_eq]
  dsimp [lambdaEM]
  rw [hnp, hnm]
  simp only [coefficientBracket]
  noncomm_ring

theorem deltaW_pure_triplet (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : Z) (mu : Fin 4) (i : Fin 3)
    (hnp : Lambda.n_plus = 0) (hnm : Lambda.n_minus = 0) :
    deltaW p Phi Lambda mu i =
      coefficientBracket (p mu) (wTriplet Lambda i) -
      (NCZornElement.zornCross (Phi mu).sigma_minus Lambda.sigma_minus i -
       NCZornElement.zornCross Lambda.sigma_minus (Phi mu).sigma_minus i) +
      (NCZornElement.zornCross (Phi mu).sigma_plus Lambda.sigma_plus i -
       NCZornElement.zornCross Lambda.sigma_plus (Phi mu).sigma_plus i) := by
  rw [deltaW_apply]
  rw [hnp, hnm]
  noncomm_ring

end InfoGeometry.Canonical.OperatorZornChiralProjection
