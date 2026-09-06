import proofs.KleinBottleSixfoldCyclotomic
import proofs.KleinSixStateBundle

/-!
# Standard-form modular conjugation identification

This owner works on the finite Hilbert--Schmidt standard form.  For a
self-adjoint involution `Theta`, the anti-linear map
`X ↦ Theta X† Theta` exchanges left multiplication with right multiplication.
The concrete `internalGlide` candidate is supplied separately with its Weyl
involution hypotheses.
-/

noncomputable section
namespace SixStateModularConjugationIdentification

open TwoSheetThreeColorWeyl
open KleinBottleSixfoldCyclotomic

abbrev HS6 := M6C

def leftAction (A X : HS6) : HS6 := A * X
def rightAction (X A : HS6) : HS6 := X * A

def twistedTomita (Theta X : HS6) : HS6 :=
  Theta * Matrix.conjTranspose X * Theta

structure ThetaInvolution where
  theta : HS6
  sq : theta * theta = (1 : HS6)
  selfAdjoint : Matrix.conjTranspose theta = theta

@[simp] theorem twistedTomita_involutive
    (Θ : ThetaInvolution) (X : HS6) :
    twistedTomita Θ.theta (twistedTomita Θ.theta X) = X := by
  unfold twistedTomita
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Θ.selfAdjoint, Matrix.conjTranspose_conjTranspose]
  calc
    Θ.theta * (Θ.theta * (X * Θ.theta)) * Θ.theta =
        (Θ.theta * Θ.theta) * X * (Θ.theta * Θ.theta) := by noncomm_ring
    _ = X := by simp [Θ.sq]

theorem twistedTomita_left_to_right
    (Θ : ThetaInvolution) (A X : HS6) :
    twistedTomita Θ.theta (leftAction A (twistedTomita Θ.theta X)) =
      rightAction X (Θ.theta * Matrix.conjTranspose A * Θ.theta) := by
  unfold twistedTomita leftAction rightAction
  simp only [Matrix.conjTranspose_mul, Θ.selfAdjoint,
    Matrix.conjTranspose_conjTranspose]
  calc
    Θ.theta * (Θ.theta * (X * Θ.theta) * Matrix.conjTranspose A) * Θ.theta =
        (Θ.theta * Θ.theta) * X * Θ.theta * Matrix.conjTranspose A * Θ.theta := by
          noncomm_ring
    _ = X * Θ.theta * Matrix.conjTranspose A * Θ.theta := by
          rw [Θ.sq, Matrix.one_mul]
    _ = X * (Θ.theta * Matrix.conjTranspose A * Θ.theta) := by
          simp [Matrix.mul_assoc]

def thetaSix : HS6 := internalGlide

def thetaSixData (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : ThetaInvolution where
  theta := thetaSix
  sq := (internal_klein_relations ω hω).1
  selfAdjoint := by
    ext ⟨s, a⟩ ⟨t, b⟩
    fin_cases s <;> fin_cases a <;> fin_cases t <;> fin_cases b <;>
      simp [thetaSix, internalGlide, tensor, sheetFlip,
        colorReflection, Matrix.conjTranspose, Matrix.kroneckerMap_apply]

theorem thetaSix_twistedTomita_involutive
    (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (X : HS6) :
    twistedTomita thetaSix (twistedTomita thetaSix X) = X := by
  exact twistedTomita_involutive (thetaSixData ω hω) X

structure DensityDatum (Θ : ThetaInvolution) where
  rho : HS6
  rhoInv : HS6
  rho_mul_inv : rho * rhoInv = (1 : HS6)
  inv_mul_rho : rhoInv * rho = (1 : HS6)
  rho_selfAdjoint : Matrix.conjTranspose rho = rho
  rhoInv_selfAdjoint : Matrix.conjTranspose rhoInv = rhoInv
  theta_rho : Θ.theta * rho * Θ.theta = rho
  theta_rhoInv : Θ.theta * rhoInv * Θ.theta = rhoInv

def modularOperatorRho (D : DensityDatum Θ) (X : HS6) : HS6 :=
  D.rho * X * D.rhoInv

def modularOperatorRhoInv (D : DensityDatum Θ) (X : HS6) : HS6 :=
  D.rhoInv * X * D.rho

theorem twistedTomita_modular_inverse
    (D : DensityDatum Θ) (X : HS6) :
    twistedTomita Θ.theta (modularOperatorRho D
      (twistedTomita Θ.theta X)) = modularOperatorRhoInv D X := by
  unfold twistedTomita modularOperatorRho modularOperatorRhoInv
  simp only [Matrix.conjTranspose_mul, Θ.selfAdjoint,
    D.rho_selfAdjoint, D.rhoInv_selfAdjoint,
    Matrix.conjTranspose_conjTranspose]
  calc
    Θ.theta * (D.rhoInv * (Θ.theta * (X * Θ.theta) * D.rho)) * Θ.theta =
        (Θ.theta * D.rhoInv * Θ.theta) * X * (Θ.theta * D.rho * Θ.theta) := by
          noncomm_ring
    _ = D.rhoInv * X * D.rho := by rw [D.theta_rhoInv, D.theta_rho]

theorem modularOperatorRho_mul_inv
    (D : DensityDatum Θ) (X : HS6) :
    modularOperatorRho D (modularOperatorRhoInv D X) = X := by
  unfold modularOperatorRho modularOperatorRhoInv
  calc
    D.rho * (D.rhoInv * X * D.rho) * D.rhoInv =
        (D.rho * D.rhoInv) * X * (D.rho * D.rhoInv) := by noncomm_ring
    _ = X := by simp [D.rho_mul_inv]

def thetaConjugation (A : HS6) : HS6 :=
  thetaSix * A * thetaSix

theorem thetaConjugation_internalParity
    (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    thetaConjugation internalParity = -internalParity := by
  unfold thetaConjugation thetaSix internalGlide
  unfold internalParity
  rcases sheet_parity with ⟨_, _, hJΓ⟩
  rcases color_reflection_relations ω hω with ⟨hR, _, _⟩
  calc
    tensor sheetFlip colorReflection * tensor sheetGamma (1 : M3C) *
        tensor sheetFlip colorReflection =
        tensor (sheetFlip * sheetGamma * sheetFlip)
          (colorReflection * (1 : M3C) * colorReflection) := by
            simp [tensor_mul, Matrix.mul_assoc]
    _ = tensor (-sheetGamma) (1 : M3C) := by
      rw [hJΓ, Matrix.mul_one, hR]
    _ = -internalParity := by
      ext ⟨s, a⟩ ⟨t, b⟩
      fin_cases s <;> fin_cases t <;>
        simp [tensor, internalParity, Matrix.kroneckerMap_apply]

theorem thetaConjugation_triality
    (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    thetaConjugation sixfoldTriality = -(sixfoldTriality ^ 5) := by
  exact KleinSixStateBundle.theta_triality_theta ω hω

end SixStateModularConjugationIdentification
end noncomputable section
