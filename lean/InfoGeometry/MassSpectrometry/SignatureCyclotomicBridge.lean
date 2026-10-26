import InfoGeometry.MassSpectrometry.SignatureCorrelationGeometry
import InfoGeometry.Core.PeirceWeylUnits

/-!
# Observable support → square-zero pair → supported cyclotomic operators

This is a representation on a doubled carrier, constructed from an actual
signature projector. It does not turn the transient K itself into a root of
identity, nor infer measured periodicity from correlation. The existing Peirce
and Weyl owners supply the polynomial laws and harmonic completion.
-/
noncomputable section
namespace InfoGeometry.MassSpectrometry.SignatureCyclotomic
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra
open InfoGeometry.Core.PeirceWeylUnits
open SignatureGeometry

section Algebra
variable {A : Type*} [Ring A] [StarRing A]

/-- The canonical directed corner of the doubled observable support. -/
def raise (P : A) : Matrix (Fin 2) (Fin 2) A := !![0, P; 0, 0]
def lower (P : A) : Matrix (Fin 2) (Fin 2) A := !![0, 0; P, 0]

omit [StarRing A] in
theorem raise_square_zero (P : A) : raise P * raise P = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [raise, Matrix.mul_apply, Fin.sum_univ_two]

omit [StarRing A] in
theorem lower_square_zero (P : A) : lower P * lower P = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower, Matrix.mul_apply, Fin.sum_univ_two]

/-- A self-adjoint idempotent supplies the partner; no inverse is postulated. -/
theorem doubled_mp_pair (P : A) (hp : P*P=P) (hs : star P=P) :
    IsMoorePenroseInverse (raise P) (lower P) := by
  refine IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [raise, lower, Matrix.mul_apply, Fin.sum_univ_two, hp]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [raise, lower, Matrix.mul_apply, Fin.sum_univ_two, hp]
  · change (raise P * lower P).conjTranspose = raise P * lower P
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [raise, lower, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two, hp, hs]
  · change (lower P * raise P).conjTranspose = lower P * raise P
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [raise, lower, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two, hp, hs]

omit [StarRing A] in
theorem doubled_support (P : A) (hp : P*P=P) :
    activeSupport (raise P) (lower P) = !![P, 0; 0, P] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [activeSupport, exactSupport, coexactSupport, raise, lower, hp]

omit [StarRing A] in
/-- A nilpotent in a nontrivial ring cannot itself be a unit. -/
theorem nilpotent_not_unit [Nontrivial A] (a : A) (N : ℕ) (h : a^N=0) : ¬ IsUnit a := by
  intro hu
  have hn := hu.pow N
  rw [h] at hn
  exact not_isUnit_zero hn

end Algebra

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def signatureRaise (O : E →L[ℝ] F) := raise (visible O)
def signatureLower (O : E →L[ℝ] F) := lower (visible O)

theorem signature_mp_pair (O : E →L[ℝ] F) :
    IsMoorePenroseInverse (signatureRaise O) (signatureLower O) :=
  doubled_mp_pair _ (visible_idempotent O) (visible_selfAdjoint O)

/-- The four/equivariant root is an actual ambient unit on the doubled state space. -/
def signatureWeylUnit (O : E →L[ℝ] F) :
    (Matrix (Fin 2) (Fin 2) (E →L[ℝ] E))ˣ :=
  weylUnit (signature_mp_pair O) (raise_square_zero (visible O))

theorem signatureWeyl_fourth (O : E →L[ℝ] F) :
    (signatureWeylUnit O).val ^ 4 = 1 :=
  weyl_fourth (signature_mp_pair O) (raise_square_zero (visible O))

/-- Supported Phi_3, Phi_4 and Phi_6 identities, not ambient scalar roots. -/
theorem signature_cyclotomic_laws (O : E →L[ℝ] F) :
    let d := signatureRaise O
    let b := signatureLower O
    let Δ := activeSupport d b
    (majoranaMinus d b * majoranaMinus d b = -Δ) ∧
    (thirdRoot d b * thirdRoot d b + thirdRoot d b + Δ = 0) ∧
    (thirdRoot d b ^ 3 = Δ) ∧
    (sixthRoot d b * sixthRoot d b - sixthRoot d b + Δ = 0) ∧
    (sixthRoot d b ^ 3 = -Δ) ∧ (sixthRoot d b ^ 6 = Δ) := by
  dsimp only
  have h := signature_mp_pair O
  have hz := raise_square_zero (visible O)
  exact ⟨skew_square h hz, thirdRoot_polynomial h hz,
    thirdRoot_cube h hz, sixthRoot_laws h hz⟩

/-- The missing ambient constant is exactly the invisible doubled complement. -/
theorem fourth_polynomial_residual (O : E →L[ℝ] F) :
    majoranaMinus (signatureRaise O) (signatureLower O) ^ 2 + 1 =
      1 - activeSupport (signatureRaise O) (signatureLower O) := by
  rw [pow_two, skew_square (signature_mp_pair O) (raise_square_zero (visible O))]
  abel

/-- Same Gram-null directions are exactly annihilated by the visible support. -/
theorem support_detects_gram (O : E →L[ℝ] F) (x : E) :
    visible O x = 0 ↔ gram O x = 0 := visible_gram_kernel O x

end InfoGeometry.MassSpectrometry.SignatureCyclotomic
