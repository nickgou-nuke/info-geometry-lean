import Mathlib
import proofs.FiniteMatrixKnillLaflamme
import proofs.PeirceTensorQEC

noncomputable section

namespace CuntzPeirceKnillLaflamme

open PeirceTensorQEC

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def SatisfiesKnillLaflammeIn {ι : Type*}
    (P : A) (E : ι → A) : Prop :=
  ∃ coeff : ι → ι → ℂ, ∀ a b, P * star (E a) * E b * P = (coeff a b) • P

theorem SatisfiesKnillLaflammeIn.map {B ι : Type*} [Ring B] [StarRing B]
    [Algebra ℂ B] [StarModule ℂ B]
    (Φ : B →⋆ₐ[ℂ] A) {P : B} {E : ι → B}
    (hKL : ∃ coeff : ι → ι → ℂ,
      ∀ a b, P * star (E a) * E b * P = (coeff a b) • P) :
    SatisfiesKnillLaflammeIn (Φ P) (fun a => Φ (E a)) := by
  rcases hKL with ⟨coeff, hcoeff⟩
  refine ⟨coeff, ?_⟩
  intro a b
  have h := congrArg Φ (hcoeff a b)
  simpa only [map_mul, map_star, map_smul] using h

theorem peirce_knillLaflamme_transport
    {ι : Type*} (Φ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →⋆ₐ[ℂ] A)
    (F : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    SatisfiesKnillLaflammeIn (Φ peirceCodeProjector)
      (fun a => Φ (firstFactorError F a)) := by
  apply SatisfiesKnillLaflammeIn.map Φ
  simpa [FiniteMatrixKnillLaflamme.SatisfiesKnillLaflamme,
    Matrix.conjTranspose] using (peirceTensor_knillLaflamme F)

end CuntzPeirceKnillLaflamme
