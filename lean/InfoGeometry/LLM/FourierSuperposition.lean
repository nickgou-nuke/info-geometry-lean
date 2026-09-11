import InfoGeometry.LLM.FourierCharacterEncoding
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.LLM

/-! Finite Fourier superpositions of relative-position characters. -/

noncomputable def finiteFourierKernel {G ι : Type*} [AddMonoid G]
    [Fintype ι] (coeff : ι → ℂ) (characters : ι → FourierCharacter G)
    (t s : G) : ℂ :=
  ∑ i, coeff i * fourierCharacterKernel (characters i) t s

theorem finiteFourierKernel_zero {G ι : Type*} [AddGroup G]
    [Fintype ι] (coeff : ι → ℂ) (characters : ι → FourierCharacter G)
    (t : G) :
    finiteFourierKernel coeff characters t (-t) = ∑ i, coeff i := by
  simp [finiteFourierKernel, fourierCharacterKernel_zero]

theorem finiteFourierKernel_translation_invariant
    {G ι : Type*} [AddCommGroup G] [Fintype ι]
    (coeff : ι → ℂ) (characters : ι → FourierCharacter G)
    (t s a : G) :
    finiteFourierKernel coeff characters (t + a) (-(s + a)) =
      finiteFourierKernel coeff characters t (-s) := by
  apply Finset.sum_congr rfl
  intro i hi
  have h := fourierCharacterKernel_add_left (characters i) a t s
  simpa [add_comm] using congrArg (fun z : ℂ => coeff i * z) h

end InfoGeometry.LLM
