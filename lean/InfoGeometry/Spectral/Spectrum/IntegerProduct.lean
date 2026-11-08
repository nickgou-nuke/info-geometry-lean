import InfoGeometry.Spectral.Spectrum.Integer
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Products of integer-indexed spectra

The product is levelwise.  The structure equivalences are transported by
`Equiv.prodCongr`; no stable or topological smash-product claim is made here.
-/

namespace InfoGeometry.Spectral.Spectrum.Integer

def product (E F : Spectrum) : Spectrum where
  toPrespectrum := {
    space := fun n => E.space n × F.space n
    step := fun n x => (E.step n x.1, F.step n x.2)
  }
  stepEquiv := fun n => Equiv.prodCongr (E.stepEquiv n) (F.stepEquiv n)
  stepEquiv_apply := by
    intro n x
    rcases x with ⟨x, y⟩
    simp [Spectrum.stepEquiv_readback]

@[simp] theorem product_space (E F : Spectrum) (n : ℤ) :
    (product E F).space n = (E.space n × F.space n) :=
  rfl

@[simp] theorem product_step (E F : Spectrum) (n : ℤ)
    (x : E.space n × F.space n) :
    (product E F).step n x = (E.step n x.1, F.step n x.2) :=
  rfl

@[simp] theorem product_stepEquiv_apply (E F : Spectrum) (n : ℤ)
    (x : E.space n × F.space n) :
    (product E F).stepEquiv n x = (E.stepEquiv n x.1, F.stepEquiv n x.2) :=
  rfl

def productMap {E E' F F' : Spectrum}
    (f : SpectrumMap E E') (g : SpectrumMap F F') :
    SpectrumMap (product E F) (product E' F') where
  toMap := {
    toFun := fun n x => (f n x.1, g n x.2)
    comm := by
      intro n x
      rcases x with ⟨x, y⟩
      simp
  }

@[simp] theorem productMap_apply {E E' F F' : Spectrum}
    (f : SpectrumMap E E') (g : SpectrumMap F F')
    (n : ℤ) (x : E.space n × F.space n) :
    productMap f g n x = (f n x.1, g n x.2) :=
  rfl

@[simp] theorem productMap_id_apply {E F : Spectrum} (n : ℤ)
    (x : E.space n × F.space n) :
    productMap (SpectrumMap.id E) (SpectrumMap.id F) n x = x :=
  rfl

theorem productMap_comp_apply {E E' E'' F F' F'' : Spectrum}
    (f₂ : SpectrumMap E' E'') (f₁ : SpectrumMap E E')
    (g₂ : SpectrumMap F' F'') (g₁ : SpectrumMap F F')
    (n : ℤ) (x : E.space n × F.space n) :
    productMap (SpectrumMap.comp f₂ f₁) (SpectrumMap.comp g₂ g₁) n x =
      productMap f₂ g₂ n (productMap f₁ g₁ n x) :=
  rfl

end InfoGeometry.Spectral.Spectrum.Integer
