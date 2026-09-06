import InfoGeometry.Spectral.Spectrum.GPreSpectrum

/-!
# Levelwise products of prespectra

This is the carrier-level algebraic part of the old smash-spectrum interface.
It does not assert a topological smash product or spectrification.
-/

namespace InfoGeometry.Spectral.Spectrum.Product

open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Spectral.Spectrum.GPreSpectrum

/-- Levelwise product of two prespectrum-shaped sequences. -/
def prespectrum (E F : Prespectrum) : Prespectrum where
  space := fun n => E.space n × F.space n
  step := fun n x => (E.step n x.1, F.step n x.2)

@[simp]
theorem prespectrum_space (E F : Prespectrum) (n : ℕ) :
    (prespectrum E F).space n = (E.space n × F.space n) :=
  rfl

@[simp]
theorem prespectrum_step (E F : Prespectrum) (n : ℕ)
    (x : E.space n × F.space n) :
    (prespectrum E F).step n x = (E.step n x.1, F.step n x.2) :=
  rfl

/-- Product of two spectrum conditions, with no additional axioms. -/
def isSpectrum {E F : Prespectrum} (hE : IsSpectrum E) (hF : IsSpectrum F) :
    IsSpectrum (prespectrum E F) where
  stepEquiv := fun n => Equiv.prodCongr (hE.stepEquiv n) (hF.stepEquiv n)
  stepEquiv_apply := by
    intro n x
    rcases x with ⟨x, y⟩
    simp [hE.stepEquiv_apply, hF.stepEquiv_apply]

def spectrum (E F : GPreSpectrum.Spectrum) : GPreSpectrum.Spectrum where
  prespectrum := prespectrum E.prespectrum F.prespectrum
  isSpectrum := isSpectrum E.isSpectrum F.isSpectrum

@[simp]
theorem spectrum_prespectrum (E F : GPreSpectrum.Spectrum) :
    (spectrum E F).prespectrum = prespectrum E.prespectrum F.prespectrum :=
  rfl

/-- Levelwise product of two spectrum maps. -/
def map {E E' F F' : GPreSpectrum.Spectrum}
    (f : SpectrumMap E E') (g : SpectrumMap F F') :
    SpectrumMap (spectrum E F) (spectrum E' F') where
  toMap := {
    toFun := fun n x => (f n x.1, g n x.2)
    comm := by
      intro n x
      rcases x with ⟨x, y⟩
      simp [prespectrum, f.toMap.comm, g.toMap.comm]
  }

@[simp]
theorem map_apply {E E' F F' : GPreSpectrum.Spectrum}
    (f : SpectrumMap E E') (g : SpectrumMap F F')
    (n : ℕ) (x : E.prespectrum.space n × F.prespectrum.space n) :
    map f g n x = (f n x.1, g n x.2) :=
  rfl

@[simp]
theorem map_id_left {E F F' : GPreSpectrum.Spectrum} (g : SpectrumMap F F')
    (n : ℕ) (x : E.prespectrum.space n × F.prespectrum.space n) :
    map (SpectrumMap.id E) g n x = (x.1, g n x.2) :=
  rfl

@[simp]
theorem map_id_right {E E' F : GPreSpectrum.Spectrum} (f : SpectrumMap E E')
    (n : ℕ) (x : E.prespectrum.space n × F.prespectrum.space n) :
    map f (SpectrumMap.id F) n x = (f n x.1, x.2) :=
  rfl

theorem map_comp {E E' E'' F F' F'' : GPreSpectrum.Spectrum}
    (f₂ : SpectrumMap E' E'') (f₁ : SpectrumMap E E')
    (g₂ : SpectrumMap F' F'') (g₁ : SpectrumMap F F')
    (n : ℕ) (x : E.prespectrum.space n × F.prespectrum.space n) :
    map (SpectrumMap.comp f₂ f₁) (SpectrumMap.comp g₂ g₁) n x =
      map f₂ g₂ n (map f₁ g₁ n x) :=
  rfl

@[simp] theorem map_id {E F : GPreSpectrum.Spectrum} :
    map (SpectrumMap.id E) (SpectrumMap.id F) =
      SpectrumMap.id (spectrum E F) := by
  apply SpectrumMap.ext
  intro n x
  rfl

theorem map_comp_eq {E E' E'' F F' F'' : GPreSpectrum.Spectrum}
    (f₂ : SpectrumMap E' E'') (f₁ : SpectrumMap E E')
    (g₂ : SpectrumMap F' F'') (g₁ : SpectrumMap F F') :
    map (SpectrumMap.comp f₂ f₁) (SpectrumMap.comp g₂ g₁) =
      SpectrumMap.comp (map f₂ g₂) (map f₁ g₁) := by
  apply SpectrumMap.ext
  intro n x
  exact map_comp f₂ f₁ g₂ g₁ n x

end InfoGeometry.Spectral.Spectrum.Product
