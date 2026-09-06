import InfoGeometry.Spectral.Spectrum.Integer

/-!
# Spectrification boundary for integer-indexed spectra

This records the universal-property interface for a prespectrum mapping into a
genuine integer-indexed spectrum.  It does not construct a quotient, colimit,
or stable homotopy object.
-/

namespace InfoGeometry.Spectral.Spectrum.Integer.Spectrification

abbrev PrespectrumToSpectrumMap (E : Prespectrum) (F : Spectrum) : Type _ :=
  Map E F.toPrespectrum

structure Data (E : Prespectrum) where
  spectrum : Spectrum
  unit : PrespectrumToSpectrumMap E spectrum
  extend : ∀ {F : Spectrum}, PrespectrumToSpectrumMap E F → SpectrumMap spectrum F
  extend_unit : ∀ {F : Spectrum} (f : PrespectrumToSpectrumMap E F),
    ∀ n x, (extend f).toMap.toFun n (unit n x) = f n x
  extend_unique : ∀ {F : Spectrum} (f : PrespectrumToSpectrumMap E F)
    (g : SpectrumMap spectrum F),
    (∀ n x, g.toMap.toFun n (unit n x) = f n x) → g = extend f

def ofSpectrum (E : Spectrum) : Data E.toPrespectrum where
  spectrum := E
  unit := Map.id E.toPrespectrum
  extend := fun f => { toMap := f }
  extend_unit := by intro F f n x; rfl
  extend_unique := by
    intro F f g h
    cases g with
    | mk toMap =>
      cases toMap with
      | mk toFun comm =>
        cases f with
        | mk fToFun fComm =>
          have hfun : toFun = fToFun := by
            funext n x
            simpa using h n x
          cases hfun
          rfl

namespace Data

variable {E : Prespectrum} (D : Data E)

@[simp] theorem extend_unit_apply {F : Spectrum}
    (f : PrespectrumToSpectrumMap E F) (n : ℤ) (x : E.space n) :
    D.extend f n (D.unit n x) = f n x :=
  D.extend_unit f n x

theorem extend_unique' {F : Spectrum}
    (f : PrespectrumToSpectrumMap E F) (g : SpectrumMap D.spectrum F)
    (h : ∀ n x, g n (D.unit n x) = f n x) :
    g = D.extend f :=
  D.extend_unique f g h

end Data

@[simp] theorem ofSpectrum_spectrum (E : Spectrum) :
    (ofSpectrum E).spectrum = E :=
  rfl

@[simp] theorem ofSpectrum_unit (E : Spectrum) (n : ℤ) (x : E.space n) :
    (ofSpectrum E).unit n x = x :=
  rfl

end InfoGeometry.Spectral.Spectrum.Integer.Spectrification
