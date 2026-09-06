import InfoGeometry.Spectral.Spectrum.GPreSpectrum

/-!
# The spectrification interface

The old HoTT development specified spectrification as a left adjoint from
prespectra to spectra.  This file ports that universal-property boundary.  It
does not pretend to construct the sequential colimit or a topological stable
homotopy object; those are separate implementation layers.
-/

namespace InfoGeometry.Spectral.Spectrum.Spectrification

open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Spectral.Spectrum.GPreSpectrum

/-- A map from a prespectrum to the underlying prespectrum of a spectrum. -/
abbrev PrespectrumToSpectrumMap (E : Prespectrum)
    (F : GPreSpectrum.Spectrum) : Type _ :=
  Map E F.prespectrum

/-!
The universal property is deliberately stated with the existing spectrum-map
carrier.  Thus a spectrification datum supplies an actual spectrum, a unit,
and a unique extension operation; no hidden quotient or colimit is assumed.
-/
structure SpectrificationData (E : Prespectrum) where
  spectrum : GPreSpectrum.Spectrum
  unit : PrespectrumToSpectrumMap E spectrum
  extend : ∀ {F : GPreSpectrum.Spectrum},
    PrespectrumToSpectrumMap E F → SpectrumMap spectrum F
  extend_unit : ∀ {F : GPreSpectrum.Spectrum} (f : PrespectrumToSpectrumMap E F),
    (extend f).toMap.comp unit = f
  extend_unique : ∀ {F : GPreSpectrum.Spectrum}
    (f : PrespectrumToSpectrumMap E F) (g : SpectrumMap spectrum F),
    g.toMap.comp unit = f → g = extend f

/-- A spectrum is already spectrified by its underlying prespectrum. -/
def ofSpectrum (E : GPreSpectrum.Spectrum) :
    SpectrificationData E.prespectrum where
  spectrum := E
  unit := GPreSpectrum.Map.id E.prespectrum
  extend := fun f =>
    { toMap := f }
  extend_unit := by
    intro F f
    rfl
  extend_unique := by
    intro F f g h
    cases g with
    | mk toMap =>
      cases toMap with
      | mk toFun comm =>
        cases f with
        | mk fToFun fComm =>
          simp only [GPreSpectrum.Map.comp, GPreSpectrum.Map.id] at h
          cases h
          rfl

namespace SpectrificationData

variable {E : Prespectrum} (D : SpectrificationData E)

@[simp]
theorem ofSpectrum_spectrum (E : GPreSpectrum.Spectrum) :
    (ofSpectrum E).spectrum = E :=
  rfl

@[simp]
theorem ofSpectrum_unit (E : GPreSpectrum.Spectrum) (n : ℕ)
    (x : E.prespectrum.space n) :
    (ofSpectrum E).unit n x = x :=
  rfl

@[simp]
theorem extend_unit_apply {F : GPreSpectrum.Spectrum}
    (f : PrespectrumToSpectrumMap E F) (n : ℕ) (x : E.space n) :
    D.extend f n (D.unit n x) = f n x := by
  exact congrFun (congrArg (fun h => h n) (D.extend_unit f)) x

theorem extend_unique' {F : GPreSpectrum.Spectrum}
    (f : PrespectrumToSpectrumMap E F) (g : SpectrumMap D.spectrum F)
    (h : g.toMap.comp D.unit = f) :
    g = D.extend f :=
  D.extend_unique f g h

end SpectrificationData

end InfoGeometry.Spectral.Spectrum.Spectrification
