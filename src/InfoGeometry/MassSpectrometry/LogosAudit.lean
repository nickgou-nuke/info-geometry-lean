import InfoGeometry.MassSpectrometry.LogosMap
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Build-time audit of the mass-spectrometry language-to-Logos map

Because the root `InfoGeometry` library builds all submodules, this command is
executed during the ordinary build and rejects stale owner names or accidental
promotion of open debt into a purported formal owner.
-/

#audit_mass_spectrometry_logos
