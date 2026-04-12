import InfoGeometry.Canonical.DrazinInfiniteCore
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Basic

namespace InfoGeometry.Canonical.DrazinInfiniteCore

variable {𝕂 E : Type*} [NormedField 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
variable {T : E →L[𝕂] E}

/--
Bridge constructor for the finite ascent/descent lane at spectral point `0`.

This is an explicit witness re-projection surface:
- it records that the spectral isolation witness `h` is in scope;
- it does not hide any additional algebraic requirements.
-/
noncomputable def HasFiniteAscentDescentAtZero_of_zeroIsolatedInSpectrum
    (_h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap) :
    HasFiniteAscentDescentAtZero T.toLinearMap :=
  hFinite

/--
Bridge constructor for the full infinite-dimensional Drazin assumption package.

This definition is intentionally explicit: every nontrivial algebraic field is
provided as a caller witness, while `h` supplies the spectral-isolation field.
-/
noncomputable def DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum
    (h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap)
    (hClassical : HasClassicalRieszDecompositionAtZero T)
    (hGeneralized : HasGeneralizedRieszDecompositionAtZero T) :
    DrazinInfiniteAssumptions T where
  finite_ascent_descent :=
    HasFiniteAscentDescentAtZero_of_zeroIsolatedInSpectrum h hFinite
  zero_isolated_spectrum := h
  classical_riesz := hClassical
  generalized_riesz := hGeneralized

end InfoGeometry.Canonical.DrazinInfiniteCore
