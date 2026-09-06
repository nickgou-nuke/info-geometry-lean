import InfoGeometry.Canonical.DrazinInfiniteCore
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# InfoGeometry.Canonical.DrazinSpectralBridge

Closure-clean spectral bridge constructors for the infinite-dimensional Drazin lane.

This file does not introduce new ontological assumptions. It packages explicit
re-projection constructors from:
- spectral isolation at `0`,
- finite ascent/descent witness,
- classical and generalized Riesz interfaces,

into the bundled `DrazinInfiniteAssumptions` owner from
`InfoGeometry.Canonical.DrazinInfiniteCore`.
-/

namespace InfoGeometry.Canonical.DrazinSpectralBridge

open InfoGeometry.Canonical
open DrazinInfiniteCore

variable {𝕂 E : Type*} [NormedField 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
variable {T : E →L[𝕂] E}

/--
Bridge constructor for the finite ascent/descent lane at spectral point `0`.

This is an explicit witness re-projection surface:
- it records that the spectral isolation witness `h` is in scope;
- it does not hide any additional algebraic requirements.
-/
@[rep_depth operator]
noncomputable def HasFiniteAscentDescentAtZero_of_zeroIsolatedInSpectrum
    (_h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap) :
    HasFiniteAscentDescentAtZero T.toLinearMap :=
  hFinite

/--
The finite ascent/descent bridge constructor is definitional on the finite witness.
-/
@[rep_depth operator]
theorem HasFiniteAscentDescentAtZero_of_zeroIsolatedInSpectrum_eq
    (h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap) :
    HasFiniteAscentDescentAtZero_of_zeroIsolatedInSpectrum (T := T) h hFinite = hFinite := rfl

/--
Bridge constructor for the full infinite-dimensional Drazin assumption package.

This definition is intentionally explicit: every nontrivial algebraic field is
provided as a caller witness, while `h` supplies the spectral-isolation field.
-/
@[rep_depth operator]
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

/--
Field projection: finite ascent/descent witness of the bundled bridge package.
-/
@[rep_depth operator]
theorem DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_finite_ascent_descent
    (h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap)
    (hClassical : HasClassicalRieszDecompositionAtZero T)
    (hGeneralized : HasGeneralizedRieszDecompositionAtZero T) :
    (DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum (T := T) h hFinite hClassical hGeneralized).finite_ascent_descent
      = hFinite := by
  rfl

/--
Field projection: spectral isolation witness of the bundled bridge package.
-/
@[rep_depth operator]
theorem DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_zero_isolated
    (h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap)
    (hClassical : HasClassicalRieszDecompositionAtZero T)
    (hGeneralized : HasGeneralizedRieszDecompositionAtZero T) :
    (DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum (T := T) h hFinite hClassical hGeneralized).zero_isolated_spectrum
      = h := by
  rfl

/--
Field projection: classical Riesz witness of the bundled bridge package.
-/
@[rep_depth operator]
theorem DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_classical
    (h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap)
    (hClassical : HasClassicalRieszDecompositionAtZero T)
    (hGeneralized : HasGeneralizedRieszDecompositionAtZero T) :
    (DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum (T := T) h hFinite hClassical hGeneralized).classical_riesz
      = hClassical := by
  rfl

/--
Field projection: generalized Riesz witness of the bundled bridge package.
-/
@[rep_depth operator]
theorem DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_generalized
    (h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap)
    (hClassical : HasClassicalRieszDecompositionAtZero T)
    (hGeneralized : HasGeneralizedRieszDecompositionAtZero T) :
    (DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum (T := T) h hFinite hClassical hGeneralized).generalized_riesz
      = hGeneralized := by
  rfl

/--
Constructive spectral bridge:
from isolation at `0` plus finite ascent/descent, recover a Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_zeroIsolatedInSpectrum_finiteAscentDescent
    (_h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap) :
    ∃ k TD, InfoGeometry.Canonical.Drazin.IsDrazinInverse T.toLinearMap TD k := by
  exact
    DrazinInfiniteCore.exists_drazinInverse_of_finiteAscentDescent_constructive
      (T := T.toLinearMap) hFinite

/--
The bundled spectral bridge package carries a canonical Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_zeroIsolatedInSpectrum_package
    (h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap)
    (_hClassical : HasClassicalRieszDecompositionAtZero T)
    (_hGeneralized : HasGeneralizedRieszDecompositionAtZero T) :
    ∃ k TD, InfoGeometry.Canonical.Drazin.IsDrazinInverse T.toLinearMap TD k := by
  exact exists_drazinInverse_of_zeroIsolatedInSpectrum_finiteAscentDescent
    (T := T) h hFinite

end InfoGeometry.Canonical.DrazinSpectralBridge
