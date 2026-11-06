/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinInfiniteCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
  finite_ascent_descent := hFinite
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
Constructive spectral bridge: finite ascent/descent at `0` alone recovers a
Drazin witness.  Spectral isolation at `0` is not needed for this implication,
so it is not taken as a hypothesis.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_finiteAscentDescentAtZero
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap) :
    ∃ k TD, InfoGeometry.Canonical.Drazin.IsDrazinInverse T.toLinearMap TD k :=
  DrazinInfiniteCore.exists_drazinInverse_of_finiteAscentDescent_constructive
    (T := T.toLinearMap) hFinite

/--
The bundled spectral package carries a Drazin witness, extracted from its
finite ascent/descent field.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_drazinInfiniteAssumptions
    (A : DrazinInfiniteAssumptions T) :
    ∃ k TD, InfoGeometry.Canonical.Drazin.IsDrazinInverse T.toLinearMap TD k :=
  exists_drazinInverse_of_finiteAscentDescentAtZero A.finite_ascent_descent

end InfoGeometry.Canonical.DrazinSpectralBridge
