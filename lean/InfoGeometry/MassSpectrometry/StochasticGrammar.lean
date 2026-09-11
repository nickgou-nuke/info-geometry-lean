import InfoGeometry.MassSpectrometry.StochasticFragmentGrammar
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.MassSpectrometry.FragmentationPath

/-!
# Mass-spectrometry stochastic grammar compatibility surface

The stochastic-kernel owner remains `StochasticFragmentGrammar`; typed path
composition and path-level probability/surprisal laws are owned by
`FragmentationPath`.  This module provides the shorter public import path used
by the mass-spectrometry architecture without duplicating declarations.
-/
