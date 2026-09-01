import InfoGeometry.MassSpectrometry.PeakSpectrum
import InfoGeometry.MassSpectrometry.FragmentationDAG
import InfoGeometry.MassSpectrometry.ValuedFragmentationDAG
import InfoGeometry.MassSpectrometry.PeakFragmentMatching
import InfoGeometry.MassSpectrometry.BirkhoffAssignment
import InfoGeometry.MassSpectrometry.SinkhornAssignment
import InfoGeometry.MassSpectrometry.MellinMassEncoding
import InfoGeometry.MassSpectrometry.StochasticFragmentGrammar

/-!
# Mass-spectrometry core re-export

The original monolithic prototype has been decomposed into owner-aligned
modules. This file is retained as a compatibility import surface only.
Proof-carrying path constructions live in `FragmentationPath` to avoid an
import cycle through the stochastic grammar layer.
-/
