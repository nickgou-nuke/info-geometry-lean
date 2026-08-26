import Mathlib
import InfoGeometry.Spectral.Spectrum.Basic
import InfoGeometry.Spectral.Spectrum.GPreSpectrum
import InfoGeometry.Spectral.Spectrum.Product
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotient
import InfoGeometry.Topology.SplitCliffordCanonicalTopology

/-!
# Homotopy-quotient bridge for the finite split-Clifford prespectrum

This wires `Spectrum.Basic.SplitCliffordPrespectrum` into the based-loop
homotopy-quotient machinery of `InfoGeometry.Topology` (Area 1).

Each stage `SplitClNNAlg n` is `CliffordAlgebra (Qsplit n)` over the iterated
product `SplitSpace n` of `ℝ × ℝ`, hence a finite-dimensional real algebra.
The canonical topology owner transports the coordinate topology along a finite
basis; the bridge is therefore admissible to
`SymbolicLatentBasedLoopHomotopyQuotient` without an extra topology parameter.

No spectrification and no Bott-periodicity *equivalence* is claimed here.  The
algebraic 8-step Bott clock already proved in `Spectrum.Basic`
(`bottClockStage`, `stableHomotopyClifford_period`) is the finite,
hardware-realizable shadow of real Bott periodicity; lifting it to a homotopy
equivalence of the loop spaces is explicitly left as future work.
-/

namespace InfoGeometry.Spectral.Spectrum.HomotopyBridge

open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Topology

/-- The split-Clifford prespectrum steps into the Area-1 based-loop homotopy
quotient: every stage that carries its natural finite-dimensional topology
admits an inhabited based loop at any point. -/
lemma splitCliffordPrespectrum_basedLoop
    (n : ℕ) (x : SplitClNNAlg n) :
    Nonempty (SymbolicLatentBasedLoopHomotopyQuotient x) :=
  ⟨symbolicLatentBasedLoopHomotopyQuotient_constant x⟩

/-- In particular the zero stage admits a based loop. -/
lemma splitCliffordPrespectrum_zero_basedLoop
    (n : ℕ) :
    Nonempty (SymbolicLatentBasedLoopHomotopyQuotient (0 : SplitClNNAlg n)) :=
  splitCliffordPrespectrum_basedLoop n 0

end InfoGeometry.Spectral.Spectrum.HomotopyBridge
