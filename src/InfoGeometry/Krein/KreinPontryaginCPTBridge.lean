import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.InvolutiveSelfDualCarrier
import InfoGeometry.Krein.KreinSpace

/-!
# Retired coordinate Krein/CPT readout

The former owner used `State := ℝ × ℝ` and proved a split-signature identity by
coordinate expansion.  That is not a Pontryagin-space construction and does
not establish a CPT action on the repository's GNS or colimit carriers.

The canonical noncommutative/operatorial owners are now:

* `InfoGeometry.Krein.DoubledSpace` for the doubled Hilbert carrier and its
  continuous-linear `modular_j`/`spectral_epsilon` symmetries;
* `InfoGeometry.Krein.InvolutiveSelfDualCarrier` for the abstract Krein
  pairing, involutions, and nondegeneracy laws;
* `InfoGeometry.Krein.KreinSpace` for the native fundamental-symmetry API.

This compatibility module exports no scalar `State`, Casimir, NESS, or CPT
surrogate.  Fixed-locus and colimit claims must be proved on those operator
carriers with their actual transport hypotheses.
-/

namespace InfoGeometry.Krein.Pontryagin

end InfoGeometry.Krein.Pontryagin
