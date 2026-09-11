import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit

/-!
# Prime Clifford-wavelet colimit readout: actual completed `riemannXi`

The upstream wavelet owner is a conditional realization interface: it accepts
a completed-`xi` function and a reconstruction theorem as fields.  This
consumer removes one artificial abstraction by supplying Mathlib's concrete
`riemannXi` as the function carried by the interface.

The wavelet/colimit realization itself is still an explicit datum.  This file
does not construct it, does not assert a limit from prime approximants, and
does not identify Lee--Yang zeros with Riemann zeros.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeCliffordWaveletActualXiBridge

open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit

/-- The actual completed `riemannXi` packaged for the wavelet interface. -/
def actualCompletedXiFunction : CompletedXiFunction :=
  ⟨riemannXi,
    ⟨(2 : ℂ), riemannXi_ne_zero_of_one_lt_re (s := (2 : ℂ)) (by norm_num)⟩⟩

@[simp] theorem actualCompletedXiFunction_apply (s : ℂ) :
    actualCompletedXiFunction.xi s = riemannXi s := rfl

/-- The supplied colimit/wavelet reconstruction is now literally a readout of
the concrete completed `riemannXi` after the Cayley inverse. -/
theorem wavelet_reconstruction_eq_actual_riemannXi
    (W : InfoGeometry.Analysis.CliffordWaveletTransform.CliffordWaveletModel)
    (A : PrimeLeeYangApproximants)
    (R : PrimeCliffordWaveletRealization W A actualCompletedXiFunction)
    (z : ℂ) :
    R.waveletLimit z = riemannXi (cayleyInv z) := by
  simpa only [actualCompletedXiFunction_apply] using
    R.reconstruction_eq_xi_cayley z

/- The finite cutoff readout remains connected to the same realization. -/
theorem wavelet_partial_eq_renormZ
    (W : InfoGeometry.Analysis.CliffordWaveletTransform.CliffordWaveletModel)
    (A : PrimeLeeYangApproximants)
    (R : PrimeCliffordWaveletRealization W A actualCompletedXiFunction)
    (N : ℕ) (z : ℂ) :
    R.waveletPartial N z = A.renormZ N z :=
  R.partial_eq_renormZ N z

/- The locally uniform limit theorem is inherited, not re-proved here. -/
theorem actual_riemannXi_colimit_readout
    (W : InfoGeometry.Analysis.CliffordWaveletTransform.CliffordWaveletModel)
    (A : PrimeLeeYangApproximants)
    (R : PrimeCliffordWaveletRealization W A actualCompletedXiFunction) :
    TendstoLocallyUniformly R.waveletPartial
      (fun z => riemannXi (cayleyInv z)) Filter.atTop := by
  have hlimit := R.locallyUniformRenormalizedLimit
  convert hlimit using 1
  funext z
  exact (wavelet_reconstruction_eq_actual_riemannXi W A R z).symm

end InfoGeometry.Canonical.PrimeCliffordWaveletActualXiBridge
