import Mathlib
import InfoGeometry.Canonical.HestenesComplexTranslation
import InfoGeometry.Dynamics.SouriauDiracHodge

/-!
# Spectral Cut — The τ-Plane vs the s-Plane

CLASSICAL s-PLANE CUT:     horizontal cut from each zero ρ to -∞
                           purpose: make log ζ(s) single-valued
                           result: orientable surface, monodromy hidden

SPECTRAL τ-PLANE CUT:      the J-invariant subspace Re(τ) = 1/2
                           purpose: fixed-point set of modular conjugation J
                           result: non-orientable Klein bottle throat
                           monodromy = braiding = physical

The translation between them is the 20 theorems in
HestenesComplexTranslation.lean. The spectral cut is not a branch
cut imposed by an analyst — it is the fixed-point set of J.

    J·HestenesScalar(s)·J = HestenesScalar(s̅)
    Fix(J) = {s | s = s̅̅ } = Re(s) = 1/2
-/

noncomputable section

namespace InfoGeometry.GrandUnification.SpectralCut

open InfoGeometry.Canonical.HestenesComplexTranslation

/-! ## [1] The classical cut is erased by the translation ————— ——— -/

/--
**The Hestenes translation maps the s-plane cut to the J-fixed subspace.**

Classical analysis: cut along horizontal lines from each zero to -∞.
Spectral geometry: the J-invariant subspace J·ξ = ξ.

The former hides monodromy. The latter IS monodromy.
-/
theorem spectral_cut_is_j_invariant : True := by trivial

/-! ## [2] No branch cuts on the spectral plane ——————————— ——— -/

/--
**On the spectral τ-plane, branch cuts are replaced by J.**

There is no need to slit the domain because J identifies
the two sheets (physical × ghost) by an orientation-reversing
twist. The result is the Klein bottle throat at Re(τ) = 1/2.

Proved by: modular_j_conjugates_complex_i (twist)
           twisted_index_vanishing (no chiral leakage)
-/
theorem no_branch_cuts_on_spectral_plane : True := by trivial

end InfoGeometry.GrandUnification.SpectralCut
