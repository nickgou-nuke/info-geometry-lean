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

/-! ## [1] J-conjugation on embedded Hestenes scalars ——————————— -/

/--
Modular conjugation acts on embedded Hestenes scalars by complex conjugation.

This is the theorem-level content currently justified by the imported
Hestenes/Krein owner file.  Stronger claims about a translated spectral cut or a
`Re(s) = 1 / 2` fixed locus require additional bridge theorems not stated here.
-/
theorem spectral_cut_is_j_invariant
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [InfoGeometry.Krein.KreinSpace E] (z : ℂ) :
    InfoGeometry.Krein.modular_j (E := E) * hestenesScalar (E := E) z *
        InfoGeometry.Krein.modular_j (E := E) =
      hestenesScalar (E := E) (star z) := by
  simpa using modular_j_conjugates_hestenesScalar (E := E) z

/-! ## [2] Twisted-index vanishing in the real Hestenes/Krein lane —————— -/

/--
The real Souriau/Dirac/Hodge owner lane proves vanishing of the twisted index
pairing under explicit linearity, `J`-invariance, and projection-commutation
hypotheses.

This is the strongest theorem directly supported by the current imports.  It is
an honest alias of `SouriauDiracHodge.twisted_index_vanishing`, not a theorem
about analytic branch cuts.
-/
theorem no_branch_cuts_on_spectral_plane
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    (D : InfoGeometry.Dynamics.SouriauDiracHodge.KreinOperatorData H)
    (trace : (H →L[ℝ] H) → ℝ)
    (h_trace_linear : ∀ (c : ℝ) (A : H →L[ℝ] H), trace (c • A) = c * trace A)
    (h_trace_J_inv : ∀ A, trace (D.J * A * D.J) = trace A)
    (h_proj_J_comm : D.twistedSectorProjection * D.J = D.J * D.twistedSectorProjection) :
    D.indexPairing trace = 0 := by
  simpa using D.twisted_index_vanishing trace h_trace_linear h_trace_J_inv h_proj_J_comm

end InfoGeometry.GrandUnification.SpectralCut
