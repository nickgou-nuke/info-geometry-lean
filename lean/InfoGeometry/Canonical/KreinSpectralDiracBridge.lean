import InfoGeometry.Physics.Algebra.KreinSpectralDiracCommutator

/-!
# Krein spectral Dirac bridge

Canonical re-export of the bounded Krein self-adjointness and Dirac
commutator lane.  This bridge does not introduce new analytic structure; it
only forwards the verified physics owner into the canonical surface.
-/

namespace InfoGeometry.Canonical.KreinSpectralDiracBridge

open InfoGeometry.Physics.Algebra

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Canonical alias for the Krein-space structure. -/
abbrev KreinSpaceStructure (H : Type*) [NormedAddCommGroup H]
    [NormedSpace ℝ H] := InfoGeometry.Physics.Algebra.KreinSpaceStructure H

/-- Canonical alias for the Jordan self-adjointness witness. -/
theorem krein_jordan_self_adjointness
    (K : InfoGeometry.Physics.Algebra.KreinSpaceStructure H) (N Nstar : H →L[ℝ] H)
    (h : K.J.comp (Nstar.comp K.J) = N) :
    InfoGeometry.Physics.Algebra.kreinOperatorAdjoint K N Nstar = N :=
  InfoGeometry.Physics.Algebra.krein_jordan_self_adjointness (H := H) K N Nstar h

/-- Canonical alias for the monodromy commutator reduction. -/
theorem spectral_dirac_monodromy_commutator
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H)
    (D : H →L[ℝ] H) :
    D.comp (M.lambda • ((1 : H →L[ℝ] H) + M.N)) -
        (M.lambda • ((1 : H →L[ℝ] H) + M.N)).comp D =
      M.lambda • (D.comp M.N - M.N.comp D) :=
  InfoGeometry.Physics.Algebra.spectral_dirac_monodromy_commutator (H := H) M D

/-- Canonical alias for the norm bound on the monodromy commutator. -/
theorem spectral_dirac_commutator_norm_bound
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H)
    (D : H →L[ℝ] H) :
    ‖M.lambda • (D.comp M.N - M.N.comp D)‖ ≤
      |M.lambda| * ‖D.comp M.N - M.N.comp D‖ :=
  InfoGeometry.Physics.Algebra.spectral_dirac_commutator_norm_bound (H := H) M D

end InfoGeometry.Canonical.KreinSpectralDiracBridge
