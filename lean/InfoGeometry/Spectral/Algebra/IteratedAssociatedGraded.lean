import InfoGeometry.Spectral.Algebra.ExactCoupleFiltration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Spectral.Algebra.IteratedPageStabilization

/-!
# Eventual pages and the associated graded of a stable exact-couple stage

This file states the fixed-index convergence consequence directly.  It does
not introduce a convergence packet: vanishing of the relevant `k` map
identifies the stable page with an associated graded quotient, while eventual
vanishing of adjacent differentials identifies all later pages with that
stable page.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedExactCouple

variable {R : Type u} [Ring R]
variable {I : Type v}

/-- Once the page at the stable index has zero adjacent differentials and the
stable exact couple has zero outgoing `k`, every later page is linearly
equivalent to the associated graded quotient of the stable `D` filtration. -/
noncomputable def iteratedPageEquivAssociatedGraded
    (S : Stage R I) (p : I) (N m : ℕ) (hNm : N ≤ m)
    (hk :
      (iteratedStage S N).couple.k
        ((iteratedStage S N).jDeg
          ((iteratedStage S N).iDeg p)) = 0)
    (hIncoming :
      ∀ n, N ≤ n →
        (iteratedStage S n).couple.differential
          ((iteratedStage S n).couple.differentialDegree.symm
            ((iteratedStage S N).jDeg
              ((iteratedStage S N).iDeg p))) = 0)
    (hOutgoing :
      ∀ n, N ≤ n →
        (iteratedStage S n).couple.differential
          ((iteratedStage S n).couple.differentialDegree
            ((iteratedStage S n).couple.differentialDegree.symm
              ((iteratedStage S N).jDeg
                ((iteratedStage S N).iDeg p)))) = 0) :
    (page S m
        ((iteratedStage S N).jDeg
          ((iteratedStage S N).iDeg p)) : Type u) ≃ₗ[R]
      (iteratedStage S N).couple.associatedGraded 0
        ((iteratedStage S N).iDeg p) :=
  (iteratedPageEquivOfEventuallyAdjacentDifferentialsZero
      S
      ((iteratedStage S N).jDeg
        ((iteratedStage S N).iDeg p))
      N m hNm hIncoming hOutgoing).trans
    ((iteratedStage S N).couple
      |>.associatedGradedZeroEquivEOfKZero p hk).symm

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
