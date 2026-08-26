import InfoGeometry.Spectral.Algebra.IteratedAssociatedGraded

/-!
# Associated-graded reconstruction for a stabilized exact-couple page

This owner exposes the fixed-index reconstruction already proved by
`iteratedPageEquivAssociatedGraded`.  It deliberately does not identify the
associated graded object with an external abutment: that requires separate
filtration and comparison data.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedExactCouple

variable {R : Type u} [Ring R]
variable {I : Type v}

/-- A page in the stabilized tail is canonically linearly equivalent to the
associated graded quotient of the stable exact-couple filtration, under the
explicit adjacent-differential and `k`-vanishing hypotheses. -/
noncomputable def stabilizedPageEquivAssociatedGraded
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
  iteratedPageEquivAssociatedGraded
    S p N m hNm hk hIncoming hOutgoing

@[simp]
theorem stabilizedPageEquivAssociatedGraded_apply
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
                ((iteratedStage S N).iDeg p)))) = 0)
    (x : page S m
      ((iteratedStage S N).jDeg
        ((iteratedStage S N).iDeg p))) :
    stabilizedPageEquivAssociatedGraded
        S p N m hNm hk hIncoming hOutgoing x =
      iteratedPageEquivAssociatedGraded
        S p N m hNm hk hIncoming hOutgoing x :=
  rfl

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
