import InfoGeometry.Spectral.Algebra.IteratedAssociatedGraded
import InfoGeometry.Spectral.Algebra.StablePage

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

/-- Explicit data needed to identify a stabilized page with the associated
graded piece at a fixed iterated-stage index.  This package keeps the
reconstruction hypotheses visible instead of treating stabilization alone as
an abutment theorem. -/
structure FiltrationReconstructionData
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (N : ℕ) where
  hN : h.bound ((iteratedStage S N).jDeg ((iteratedStage S N).iDeg p)) ≤ N
  hk :
    (iteratedStage S N).couple.k
      ((iteratedStage S N).jDeg ((iteratedStage S N).iDeg p)) = 0
  hIncoming :
    ∀ n, N ≤ n →
      (iteratedStage S n).couple.differential
        ((iteratedStage S n).couple.differentialDegree.symm
          ((iteratedStage S N).jDeg ((iteratedStage S N).iDeg p))) = 0
  hOutgoing :
    ∀ n, N ≤ n →
      (iteratedStage S n).couple.differential
        ((iteratedStage S n).couple.differentialDegree
          ((iteratedStage S n).couple.differentialDegree.symm
            ((iteratedStage S N).jDeg ((iteratedStage S N).iDeg p)))) = 0

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

/-- Reconstruction on the stable-page carrier at the actual iterated page
index.  The index is explicit so no dependent cast between `p` and
`jDeg (iDeg p)` is hidden in the statement. -/
noncomputable def stableIteratedPageEquivAssociatedGraded
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (N : ℕ)
    (hN : h.bound ((iteratedStage S N).jDeg ((iteratedStage S N).iDeg p)) ≤ N)
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
    stablePage S h ((iteratedStage S N).jDeg ((iteratedStage S N).iDeg p))
      ≃ₗ[R]
      (iteratedStage S N).couple.associatedGraded 0
        ((iteratedStage S N).iDeg p) :=
  (stablePageEquiv S h _ N hN).symm.trans
  (stabilizedPageEquivAssociatedGraded S p N N le_rfl hk hIncoming hOutgoing)

/-- Reconstruction obtained from the explicit data package. -/
noncomputable def stablePageEquivAssociatedGradedOfData
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (N : ℕ)
    (d : FiltrationReconstructionData S h p N) :
    stablePage S h
        ((iteratedStage S N).jDeg ((iteratedStage S N).iDeg p))
      ≃ₗ[R]
      (iteratedStage S N).couple.associatedGraded 0
        ((iteratedStage S N).iDeg p) :=
  stableIteratedPageEquivAssociatedGraded S h p N d.hN d.hk
    d.hIncoming d.hOutgoing

/-- The same index-correct reconstruction, followed by the canonical
associated-graded-to-`E` equivalence supplied by the exact-couple
filtration. -/
noncomputable def stableIteratedPageEquivE
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (N : ℕ)
    (hN : h.bound ((iteratedStage S N).jDeg ((iteratedStage S N).iDeg p)) ≤ N)
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
    stablePage S h ((iteratedStage S N).jDeg ((iteratedStage S N).iDeg p))
      ≃ₗ[R]
      (iteratedStage S N).E ((iteratedStage S N).jDeg
        ((iteratedStage S N).iDeg p)) :=
  (stableIteratedPageEquivAssociatedGraded S h p N hN hk hIncoming hOutgoing).trans
    ((iteratedStage S N).couple.associatedGradedZeroEquivEOfKZero p hk)

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
