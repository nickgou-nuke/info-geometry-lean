import InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Closed topology of a projective null boundary

This owner identifies the projective null locus as a closed subset for the
repository's quotient topology, assuming only continuity of the quadratic
form and a Hausdorff scalar topology.  It then transports Hausdorffness and
local compactness from the ambient projectivization to the null subtype.

No affine chart is identified with the global projective boundary, and no
compactness, manifold, fundamental-group, braid, or monodromy claim is made.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullBoundaryTopology

open InfoGeometry.Twistor
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open Topology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A continuous quadratic form cuts out a closed locus in the quotient
projectivization topology.  The proof descends the native zero locus on
nonzero representatives; it does not choose projective coordinates. -/
theorem projectiveNullLocus_isClosed
    [TopologicalSpace K] [T2Space K] [TopologicalSpace V]
    (Q : QuadraticForm K V) (hQ : Continuous (Q : V → K)) :
    let _ := projectivizationQuotientTopology (K := K) (V := V)
    IsClosed {p : ℙ K V | IsNull Q p} := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  rw [isClosed_coinduced]
  change IsClosed {v : {v : V // v ≠ 0} |
    IsNull Q (Projectivization.mk K v v.property)}
  simp only [isNull_mk_iff]
  exact isClosed_eq (hQ.comp continuous_subtype_val) continuous_const

/-- Hausdorffness of the ambient projectivization passes to the projective
null subtype equipped with the repository's induced topology. -/
theorem nullBoundary_t2Space
    [TopologicalSpace V]
    (Q : QuadraticForm K V)
    (hT2 : @T2Space (ℙ K V)
      (projectivizationQuotientTopology (K := K) (V := V))) :
    @T2Space (TwistorSpace Q) (nullBoundaryTopology Q) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : T2Space (ℙ K V) := hT2
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  exact Topology.IsEmbedding.subtypeVal.t2Space

/-- Local compactness of the ambient projectivization passes to the closed
projective null subtype. -/
theorem nullBoundary_locallyCompactSpace
    [TopologicalSpace K] [T2Space K] [TopologicalSpace V]
    (Q : QuadraticForm K V) (hQ : Continuous (Q : V → K))
    (hLC : @LocallyCompactSpace (ℙ K V)
      (projectivizationQuotientTopology (K := K) (V := V))) :
    @LocallyCompactSpace (TwistorSpace Q) (nullBoundaryTopology Q) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : LocallyCompactSpace (ℙ K V) := hLC
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  exact (projectiveNullLocus_isClosed Q hQ).locallyCompactSpace

end InfoGeometry.Twistor.ProjectiveNullBoundaryTopology
