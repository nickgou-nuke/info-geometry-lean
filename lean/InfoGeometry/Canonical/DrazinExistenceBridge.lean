import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Singular.Drazin

/-!
# InfoGeometry.Canonical.DrazinExistenceBridge

Bridge layer between the singular Drazin existence theorem and the canonical
Drazin predicate used by the regularization/capstone lanes.
-/

namespace DrazinExistenceBridge

open Drazin

/--
Translate a singular-lane Drazin witness into the canonical Drazin predicate.
-/
theorem canonical_isDrazinInverse_of_singular
    {R : Type*} [Ring R]
    {A D : R} {k : ℕ}
    (h : IsDrazinInverse A D k) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse A D k := by
  refine InfoGeometry.Canonical.Drazin.IsDrazinInverse.mk ?_ ?_ ?_
  · exact h.2.1
  · exact h.1
  · exact h.2.2.symm

/--
Translate a canonical Drazin witness into the singular-lane predicate.
-/
theorem singular_isDrazinInverse_of_canonical
    {R : Type*} [Ring R]
    {A D : R} {k : ℕ}
    (h : InfoGeometry.Canonical.Drazin.IsDrazinInverse A D k) :
    IsDrazinInverse A D k := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · exact h.2.1
  · exact h.1
  · exact h.2.2.symm

/--
Global finite-dimensional existence of a canonical Drazin inverse on
`Module.End`, obtained by descending the singular global existence theorem.
-/
theorem exists_canonicalDrazinInverse_global
    {K V : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : Module.End K V) :
    ∃ (k : ℕ) (D : Module.End K V),
      InfoGeometry.Canonical.Drazin.IsDrazinInverse A D k := by
  rcases exists_drazinInverse_global (K := K) (V := V) (A := A) with
    ⟨k, D, hD⟩
  exact ⟨k, D, canonical_isDrazinInverse_of_singular hD⟩

/--
Operator-lane specialization on continuous linear endomorphisms.
-/
theorem exists_canonicalDrazinInverse_global_endCLM
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) :
    ∃ (k : ℕ) (D : E →L[ℝ] E),
      InfoGeometry.Canonical.Drazin.IsDrazinInverse A D k := by
  rcases exists_canonicalDrazinInverse_global
      (K := ℝ) (V := E) (A := A.toLinearMap) with ⟨k, Dlin, hDlin⟩
  let D : E →L[ℝ] E := LinearMap.toContinuousLinearMap Dlin
  have hCommLin : A.toLinearMap * D.toLinearMap = D.toLinearMap * A.toLinearMap := by
    simpa [D] using hDlin.1
  have hIdemLin : D.toLinearMap * A.toLinearMap * D.toLinearMap = D.toLinearMap := by
    simpa [D] using hDlin.2.1
  have hPowLin : A.toLinearMap ^ (k + 1) * D.toLinearMap = A.toLinearMap ^ k := by
    simpa [D] using hDlin.2.2
  refine ⟨k, D, InfoGeometry.Canonical.Drazin.IsDrazinInverse.mk ?_ ?_ ?_⟩
  · ext x
    simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) hCommLin
  · ext x
    simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) hIdemLin
  ·
    have hPowCont : (A ^ (k + 1) * D).toLinearMap = (A ^ k).toLinearMap := by
      change (ContinuousLinearMap.toLinearMapRingHom : (E →L[ℝ] E) →+* (E →ₗ[ℝ] E))
          (A ^ (k + 1) * D) =
        (ContinuousLinearMap.toLinearMapRingHom : (E →L[ℝ] E) →+* (E →ₗ[ℝ] E))
          (A ^ k)
      simpa [map_mul, map_pow, D] using hPowLin
    have hPow' : A ^ (k + 1) * D = ((A ^ k).toLinearMap).toContinuousLinearMap :=
      (ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap
          (g := A ^ (k + 1) * D) (f := (A ^ k).toLinearMap)).1 hPowCont
    have hRoundTrip : ((A ^ k).toLinearMap).toContinuousLinearMap = A ^ k := by
      exact (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap
        (f := (A ^ k).toLinearMap) (g := A ^ k)).2 rfl
    exact hPow'.trans hRoundTrip

end DrazinExistenceBridge
