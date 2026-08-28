import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Clifford.Relations
import Mathlib.Analysis.InnerProductSpace.Basic

namespace InfoGeometry.Canonical.KaehlerGeometry

open InfoGeometry.Convex
open InfoGeometry.Clifford

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Symplectic Form on the belief space.
ω(u, v) represents the 'Information Phase' or 'Berry Curvature'
between two belief updates.
-/
def SymplecticForm (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  E → E → ℝ

/--
A belief manifold is Kähler if it possesses a symmetric Fisher metric g
and an antisymmetric symplectic form ω that are compatible via a
complex structure J: ω(u, v) = g(J u, v).
-/
structure KaehlerInformationGeometry (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  H : HessianGeometry E
  ω : SymplecticForm E
  J : E →L[ℝ] E
  /-- J is a complex structure: J² = -I -/
  j_sq_eq_neg_id : J * J = -1
  /-- Compatibility: ω(u, v) = <J u, metricOp v> -/
  compatibility : ∀ u v, ω u v = inner ℝ (J u) (H.metricOp u v)

namespace KaehlerInformationGeometry

variable (K : KaehlerInformationGeometry E)

/--
The Log-f potential (Kähler Potential).
In information geometry, this is exactly our log-partition function ψ.
The metric is recovered as the Hessian of this potential.
-/
def logF : E → ℝ := K.H.potential

omit [FiniteDimensional ℝ E] in
@[simp] theorem logF_eq_potential : K.logF = K.H.potential := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem logF_apply (x : E) : K.logF x = K.H.potential x := rfl

/--
The Symplectic Curvature associated with the Kähler structure.
This measures the 'Area' of information enclosed by a belief loop.
-/
noncomputable def symplecticCurvature (u v : E) : ℝ :=
  K.ω u v

end KaehlerInformationGeometry

/-! ## Algebraic para-Kähler skewness

The para-complex and complex cases share this finite algebraic step: an
anti-self-adjoint operator turns the inner product into a skew form.  No
nondegeneracy, closedness, or Hamiltonian vector field is asserted here.
-/

def ParaSymplecticForm (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (J : E →L[ℝ] E) : E → E → ℝ :=
  fun u v => inner ℝ (J u) v

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem paraSymplecticForm_skew
    (J : E →L[ℝ] E)
    (hJ : ∀ u v : E, inner ℝ (J u) v = -inner ℝ u (J v))
    (u v : E) :
    ParaSymplecticForm E J u v = -ParaSymplecticForm E J v u := by
  unfold ParaSymplecticForm
  rw [hJ u v, real_inner_comm]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem paraSymplecticForm_left_nondegenerate
    (J : E →L[ℝ] E)
    (hJinj : Function.Injective J)
    (u : E)
    (hzero : ∀ v : E, ParaSymplecticForm E J u v = 0) :
    u = 0 := by
  have hJu : J u = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    simpa [ParaSymplecticForm] using hzero (J u)
  apply hJinj
  simpa using hJu

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem paraSymplecticForm_right_nondegenerate
    (J : E →L[ℝ] E)
    (hJ : ∀ u v : E, inner ℝ (J u) v = -inner ℝ u (J v))
    (hJinj : Function.Injective J)
    (v : E)
    (hzero : ∀ u : E, ParaSymplecticForm E J u v = 0) :
    v = 0 := by
  apply paraSymplecticForm_left_nondegenerate J hJinj v
  intro u
  rw [paraSymplecticForm_skew J hJ v u]
  simp [hzero u]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem paraSymplecticForm_nondegenerate
    (J : E →L[ℝ] E)
    (hJ : ∀ u v : E, inner ℝ (J u) v = -inner ℝ u (J v))
    (hJinj : Function.Injective J) :
    (∀ u : E, (∀ v : E, ParaSymplecticForm E J u v = 0) → u = 0) ∧
      (∀ v : E, (∀ u : E, ParaSymplecticForm E J u v = 0) → v = 0) := by
  constructor
  · intro u hzero
    exact paraSymplecticForm_left_nondegenerate J hJinj u hzero
  · intro v hzero
    exact paraSymplecticForm_right_nondegenerate J hJ hJinj v hzero

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem paraSymplecticForm_nondegenerate_of_involutive
    (J : E →L[ℝ] E)
    (hJ : ∀ u v : E, inner ℝ (J u) v = -inner ℝ u (J v))
    (hJinv : ∀ u : E, J (J u) = u) :
    (∀ u : E, (∀ v : E, ParaSymplecticForm E J u v = 0) → u = 0) ∧
      (∀ v : E, (∀ u : E, ParaSymplecticForm E J u v = 0) → v = 0) := by
  apply paraSymplecticForm_nondegenerate J hJ
  intro u v huv
  calc
    u = J (J u) := (hJinv u).symm
    _ = J (J v) := congrArg (fun z : E => J z) huv
    _ = v := hJinv v

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem para_involutive_antiSelfAdjoint_forces_zero
    (J : E →L[ℝ] E)
    (hJ : ∀ u v : E, inner ℝ (J u) v = -inner ℝ u (J v))
    (hJinv : ∀ u : E, J (J u) = u)
    (u : E) :
    u = 0 := by
  have hnorm : inner ℝ (J u) (J u) = -inner ℝ u u := by
    simpa [hJinv u] using hJ u (J u)
  have hnonneg₁ : 0 ≤ inner ℝ (J u) (J u) :=
    real_inner_self_nonneg
  have hnonneg₂ : 0 ≤ inner ℝ u u :=
    real_inner_self_nonneg
  have hzero : inner ℝ u u = 0 := by
    nlinarith
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp hzero

end InfoGeometry.Canonical.KaehlerGeometry
