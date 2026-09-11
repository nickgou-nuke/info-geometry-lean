import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.QCCRResidual
import InfoGeometry.Krein.Automorphisms
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological CAR locus for real Majorana endomorphisms

The real Majorana owner supplies CAR as an equality of continuous-linear
endomorphisms.  This file exposes that equality as a closed locus in the
non-commutative endomorphism ring, so it can be compared with the existing
q-CCR/Cuntz parameter and colimit surfaces without introducing a matrix model.
-/

noncomputable section

namespace InfoGeometry.Canonical.MajoranaCARTopologicalLocus

open CategoryTheory
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Quantum.RealMajorana

variable {S : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]

abbrev EndS := S →L[ℝ] S

/-- The CAR residual for a pair of real endomorphisms at two mode vectors. -/
def majoranaCARResidual (u v : S) (A B : EndS (S := S)) : EndS (S := S) :=
  A * B + B * A - (2 * inner ℝ u v) • ContinuousLinearMap.id ℝ S

/-- The residual is continuous on the product of the non-commutative operator rings. -/
def majoranaCARResidualMap (u v : S) :
    ContinuousMap (EndS (S := S) × EndS (S := S)) (EndS (S := S)) :=
  { toFun := fun p => majoranaCARResidual u v p.1 p.2
    continuous_toFun := by
      change Continuous (fun p : EndS (S := S) × EndS (S := S) =>
        p.1 * p.2 + p.2 * p.1 -
          (2 * inner ℝ u v) • ContinuousLinearMap.id ℝ S)
      fun_prop }

/-- TopCat presentation of the CAR residual map. -/
def majoranaCARResidualTopCatHom (u v : S) :
    TopCat.of (EndS (S := S) × EndS (S := S)) ⟶ TopCat.of (EndS (S := S)) :=
  TopCat.ofHom (majoranaCARResidualMap u v)

@[simp] theorem majoranaCARResidualMap_apply
    (u v : S) (A B : EndS (S := S)) :
    majoranaCARResidualMap u v (A, B) = majoranaCARResidual u v A B :=
  rfl

@[simp] theorem majoranaCARResidualTopCatHom_apply
    (u v : S) (A B : EndS (S := S)) :
    majoranaCARResidualTopCatHom u v (A, B) = majoranaCARResidual u v A B :=
  rfl

/-- Closed CAR locus for the pair of mode vectors `(u,v)`. -/
def majoranaCARLocus (u v : S) :
    Set (EndS (S := S) × EndS (S := S)) :=
  majoranaCARResidualMap u v ⁻¹' ({0} : Set (EndS (S := S)))

theorem majoranaCARLocus_isClosed (u v : S) :
    IsClosed (majoranaCARLocus u v) := by
  exact isClosed_singleton.preimage (majoranaCARResidualMap u v).continuous

/-- Every CAR pair supplied by a real Majorana datum lies in the closed locus. -/
theorem majoranaCAR_pair_mem_closed_locus
    (M : RealMajoranaDatum (S := S)) (u v : S) :
    (M.gamma u, M.gamma v) ∈ majoranaCARLocus u v := by
  change majoranaCARResidual u v (M.gamma u) (M.gamma v) = 0
  apply sub_eq_zero.mpr
  simpa [majoranaCARResidual, anticommutator] using M.car u v

/-- The normalized CAR locus is the `q = -1` q-CCR fiber. -/
theorem majoranaCAR_pair_qccr_neg_one_of_normalized_pair
    (M : RealMajoranaDatum (S := S)) (u v : S)
    (h_norm : 2 * inner ℝ u v = 1) :
    qCcrRelation (M.gamma u) (M.gamma v) (-1) = 0 := by
  have h_car : M.gamma u * M.gamma v + M.gamma v * M.gamma u = 1 := by
    calc
      M.gamma u * M.gamma v + M.gamma v * M.gamma u =
          (2 * inner ℝ u v) • ContinuousLinearMap.id ℝ S := by
            simpa [anticommutator] using M.car u v
      _ = 1 := by
        rw [h_norm, one_smul]
        rfl
  exact car_is_neg_one_qccr _ _ h_car

/-- Continuous conjugation of Majorana endomorphisms by a linear equivalence. -/
noncomputable def conjugateEndMap (U : S ≃L[ℝ] S) :
    ContinuousMap (EndS (S := S)) (EndS (S := S)) :=
  { toFun := conjugateCLM U
    continuous_toFun := (U.arrowCongr U).continuous_toFun }

/-- The induced continuous action on ordered pairs of endomorphisms. -/
noncomputable def conjugatePairMap (U : S ≃L[ℝ] S) :
    ContinuousMap
      (EndS (S := S) × EndS (S := S))
      (EndS (S := S) × EndS (S := S)) :=
  (conjugateEndMap U).prodMap (conjugateEndMap U)

@[simp] theorem conjugatePairMap_apply
    (U : S ≃L[ℝ] S) (A B : EndS (S := S)) :
    conjugatePairMap U (A, B) =
      (conjugateCLM U A, conjugateCLM U B) :=
  rfl

/-- An inner-product-preserving conjugation transports the closed CAR locus. -/
theorem conjugation_maps_car_locus
    (U : S ≃L[ℝ] S)
    (hU : ∀ u v : S, inner ℝ (U u) (U v) = inner ℝ u v)
    (u v : S) (A B : EndS (S := S))
    (hp : (A, B) ∈ majoranaCARLocus u v) :
    conjugatePairMap U (A, B) ∈ majoranaCARLocus (U u) (U v) := by
  change majoranaCARResidual (U u) (U v)
    (conjugateCLM U A) (conjugateCLM U B) = 0
  rw [show majoranaCARResidual (U u) (U v)
      (conjugateCLM U A) (conjugateCLM U B) =
      conjugateCLM U (majoranaCARResidual u v A B) by
        simp [majoranaCARResidual, hU]]
  rw [show majoranaCARResidual u v A B = 0 from hp]
  exact map_zero (conjEnd U)

/-- Mathlib continuous-linear-equivalence package for a Bogoliubov transport. -/
noncomputable def bogoliubovContinuousLinearEquiv
    {M : RealMajoranaDatum (S := S)}
    (T : RealBogoliubovTransform (S := S) M) [CompleteSpace S] :
    S ≃L[ℝ] S :=
  { toLinearEquiv :=
      { toFun := T.B
        invFun := T.Binv
        left_inv := by
          intro x
          exact T.Binv_apply_B x
        right_inv := by
          intro x
          exact T.B_apply_Binv x
        map_add' := by
          intro x y
          simp
        map_smul' := by
          intro c x
          simp }
    continuous_toFun := T.B.continuous
    continuous_invFun := T.Binv.continuous }

@[simp] theorem bogoliubovContinuousLinearEquiv_apply
    {M : RealMajoranaDatum (S := S)}
    (T : RealBogoliubovTransform (S := S) M) [CompleteSpace S]
    (x : S) :
    bogoliubovContinuousLinearEquiv T x = T.B x :=
  rfl

@[simp] theorem bogoliubovContinuousLinearEquiv_symm_apply
    {M : RealMajoranaDatum (S := S)}
    (T : RealBogoliubovTransform (S := S) M) [CompleteSpace S]
    (x : S) :
    (bogoliubovContinuousLinearEquiv T).symm x = T.Binv x :=
  rfl

theorem transportedMajorana_pair_mem_closed_locus
    {M : RealMajoranaDatum (S := S)}
    (T : RealBogoliubovTransform (S := S) M)
    [CompleteSpace S]
    (u v : S) :
    (T.transportGamma u, T.transportGamma v) ∈
      majoranaCARLocus (T.B u) (T.B v) := by
  change majoranaCARResidual (T.B u) (T.B v)
    (T.transportGamma u) (T.transportGamma v) = 0
  apply sub_eq_zero.mpr
  rw [T.preserves_inner u v]
  simpa [majoranaCARResidual, anticommutator] using T.transportGamma_car u v

end InfoGeometry.Canonical.MajoranaCARTopologicalLocus
