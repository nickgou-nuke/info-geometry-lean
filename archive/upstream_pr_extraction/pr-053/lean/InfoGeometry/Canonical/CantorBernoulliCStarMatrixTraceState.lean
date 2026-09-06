import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
import InfoGeometry.Canonical.CompatibleStateContinuousReadout

/-!
# Native finite C⋆-matrix trace state

The ordinary `MatrixStage` is the algebraic matrix carrier.  Mathlib's
operator-norm C⋆ structure lives on the type-copy `CStarMatrix`; this owner
performs that explicit transport instead of installing a false C⋆ instance on
the reducible matrix alias.
-/

noncomputable section

open CStarStateColimit.Native
open CStarStateColimit.Native.ContinuousStarInductiveSystem
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness
open scoped ComplexOrder InnerProductSpace NNReal

namespace InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState

abbrev CStarMatrixStage (n : ℕ) :=
  CStarMatrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

private def matrixEquiv (n : ℕ) :
    MatrixStage n ≃⋆ₐ[ℂ] CStarMatrixStage n :=
  CStarMatrix.ofMatrixStarAlgEquiv

private def matrixEquivStarAlgHom (n : ℕ) :
    MatrixStage n →⋆ₐ[ℂ] CStarMatrixStage n :=
  { toFun := matrixEquiv n
    map_one' := by rfl
    map_mul' := by intros; rfl
    map_zero' := by rfl
    map_add' := by intros; rfl
    commutes' := by
      intro r
      rfl
    map_star' := by intro A; rfl }

private def matrixEquivSymmStarAlgHom (n : ℕ) :
    CStarMatrixStage n →⋆ₐ[ℂ] MatrixStage n :=
  { toFun := (matrixEquiv n).symm
    map_one' := by rfl
    map_mul' := by intros; rfl
    map_zero' := by rfl
    map_add' := by intros; rfl
    commutes' := by
      intro r
      rfl
    map_star' := by intro A; rfl }

/-- The concrete successor embedding transported to Mathlib's finite C⋆ matrix
stages.  This is a finite-stage instance of the existing matrix tower, not an
infinite C⋆ completion. -/
def cstarConcreteStep (n : ℕ) :
    CStarMatrixStage n →⋆ₐ[ℂ] CStarMatrixStage (n + 1) :=
  (matrixEquivStarAlgHom (n + 1)).comp
    ((concreteStep n).comp (matrixEquivSymmStarAlgHom n))

def cstarConcreteMap {i j : ℕ} (hij : i ≤ j) :
    CStarMatrixStage i →⋆ₐ[ℂ] CStarMatrixStage j :=
  (matrixEquivStarAlgHom j).comp
    ((concreteMap hij).comp (matrixEquivSymmStarAlgHom i))

def cstarMatrixInductiveSystem :
    CStarStateColimit.Native.ContinuousStarInductiveSystem CStarMatrixStage where
  map := fun {i j} hij => cstarConcreteMap hij
  map_id := by
    intro i
    apply StarAlgHom.ext
    intro A
    change (matrixEquiv i)
        (concreteMap (le_refl i) ((matrixEquiv i).symm A)) = A
    rw [concreteMap_id]
    exact (matrixEquiv i).apply_symm_apply A
  map_comp := by
    intro i j k hij hjk
    apply StarAlgHom.ext
    intro A
    change (matrixEquiv k)
        (concreteMap hjk (concreteMap hij ((matrixEquiv i).symm A))) =
      (matrixEquiv k)
        (concreteMap (le_trans hij hjk) ((matrixEquiv i).symm A))
    rw [show concreteMap hjk (concreteMap hij ((matrixEquiv i).symm A)) =
        concreteMap (le_trans hij hjk) ((matrixEquiv i).symm A) by
      exact congrArg (fun f => f ((matrixEquiv i).symm A))
        (concreteMap_comp hij hjk)]

def cstarMatrixTraceFunctional (n : ℕ) :
    CStarMatrixStage n →ₗ[ℂ] ℂ :=
  (matrixTraceFunctional n).comp
    (matrixEquiv n).symm.toAlgEquiv.toLinearMap

@[simp] theorem cstarMatrixTraceFunctional_apply
    (n : ℕ) (A : CStarMatrixStage n) :
    cstarMatrixTraceFunctional n A =
      matrixTraceState n ((matrixEquiv n).symm A) :=
  rfl

theorem cstarMatrixTraceFunctional_monotone (n : ℕ) :
    Monotone (cstarMatrixTraceFunctional n) := by
  intro A B hAB
  rw [← sub_nonneg] at hAB ⊢
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hAB
  rw [← map_sub, hC]
  let C' : MatrixStage n := (matrixEquiv n).symm C
  have hC' : (matrixEquiv n).symm (star C * C) = star C' * C' := by
    rw [map_mul, map_star]
  change 0 ≤ matrixTraceState n ((matrixEquiv n).symm (star C * C))
  rw [hC']
  apply Complex.le_def.mpr
  constructor
  · exact matrixTraceState_star_mul_self_re_nonneg n C'
  · exact (matrixTraceState_star_mul_self_im_zero n C').symm

def cstarMatrixPositiveTraceFunctional (n : ℕ) :
    CStarMatrixStage n →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk (cstarMatrixTraceFunctional n)
    (cstarMatrixTraceFunctional_monotone n)

@[simp] theorem cstarMatrixPositiveTraceFunctional_apply
    (n : ℕ) (A : CStarMatrixStage n) :
    cstarMatrixPositiveTraceFunctional n A =
      matrixTraceState n ((matrixEquiv n).symm A) :=
  rfl

theorem cstarMatrixPositiveTraceFunctional_one (n : ℕ) :
    cstarMatrixPositiveTraceFunctional n (1 : CStarMatrixStage n) = 1 := by
  rw [cstarMatrixPositiveTraceFunctional_apply]
  simp

/-! Positive elements already satisfy the sharp finite-stage norm bound.  This
is the order-theoretic estimate needed by any later extension argument; it is
not yet a bound for the full infinite Cuntz closure. -/
theorem cstarMatrixPositiveTraceFunctional_norm_apply_le
    (n : ℕ) (A : CStarMatrixStage n) (hA : 0 ≤ A) :
    ‖cstarMatrixPositiveTraceFunctional n A‖ ≤ ‖A‖ := by
  have h := PositiveLinearMap.norm_apply_le_of_nonneg
    (cstarMatrixPositiveTraceFunctional n) A hA
  simpa [cstarMatrixPositiveTraceFunctional_one n] using h

/-! A uniform bound on arbitrary finite-stage elements, obtained from the
four-positive decomposition of a C⋆-algebra element.  The constant `4` is
deliberately explicit; the sharper state norm bound is a separate theorem. -/
theorem cstarMatrixPositiveTraceFunctional_norm_apply_le_four
    (n : ℕ) (A : CStarMatrixStage n) :
    ‖cstarMatrixPositiveTraceFunctional n A‖ ≤ 4 * ‖A‖ := by
  obtain ⟨x, hx_nonneg, hx_norm, hx_sum⟩ :=
    CStarAlgebra.exists_sum_four_nonneg A
  conv_lhs => rw [hx_sum]
  simp only [map_sum, map_smul]
  apply (norm_sum_le _ _).trans
  have hterm : ∀ i : Fin 4,
      ‖(Complex.I ^ (i : ℕ)) •
          cstarMatrixPositiveTraceFunctional n (x i)‖ ≤ ‖A‖ := by
    intro i
    rw [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
    exact (cstarMatrixPositiveTraceFunctional_norm_apply_le n (x i) (hx_nonneg i)).trans
      (hx_norm i)
  calc
    (∑ i : Fin 4,
        ‖(Complex.I ^ (i : ℕ)) •
          cstarMatrixPositiveTraceFunctional n (x i)‖) ≤
        ∑ _i : Fin 4, ‖A‖ :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = 4 * ‖A‖ := by simp [Finset.card_univ]

/-- Every finite-stage positive trace is bounded by the native C⋆ positive-map
API.  This is a finite-stage continuity result; it does not construct an
infinite UHF or Cuntz completion. -/
theorem cstarMatrixPositiveTraceFunctional_exists_norm_apply_le (n : ℕ) :
    ∃ C : ℝ≥0, ∀ (A : CStarMatrixStage n),
      ‖cstarMatrixPositiveTraceFunctional n A‖ ≤ (C : ℝ) * ‖A‖ := by
  exact PositiveLinearMap.exists_norm_apply_le
    (cstarMatrixPositiveTraceFunctional n)

theorem cstarMatrixPositiveTraceFunctional_continuous (n : ℕ) :
    Continuous (fun A : CStarMatrixStage n =>
      cstarMatrixPositiveTraceFunctional n A) := by
  exact ContinuousMapClass.map_continuous
    (cstarMatrixPositiveTraceFunctional n)

def cstarMatrixTraceState (n : ℕ) : State (CStarMatrixStage n) where
  functional := cstarMatrixPositiveTraceFunctional n
  normalized := cstarMatrixPositiveTraceFunctional_one n

theorem cstarMatrixTraceState_faithful
    (n : ℕ) (A : CStarMatrixStage n) :
    (cstarMatrixTraceState n).functional (star A * A) = 0 ↔ A = 0 := by
  change cstarMatrixPositiveTraceFunctional n (star A * A) = 0 ↔ A = 0
  rw [cstarMatrixPositiveTraceFunctional_apply]
  have htransport :
      (matrixEquiv n).symm (star A * A) =
        star ((matrixEquiv n).symm A) * (matrixEquiv n).symm A := by
    rw [map_mul, map_star]
  rw [htransport]
  rw [matrixTraceState_star_mul_self_eq_zero_iff]
  exact (matrixEquiv n).symm.injective.eq_iff

/-- The native finite C⋆ trace states are compatible with the transported
successor maps.  This is the concrete state-family wire; it does not assert
the existence of an infinite C⋆ completion. -/
theorem cstarMatrixTraceState_transition (n : ℕ) (A : CStarMatrixStage n) :
    (cstarMatrixTraceState (n + 1)).functional
        (cstarConcreteStep n A) =
      (cstarMatrixTraceState n).functional A := by
  change matrixTraceState (n + 1)
      ((matrixEquiv (n + 1)).symm (cstarConcreteStep n A)) =
    matrixTraceState n ((matrixEquiv n).symm A)
  change matrixTraceState (n + 1)
      (concreteStep n ((matrixEquiv n).symm A)) =
    matrixTraceState n ((matrixEquiv n).symm A)
  exact concrete_trace_compatible n ((matrixEquiv n).symm A)

theorem cstarMatrixTraceState_restrict (n : ℕ) :
    (cstarMatrixTraceState (n + 1)).restrict (cstarConcreteStep n) =
      cstarMatrixTraceState n := by
  ext A
  exact cstarMatrixTraceState_transition n A

theorem cstarMatrixTraceState_transition_general
    {i j : ℕ} (hij : i ≤ j) (A : CStarMatrixStage i) :
    (cstarMatrixTraceState j).functional (cstarConcreteMap hij A) =
      (cstarMatrixTraceState i).functional A := by
  change matrixTraceState j
      ((matrixEquiv j).symm (cstarConcreteMap hij A)) =
    matrixTraceState i ((matrixEquiv i).symm A)
  change matrixTraceState j
      (concreteMap hij ((matrixEquiv i).symm A)) =
    matrixTraceState i ((matrixEquiv i).symm A)
  exact concreteMap_trace hij ((matrixEquiv i).symm A)

def cstarMatrixTraceStateFamily :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      CStarMatrixStage cstarMatrixInductiveSystem where
  state := cstarMatrixTraceState
  compatible := by
    intro i j hij
    ext A
    exact cstarMatrixTraceState_transition_general hij A

/-! The compatible native states also give the existing topological-colimit
readout.  This is a continuous scalar readout of the finite-stage colimit;
it is not an infinite C⋆ state or a completion theorem. -/

noncomputable def cstarMatrixTraceStateTopologicalColimitMap :
    topologicalColimit CStarMatrixStage cstarMatrixInductiveSystem ⟶
      TopCat.of (ULift ℂ) :=
  cstarMatrixTraceStateFamily.toTopologicalColimitMap
    CStarMatrixStage cstarMatrixInductiveSystem

theorem cstarMatrixTraceStateTopologicalColimitMap_inclusion
    (n : ℕ) (A : CStarMatrixStage n) :
    cstarMatrixTraceStateTopologicalColimitMap
        (topologicalInjection CStarMatrixStage cstarMatrixInductiveSystem n A) =
      ULift.up ((cstarMatrixTraceState n).functional A) := by
  exact cstarMatrixTraceStateFamily.toTopologicalColimitMap_inclusion
    CStarMatrixStage cstarMatrixInductiveSystem n A

/-! The same finite trace family can be viewed through the native continuous
readout interface.  This is an interface-level compatibility result; it does
not add an infinite C⋆ completion. -/

noncomputable def cstarMatrixTraceCompatibleContinuousReadout :
    CompatibleContinuousStateReadout
      CStarMatrixStage cstarMatrixInductiveSystem :=
  cstarMatrixTraceStateFamily.toContinuousReadout
    CStarMatrixStage cstarMatrixInductiveSystem

@[simp] theorem cstarMatrixTraceCompatibleContinuousReadout_apply
    (n : ℕ) (A : CStarMatrixStage n) :
    cstarMatrixTraceCompatibleContinuousReadout.readout n A =
      (cstarMatrixTraceState n).functional A :=
  rfl

theorem cstarMatrixTraceStateTopologicalColimitMap_eq_compatibleReadout :
    cstarMatrixTraceStateTopologicalColimitMap =
      cstarMatrixTraceCompatibleContinuousReadout.toTopologicalColimitMap
        CStarMatrixStage cstarMatrixInductiveSystem := by
  apply CompatibleContinuousStateReadout.toTopologicalColimitMap_unique
    (Stage := CStarMatrixStage) (sys := cstarMatrixInductiveSystem)
    cstarMatrixTraceCompatibleContinuousReadout
    cstarMatrixTraceStateTopologicalColimitMap
  intro n A
  rw [cstarMatrixTraceStateTopologicalColimitMap_inclusion]
  rfl

end InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
