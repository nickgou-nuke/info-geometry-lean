import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Complex.Basic
import InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms
import InfoGeometry.Optics.OperatorValuedConnection
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
import InfoGeometry.Canonical.SouriauOnsagerBKMBridge

/-!
# Positive probe interface for operator-valued BKM readouts

The finite operator carrier does not carry the ordered C⋆-algebra structure
needed by Mathlib's `PositiveLinearMap`.  This owner therefore records exactly
the scalar positivity and normalization used by a BKM readout, without
identifying it with a GNS or spinor state.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace InfoGeometry.Thermo.SouriauOnsagerBKMProbe

open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

structure NormalizedPositiveProbe where
  toLinearMap : A →ₗ[ℂ] ℂ
  positive : ∀ x : A, 0 ≤ (toLinearMap (star x * x)).re
  normalized : toLinearMap 1 = 1

instance : CoeFun (NormalizedPositiveProbe (A := A)) (fun _ => A → ℂ) where
  coe φ := φ.toLinearMap

@[simp] theorem normalized_apply_one (φ : NormalizedPositiveProbe (A := A)) :
    φ (1 : A) = 1 := φ.normalized

theorem positive_star_mul_self
    (φ : NormalizedPositiveProbe (A := A)) (x : A) :
    0 ≤ (φ (star x * x)).re := φ.positive x

def matrixTraceProbe (n : ℕ) :
    NormalizedPositiveProbe (A := MatrixStage n) where
  toLinearMap := matrixTraceFunctional n
  positive := by
    intro A
    exact InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness.matrixTraceState_star_mul_self_re_nonneg n A
  normalized := by
    exact matrixTraceState_one n

@[simp] theorem matrixTraceProbe_apply
    (n : ℕ) (A : MatrixStage n) :
    matrixTraceProbe n A = matrixTraceState n A := rfl

theorem matrixTraceProbe_positive
    (n : ℕ) (A : MatrixStage n) :
    0 ≤ (matrixTraceProbe n (star A * A)).re := by
  exact matrixTraceProbe n |>.positive A

@[simp] theorem matrixTraceProbe_normalized (n : ℕ) :
    matrixTraceProbe n (1 : MatrixStage n) = 1 := by
  exact (matrixTraceProbe n).normalized

def bitWordMatrixTraceProbe (n : ℕ) :
    NormalizedPositiveProbe (A := BitWordMatrixStage n) where
  toLinearMap :=
    (matrixTraceProbe n).toLinearMap.comp
      (bitWordStageStarAlgEquiv n).toAlgEquiv.toLinearMap
  positive := by
    intro A
    change 0 ≤
      (matrixTraceProbe n
        (bitWordStageStarAlgEquiv n (star A * A))).re
    have hmap :
        bitWordStageStarAlgEquiv n (star A * A) =
          star (bitWordStageStarAlgEquiv n A) *
            bitWordStageStarAlgEquiv n A := by
      simp only [map_mul, map_star]
    rw [hmap]
    exact (matrixTraceProbe n).positive
      (bitWordStageStarAlgEquiv n A)
  normalized := by
    change matrixTraceProbe n (bitWordStageStarAlgEquiv n (1 : BitWordMatrixStage n)) = 1
    have hone : bitWordStageStarAlgEquiv n (1 : BitWordMatrixStage n) = 1 :=
      (bitWordStageStarAlgEquiv n).map_one
    rw [hone]
    exact (matrixTraceProbe n).normalized

@[simp] theorem bitWordMatrixTraceProbe_apply
    (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordMatrixTraceProbe n A =
      matrixTraceProbe n (bitWordStageStarAlgEquiv n A) := rfl

theorem bitWordMatrixTraceProbe_eq_gaugeReadout
    (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordMatrixTraceProbe n A =
      bitWordMatrixGaugeReadout n A := by
  rw [bitWordMatrixTraceProbe_apply, matrixTraceProbe_apply]
  exact (bitWordMatrixGaugeReadout_transport n A).symm

theorem bitWordMatrixTraceProbe_positive
    (n : ℕ) (A : BitWordMatrixStage n) :
    0 ≤ (bitWordMatrixTraceProbe n (star A * A)).re := by
  exact (bitWordMatrixTraceProbe n).positive A

@[simp] theorem bitWordMatrixTraceProbe_normalized (n : ℕ) :
    bitWordMatrixTraceProbe n (1 : BitWordMatrixStage n) = 1 := by
  exact (bitWordMatrixTraceProbe n).normalized

theorem bitWordMatrixTraceProbe_colimit_inclusion
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    (n : ℕ) (A : BitWordMatrixStage n) :
    traceColimitFunctional T
        (traceColimitInclusion T n (bitWordStageStarAlgEquiv n A)) =
      bitWordMatrixTraceProbe n A := by
  rw [traceColimitFunctional_inclusion T n (bitWordStageStarAlgEquiv n A)]
  rw [bitWordMatrixTraceProbe_apply, matrixTraceProbe_apply]
  rfl

def readout
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : NormalizedPositiveProbe (A := A))
    (κ : Op2Form ℂ V A) (u v : V) : ℂ :=
  φ (κ u v)

theorem readout_skew
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : NormalizedPositiveProbe (A := A))
    (κ : Op2Form ℂ V A) (u v : V) :
    readout φ κ u v = -readout φ κ v u := by
  unfold readout
  rw [κ.skew]
  exact φ.toLinearMap.map_neg (κ v u)

def bkmProbeReadoutOfState
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : NormalizedPositiveProbe (A := A))
    (κ : Op2Form ℂ V A) (u v : V) : ℂ :=
  readout φ κ u v

def traceColimitBkmReadout
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    (n : ℕ) (κ : Op2Form ℂ V (BitWordMatrixStage n)) (u v : V) : ℂ :=
  traceColimitFunctional T
    (traceColimitInclusion T n (bitWordStageStarAlgEquiv n (κ u v)))

theorem traceColimitBkmReadout_eq_finite_probe
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    (n : ℕ) (κ : Op2Form ℂ V (BitWordMatrixStage n)) (u v : V) :
    traceColimitBkmReadout T hT n κ u v =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe n) κ u v := by
  unfold traceColimitBkmReadout bkmProbeReadoutOfState readout
  rw [traceColimitFunctional_inclusion T n (bitWordStageStarAlgEquiv n (κ u v))]
  rw [bitWordMatrixTraceProbe_apply, matrixTraceProbe_apply]
  rfl

theorem bkmProbeReadoutOfState_colimit_inclusion
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    (n : ℕ) (κ : Op2Form ℂ V (BitWordMatrixStage n)) (u v : V) :
    traceColimitFunctional T
        (traceColimitInclusion T n
          (bitWordStageStarAlgEquiv n (κ u v))) =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe n) κ u v := by
  unfold bkmProbeReadoutOfState readout
  exact bitWordMatrixTraceProbe_colimit_inclusion T hT n (κ u v)

theorem bkmProbeReadoutOfState_wedge_self_colimit_inclusion
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    (n : ℕ) (α : Op1Form ℂ V (BitWordMatrixStage n)) (u v : V) :
    traceColimitFunctional T
        (traceColimitInclusion T n
          (bitWordStageStarAlgEquiv n ((wedge α α) u v))) =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe n) (wedge α α) u v := by
  exact bkmProbeReadoutOfState_colimit_inclusion T hT n (wedge α α) u v

theorem bkmProbeReadoutOfState_wedge_self_colimit_inclusion_diag_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    (n : ℕ) (α : Op1Form ℂ V (BitWordMatrixStage n)) (u : V) :
    traceColimitFunctional T
        (traceColimitInclusion T n
          (bitWordStageStarAlgEquiv n ((wedge α α) u u))) = 0 := by
  rw [bkmProbeReadoutOfState_colimit_inclusion T hT n (wedge α α) u u]
  unfold bkmProbeReadoutOfState readout
  rw [wedge_apply]
  simp

theorem bitWordMatrixTraceProbe_transition
    (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordMatrixTraceProbe (n + 1)
        (bitWordDyadicStarEmbedding n A) =
      bitWordMatrixTraceProbe n A := by
  rw [bitWordMatrixTraceProbe_apply, bitWordMatrixTraceProbe_apply]
  rw [matrixTraceProbe_apply, matrixTraceProbe_apply]
  rw [bitWordDyadicStarEmbedding_apply]
  simp only [StarAlgEquiv.apply_symm_apply]
  exact concreteData.trace_compatible n (bitWordStageStarAlgEquiv n A)

theorem bitWordMatrixTraceProbe_map
    {i j : ℕ} (hij : i ≤ j) (A : BitWordMatrixStage i) :
    bitWordMatrixTraceProbe j (bitWordStarMap bitWordDyadicStarData hij A) =
      bitWordMatrixTraceProbe i A := by
  induction hij with
  | refl =>
      simp
  | step hjm ih =>
      rw [bitWordStarMap_succ bitWordDyadicStarData hjm]
      change bitWordMatrixTraceProbe _
          (bitWordDyadicStarEmbedding _
            (bitWordStarMap bitWordDyadicStarData hjm A)) = _
      rw [bitWordMatrixTraceProbe_transition]
      exact ih

def bitWordOp2FormMap
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (κ : Op2Form ℂ V (BitWordMatrixStage i)) :
    Op2Form ℂ V (BitWordMatrixStage j) where
  toBilin := {
    toFun := fun u => {
      toFun := fun v => bitWordStarMap bitWordDyadicStarData hij (κ u v)
      map_add' := by
        intro v w
        change (bitWordStarMap bitWordDyadicStarData hij)
            (κ.toBilin u (v + w)) = _
        rw [(κ.toBilin u).map_add]
        exact (bitWordStarMap bitWordDyadicStarData hij).map_add _ _
      map_smul' := by
        intro c v
        change (bitWordStarMap bitWordDyadicStarData hij)
            (κ.toBilin u (c • v)) = _
        rw [(κ.toBilin u).map_smul]
        exact map_smul (bitWordStarMap bitWordDyadicStarData hij) c _ }
    map_add' := by
      intro u w
      apply LinearMap.ext
      intro v
      change (bitWordStarMap bitWordDyadicStarData hij)
          (κ.toBilin (u + w) v) = _
      rw [κ.toBilin.map_add]
      exact (bitWordStarMap bitWordDyadicStarData hij).map_add _ _
    map_smul' := by
      intro c u
      apply LinearMap.ext
      intro v
      change (bitWordStarMap bitWordDyadicStarData hij)
          (κ.toBilin (c • u) v) = _
      rw [κ.toBilin.map_smul]
      exact map_smul (bitWordStarMap bitWordDyadicStarData hij) c _ }
  alt' := by
    intro u
    change (bitWordStarMap bitWordDyadicStarData hij)
        (κ.toBilin u u) = 0
    rw [κ.alt' u]
    exact (bitWordStarMap bitWordDyadicStarData hij).map_zero

@[simp] theorem bitWordOp2FormMap_apply
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (κ : Op2Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    bitWordOp2FormMap hij κ u v =
      bitWordStarMap bitWordDyadicStarData hij (κ u v) := by
  rfl

theorem bitWordOp2FormMap_comp
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (κ : Op2Form ℂ V (BitWordMatrixStage i)) :
    bitWordOp2FormMap hjk (bitWordOp2FormMap hij κ) =
      bitWordOp2FormMap (le_trans hij hjk) κ := by
  apply Op2Form.ext
  intro u v
  rw [bitWordOp2FormMap_apply, bitWordOp2FormMap_apply,
    bitWordOp2FormMap_apply]
  rw [← bitWordStarMap_comp bitWordDyadicStarData hij hjk]
  rfl

theorem bkmProbeReadoutOfState_map
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (κ : Op2Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    bkmProbeReadoutOfState (bitWordMatrixTraceProbe j)
        (bitWordOp2FormMap hij κ) u v =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe i) κ u v := by
  unfold bkmProbeReadoutOfState readout
  rw [bitWordOp2FormMap_apply]
  exact bitWordMatrixTraceProbe_map hij (κ u v)

theorem bkmProbeReadoutOfState_map_comp
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (κ : Op2Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    bkmProbeReadoutOfState (bitWordMatrixTraceProbe k)
        (bitWordOp2FormMap hjk (bitWordOp2FormMap hij κ)) u v =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe i) κ u v := by
  rw [bitWordOp2FormMap_comp hij hjk κ]
  exact bkmProbeReadoutOfState_map (le_trans hij hjk) κ u v

def bitWordOp1FormMap
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (α : Op1Form ℂ V (BitWordMatrixStage i)) :
    Op1Form ℂ V (BitWordMatrixStage j) where
  toFun := fun u => bitWordStarMap bitWordDyadicStarData hij (α u)
  map_add' := by
    intro u v
    rw [α.map_add]
    exact (bitWordStarMap bitWordDyadicStarData hij).map_add _ _
  map_smul' := by
    intro c u
    rw [α.map_smul]
    exact map_smul (bitWordStarMap bitWordDyadicStarData hij) c _

@[simp] theorem bitWordOp1FormMap_apply
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (α : Op1Form ℂ V (BitWordMatrixStage i)) (u : V) :
    bitWordOp1FormMap hij α u =
    bitWordStarMap bitWordDyadicStarData hij (α u) := rfl

theorem bitWordOp1FormMap_comp
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (α : Op1Form ℂ V (BitWordMatrixStage i)) :
    bitWordOp1FormMap hjk (bitWordOp1FormMap hij α) =
      bitWordOp1FormMap (le_trans hij hjk) α := by
  ext u
  rw [bitWordOp1FormMap_apply, bitWordOp1FormMap_apply,
    bitWordOp1FormMap_apply]
  rw [← bitWordStarMap_comp bitWordDyadicStarData hij hjk]
  rfl

theorem bitWordOp1FormMap_wedge
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (α β : Op1Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    wedge (bitWordOp1FormMap hij α) (bitWordOp1FormMap hij β) u v =
      bitWordOp2FormMap hij (wedge α β) u v := by
  change
    (bitWordStarMap bitWordDyadicStarData hij (α u)) *
        (bitWordStarMap bitWordDyadicStarData hij (β v)) -
      (bitWordStarMap bitWordDyadicStarData hij (α v)) *
        (bitWordStarMap bitWordDyadicStarData hij (β u)) =
      bitWordStarMap bitWordDyadicStarData hij ((wedge α β) u v)
  rw [wedge_apply, map_sub, map_mul, map_mul]

theorem bkmProbeReadoutOfState_map_wedge
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (α β : Op1Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    bkmProbeReadoutOfState (bitWordMatrixTraceProbe j)
        (bitWordOp2FormMap hij (wedge α β)) u v =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe i)
        (wedge α β) u v := by
  exact bkmProbeReadoutOfState_map hij (wedge α β) u v

theorem bkmProbeReadoutOfState_map_wedge_self_diag_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (α : Op1Form ℂ V (BitWordMatrixStage i)) (u : V) :
    bkmProbeReadoutOfState (bitWordMatrixTraceProbe j)
        (bitWordOp2FormMap hij (wedge α α)) u u = 0 := by
  rw [bkmProbeReadoutOfState_map_wedge]
  unfold bkmProbeReadoutOfState readout
  rw [wedge_apply]
  simp

theorem traceColimitBkmReadout_map_wedge
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    {i j : ℕ} (hij : i ≤ j)
    (α β : Op1Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    traceColimitBkmReadout T hT j
        (bitWordOp2FormMap hij (wedge α β)) u v =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe i)
        (wedge α β) u v := by
  rw [traceColimitBkmReadout_eq_finite_probe]
  exact bkmProbeReadoutOfState_map_wedge hij α β u v

theorem traceColimitBkmReadout_map_comp
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (κ : Op2Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    traceColimitBkmReadout T hT k
        (bitWordOp2FormMap hjk (bitWordOp2FormMap hij κ)) u v =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe i) κ u v := by
  rw [traceColimitBkmReadout_eq_finite_probe]
  exact bkmProbeReadoutOfState_map_comp hij hjk κ u v

theorem traceColimitBkmReadout_map_wedge_self_diag_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    {i j : ℕ} (hij : i ≤ j)
    (α : Op1Form ℂ V (BitWordMatrixStage i)) (u : V) :
    traceColimitBkmReadout T hT j
        (bitWordOp2FormMap hij (wedge α α)) u u = 0 := by
  rw [traceColimitBkmReadout_eq_finite_probe]
  exact bkmProbeReadoutOfState_map_wedge_self_diag_zero hij α u

def bitWordOperatorOneForm
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (α : Op1Form ℂ V (BitWordMatrixStage i)) :
    OperatorOneForm Unit V (BitWordMatrixStage i) :=
  fun _ u => α u

@[simp] theorem bitWordOperatorOneForm_apply
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (α : Op1Form ℂ V (BitWordMatrixStage i)) (u : V) :
    bitWordOperatorOneForm α () u = α u := rfl

theorem bitWordOperatorOneForm_wedgeSquare
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (u v : V) :
    wedgeSquare (bitWordOperatorOneForm α) () u v =
      (wedge α α) u v := by
  rw [wedge_apply]
  rfl

def bitWordConnection
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : V → V → BitWordMatrixStage i)
    (h_swap : ∀ u v, dα v u = -dα u v)
    (h_diag : ∀ u, dα u u = 0) :
    Connection (Point := Unit) (Tangent := V)
      (Value := BitWordMatrixStage i) where
  form := bitWordOperatorOneForm α
  derivative := fun _ => dα
  derivative_swap := by
    intro _ u v
    exact h_swap u v
  derivative_same := by
    intro _ u
    exact h_diag u

theorem bitWordConnection_curvature
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : V → V → BitWordMatrixStage i)
    (h_swap : ∀ u v, dα v u = -dα u v)
    (h_diag : ∀ u, dα u u = 0) (u v : V) :
    curvature (bitWordConnection α dα h_swap h_diag) () u v =
      dα u v + (wedge α α) u v := by
  unfold curvature wedgeSquare bitWordConnection
  rw [wedge_apply]
  rfl

def bitWordOp2FormConnection
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i : ℕ}
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : Op2Form ℂ V (BitWordMatrixStage i)) :
    Connection (Point := Unit) (Tangent := V)
      (Value := BitWordMatrixStage i) :=
  bitWordConnection α (fun u v => dα u v) (by
    intro u v
    rw [dα.skew v u]
    ) dα.alt

theorem bitWordOp2FormConnection_curvature
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i : ℕ}
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : Op2Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    curvature (bitWordOp2FormConnection α dα) () u v =
      dα u v + (wedge α α) u v := by
  apply bitWordConnection_curvature α (fun u v => dα u v) ?_ dα.alt u v
  intro u v
  rw [dα.skew v u]

def bitWordOp2FormConnectionCurvature
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i : ℕ}
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : Op2Form ℂ V (BitWordMatrixStage i)) :
    Op2Form ℂ V (BitWordMatrixStage i) where
  toBilin := {
    toFun := fun u => {
      toFun := fun v => dα u v + (wedge α α) u v
      map_add' := by
        intro v₁ v₂
        rw [dα.map_add_right, Op2Form.map_add_right]
        abel
      map_smul' := by
        intro c v
        rw [dα.map_smul_right, Op2Form.map_smul_right]
        simp only [RingHom.id_apply, smul_add]
    }
    map_add' := by
      intro u₁ u₂
      apply LinearMap.ext
      intro v
      change dα (u₁ + u₂) v + (wedge α α) (u₁ + u₂) v =
        (dα u₁ v + (wedge α α) u₁ v) +
          (dα u₂ v + (wedge α α) u₂ v)
      rw [dα.map_add_left, Op2Form.map_add_left]
      abel
    map_smul' := by
      intro c u
      apply LinearMap.ext
      intro v
      change dα (c • u) v + (wedge α α) (c • u) v =
        c • (dα u v + (wedge α α) u v)
      rw [dα.map_smul_left, Op2Form.map_smul_left]
      simp only [smul_add]
  }
  alt' := by
    intro u
    change dα u u + (wedge α α) u u = 0
    rw [dα.alt]
    simp

theorem bitWordOp2FormConnection_curvature_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i : ℕ}
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : Op2Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    bitWordOp2FormConnectionCurvature α dα u v =
      curvature (bitWordOp2FormConnection α dα) () u v := by
  rfl

theorem bitWordConnection_curvature_map
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : V → V → BitWordMatrixStage i)
    (h_swap : ∀ u v, dα v u = -dα u v)
    (h_diag : ∀ u, dα u u = 0)
    (u v : V) :
    curvature
        (bitWordConnection
          (bitWordOp1FormMap hij α)
          (fun u v => bitWordStarMap bitWordDyadicStarData hij (dα u v))
          (by
            intro u v
            change (bitWordStarMap bitWordDyadicStarData hij) (dα v u) = _
            rw [h_swap, map_neg])
          (by
            intro u
            change (bitWordStarMap bitWordDyadicStarData hij) (dα u u) = 0
            rw [h_diag]
            exact (bitWordStarMap bitWordDyadicStarData hij).map_zero))
        () u v =
      bitWordStarMap bitWordDyadicStarData hij
        (curvature (bitWordConnection α dα h_swap h_diag) () u v) := by
  rw [bitWordConnection_curvature]
  rw [bitWordConnection_curvature]
  rw [map_add]
  simp [bitWordOp1FormMap_apply] at *

theorem bitWordOp2FormConnection_curvature_map
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : Op2Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    curvature
        (bitWordOp2FormConnection
          (bitWordOp1FormMap hij α)
          (bitWordOp2FormMap hij dα)) () u v =
      bitWordStarMap bitWordDyadicStarData hij
        (curvature (bitWordOp2FormConnection α dα) () u v) := by
  apply bitWordConnection_curvature_map hij α (fun u v => dα u v) ?_ dα.alt u v
  intro u v
  rw [dα.skew v u]

theorem bitWordOp2FormConnectionCurvature_map
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : Op2Form ℂ V (BitWordMatrixStage i)) :
    bitWordOp2FormConnectionCurvature
        (bitWordOp1FormMap hij α)
        (bitWordOp2FormMap hij dα) =
      bitWordOp2FormMap hij
        (bitWordOp2FormConnectionCurvature α dα) := by
  apply Op2Form.ext
  intro u v
  change (bitWordOp2FormMap hij dα) u v +
      (wedge (bitWordOp1FormMap hij α) (bitWordOp1FormMap hij α)) u v =
    bitWordStarMap bitWordDyadicStarData hij
      (dα u v + (wedge α α) u v)
  rw [bitWordOp2FormMap_apply, bitWordOp1FormMap_wedge, map_add]
  rfl

theorem bitWordOp2FormConnectionCurvature_map_comp
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : Op2Form ℂ V (BitWordMatrixStage i)) :
    bitWordOp2FormConnectionCurvature
        (bitWordOp1FormMap hjk (bitWordOp1FormMap hij α))
        (bitWordOp2FormMap hjk (bitWordOp2FormMap hij dα)) =
      bitWordOp2FormMap (le_trans hij hjk)
        (bitWordOp2FormConnectionCurvature α dα) := by
  apply Op2Form.ext
  intro u v
  change curvature
      (bitWordOp2FormConnection
        (bitWordOp1FormMap hjk (bitWordOp1FormMap hij α))
        (bitWordOp2FormMap hjk (bitWordOp2FormMap hij dα))) () u v =
    bitWordOp2FormMap (le_trans hij hjk)
      (bitWordOp2FormConnectionCurvature α dα) u v
  rw [bitWordOp2FormConnection_curvature_map hjk
    (bitWordOp1FormMap hij α) (bitWordOp2FormMap hij dα)]
  rw [bitWordOp2FormConnection_curvature_map hij α dα]
  rw [bitWordOp2FormMap_apply]
  exact congrArg
    (fun F : BitWordMatrixStage i →⋆ₐ[ℂ] BitWordMatrixStage k =>
      F (curvature (bitWordOp2FormConnection α dα) () u v))
    (bitWordStarMap_comp bitWordDyadicStarData hij hjk)

theorem bkmProbeReadoutOfState_curvature_map
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j : ℕ} (hij : i ≤ j)
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : Op2Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    bkmProbeReadoutOfState (bitWordMatrixTraceProbe j)
        (bitWordOp2FormMap hij
          (bitWordOp2FormConnectionCurvature α dα)) u v =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe i)
        (bitWordOp2FormConnectionCurvature α dα) u v := by
  exact bkmProbeReadoutOfState_map hij
    (bitWordOp2FormConnectionCurvature α dα) u v

theorem bkmProbeReadoutOfState_curvature_map_comp
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : Op2Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    bkmProbeReadoutOfState (bitWordMatrixTraceProbe k)
        (bitWordOp2FormMap hjk
          (bitWordOp2FormMap hij
            (bitWordOp2FormConnectionCurvature α dα))) u v =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe i)
        (bitWordOp2FormConnectionCurvature α dα) u v := by
  exact bkmProbeReadoutOfState_map_comp hij hjk
    (bitWordOp2FormConnectionCurvature α dα) u v

theorem bkmProbeReadoutOfState_curvature_diag_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (n : ℕ)
    (α : Op1Form ℂ V (BitWordMatrixStage n))
    (dα : Op2Form ℂ V (BitWordMatrixStage n)) (u : V) :
    bkmProbeReadoutOfState (bitWordMatrixTraceProbe n)
        (bitWordOp2FormConnectionCurvature α dα) u u = 0 := by
  unfold bkmProbeReadoutOfState readout
  rw [Op2Form.alt]
  exact (bitWordMatrixTraceProbe n).toLinearMap.map_zero

theorem traceColimitBkmReadout_curvature_map
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    {i j : ℕ} (hij : i ≤ j)
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : Op2Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    traceColimitBkmReadout T hT j
        (bitWordOp2FormMap hij
          (bitWordOp2FormConnectionCurvature α dα)) u v =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe i)
        (bitWordOp2FormConnectionCurvature α dα) u v := by
  rw [traceColimitBkmReadout_eq_finite_probe]
  exact bkmProbeReadoutOfState_curvature_map hij α dα u v

theorem traceColimitBkmReadout_curvature_map_comp
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (α : Op1Form ℂ V (BitWordMatrixStage i))
    (dα : Op2Form ℂ V (BitWordMatrixStage i)) (u v : V) :
    traceColimitBkmReadout T hT k
        (bitWordOp2FormMap hjk
          (bitWordOp2FormMap hij
            (bitWordOp2FormConnectionCurvature α dα))) u v =
      bkmProbeReadoutOfState (bitWordMatrixTraceProbe i)
        (bitWordOp2FormConnectionCurvature α dα) u v := by
  rw [traceColimitBkmReadout_eq_finite_probe]
  exact bkmProbeReadoutOfState_curvature_map_comp hij hjk α dα u v

theorem traceColimitBkmReadout_curvature_diag_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    (n : ℕ)
    (α : Op1Form ℂ V (BitWordMatrixStage n))
    (dα : Op2Form ℂ V (BitWordMatrixStage n)) (u : V) :
    traceColimitBkmReadout T hT n
        (bitWordOp2FormConnectionCurvature α dα) u u = 0 := by
  rw [traceColimitBkmReadout_eq_finite_probe]
  unfold bkmProbeReadoutOfState readout
  rw [Op2Form.alt]
  exact (bitWordMatrixTraceProbe n).toLinearMap.map_zero

theorem traceColimitBkmReadout_curvature_skew
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    (n : ℕ)
    (α : Op1Form ℂ V (BitWordMatrixStage n))
    (dα : Op2Form ℂ V (BitWordMatrixStage n)) (u v : V) :
    traceColimitBkmReadout T hT n
        (bitWordOp2FormConnectionCurvature α dα) u v =
      -traceColimitBkmReadout T hT n
        (bitWordOp2FormConnectionCurvature α dα) v u := by
  rw [traceColimitBkmReadout_eq_finite_probe]
  rw [traceColimitBkmReadout_eq_finite_probe]
  exact readout_skew (bitWordMatrixTraceProbe n)
    (bitWordOp2FormConnectionCurvature α dα) u v

theorem bkmProbeReadoutOfState_skew
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : NormalizedPositiveProbe (A := A))
    (κ : Op2Form ℂ V A) (u v : V) :
    bkmProbeReadoutOfState φ κ u v =
      -bkmProbeReadoutOfState φ κ v u := by
  exact readout_skew φ κ u v

end InfoGeometry.Thermo.SouriauOnsagerBKMProbe
