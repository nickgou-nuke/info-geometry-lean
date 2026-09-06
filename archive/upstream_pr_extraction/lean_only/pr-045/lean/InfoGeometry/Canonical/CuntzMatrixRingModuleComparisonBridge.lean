import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Canonical.CuntzMatrixRingColimitHestenesBridge
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.CuntzMatrixStarColimitBridge
import InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
import InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional

/-!
# Comparison and Trace Transport between RingCat and ModuleCat Colimits

This module bridges the `RingCat` filtered colimit $A_\infty^{\rm ring}$ and the
`ModuleCat ℂ` colimit $A_\infty^{\rm lin}$.

Since every finite matrix stage $M_{2^n}(\mathbb{C})$ carries both ring multiplication
and $\mathbb{C}$-linear structure with canonical normalized trace $\tau_n$, and the
directed transition embeddings $\iota_{m,n} : M_{2^m}(\mathbb{C}) \to M_{2^n}(\mathbb{C})$
are star-algebra homomorphisms preserving both multiplication and normalized trace:
$$\tau_n(\iota_{m,n}(A)) = \tau_m(A),$$
the trace functional $\tau_\infty$ descends consistently across all finite-stage representatives
of the ring colimit $A_\infty^{\rm ring}$.

## Key Theorems:
- `stageTrace_transition`: Trace evaluation is invariant under stage transitions $\iota_{m,n}$.
- `stageTrace_one`: $\tau(1) = 1$.
- `stageTrace_add`, `stageTrace_smul`: Trace is $\mathbb{C}$-linear on stage representatives.
- `stageTrace_mul_comm`: Trace cyclicity $\tau(A B) = \tau(B A)$ holds on every stage representative.
- `stageTrace_star`: $\tau(A^*) = \overline{\tau(A)}$.
- `stageTrace_star_mul_self_nonneg`: $\operatorname{Re}(\tau(B^* B)) \ge 0$ (state positivity).
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixRingModuleComparisonBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixRingColimitHestenesBridge
open InfoGeometry.Canonical.CuntzMatrixStarColimitBridge
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional

/-- Normalized trace evaluation on a stage representative in the ring colimit. -/
def stageTrace (n : ℕ) (A : MatrixStage n) : ℂ :=
  matrixTraceState n A

/-- Trace evaluation is invariant under stage transitions in the ring colimit. -/
theorem stageTrace_transition {m n : ℕ} (hmn : m ≤ n) (A : MatrixStage m) :
    stageTrace n (concreteMap hmn A) = stageTrace m A := by
  dsimp [stageTrace]
  exact concreteMap_trace hmn A

/-- Normalized trace on stage unit is 1. -/
theorem stageTrace_one (n : ℕ) : stageTrace n (1 : MatrixStage n) = 1 := by
  dsimp [stageTrace]
  exact matrixTraceState_one n

/-- Normalized trace on stage zero is 0. -/
theorem stageTrace_zero (n : ℕ) : stageTrace n (0 : MatrixStage n) = 0 := by
  dsimp [stageTrace, matrixTraceState, matrixTraceFunctional]
  simp

/-- Trace is linear on stage representatives. -/
theorem stageTrace_add (n : ℕ) (A B : MatrixStage n) :
    stageTrace n (A + B) = stageTrace n A + stageTrace n B := by
  dsimp [stageTrace, matrixTraceState]
  exact (matrixTraceFunctional n).map_add A B

theorem stageTrace_smul (n : ℕ) (c : ℂ) (A : MatrixStage n) :
    stageTrace n (c • A) = c * stageTrace n A := by
  dsimp [stageTrace, matrixTraceState]
  exact (matrixTraceFunctional n).map_smul c A

/-- Trace cyclicity holds on each stage of the ring colimit. -/
theorem stageTrace_mul_comm (n : ℕ) (A B : MatrixStage n) :
    stageTrace n (A * B) = stageTrace n (B * A) := by
  dsimp [stageTrace]
  exact matrixTraceState_mul_comm n A B

/-- Trace of adjoint is complex conjugate of trace. -/
theorem stageTrace_star (n : ℕ) (A : MatrixStage n) :
    star (stageTrace n A) = stageTrace n (star A) := by
  dsimp [stageTrace]
  exact matrixTraceState_star n A

/-- Trace of a positive element (B* B) is real non-negative. -/
theorem stageTrace_star_mul_self_nonneg (n : ℕ) (B : MatrixStage n) :
    0 ≤ (stageTrace n (star B * B)).re := by
  dsimp [stageTrace]
  exact matrixTraceState_realPart_star_mul_self_nonneg n B

/-! ## Native comparison of the two algebraic colimit presentations -/

abbrev AlgebraicCarrier : Type :=
  CuntzMatrixAlgebraicStarColimit.Carrier

/-- Ring map from the explicit directed-limit presentation to the native `RingCat` colimit. -/
def algebraicCarrierToRingColimit : AlgebraicCarrier →+* RingColimit :=
  DirectLimit.Ring.lift
    MatrixStage
    (fun _ _ hij => rawMap hij)
    RingColimit
    (fun n => ringColimitInclusion n)
    (by
      intro m n hmn A
      exact ringColimit_stage_transition hmn A)

@[simp] theorem algebraicCarrierToRingColimit_stage
    (n : ℕ) (A : MatrixStage n) :
    algebraicCarrierToRingColimit (stageInjection n A) =
      ringColimitInclusion n A := by
  rfl

/-- A RingCat cocone with legs given by the explicit direct-limit injections. -/
def algebraicCarrierRingCocone : Cocone ringDiagram where
  pt := RingCat.of AlgebraicCarrier
  ι :=
    { app := fun n => RingCat.ofHom (stageInjection n).toRingHom
      naturality := by
        intro m n f
        apply RingCat.hom_ext
        ext A
        change stageInjection n (rawMap (leOfHom f) A) = stageInjection m A
        exact stageInjection_transition (leOfHom f) A }

def ringColimitToAlgebraicCarrier : RingColimit →+* AlgebraicCarrier :=
  (ringColimit_isColimit.desc algebraicCarrierRingCocone).hom

@[simp] theorem ringColimitToAlgebraicCarrier_stage
    (n : ℕ) (A : MatrixStage n) :
    ringColimitToAlgebraicCarrier (ringColimitInclusion n A) =
      stageInjection n A := by
  have h := ringColimit_isColimit.fac algebraicCarrierRingCocone n
  exact congrArg (fun f => f.hom A) h

/-- The two native algebraic colimit presentations are canonically isomorphic as rings. -/
def algebraicCarrierRingEquiv : AlgebraicCarrier ≃+* RingColimit where
  toEquiv :=
    { toFun := algebraicCarrierToRingColimit
      invFun := ringColimitToAlgebraicCarrier
      left_inv := by
        intro x
        induction x using DirectLimit.induction with
        | _ n A =>
            change ringColimitToAlgebraicCarrier
              (algebraicCarrierToRingColimit (stageInjection n A)) = stageInjection n A
            rw [algebraicCarrierToRingColimit_stage,
              ringColimitToAlgebraicCarrier_stage]
      right_inv := by
        intro x
        have hcomp :
            RingCat.ofHom (RingHom.id RingColimit) =
              RingCat.ofHom
                (algebraicCarrierToRingColimit.comp ringColimitToAlgebraicCarrier) := by
          apply ringColimit_hom_ext
          intro n
          apply RingCat.hom_ext
          ext A
          change ringColimitInclusion n A =
            algebraicCarrierToRingColimit
              (ringColimitToAlgebraicCarrier (ringColimitInclusion n A))
          rw [ringColimitToAlgebraicCarrier_stage,
            algebraicCarrierToRingColimit_stage]
        have hx := congrArg (fun f => f.hom x) hcomp
        simpa using hx.symm }
  map_mul' := map_mul algebraicCarrierToRingColimit
  map_add' := map_add algebraicCarrierToRingColimit

@[simp] theorem algebraicCarrierRingEquiv_stage
    (n : ℕ) (A : MatrixStage n) :
    algebraicCarrierRingEquiv (stageInjection n A) =
      ringColimitInclusion n A := by
  rfl

@[simp] theorem algebraicCarrierRingEquiv_symm_stage
    (n : ℕ) (A : MatrixStage n) :
    algebraicCarrierRingEquiv.symm (ringColimitInclusion n A) =
      stageInjection n A := by
  change ringColimitToAlgebraicCarrier (ringColimitInclusion n A) = stageInjection n A
  exact ringColimitToAlgebraicCarrier_stage n A

/-! The trace is now readable on the `RingCat` carrier through this equivalence.
It is exposed first as an additive/cyclic readout; no unproved `ℂ`-module
structure is introduced on the `RingCat` colimit. -/

/-- The star operation transported from the explicit algebraic colimit presentation.
This is algebraic only; no norm or completion is introduced. -/
def transportedRingColimitStar (x : RingColimit) : RingColimit :=
  algebraicCarrierRingEquiv (star (algebraicCarrierRingEquiv.symm x))

instance ringColimitStarRing : StarRing RingColimit where
  star := transportedRingColimitStar
  star_involutive := by
    intro x
    unfold transportedRingColimitStar
    rw [algebraicCarrierRingEquiv.symm_apply_apply, star_involutive, algebraicCarrierRingEquiv.apply_symm_apply]
  star_mul := by
    intro x y
    unfold transportedRingColimitStar
    simp only [map_mul, star_mul]
  star_add := by
    intro x y
    unfold transportedRingColimitStar
    simp only [map_add, star_add]

def ringColimitTraceReadout (x : RingColimit) : ℂ :=
  traceFunctional (algebraicCarrierRingEquiv.symm x)

@[simp] theorem ringColimitTraceReadout_stage
    (n : ℕ) (A : MatrixStage n) :
    ringColimitTraceReadout (ringColimitInclusion n A) =
      matrixTraceState n A := by
  dsimp [ringColimitTraceReadout]
  rw [algebraicCarrierRingEquiv_symm_stage, traceFunctional_stage]

theorem ringColimitTraceReadout_add (x y : RingColimit) :
    ringColimitTraceReadout (x + y) =
      ringColimitTraceReadout x + ringColimitTraceReadout y := by
  dsimp [ringColimitTraceReadout]
  rw [map_add]
  exact map_add (traceFunctional) _ _

theorem ringColimitTraceReadout_cyclic (x y : RingColimit) :
    ringColimitTraceReadout (x * y) =
      ringColimitTraceReadout (y * x) := by
  dsimp [ringColimitTraceReadout]
  rw [(algebraicCarrierRingEquiv.symm).map_mul,
    (algebraicCarrierRingEquiv.symm).map_mul]
  exact traceFunctional_cyclic _ _

theorem ringColimitTraceReadout_star (x : RingColimit) :
    ringColimitTraceReadout (star x) = star (ringColimitTraceReadout x) := by
  dsimp [ringColimitTraceReadout]
  rw [show star x = transportedRingColimitStar x by rfl]
  unfold transportedRingColimitStar
  rw [algebraicCarrierRingEquiv.symm_apply_apply]
  exact traceFunctional_star _

end InfoGeometry.Canonical.CuntzMatrixRingModuleComparisonBridge
