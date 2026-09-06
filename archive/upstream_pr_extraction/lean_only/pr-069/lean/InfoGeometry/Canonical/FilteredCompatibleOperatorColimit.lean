import InfoGeometry.Canonical.FilteredIsometricHilbertCompletion
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Compatible bounded operators on filtered Hilbert colimits

A coherent uniformly bounded family of operators on an isometric filtered
system descends through Mathlib's genuine module direct limit.  Its norm bound
then extends the descended operator continuously to the completed Hilbert
colimit.

This is the reusable operator-topology layer needed for filtered GNS
representations: no coordinates, diagonalization, ambient operator, or
analytic limiting parameter is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredCompatibleOperatorColimit

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (E : I → Type u)
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, InnerProductSpace ℂ (E i)]
variable (sys : IsometricDirectSystem E)

local notation "D∞" => RealDirectLimit E sys
local notation "H∞" => HilbertDirectLimit E sys

/-- A stagewise operator family that intertwines every transition and obeys
one uniform operator bound. -/
abbrev CompatibleOperatorFamily := ∀ i, E i →L[ℂ] E i

variable (T : CompatibleOperatorFamily E)

/-- One stage operator followed by the canonical algebraic-colimit
inclusion, viewed over the real scalar ring used by `Module.DirectLimit`. -/
def stageOperatorToDirectLimitRealMap
    (i : I) :
    E i →ₗ[ℝ] D∞ where
  toFun := fun x =>
    stageToDirectLimitLinearMap E sys i (T i x)
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro r x
    have hop :=
      (T i).toLinearMap.map_smul_of_tower r x
    change
      (Module.DirectLimit.of
        ℝ I E
        (fun _ _ hij => realTransition E sys hij)
        i) (T i (r • x)) =
      r •
        (Module.DirectLimit.of
          ℝ I E
          (fun _ _ hij => realTransition E sys hij)
          i) (T i x)
    calc
      (Module.DirectLimit.of
        ℝ I E
        (fun _ _ hij => realTransition E sys hij)
        i) (T i (r • x)) =
          (Module.DirectLimit.of
            ℝ I E
            (fun _ _ hij => realTransition E sys hij)
            i) (r • T i x) :=
        congrArg
          (Module.DirectLimit.of
            ℝ I E
            (fun _ _ hij => realTransition E sys hij)
            i) hop
      _ = r •
          (Module.DirectLimit.of
            ℝ I E
            (fun _ _ hij => realTransition E sys hij)
            i) (T i x) :=
        (Module.DirectLimit.of
          ℝ I E
          (fun _ _ hij => realTransition E sys hij)
          i).map_smul r (T i x)

/-- The stage operator maps form a cocone over the underlying real direct
system. -/
theorem stageOperatorToDirectLimitRealMap_compatible
    (hintertwines :
      ∀ {i j : I} (hij : i ≤ j) (x : E i),
        sys.map hij (T i x) = T j (sys.map hij x))
    (i j : I) (hij : i ≤ j) (x : E i) :
    stageOperatorToDirectLimitRealMap E sys T j
        (realTransition E sys hij x) =
      stageOperatorToDirectLimitRealMap E sys T i x := by
  change
    stageToDirectLimitLinearMap E sys j
        (T j (sys.map hij x)) =
      stageToDirectLimitLinearMap E sys i (T i x)
  rw [← hintertwines hij x]
  exact
    stageToDirectLimitLinearMap_transition
      E sys hij (T i x)

/-- Real-linear operator descended through the algebraic module direct
limit. -/
def algebraicOperatorReal
    (hintertwines :
      ∀ {i j : I} (hij : i ≤ j) (x : E i),
        sys.map hij (T i x) = T j (sys.map hij x)) :
    D∞ →ₗ[ℝ] D∞ :=
  Module.DirectLimit.lift
    ℝ I E
    (fun _ _ hij => realTransition E sys hij)
    (stageOperatorToDirectLimitRealMap E sys T)
    (stageOperatorToDirectLimitRealMap_compatible E sys T hintertwines)

@[simp] theorem algebraicOperatorReal_of
    (hintertwines :
      ∀ {i j : I} (hij : i ≤ j) (x : E i),
        sys.map hij (T i x) = T j (sys.map hij x))
    (i : I) (x : E i) :
    algebraicOperatorReal E sys T hintertwines
        (Module.DirectLimit.of
          ℝ I E
          (fun _ _ hij => realTransition E sys hij)
          i x) =
      Module.DirectLimit.of
        ℝ I E
        (fun _ _ hij => realTransition E sys hij)
        i (T i x) := by
  simpa only [stageOperatorToDirectLimitRealMap,
    stageToDirectLimitLinearMap] using
    (Module.DirectLimit.lift_of
      (g := stageOperatorToDirectLimitRealMap E sys T)
      (stageOperatorToDirectLimitRealMap_compatible E sys T hintertwines)
      (i := i) x)

/-- The descended operator is complex-linear; complex scalar multiplication
was itself descended from the same transition system. -/
def algebraicOperator
    (hintertwines :
      ∀ {i j : I} (hij : i ≤ j) (x : E i),
        sys.map hij (T i x) = T j (sys.map hij x)) :
    D∞ →ₗ[ℂ] D∞ where
  toFun := algebraicOperatorReal E sys T hintertwines
  map_add' := (algebraicOperatorReal E sys T hintertwines).map_add
  map_smul' := by
    intro c z
    induction z using Module.DirectLimit.induction_on with
    | ih i x =>
        simp only [complex_smul_of,
          algebraicOperatorReal_of, map_smul]
        rfl

@[simp] theorem algebraicOperator_of
    (hintertwines :
      ∀ {i j : I} (hij : i ≤ j) (x : E i),
        sys.map hij (T i x) = T j (sys.map hij x))
    (i : I) (x : E i) :
    algebraicOperator E sys T hintertwines
        (stageToDirectLimitLinearMap E sys i x) =
      stageToDirectLimitLinearMap E sys i (T i x) := by
  exact algebraicOperatorReal_of E sys T hintertwines i x

/-- The stagewise uniform bound descends unchanged to the algebraic
colimit. -/
theorem algebraicOperator_norm_le
    (hintertwines :
      ∀ {i j : I} (hij : i ≤ j) (x : E i),
        sys.map hij (T i x) = T j (sys.map hij x))
    (bound : ℝ)
    (hnorm_le : ∀ i (x : E i), ‖T i x‖ ≤ bound * ‖x‖)
    (z : D∞) :
    ‖algebraicOperator E sys T hintertwines z‖ ≤
      bound * ‖z‖ := by
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      change
        ‖algebraicOperator E sys T hintertwines
            (stageToDirectLimitLinearMap E sys i x)‖ ≤
          bound *
            ‖stageToDirectLimitLinearMap E sys i x‖
      rw [algebraicOperator_of E sys T hintertwines]
      change
        ‖stageToDirectLimitLinearIsometry E sys i
            (T i x)‖ ≤
          bound *
            ‖stageToDirectLimitLinearIsometry E sys i x‖
      rw [(stageToDirectLimitLinearIsometry E sys i).norm_map,
        (stageToDirectLimitLinearIsometry E sys i).norm_map]
      exact hnorm_le i x

/-- The descended algebraic operator bundled as a bounded complex-linear
operator. -/
def algebraicOperatorCLM
    (hintertwines :
      ∀ {i j : I} (hij : i ≤ j) (x : E i),
        sys.map hij (T i x) = T j (sys.map hij x))
    (bound : ℝ)
    (hnorm_le : ∀ i (x : E i), ‖T i x‖ ≤ bound * ‖x‖) :
    D∞ →L[ℂ] D∞ :=
  (algebraicOperator E sys T hintertwines).mkContinuous
    bound
    (algebraicOperator_norm_le E sys T hintertwines bound hnorm_le)

@[simp] theorem algebraicOperatorCLM_apply
    (hintertwines :
      ∀ {i j : I} (hij : i ≤ j) (x : E i),
        sys.map hij (T i x) = T j (sys.map hij x))
    (bound : ℝ)
    (hnorm_le : ∀ i (x : E i), ‖T i x‖ ≤ bound * ‖x‖)
    (z : D∞) :
    algebraicOperatorCLM E sys T hintertwines bound hnorm_le z =
      algebraicOperator E sys T hintertwines z :=
  rfl

/-- Continuous extension of the descended operator to the completed filtered
Hilbert colimit. -/
def completedOperator
    (hintertwines :
      ∀ {i j : I} (hij : i ≤ j) (x : E i),
        sys.map hij (T i x) = T j (sys.map hij x))
    (bound : ℝ)
    (hnorm_le : ∀ i (x : E i), ‖T i x‖ ≤ bound * ‖x‖) :
    H∞ →L[ℂ] H∞ :=
  (algebraicOperatorCLM E sys T hintertwines bound hnorm_le).completion

/-- On the dense algebraic carrier, the completed operator is exactly the
completion embedding of the descended operator. -/
theorem completedOperator_coe
    (hintertwines :
      ∀ {i j : I} (hij : i ≤ j) (x : E i),
        sys.map hij (T i x) = T j (sys.map hij x))
    (bound : ℝ)
    (hnorm_le : ∀ i (x : E i), ‖T i x‖ ≤ bound * ‖x‖)
    (z : D∞) :
    completedOperator E sys T hintertwines bound hnorm_le
        (directLimitToCompletion E sys z) =
      directLimitToCompletion E sys
        (algebraicOperator E sys T hintertwines z) := by
  apply UniformSpace.Completion.map_coe
  exact (algebraicOperatorCLM E sys T hintertwines bound hnorm_le).uniformContinuous

/-- The completed operator acts on every stage image by the corresponding
stage operator. -/
@[simp] theorem completedOperator_stage
    (hintertwines :
      ∀ {i j : I} (hij : i ≤ j) (x : E i),
        sys.map hij (T i x) = T j (sys.map hij x))
    (bound : ℝ)
    (hnorm_le : ∀ i (x : E i), ‖T i x‖ ≤ bound * ‖x‖)
    (i : I) (x : E i) :
    completedOperator E sys T hintertwines bound hnorm_le
        (stageToHilbertDirectLimit E sys i x) =
      stageToHilbertDirectLimit E sys i
        (T i x) := by
  rw [stageToHilbertDirectLimit_apply,
    stageToHilbertDirectLimit_apply,
    completedOperator_coe,
    algebraicOperator_of E sys T hintertwines]

end InfoGeometry.Canonical.FilteredCompatibleOperatorColimit
