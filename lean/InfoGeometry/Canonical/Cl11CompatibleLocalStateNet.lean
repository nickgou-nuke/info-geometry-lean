import InfoGeometry.Clifford.Cl11MarkovJonesEngine
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RelativeModularCenteredFunctional

set_option autoImplicit false

/-!
# InfoGeometry.Canonical.Cl11CompatibleLocalStateNet

Concrete bridge from the executable `Cl(1,1)` binary matrix tower to the local
compatible-state-net interface.

This file packages only finite-stage algebra already present in the concrete
matrix tower:

- the stages are `Cl11TensorTower.MatStage n`;
- the state at stage `n` is the normalized trace;
- the one-step inductive algebra net is the existing `Cl11MarkovJonesEngine`
  embedding `A ↦ A ⊗ I₂`;
- the restriction map is the diagonal-block average, which is a genuine left
  inverse to the embedding and is exactly compatible with the normalized trace.

No completion, factor classification, Fuglede--Kadison theorem, or Virasoro
limit theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11CompatibleLocalStateNet

open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Canonical.RelativeModularCenteredFunctional

/--
Diagonal-block average from stage `n+1` back to stage `n`.

For a matrix on `(Idx n × Fin 2) × (Idx n × Fin 2)`, keep the two diagonal
`Idx n × Idx n` blocks and average them.
-/
def stageRestrict (n : ℕ) : MatStage (n + 1) →ₗ[ℝ] MatStage n where
  toFun X := fun i j => (X (i, 0) (j, 0) + X (i, 1) (j, 1)) / 2
  map_add' := by
    intro X Y
    ext i j
    simp [div_eq_mul_inv, add_mul]
    ring
  map_smul' := by
    intro c X
    ext i j
    simp [div_eq_mul_inv, add_mul, mul_assoc]
    ring

@[simp] theorem stageRestrict_apply (n : ℕ) (X : MatStage (n + 1))
    (i j : InfoGeometry.Clifford.TowerMatrix.Idx n) :
    stageRestrict n X i j = (X (i, 0) (j, 0) + X (i, 1) (j, 1)) / 2 :=
  rfl

/-- The diagonal-block restriction is a left inverse to `A ↦ A ⊗ I₂`. -/
@[simp] theorem stageRestrict_stageEmbed (n : ℕ) (A : MatStage n) :
    stageRestrict n (stageEmbed n A) = A := by
  ext i j
  simp [stageRestrict, stageEmbed_apply, matStageEmbed]

/-- Trace readback of the diagonal-block restriction. -/
theorem trace_stageRestrict (n : ℕ) (X : MatStage (n + 1)) :
    Matrix.trace (stageRestrict n X) = Matrix.trace X / 2 := by
  classical
  unfold Matrix.trace stageRestrict
  simp [div_eq_mul_inv]
  calc
    (∑ x : InfoGeometry.Clifford.TowerMatrix.Idx n,
        (X (x, 0) (x, 0) + X (x, 1) (x, 1)) * ((2 : ℝ)⁻¹)) =
        ((∑ x : InfoGeometry.Clifford.TowerMatrix.Idx n, X (x, 0) (x, 0)) +
          (∑ x : InfoGeometry.Clifford.TowerMatrix.Idx n, X (x, 1) (x, 1))) * ((2 : ℝ)⁻¹) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    _ = (∑ x : InfoGeometry.Clifford.TowerMatrix.Idx (n + 1), X x x) * ((2 : ℝ)⁻¹) := by
      congr 1
      symm
      change (∑ x : InfoGeometry.Clifford.TowerMatrix.Idx n × Fin 2, X x x) =
        (∑ x : InfoGeometry.Clifford.TowerMatrix.Idx n, X (x, 0) (x, 0)) +
          (∑ x : InfoGeometry.Clifford.TowerMatrix.Idx n, X (x, 1) (x, 1))
      rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro x hx
      simp

/-- The normalized trace is exactly compatible with the diagonal-block restriction. -/
@[simp] theorem normalizedTrace_stageRestrict (n : ℕ) (X : MatStage (n + 1)) :
    normalizedTrace n (stageRestrict n X) = normalizedTrace (n + 1) X := by
  unfold normalizedTrace
  rw [trace_stageRestrict, pow_succ]
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]

/--
The concrete `Cl(1,1)` matrix tower viewed as a compatible local state net,
with state given by the normalized trace and restriction given by the
block-average left inverse.
-/
def cl11CompatibleLocalStateNet : CompatibleLocalStateNet (A := MatStage) where
  ring_A _ := inferInstance
  algebra_A _ := inferInstance
  state := normalizedTraceLinear
  restrict := stageRestrict
  compatible := by
    intro n a
    symm
    exact normalizedTrace_stageRestrict n a

/-- The state field of the compatible net is definitionally the packaged Markov trace. -/
@[simp] theorem cl11CompatibleLocalStateNet_state_eq_markovTrace (n : ℕ) (A : MatStage n) :
    cl11CompatibleLocalStateNet.state n A = cl11MarkovTraceNet.trace n A := by
  rfl

/-- The restriction field of the compatible net is the diagonal-block average. -/
@[simp] theorem cl11CompatibleLocalStateNet_restrict_eq (n : ℕ) :
    cl11CompatibleLocalStateNet.restrict n = stageRestrict n :=
  rfl

/-- The compatible-net restriction is a left inverse to the inductive embedding. -/
@[simp] theorem cl11CompatibleLocalStateNet_restrict_embed (n : ℕ) (A : MatStage n) :
    cl11CompatibleLocalStateNet.restrict n (cl11InductiveAlgebraNet.embed n A) = A := by
  simpa [cl11CompatibleLocalStateNet] using stageRestrict_stageEmbed n A

/-- The compatible net and the inductive Markov net agree on one-step embedding readback. -/
@[simp] theorem cl11CompatibleLocalStateNet_state_embed
    (n : ℕ) (A : MatStage n) :
    cl11CompatibleLocalStateNet.state (n + 1) (cl11InductiveAlgebraNet.embed n A) =
      cl11CompatibleLocalStateNet.state n A := by
  simpa [cl11CompatibleLocalStateNet] using cl11_normalizedTrace_one_step n A

/-- The compatible net inherits finite stability along every iterated embedding. -/
theorem cl11CompatibleLocalStateNet_state_embedMap
    (m n : ℕ) (h : m ≤ n) (A : MatStage m) :
    cl11CompatibleLocalStateNet.state n (cl11InductiveAlgebraNet.embedMap m n h A) =
      cl11CompatibleLocalStateNet.state m A := by
  simpa [cl11CompatibleLocalStateNet] using cl11_normalizedTrace_stable_embedMap m n h A

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
- `stageRestrict_stageEmbed`
- `trace_stageRestrict`
- `normalizedTrace_stageRestrict`
- `cl11CompatibleLocalStateNet`
- `cl11CompatibleLocalStateNet_restrict_embed`
- `cl11CompatibleLocalStateNet_state_embed`
- `cl11CompatibleLocalStateNet_state_embedMap`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- none

#### BUCKET 3: OPEN CLOSURE DEBT
- no completion theorem
- no factor classification theorem
- no Fuglede--Kadison theorem
- no Virasoro-limit theorem asserted in this module
-/

end InfoGeometry.Canonical.Cl11CompatibleLocalStateNet
