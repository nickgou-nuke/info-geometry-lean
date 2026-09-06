import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Meta.MarkovJonesInduction

/-!
# InfoGeometry.Clifford.Cl11MarkovJonesEngine

Finite Markov/Jones readout for the concrete `Cl(1,1)` matrix tensor tower.

This module connects existing owner surfaces:

* `Cl11TensorTower.stageEmbed` is the concrete one-step embedding
  `A ↦ A ⊗ I₂` on the binary matrix tower;
* `Cl11TensorTower.normalizedTrace` is packaged as a finite Markov trace net;
* the normalized trace is stable under every finite iterated embedding;
* the determinant lane remains the existing normalized log-absolute-determinant
  readout, stable one step under `A ↦ A ⊗ I₂`.

No infinite matrix is constructed here.  No Type II₁/Type III factor existence,
Fuglede--Kadison determinant theorem, or Jordan--Wigner/CAR completion is
asserted here.  Existing Super-Virasoro finite-window/limit closure theorems live
in the canonical Super-Virasoro modules; this file only packages the finite
Markov/Jones trace-determinant side of the engine.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11MarkovJonesEngine

open Matrix
open InfoGeometry.Clifford.Cl11TensorTower

/-- Cardinality of the binary matrix-tower index set. -/
theorem card_tower_idx (n : ℕ) :
    Fintype.card (InfoGeometry.Clifford.TowerMatrix.Idx n) = 2 ^ n :=
  InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two n

/-- Trace of the identity at binary depth `n`. -/
theorem trace_one_matStage (n : ℕ) :
    Matrix.trace (1 : MatStage n) = (2 : ℝ) ^ n := by
  rw [Matrix.trace_one]
  norm_num [card_tower_idx n]

/-- The concrete `Cl(1,1)` matrix tower as a finite algebraic inductive net. -/
def cl11InductiveAlgebraNet :
    InfoGeometry.Meta.MarkovJonesInduction.InductiveAlgebraNet
      (𝕜 := ℝ) (A := MatStage) :=
  stageEmbed

/-- Binary-volume normalized trace as a linear map at stage `n`. -/
def normalizedTraceLinear (n : ℕ) : MatStage n →ₗ[ℝ] ℝ where
  toFun := normalizedTrace n
  map_add' := by
    intro A B
    unfold normalizedTrace
    rw [Matrix.trace_add]
    ring
  map_smul' := by
    intro c A
    unfold normalizedTrace
    rw [Matrix.trace_smul]
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- The concrete normalized trace is a finite Markov trace net on the tower. -/
def cl11MarkovTraceNet :
    InfoGeometry.Meta.MarkovJonesInduction.MarkovTraceNet
      (𝕜 := ℝ) (A := MatStage) cl11InductiveAlgebraNet where
  trace := normalizedTraceLinear
  trace_one := by
    intro n
    change normalizedTrace n (1 : MatStage n) = 1
    unfold normalizedTrace
    rw [trace_one_matStage]
    field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]
  trace_stable := by
    intro n A
    change normalizedTrace (n + 1) (stageEmbed n A) = normalizedTrace n A
    exact normalizedTrace_matStageEmbed n A

/-- The packaged Markov trace agrees definitionally with `normalizedTrace`. -/
theorem cl11MarkovTraceNet_apply (n : ℕ) (A : MatStage n) :
    cl11MarkovTraceNet.trace n A = normalizedTrace n A :=
  rfl

/-- Concrete one-step finite Markov stability. -/
theorem cl11_normalizedTrace_one_step (n : ℕ) (A : MatStage n) :
    cl11MarkovTraceNet.trace (n + 1) (cl11InductiveAlgebraNet.embed n A) =
      cl11MarkovTraceNet.trace n A :=
  cl11MarkovTraceNet.stable_one_step n A

/-- Concrete finite Markov stability along every iterated embedding. -/
theorem cl11_normalizedTrace_stable_embedMap
    (m n : ℕ) (h : m ≤ n) (A : MatStage m) :
    cl11MarkovTraceNet.trace n (cl11InductiveAlgebraNet.embedMap m n h A) =
      cl11MarkovTraceNet.trace m A :=
  cl11MarkovTraceNet.stable_embedMap m n h A

/-- Raw determinant squares under the concrete one-step binary embedding. -/
theorem cl11_rawDet_one_step_square (n : ℕ) (A : MatStage n) :
    Matrix.det (matStageEmbed n A) = Matrix.det A ^ (2 : ℕ) :=
  matStageEmbed_det n A

/-- Normalized log-absolute-determinant is stable under one finite embedding. -/
theorem cl11_normalizedLogAbsDet_one_step (n : ℕ) (A : MatStage n) :
    normalizedLogAbsDet (n + 1) (matStageEmbed n A) = normalizedLogAbsDet n A :=
  normalizedLogAbsDet_matStageEmbed n A

/-!
Closed finite facts in this file:

* the concrete binary matrix tower is an `InductiveAlgebraNet`;
* normalized trace is a finite Markov trace net;
* normalized trace is stable along all finite iterated embeddings;
* raw determinant squares under one-step embedding;
* normalized log-absolute-determinant is stable under one-step embedding.

Open closure debt, deliberately not encoded as declarations:

* a completed CAR/Jordan--Wigner inductive-limit algebra;
* a hyperfinite Type II₁ factor or Type III factor construction;
* a Fuglede--Kadison determinant theorem;
* composing this Markov/Jones package with the existing Super-Virasoro
  finite-window/limit closure theorems.
-/

end InfoGeometry.Clifford.Cl11MarkovJonesEngine
