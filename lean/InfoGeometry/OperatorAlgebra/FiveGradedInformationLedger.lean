/-
InfoGeometry/OperatorAlgebra/FiveGradedInformationLedger.lean

Projected information accounting identity and five-grade memory ledger sockets.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

variable
    {J L Obs : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]

/--
Projected information accounting identity.

If the observed cross term is the observation of the visible Lie bracket plus
two hidden memory terms, then the observed defect is exactly the observation
of the hidden total.
-/
theorem observedDefect_eq_obs_hidden_of_cross_identity
    (neg pos : J →ₗ[ℝ] L)
    (hiddenNegTwo hiddenPosTwo : J → J → L)
    (obs : L →ₗ[ℝ] Obs)
    (observedCross : J → J → Obs)
    (hcross :
      ∀ x y : J,
        observedCross x y =
          obs (⁅neg x, pos y⁆ + hiddenNegTwo x y + hiddenPosTwo x y))
    (x y : J) :
    observedCross x y - obs ⁅neg x, pos y⁆ =
      obs (hiddenNegTwo x y + hiddenPosTwo x y) := by
  let br : L := ⁅neg x, pos y⁆
  let hn : L := hiddenNegTwo x y
  let hp : L := hiddenPosTwo x y
  change observedCross x y - obs br = obs (hn + hp)
  rw [hcross x y]
  change obs (br + hn + hp) - obs br = obs (hn + hp)
  have hassoc : br + hn + hp = br + (hn + hp) := by
    abel
  rw [hassoc, map_add]
  abel

/-- Five-graded Lie-algebra carrier used by horizon/ledger sockets. -/
structure FiveGrading
    (L : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L] where
  gNegTwo : Submodule ℝ L
  gNegOne : Submodule ℝ L
  gZero : Submodule ℝ L
  gPosOne : Submodule ℝ L
  gPosTwo : Submodule ℝ L
  negOne_posOne_mem_zero :
    ∀ {X Y : L}, X ∈ gNegOne → Y ∈ gPosOne → ⁅X, Y⁆ ∈ gZero
  bracket_negTwo_posTwo :
    ∀ X Y : L, X ∈ gNegTwo → Y ∈ gPosTwo → ⁅X, Y⁆ ∈ gZero
  posOne_posOne_mem_posTwo :
    ∀ {X Y : L}, X ∈ gPosOne → Y ∈ gPosOne → ⁅X, Y⁆ ∈ gPosTwo
  negOne_negOne_mem_negTwo :
    ∀ {X Y : L}, X ∈ gNegOne → Y ∈ gNegOne → ⁅X, Y⁆ ∈ gNegTwo

namespace FiveGrading

variable {L : Type*}
variable [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]

variable (G : FiveGrading L)

/-- The concrete graded-bracket laws carried by `FiveGrading`. -/
def bracket_graded : Prop :=
  (∀ {X Y : L}, X ∈ G.gNegOne → Y ∈ G.gPosOne → ⁅X, Y⁆ ∈ G.gZero) ∧
  (∀ X Y : L, X ∈ G.gNegTwo → Y ∈ G.gPosTwo → ⁅X, Y⁆ ∈ G.gZero) ∧
  (∀ {X Y : L}, X ∈ G.gPosOne → Y ∈ G.gPosOne → ⁅X, Y⁆ ∈ G.gPosTwo) ∧
  (∀ {X Y : L}, X ∈ G.gNegOne → Y ∈ G.gNegOne → ⁅X, Y⁆ ∈ G.gNegTwo)

theorem bracket_graded_holds :
    G.bracket_graded :=
  ⟨@G.negOne_posOne_mem_zero, G.bracket_negTwo_posTwo,
    @G.posOne_posOne_mem_posTwo, @G.negOne_negOne_mem_negTwo⟩

/-- Backward-compatible mixed-grade bracket witness name. -/
theorem bracket_negOne_posOne_mem_zero
    {X Y : L}
    (hX : X ∈ G.gNegOne)
    (hY : Y ∈ G.gPosOne) :
    ⁅X, Y⁆ ∈ G.gZero :=
  G.negOne_posOne_mem_zero hX hY

end FiveGrading

/--
Projected accounting packet over a five-grading.
-/
structure FiveGradeProjectedAccounting
    (J L Obs : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    (G : FiveGrading L) where
  neg : J →ₗ[ℝ] L
  pos : J →ₗ[ℝ] L
  obs : L →ₗ[ℝ] Obs
  hiddenNegTwo : J → J → L
  hiddenPosTwo : J → J → L
  observedCross : J → J → Obs
  neg_mem : ∀ x : J, neg x ∈ G.gNegOne
  pos_mem : ∀ y : J, pos y ∈ G.gPosOne
  hiddenNegTwo_mem : ∀ x y : J, hiddenNegTwo x y ∈ G.gNegTwo
  hiddenPosTwo_mem : ∀ x y : J, hiddenPosTwo x y ∈ G.gPosTwo
  cross_identity :
    ∀ x y : J,
      observedCross x y =
        obs (⁅neg x, pos y⁆ + hiddenNegTwo x y + hiddenPosTwo x y)

namespace FiveGradeProjectedAccounting

variable
    {J L Obs : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    {G : FiveGrading L}

/-- Hidden grade-two total (`g₋₂ ⊕ g₊₂`) for the label pair `(x,y)`. -/
def hiddenTotal
    (A : FiveGradeProjectedAccounting J L Obs G)
    (x y : J) : L :=
  A.hiddenNegTwo x y + A.hiddenPosTwo x y

/-- Observed defect: observed cross minus visible bracket projection. -/
def observedDefect
    (A : FiveGradeProjectedAccounting J L Obs G)
    (x y : J) : Obs :=
  A.observedCross x y - A.obs ⁅A.neg x, A.pos y⁆

variable (A : FiveGradeProjectedAccounting J L Obs G)

/-- `observed defect = obs(hidden total)`. -/
theorem observedDefect_eq_obs_hidden
    (x y : J) :
    A.observedDefect x y = A.obs (A.hiddenTotal x y) := by
  unfold observedDefect hiddenTotal
  exact observedDefect_eq_obs_hidden_of_cross_identity
    A.neg A.pos A.hiddenNegTwo A.hiddenPosTwo A.obs A.observedCross A.cross_identity x y

/-- If hidden total is invisible under `obs`, then observed defect is zero. -/
theorem observedDefect_eq_zero_of_hidden_invisible
    (x y : J)
    (h : A.obs (A.hiddenTotal x y) = 0) :
    A.observedDefect x y = 0 := by
  rw [A.observedDefect_eq_obs_hidden x y, h]

/-- Nonzero hidden projection implies nonzero observed defect. -/
theorem observedDefect_ne_zero_of_obs_hidden_ne_zero
    (x y : J)
    (h : A.obs (A.hiddenTotal x y) ≠ 0) :
    A.observedDefect x y ≠ 0 := by
  rw [A.observedDefect_eq_obs_hidden x y]
  exact h

/-- Nonzero observed defect iff nonzero hidden projection. -/
theorem observed_defect_ne_zero_iff_obs_hidden_ne_zero
    (x y : J) :
    A.observedDefect x y ≠ 0 ↔ A.obs (A.hiddenTotal x y) ≠ 0 := by
  rw [A.observedDefect_eq_obs_hidden x y]

/-- The visible bracket term lies in grade zero. -/
theorem true_bracket_mem_zero
    (x y : J) :
    ⁅A.neg x, A.pos y⁆ ∈ G.gZero :=
  G.negOne_posOne_mem_zero (A.neg_mem x) (A.pos_mem y)

end FiveGradeProjectedAccounting

/--
Five-grade black-hole information ledger socket.
-/
structure BlackHoleInformationLedger
    (J L Obs Memory : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    (A : FiveGradeProjectedAccounting J L Obs G) where
  memoryReadout : L → Memory
  hidden_part_stored_as_memory :
    ∀ x y : J, memoryReadout (A.hiddenTotal x y) ≠ 0 → A.hiddenTotal x y ≠ 0

namespace BlackHoleInformationLedger

variable
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}

variable (B : BlackHoleInformationLedger J L Obs Memory A)

/-- Hidden grade-two sum exposed through the ledger API. -/
def hiddenGradeTwoSum
    (_B : BlackHoleInformationLedger J L Obs Memory A)
    (x y : J) : L :=
  A.hiddenTotal x y

/-- Visible projection of hidden grade-two memory. -/
def visibleHiddenProjection
    (B : BlackHoleInformationLedger J L Obs Memory A)
    (x y : J) : Obs :=
  A.obs (B.hiddenGradeTwoSum x y)

/-- Re-export of ledger nontrivial-memory implies nontrivial-hidden witness. -/
theorem hiddenGradeTwoSum_ne_zero_of_memoryReadout_ne_zero
    (x y : J)
    (hmem : B.memoryReadout (B.hiddenGradeTwoSum x y) ≠ 0) :
    B.hiddenGradeTwoSum x y ≠ 0 :=
  B.hidden_part_stored_as_memory x y hmem

/-- Observed defect equals visible projection of hidden grade-two memory. -/
theorem observedDefect_eq_visibleHiddenProjection
    (x y : J) :
    A.observedDefect x y = B.visibleHiddenProjection x y := by
  unfold visibleHiddenProjection hiddenGradeTwoSum
  exact A.observedDefect_eq_obs_hidden x y

/-- Nonzero observed defect iff nonzero visible hidden projection. -/
theorem observedDefect_ne_zero_iff_visibleHidden_ne_zero
    (x y : J) :
    A.observedDefect x y ≠ 0 ↔ B.visibleHiddenProjection x y ≠ 0 := by
  rw [B.observedDefect_eq_visibleHiddenProjection x y]

end BlackHoleInformationLedger

end InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
