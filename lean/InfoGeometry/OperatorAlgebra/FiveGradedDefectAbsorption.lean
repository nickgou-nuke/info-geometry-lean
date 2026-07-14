/-
InfoGeometry/OperatorAlgebra/FiveGradedDefectAbsorption.lean

Five-graded defect absorption and central/contact memory.

This module records the algebraic move from a three-graded TKK closure to a
five-graded or centrally extended closure.

Important correction:

In a genuine five-graded Lie algebra, `[g_i, g_j]` is routed by the grade sum.
Thus `[g_-1, g_+1]` still lands in `g_0`. The `g_+2` memory sector absorbs
defects through same-side brackets, contact terms, cocycles, or
representation-specific closure maps, not by violating the grading rule.

This file is an accounting socket. It does not prove a concrete `E7`, `E8`,
Virasoro, black-hole unitarity, Page-curve, or holographic-recovery theorem.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
import InfoGeometry.OperatorAlgebra.TKKConformalClosure
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace FiveGradedDefectAbsorption


open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure

/-! ## 1. Five-grade routing consequences -/

variable
    {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]

/--
Same positive-grade brackets land in the top contact/memory grade.

This reuses the repository's existing constructive five-grading socket from
`SuperTKKConformalClosure`.
-/
theorem plus_one_plus_one_mem_plus_two
    (G : FiveGrading L)
    {X Y : L}
    (hX : X ∈ G.gPosOne)
    (hY : Y ∈ G.gPosOne) :
    ⁅X, Y⁆ ∈ G.gPosTwo :=
  G.pos_one_pos_one_mem_pos_two hX hY

/--
Same negative-grade brackets land in the bottom contact/memory grade.
-/
theorem minus_one_minus_one_mem_minus_two
    (G : FiveGrading L)
    {X Y : L}
    (hX : X ∈ G.gNegOne)
    (hY : Y ∈ G.gNegOne) :
    ⁅X, Y⁆ ∈ G.gNegTwo :=
  G.neg_one_neg_one_mem_neg_two hX hY

/--
Opposite grade-one brackets still land in grade zero.
-/
theorem minus_one_plus_one_mem_zero
    (G : FiveGrading L)
    {X Y : L}
    (hX : X ∈ G.gNegOne)
    (hY : Y ∈ G.gPosOne) :
    ⁅X, Y⁆ ∈ G.gZero :=
  G.neg_one_pos_one_mem_zero hX hY

/-! ## 2. Three-grade defect absorbed by five-grade memory -/

/--
A representation-specific defect produced by trying to close a three-grade TKK
ledger.

`Defect` is intentionally separate from `L`: the defect may be scalar,
topological, analytic, or thermodynamic before it is absorbed into the extended
algebra.
-/
structure ThreeGradeClosureDefect
    (State Defect : Type*) where
  defect : State → Defect

namespace ThreeGradeClosureDefect

variable {State Defect : Type*}
variable (D : ThreeGradeClosureDefect State Defect)

/-- The closure-defect readout is the supplied defect function. -/
theorem defect_readout
    (s : State) :
    D.defect s = D.defect s :=
  rfl

end ThreeGradeClosureDefect

/--
Absorption of a three-grade closure defect into the positive grade-two
memory/contact sector of a five-graded algebra.
-/
structure DefectAbsorbedInPlusTwo
    (L State Defect : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Defect] [Module ℝ Defect]
    (G : FiveGrading L)
    (D : ThreeGradeClosureDefect State Defect) where
  /-- Linear embedding of defect values into the top grade. -/
  defectToPlusTwo : Defect →ₗ[ℝ] L

  /-- Defects land in `g_+2`. -/
  defect_mem_plus_two :
    ∀ s : State, defectToPlusTwo (D.defect s) ∈ G.gPosTwo

namespace DefectAbsorbedInPlusTwo

variable
    {State Defect : Type*}
    [AddCommGroup Defect] [Module ℝ Defect]
    {G : FiveGrading L}
    {D : ThreeGradeClosureDefect State Defect}

variable (A : DefectAbsorbedInPlusTwo L State Defect G D)

/-- The closure defect is stored in the top contact/memory grade. -/
theorem defect_is_plus_two_memory
    (s : State) :
    A.defectToPlusTwo (D.defect s) ∈ G.gPosTwo :=
  A.defect_mem_plus_two s

/--
The old TKK closure defect is represented by a top-grade element in the
extended algebra.
-/
theorem absorption
    (s : State) :
    A.defectToPlusTwo (D.defect s) ∈ G.gPosTwo :=
  A.defect_mem_plus_two s

end DefectAbsorbedInPlusTwo

/-! ## 3. TKK Ricci-flux defect absorption -/

/--
Absorption of the closure-defect component of a `TKKRicciFluxDatum` into
positive grade two.

This is weaker than the supercharge-square absorption in
`SuperTKKConformalClosure`: it only records a linear grade-two representative
and a geometric readout equation.
-/
structure TKKDefectAbsorbedInPlusTwo
    (L State Geometry : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    (R : InfoGeometry.OperatorAlgebra.TKKConformalClosure.TKKRicciFluxDatum L State Geometry)
    (G : FiveGrading L) where
  /-- Grade-two representative of the TKK closure defect. -/
  defectToPlusTwo : L → State → L

  /-- The representative lands in `g_+2`. -/
  defect_mem_plus_two :
    ∀ X : L, ∀ s : State, defectToPlusTwo X s ∈ G.gPosTwo

  /-- Readout from the extended algebra back to the geometry/flux codomain. -/
  plusTwoReadout : L → Geometry

  /-- The TKK closure defect is the readout of its grade-two representative. -/
  closureDefect_eq_plusTwoReadout :
    ∀ X : L, ∀ s : State,
      R.closureDefect.defect X s = plusTwoReadout (defectToPlusTwo X s)

namespace TKKDefectAbsorbedInPlusTwo

variable
    {State Geometry : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    {R : InfoGeometry.OperatorAlgebra.TKKConformalClosure.TKKRicciFluxDatum L State Geometry}
    {G : FiveGrading L}

variable (A : TKKDefectAbsorbedInPlusTwo L State Geometry R G)

/-- The TKK closure defect has a positive grade-two representative. -/
theorem defect_has_plus_two_representative
    (X : L)
    (s : State) :
    A.defectToPlusTwo X s ∈ G.gPosTwo :=
  A.defect_mem_plus_two X s

/-- The TKK closure defect is the geometry readout of its grade-two representative. -/
theorem closureDefect_eq_plusTwo
    (X : L)
    (s : State) :
    R.closureDefect.defect X s =
      A.plusTwoReadout (A.defectToPlusTwo X s) :=
  A.closureDefect_eq_plusTwoReadout X s

/--
If curvature is stationary, Ricci flux is the readout of the positive grade-two
representative.
-/
theorem ricciFlux_eq_plusTwoReadout_of_curvature_stationary
    (X : L)
    (s : State)
    (hstat :
      R.derivativeAlong.deriv R.curvatureReadout.curvature X s = 0) :
    R.ricciFlux X s =
      A.plusTwoReadout (A.defectToPlusTwo X s) := by
  rw [R.ricciFlux_def X s, hstat, zero_add]
  exact A.closureDefect_eq_plusTwo X s

end TKKDefectAbsorbedInPlusTwo

/-! ## 4. Black-hole information ledger socket -/

/--
A black-hole information ledger in a five-graded extension.

This does not prove unitary evaporation. It records the formal location of the
information that a three-grade observer sees as heat, entropy, or loss.
-/
structure BlackHoleFiveGradeLedger
    (L Visible Hidden Memory : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Memory] [Module ℝ Memory] where
  grading : FiveGrading L

  /-- Visible/local observable state embedded into the extended algebra. -/
  visibleState : Visible → L
  /-- Visible states are always grade-zero (local observer restriction). -/
  visible_mem_zero : ∀ v : Visible, visibleState v ∈ grading.gZero

  /-- Hidden/commutant state embedded into the extended algebra. -/
  hiddenState : Hidden → L

  /-- Memory/contact readout, morally carried by `g_+2`. -/
  memory : Visible → Memory

  /-- Embedding of memory into the five-graded algebra. -/
  memoryToPlusTwo : Memory →ₗ[ℝ] L

  /-- Memory lives in the `g_+2` sector. -/
  memory_mem_plus_two :
    ∀ v : Visible, memoryToPlusTwo (memory v) ∈ grading.gPosTwo

namespace BlackHoleFiveGradeLedger

variable
    {Visible Hidden Memory : Type*}
    [AddCommGroup Memory] [Module ℝ Memory]

variable (B : BlackHoleFiveGradeLedger L Visible Hidden Memory)

/-- Visible information assigned to memory is stored in the `g_+2` sector. -/
theorem memory_is_plus_two
    (v : Visible) :
    B.memoryToPlusTwo (B.memory v) ∈ B.grading.gPosTwo :=
  B.memory_mem_plus_two v

/-- Local observers do not see the full five-grade state. -/
theorem local_reduction
    (v : Visible) :
    B.visibleState v ∈ B.grading.gZero :=
  B.visible_mem_zero v

/-- The hidden/memory data are part of the enlarged algebraic state. -/
theorem full_ledger
    (v : Visible) :
    B.memoryToPlusTwo (B.memory v) ∈ B.grading.gPosTwo :=
  B.memory_mem_plus_two v

end BlackHoleFiveGradeLedger

/-! ## 5. Conserved information ledger -/

/--
A finite information ledger with a visible component and a grade-two reservoir.

This is the algebraic accounting shape of the black-hole sketch:

* a local/exterior observer reads `visible`;
* the five-grade ledger also carries `gradeTwo`;
* the full readout `total = visible + gradeTwo` is conserved.
-/
structure GradeTwoInformationLedger
    (State Info : Type*) [AddCommGroup Info] where
  total : State → Info
  visible : State → Info
  gradeTwo : State → Info

  /-- Total information decomposes into visible plus grade-two reservoir. -/
  total_eq_visible_plus_gradeTwo :
    ∀ s : State, total s = visible s + gradeTwo s

  /-- Evolution/flow of states. -/
  evolution : ℝ → State → State

  /-- The extended total information is conserved. -/
  total_conserved :
    ∀ t : ℝ, ∀ s : State, total (evolution t s) = total s

namespace GradeTwoInformationLedger

variable {State Info : Type*} [AddCommGroup Info]
variable (A : GradeTwoInformationLedger State Info)

/-- Local visible loss between a state and its evolution. -/
def visibleLoss
    (t : ℝ)
    (s : State) : Info :=
  A.visible s - A.visible (A.evolution t s)

/-- Grade-two gain between a state and its evolution. -/
def gradeTwoGain
    (t : ℝ)
    (s : State) : Info :=
  A.gradeTwo (A.evolution t s) - A.gradeTwo s

/--
Conservation theorem:

visible information lost by the three-graded/exterior observer is exactly
gained by the grade-two reservoir.
-/
theorem visibleLoss_eq_gradeTwoGain
    (t : ℝ)
    (s : State) :
    A.visibleLoss t s = A.gradeTwoGain t s := by
  dsimp [visibleLoss, gradeTwoGain]
  have h0 := A.total_eq_visible_plus_gradeTwo s
  have h1 := A.total_eq_visible_plus_gradeTwo (A.evolution t s)
  have hc := A.total_conserved t s
  have h :
      A.visible (A.evolution t s) +
          A.gradeTwo (A.evolution t s) =
        A.visible s + A.gradeTwo s := by
    rw [← h1, hc, h0]
  rw [sub_eq_sub_iff_add_eq_add]
  rw [add_comm (A.gradeTwo (A.evolution t s)) (A.visible (A.evolution t s))]
  exact h.symm

/-- The finite iterate of the supplied evolution map. -/
def stateAt
    (step : ℝ)
    (s : State) : ℕ → State
  | 0 => s
  | n + 1 => A.evolution step (stateAt step s n)

/-- Total information is conserved along every finite iterate. -/
theorem total_stateAt
    (step : ℝ)
    (s : State)
    (n : ℕ) :
    A.total (A.stateAt step s n) = A.total s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [stateAt]
      rw [A.total_conserved step (A.stateAt step s n), ih]

/--
Recursive compensation theorem: after any finite number of evolution steps,
visible loss equals grade-two reservoir gain.
-/
theorem recursive_visibleLoss_eq_gradeTwoGain
    (step : ℝ)
    (s : State)
    (n : ℕ) :
    A.visible s - A.visible (A.stateAt step s n) =
      A.gradeTwo (A.stateAt step s n) - A.gradeTwo s := by
  have h0 := A.total_eq_visible_plus_gradeTwo s
  have h1 := A.total_eq_visible_plus_gradeTwo (A.stateAt step s n)
  have hc := A.total_stateAt step s n
  have h :
      A.visible (A.stateAt step s n) + A.gradeTwo (A.stateAt step s n) =
        A.visible s + A.gradeTwo s := by
    rw [← h1, hc, h0]
  rw [sub_eq_sub_iff_add_eq_add]
  rw [add_comm (A.gradeTwo (A.stateAt step s n)) (A.visible (A.stateAt step s n))]
  exact h.symm

end GradeTwoInformationLedger

/-! ## 6. BPS/central-charge bound socket -/

/--
A BPS/central-charge bound.

This is the formal statement that a mass/energy readout is bounded below by a
central or grade-two charge readout.

The structure is intentionally scalar and witness-gated. A concrete
supergravity, Virasoro, or horizon model supplies the charge norm and the proof
of the inequality.
-/
structure BPSBoundDatum
    (State : Type*) where
  /-- Mass/energy readout. -/
  mass : State → ℝ

  /-- Central-charge or grade-two charge norm. -/
  centralNorm : State → ℝ

  /-- Positivity of the central/grade-two charge norm. -/
  centralNorm_nonneg :
    ∀ s : State, 0 ≤ centralNorm s

  /-- BPS inequality `|Z| ≤ M`, encoded by the supplied charge norm. -/
  bps_bound :
    ∀ s : State, centralNorm s ≤ mass s

/-- A state saturates the BPS bound. -/
def IsBPS
    {State : Type*}
    (B : BPSBoundDatum State)
    (s : State) : Prop :=
  B.mass s = B.centralNorm s

namespace BPSBoundDatum

variable {State : Type*}
variable (B : BPSBoundDatum State)

/-- The central/grade-two charge norm is nonnegative. -/
theorem centralNorm_nonnegative
    (s : State) :
    0 ≤ B.centralNorm s :=
  B.centralNorm_nonneg s

/-- The mass is bounded below by the central/grade-two charge norm. -/
theorem centralNorm_le_mass
    (s : State) :
    B.centralNorm s ≤ B.mass s :=
  B.bps_bound s

/-- A BPS state has mass equal to its central/grade-two charge norm. -/
theorem mass_eq_centralNorm_of_BPS
    {s : State}
    (h : IsBPS B s) :
    B.mass s = B.centralNorm s :=
  h

/-- A BPS state has nonnegative mass. -/
theorem mass_nonneg_of_BPS
    {s : State}
    (h : IsBPS B s) :
    0 ≤ B.mass s := by
  rw [h]
  exact B.centralNorm_nonnegative s

end BPSBoundDatum

/-! ## 7. Absorption readout -/

/--
Five-grade defect absorption readout.

Once a five-grade absorption witness is supplied, every old closure defect is
represented in the `g_+2` memory sector.
-/
theorem fiveGradeDefectAbsorptionOwnerTarget :
  ∀ (L State Defect : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Defect] [Module ℝ Defect],
  ∀ G : FiveGrading L,
  ∀ D : ThreeGradeClosureDefect State Defect,
  ∀ A : DefectAbsorbedInPlusTwo L State Defect G D,
  ∀ s : State,
    A.defectToPlusTwo (D.defect s) ∈ G.gPosTwo := by
  intro L State Defect _ _ _ _ _ _ G D A s
  exact A.defect_is_plus_two_memory s

/-- Packet readout for one five-grade defect absorption witness. -/
theorem fiveGradeDefectAbsorption_packet
    (L State Defect : Type*)
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Defect] [Module ℝ Defect]
    (G : FiveGrading L)
    (D : ThreeGradeClosureDefect State Defect)
    (A : DefectAbsorbedInPlusTwo L State Defect G D)
    (s : State) :
    A.defectToPlusTwo (D.defect s) ∈ G.gPosTwo :=
  fiveGradeDefectAbsorptionOwnerTarget L State Defect G D A s

/--
Owner target for installing a BPS/central-charge bound.
-/
def BPSBoundOwnerTarget
    (State : Type*) : Prop :=
  ∀ B : BPSBoundDatum State,
    (∀ s : State, 0 ≤ B.centralNorm s) ∧
      (∀ s : State, B.centralNorm s ≤ B.mass s)

/-- Installed BPS data satisfy the central-norm lower-bound target. -/
theorem bpsBoundOwnerTarget
    (State : Type*) :
    BPSBoundOwnerTarget State := by
  intro B
  exact ⟨B.centralNorm_nonnegative, B.centralNorm_le_mass⟩

end FiveGradedDefectAbsorption
