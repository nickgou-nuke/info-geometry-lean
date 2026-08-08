/-
InfoGeometry/Geometry/AnomalousErlangerHeight.lean

Anomalous Erlanger flow and Poincare height reconstruction.

This module formalizes the dictionary:

* inertial stage        = vanishing commutator / invariant frame;
* driven modular flow   = admissible deformation;
* curvature/shear       = nonzero commutator readout;
* anomaly residue       = projective obstruction;
* Poincare height       = positive scale reconstructed from anomaly data.

It does not prove GR, holography, or AdS/CFT.  It provides the property layer
where a concrete model may identify anomaly/capacity data with a geometric
height.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.OperatorAlgebra.ModularWeightTrace

noncomputable section

namespace InfoGeometry.Geometry.AnomalousErlangerHeight

open InfoGeometry.OperatorAlgebra
open scoped ENNReal

/-! ## 1. Algebraic shear / commutator -/

/-- Operator commutator. -/
def commutator
    {Op : Type*} [Ring Op]
    (E x : Op) : Op :=
  E * x - x * E

/--
An inertial operator stage.

`E` is the energy/modular generator candidate.

`observables` is the sector being tested.

The inertial condition is that `E` commutes with every observable in the chosen
sector.
-/
abbrev InertialStage
    (Op : Type*) [Ring Op] :=
  {p : Op × Set Op //
    ∀ x : Op, x ∈ p.2 → commutator p.1 x = 0}

namespace InertialStage

variable {Op : Type*} [Ring Op]
variable (I : InertialStage Op)

abbrev E : Op := I.1.1
abbrev observables : Set Op := I.1.2
abbrev inertial_commutes :
    ∀ x : Op, x ∈ I.observables → commutator I.E x = 0 := I.2

/-- Named form of the inertial commutator condition. -/
theorem commutator_eq_zero
    {x : Op}
    (hx : x ∈ I.observables) :
    commutator I.E x = 0 :=
  I.inertial_commutes x hx

end InertialStage

/-! ## 2. Driven modular/Erlanger flow -/

/--
A driven flow on an operator algebra.

This abstracts a modular/chemical-potential/curvature deformation.
-/
abbrev DrivenOperatorFlow
    (Op : Type*) [Ring Op] :=
  {f : ℝ → Op → Op //
    (∀ x : Op, f 0 x = x) ∧
      ∀ s t x, f (s + t) x = f s (f t x)}

namespace DrivenOperatorFlow

variable {Op : Type*} [Ring Op]

abbrev flow (F : DrivenOperatorFlow Op) : ℝ → Op → Op := F.1
abbrev flow_zero (F : DrivenOperatorFlow Op) : ∀ x : Op, F.flow 0 x = x := F.2.1
abbrev flow_add (F : DrivenOperatorFlow Op) :
    ∀ s t x, F.flow (s + t) x = F.flow s (F.flow t x) := F.2.2

end DrivenOperatorFlow

/--
Shear produced by applying the flow to an observable before taking the
commutator with the inertial generator.
-/
def drivenShear
    {Op : Type*} [Ring Op]
    (I : InertialStage Op)
    (F : DrivenOperatorFlow Op)
    (t : ℝ)
    (x : Op) : Op :=
  commutator I.E (F.flow t x)

/-- A state is sheared at time `t` when the driven commutator is nonzero. -/
def HasDrivenShear
    {Op : Type*} [Ring Op]
    (I : InertialStage Op)
    (F : DrivenOperatorFlow Op)
    (t : ℝ)
    (x : Op) : Prop :=
  drivenShear I F t x ≠ 0

/-! ## 3. Covariant curvature / metric readout -/

/--
A covariant readout of operator strain.

This is the Erlanger socket for quantities such as effective metric,
curvature, Einstein tensor, stress tensor, or anomaly current.
-/
structure CovariantReadout
    (G : Type*) (Op : Type*) [Group G] [Ring Op]
    (α : SymmetryAction G Op)
    (β : Type*) where
  read : Op → β

  targetAct : G → β → β

  covariance :
    ∀ g : G, ∀ x : Op,
      read (α.act g x) = targetAct g (read x)

/-- A curvature readout is a covariant readout applied to shear/commutator data. -/
structure CurvatureFromShear
    (G : Type*) (Op : Type*) [Group G] [Ring Op]
    (α : SymmetryAction G Op)
    (β : Type*) where
  readout : CovariantReadout G Op α β

  /-- Interprets a commutator/shear as curvature data. -/
  curvatureOf : Op → β

  /-- The curvature readout agrees with the covariant readout. -/
  curvature_eq_readout :
    ∀ shear : Op, curvatureOf shear = readout.read shear

/-! ## 4. Anomaly residue and height reconstruction -/

/--
A finite positive anomaly-height reconstruction datum.

`capacity` is the global scalar readout.  In a concrete model this may come
from an ordinary trace, a modular weight, a core trace, a Dixmier trace, a zeta
residue, or a cyclic cocycle.

`anomaly` is the local obstruction/residue.

`height` is the reconstructed positive Poincare/modular scale.

The primitive equation is

`height * anomaly = capacity 1`.
-/
abbrev FiniteAnomalyHeightDatum
    (Op : Type*) [Monoid Op] :=
  {p : (Op → ℝ) × (ℝ × ℝ) //
    0 < p.1 1 ∧
      0 < p.2.1 ∧
      p.2.2 * p.2.1 = p.1 1}

namespace FiniteAnomalyHeightDatum

variable {Op : Type*} [Monoid Op]
variable (H : FiniteAnomalyHeightDatum Op)

abbrev capacity : Op → ℝ := H.1.1
abbrev anomaly : ℝ := H.1.2.1
abbrev height : ℝ := H.1.2.2
abbrev capacity_pos : 0 < H.capacity 1 := H.2.1
abbrev anomaly_pos : 0 < H.anomaly := H.2.2.1
abbrev height_relation : H.height * H.anomaly = H.capacity 1 := H.2.2.2

/-- The reconstructed height is positive. -/
theorem height_pos :
    0 < H.height := by
  have hcap : 0 < H.height * H.anomaly := by
    rw [H.height_relation]
    exact H.capacity_pos
  have hcap' : 0 < H.anomaly * H.height := by
    simpa [mul_comm] using hcap
  exact pos_of_mul_pos_right hcap' (le_of_lt H.anomaly_pos)

/-- The height equals capacity divided by anomaly. -/
theorem height_eq_capacity_div_anomaly :
    H.height = H.capacity 1 / H.anomaly := by
  have hne : H.anomaly ≠ 0 := ne_of_gt H.anomaly_pos
  calc
    H.height = (H.height * H.anomaly) / H.anomaly := by
      rw [mul_div_cancel_right₀ H.height hne]
    _ = H.capacity 1 / H.anomaly := by
      rw [H.height_relation]

end FiniteAnomalyHeightDatum

/--
Extended-height datum allowing the flat/anomaly-zero branch.

Use this when the model wants to interpret `anomaly = 0` as an infinite or
boundary height.
-/
abbrev ExtendedAnomalyHeightDatum
    (Op : Type*) [Monoid Op] :=
  {p : (Op → ℝ≥0∞) × (ℝ≥0∞ × ℝ≥0∞) //
    p.2.2 * p.2.1 = p.1 1}

namespace ExtendedAnomalyHeightDatum

variable {Op : Type*} [Monoid Op]
variable (H : ExtendedAnomalyHeightDatum Op)

abbrev capacity : Op → ℝ≥0∞ := H.1.1
abbrev anomaly : ℝ≥0∞ := H.1.2.1
abbrev height : ℝ≥0∞ := H.1.2.2
abbrev height_relation : H.height * H.anomaly = H.capacity 1 := H.2

end ExtendedAnomalyHeightDatum

/-! ## 5. Anomaly as projective obstruction -/

/--
A protected anomaly/topological obstruction datum.

The grading or Clifford charge alone does not imply a nonzero anomaly.  This
structure records the model-specific theorem or property that an anomaly is
protected by a topological charge.
-/
abbrev ProtectedAnomalyDatum
    (State : Type*) :=
  {p : (State → ℝ) × (State → ℤ) //
    ∀ s : State,
      p.2 s ≠ 0 →
        p.1 s ≠ 0}

namespace ProtectedAnomalyDatum

variable {State : Type*}
variable (P : ProtectedAnomalyDatum State)

abbrev anomalyReadout : State → ℝ := P.1.1
abbrev topologicalCharge : State → ℤ := P.1.2
abbrev anomaly_protected_by_charge :
    ∀ s : State,
      P.topologicalCharge s ≠ 0 →
        P.anomalyReadout s ≠ 0 := P.2

end ProtectedAnomalyDatum

/--
A stabilization property for the “flat membrane snaps into tubule” mechanism.

This is intentionally model-level.  Clifford grading plus anomaly data do not
alone prove stability; a variational/energy property is required.
-/
structure AnomalousTubuleStabilizationWitness
    (State : Type*) where
  flatVacuum : State → Prop
  stableNonflat : State → Prop

  anomaly : State → ℝ
  topologicalCharge : State → ℤ
  energy : State → ℝ

  /-- Protected nonzero anomaly and charge force a stable non-flat solution. -/
  anomaly_charge_forces_stable_nonflat :
    ∀ s : State,
      anomaly s ≠ 0 →
      topologicalCharge s ≠ 0 →
        ∃ y : State, stableNonflat y

/-! ## 6. GR/Erlanger property layer -/

/--
An Erlanger-GR reconstruction property.

This says that effective geometric data are reconstructed from driven operator
shear and anomaly-height data.  It does not assert the Einstein equations as a
universal theorem.
-/
structure ErlangerGRReconstructionWitness
    (G : Type*) (Op : Type*) [Group G] [Ring Op]
    (α : SymmetryAction G Op)
    (Geometry : Type*) where
  inertial : InertialStage Op
  drivenFlow : DrivenOperatorFlow Op

  curvatureReadout :
    CurvatureFromShear G Op α Geometry

  /-- Model-specific effective geometry extracted from shear. -/
  effectiveGeometry :
    Op → Geometry

  effectiveGeometry_eq_curvature :
    ∀ shear : Op,
      effectiveGeometry shear =
        curvatureReadout.curvatureOf shear

  /-- Height/scale reconstructed from anomaly data. -/
  heightDatum :
    FiniteAnomalyHeightDatum Op

end InfoGeometry.Geometry.AnomalousErlangerHeight
