/-
InfoGeometry/Geometry/AnomalousErlangerHeight.lean

Anomalous Erlanger flow and Poincare height reconstruction.

This module formalizes the dictionary:

* inertial stage        = vanishing commutator / invariant frame;
* driven modular flow   = admissible deformation;
* curvature/shear       = nonzero commutator readout;
* anomaly residue       = projective obstruction;
* Poincare height       = positive scale reconstructed from anomaly data.

It does not prove GR, holography, or AdS/CFT.  It provides the witness layer
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
structure InertialStage
    (Op : Type*) [Ring Op] where
  E : Op
  observables : Set Op

  inertial_commutes :
    ∀ x : Op, x ∈ observables → commutator E x = 0

namespace InertialStage

variable {Op : Type*} [Ring Op]
variable (I : InertialStage Op)

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
structure DrivenOperatorFlow
    (Op : Type*) [Ring Op] where
  flow : ℝ → Op → Op

  flow_zero :
    ∀ x : Op, flow 0 x = x

  flow_add :
    ∀ s t x, flow (s + t) x = flow s (flow t x)

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
structure FiniteAnomalyHeightDatum
    (Op : Type*) [Monoid Op] where
  capacity : Op → ℝ
  anomaly : ℝ
  height : ℝ

  capacity_pos :
    0 < capacity 1

  anomaly_pos :
    0 < anomaly

  height_relation :
    height * anomaly = capacity 1

namespace FiniteAnomalyHeightDatum

variable {Op : Type*} [Monoid Op]
variable (H : FiniteAnomalyHeightDatum Op)

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
structure ExtendedAnomalyHeightDatum
    (Op : Type*) [Monoid Op] where
  capacity : Op → ℝ≥0∞
  anomaly : ℝ≥0∞
  height : ℝ≥0∞

  /-- Reconstruction law in extended nonnegative scalars. -/
  height_relation :
    height * anomaly = capacity 1

/-! ## 5. Anomaly as projective obstruction -/

/--
A protected anomaly/topological obstruction datum.

The grading or Clifford charge alone does not imply a nonzero anomaly.  This
structure records the model-specific theorem or hypothesis that an anomaly is
protected by a topological charge.
-/
structure ProtectedAnomalyDatum
    (State : Type*) where
  anomalyReadout : State → ℝ
  topologicalCharge : State → ℤ

  anomaly_protected_by_charge :
    ∀ s : State,
      topologicalCharge s ≠ 0 →
        anomalyReadout s ≠ 0

/--
A stabilization witness for the “flat membrane snaps into tubule” mechanism.

This is intentionally model-level.  Clifford grading plus anomaly data do not
alone prove stability; a variational/energy certificate is required.
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

/-! ## 6. GR/Erlanger witness layer -/

/--
An Erlanger-GR reconstruction witness.

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
