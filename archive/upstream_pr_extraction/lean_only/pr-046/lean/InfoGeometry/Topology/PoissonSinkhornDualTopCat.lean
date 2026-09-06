import Mathlib
import InfoGeometry.Inference.PoissonSinkhornPotentials
import InfoGeometry.Inference.PoissonBregmanTopological

/-!
# Topological dual-potential readouts for finite Poisson Sinkhorn

The finite dual objective is exposed as a continuous `TopCat` morphism on the
strictly positive-temperature and potential parameter space.  Its additive
potential gauge invariance is inherited from the native finite theorem.
-/

open scoped BigOperators

namespace InfoGeometry.Topology.PoissonSinkhornDualTopCat

open CategoryTheory
open InfoGeometry.Inference

variable {n : Nat} [Nonempty (Fin n)]

abbrev DualParameter (n : Nat) :=
  PositiveReal × (Fin n → ℝ) × (Fin n → ℝ)

noncomputable def dualObjectiveReadout
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)) :
    DualParameter n → ℝ :=
  fun p => poissonSinkhornDualObjective C p.1.1 p.2.1 p.2.2

theorem continuous_dualObjectiveReadout
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)) :
    Continuous (dualObjectiveReadout C) := by
  unfold dualObjectiveReadout poissonSinkhornDualObjective
  have heps : Continuous (fun p : DualParameter n => p.1.1) := by
    fun_prop
  have hα (i : Fin n) :
      Continuous (fun p : DualParameter n => p.2.1 i) := by
    fun_prop
  have hβ (j : Fin n) :
      Continuous (fun p : DualParameter n => p.2.2 j) := by
    fun_prop
  have hαsum : Continuous (fun p : DualParameter n =>
      ∑ i : Fin n, p.2.1 i) := by
    apply continuous_finset_sum
    intro i hi
    exact hα i
  have hβsum : Continuous (fun p : DualParameter n =>
      ∑ j : Fin n, p.2.2 j) := by
    apply continuous_finset_sum
    intro j hj
    exact hβ j
  have hkernel : Continuous (fun p : DualParameter n =>
      ∑ i : Fin n, ∑ j : Fin n,
        Real.exp ((p.2.1 i + p.2.2 j - C.cost i j) / p.1.1)) := by
    apply continuous_finset_sum
    intro i hi
    apply continuous_finset_sum
    intro j hj
    have harg : Continuous (fun p : DualParameter n =>
        (p.2.1 i + p.2.2 j - C.cost i j) / p.1.1) := by
      exact ((hα i).add (hβ j)).sub continuous_const |>.div heps
        (fun p => p.1.property.ne')
    exact Real.continuous_exp.comp harg
  exact ((hαsum.add hβsum).sub (heps.mul hkernel)).add
    (heps.mul continuous_const)

noncomputable def dualObjectiveTopCatHom
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)) :
    TopCat.of (DualParameter n) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := dualObjectiveReadout C
      continuous_toFun := continuous_dualObjectiveReadout C }

theorem dualObjectiveTopCatHom_apply
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (p : DualParameter n) :
    dualObjectiveTopCatHom C p = dualObjectiveReadout C p :=
  rfl

theorem dualObjectiveReadout_gauge_invariant
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : PositiveReal) (t : ℝ) (α β : Fin n → ℝ) :
    dualObjectiveReadout C
        (ε, (fun i => α i + t), (fun j => β j - t)) =
      dualObjectiveReadout C (ε, α, β) := by
  unfold dualObjectiveReadout
  exact poissonSinkhornDualObjective_gauge_invariant C (ε : ℝ) t α β

theorem dualObjectiveTopCatHom_gauge_invariant
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : PositiveReal) (t : ℝ) (α β : Fin n → ℝ) :
    dualObjectiveTopCatHom C
        (ε, (fun i => α i + t), (fun j => β j - t)) =
      dualObjectiveTopCatHom C (ε, α, β) := by
  rw [dualObjectiveTopCatHom_apply, dualObjectiveTopCatHom_apply]
  exact dualObjectiveReadout_gauge_invariant C ε t α β

end InfoGeometry.Topology.PoissonSinkhornDualTopCat
