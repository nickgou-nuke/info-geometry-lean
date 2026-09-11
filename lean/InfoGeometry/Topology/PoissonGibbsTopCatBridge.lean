import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.PoissonGibbsTopological

/-!
# TopCat bridge for finite Poisson Gibbs weights

The finite Poisson/Sinkhorn owners already prove positivity, normalization,
and continuity.  This file supplies only their categorical topological
readout; it does not add a convergence or projection theorem.
-/

namespace InfoGeometry.Topology.PoissonGibbsTopCatBridge

noncomputable section

open InfoGeometry.Inference

variable {Data : Type*} {Theta : Type} [Fintype Data] [Nonempty Data]
  [TopologicalSpace Theta]

def poissonWeightTopCatHom
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (i : Data) :
    TopCat.of (Theta × NonzeroTemperature) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun p => poissonWeight M p.1 p.2.1 i
      continuous_toFun := continuous_poissonWeight M hmean i }

@[simp] theorem poissonWeightTopCatHom_apply
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (i : Data) (p : Theta × NonzeroTemperature) :
    poissonWeightTopCatHom M hmean i p = poissonWeight M p.1 p.2.1 i :=
  rfl

theorem poissonWeightTopCatHom_nonnegative
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (i : Data) (p : Theta × NonzeroTemperature) :
    0 ≤ poissonWeightTopCatHom M hmean i p := by
  exact (poissonWeight_pos M p.1 p.2.1 i).le

theorem poissonWeightTopCatHom_sum_one
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (p : Theta × NonzeroTemperature) :
    ∑ i : Data, poissonWeightTopCatHom M hmean i p = 1 := by
  simpa only [poissonWeightTopCatHom_apply] using
    (poissonWeights_sum_one M p.1 p.2.1)

def poissonPartitionFunctionTopCatHom
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ)) :
    TopCat.of (Theta × NonzeroTemperature) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun p => FiniteGibbs.partitionFunction M.gibbsModel p.1 p.2.1
      continuous_toFun := continuous_poissonPartitionFunction M hmean }

@[simp] theorem poissonPartitionFunctionTopCatHom_apply
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (p : Theta × NonzeroTemperature) :
    poissonPartitionFunctionTopCatHom M hmean p =
      FiniteGibbs.partitionFunction M.gibbsModel p.1 p.2.1 :=
  rfl

def poissonFreeEnergyTopCatHom
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ)) :
    TopCat.of (Theta × NonzeroTemperature) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun p => FiniteGibbs.freeEnergy M.gibbsModel p.1 p.2.1
      continuous_toFun := continuous_poissonFreeEnergy M hmean }

@[simp] theorem poissonFreeEnergyTopCatHom_apply
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (p : Theta × NonzeroTemperature) :
    poissonFreeEnergyTopCatHom M hmean p =
      FiniteGibbs.freeEnergy M.gibbsModel p.1 p.2.1 :=
  rfl

end
end InfoGeometry.Topology.PoissonGibbsTopCatBridge
