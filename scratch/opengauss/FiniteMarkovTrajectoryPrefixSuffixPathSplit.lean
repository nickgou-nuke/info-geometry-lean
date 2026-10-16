/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Prefix/suffix factorization of successor paths

This scratch theorem applies Mathlib's product factorization of `partialTraj`
to a fixed history. It identifies the full successor-path law with the law
of its suffix block, prefixed by the known endpoint. This keeps the complete
prefix/suffix law, rather than relying only on endpoint marginals.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryPrefixSuffixPathSplit

open MeasureTheory ProbabilityTheory Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance
local instance (n : ℕ) : MeasurableSpace (Fin n → ι) := ⊤
local instance (n : ℕ) : MeasurableSingletonClass (Fin n → ι) := inferInstance

open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

/-- Successor coordinates of a trajectory beginning at time `a`. -/
def successorCoordinates (a n : ℕ) :
    (Π _ : Iic (a + n), ι) → Fin n → ι := fun x k =>
      x ⟨a + k.val + 1, mem_Iic.mpr (by have hk := k.isLt; omega)⟩

/-- Coordinates of a suffix segment indexed by `Ioc a (a+n)`. -/
def suffixCoordinates (a n : ℕ) :
    (Π _ : Ioc a (a + n), ι) → Fin n → ι := fun y k =>
      y ⟨a + k.val + 1, mem_Ioc.mpr ⟨by omega, by
        have hk := k.isLt
        omega⟩⟩

/-- The suffix restriction with both interval bounds fixed explicitly. -/
def suffixRestrict (a n : ℕ) :
    (Π _ : Iic (a + n), ι) → Π _ : Ioc a (a + n), ι :=
  restrict₂ (π := fun _ : ℕ => ι)
    (Ioc_subset_Iic_self (a := a) (b := a + n))

omit [Fintype ι] [DecidableEq ι] in
/-- The full successor coordinates are the suffix coordinates of the
`Ioc` block of the history. -/
theorem successorCoordinates_eq_suffix (a n : ℕ)
    (x : Π _ : Iic (a + n), ι) :
    successorCoordinates a n x =
      suffixCoordinates a n (suffixRestrict a n x) := by
  funext k
  rfl

set_option linter.style.haveILetI false in
/-- A fixed initial history's successor-path law is the suffix marginal of
the full trajectory kernel. The proof uses the complete prefix/suffix product
factorization of `partialTraj`; the prefix factor is a Dirac measure. -/
theorem fixed_history_path_law_eq_suffix_block
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (a n : ℕ) (h : Π _ : Iic a, ι) :
    (finiteTrajectoryKernel P hP a (a + n) h).map (successorCoordinates a n) =
      ((finiteTrajectoryKernel P hP a (a + n)).map
        (suffixRestrict a n) h).map
          (suffixCoordinates a n) := by
  haveI : ∀ m, IsSFiniteKernel (historyTransitionKernel P hP m) := by
    intro m
    infer_instance
  have hprod := Kernel.partialTraj_eq_prod
    (X := fun _ : ℕ => ι) (κ := historyTransitionKernel P hP) a (a + n)
  have hpoint := congrArg (fun κ : Kernel (Π _ : Iic a, ι) (Π _ : Iic (a+n), ι) => κ h)
    hprod
  let suffixKernel : Kernel (Π _ : Iic a, ι) (Π _ : Ioc a (a+n), ι) :=
    (Kernel.partialTraj (X := fun _ : ℕ => ι)
      (historyTransitionKernel P hP) a (a+n)).map (suffixRestrict a n)
  have hpoint' :
      (Kernel.partialTraj (X := fun _ : ℕ => ι)
        (historyTransitionKernel P hP) a (a+n)) h =
      ((Kernel.id ×ₖ suffixKernel).map
        (IicProdIoc (X := fun _ : ℕ => ι) a (a+n))) h := by
    simpa [suffixKernel, suffixRestrict] using hpoint
  have hproduct_apply :
      (Kernel.id ×ₖ suffixKernel) h = (Measure.dirac h).prod (suffixKernel h) := by
    ext s hs
    rw [Kernel.id_prod_apply' _ _ hs, Measure.dirac_prod,
      Measure.map_apply measurable_prodMk_left hs]
  change Measure.map (successorCoordinates a n)
      ((Kernel.partialTraj (X := fun _ : ℕ => ι)
        (historyTransitionKernel P hP) a (a+n)) h) =
    Measure.map (suffixCoordinates a n) (suffixKernel h)
  rw [hpoint']
  rw [Kernel.map_apply _ (by fun_prop) h]
  dsimp only [suffixKernel]
  rw [Kernel.map_apply _ (by fun_prop) h]
  rw [hproduct_apply, Measure.dirac_prod]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  dsimp only [suffixKernel]
  rw [Kernel.map_apply _ (by fun_prop) h]
  congr 1
  funext y
  let xy := IicProdIoc (X := fun _ : ℕ => ι) a (a+n) (h, y)
  have hsplit := successorCoordinates_eq_suffix a n xy
  have hrestrict : suffixRestrict a n xy = y := by
    have hcomp := congrArg (fun f => f (h, y))
      (restrict₂_comp_IicProdIoc (X := fun _ : ℕ => ι) a (a+n))
    simpa [suffixRestrict, xy, Function.comp_apply] using hcomp
  rw [hrestrict] at hsplit
  exact hsplit

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryPrefixSuffixPathSplit
end
