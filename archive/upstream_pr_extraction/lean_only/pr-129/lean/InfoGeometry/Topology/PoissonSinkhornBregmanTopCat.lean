import Mathlib
import InfoGeometry.Inference.PoissonSinkhornPotentials
import InfoGeometry.Inference.PoissonBregmanTopological

/-!
# Topology of the finite Poisson Sinkhorn Bregman gap

The logarithmic Bregman expression is exposed only on the strict positive
domain where the native continuity theorem applies.  This owner packages that
continuous gap as a `TopCat` morphism and transports its nonnegativity.  It
does not claim convergence of an iterative Sinkhorn solver.
-/

open scoped BigOperators

namespace InfoGeometry.Topology.PoissonSinkhornBregmanTopCat

open CategoryTheory
open InfoGeometry.Inference

variable {n : Nat} [Nonempty (Fin n)]

abbrev PositiveCoupling (n : Nat) :=
  {Pi : Matrix (Fin n) (Fin n) ℝ // ∀ i j, 0 < Pi i j}

abbrev BregmanParameter (n : Nat) :=
  PositiveReal × (Fin n → ℝ) × (Fin n → ℝ) × PositiveCoupling n

noncomputable def bregmanGapReadout
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)) :
    BregmanParameter n → ℝ :=
  fun p => poissonSinkhornBregmanGap C p.1.1 p.2.1 p.2.2.1 p.2.2.2.1

theorem continuous_bregmanGapReadout
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)) :
    Continuous (bregmanGapReadout C) := by
  unfold bregmanGapReadout poissonSinkhornBregmanGap
  have heps : Continuous (fun p : BregmanParameter n => p.1.1) := by
    fun_prop
  have hα (i : Fin n) :
      Continuous (fun p : BregmanParameter n => p.2.1 i) := by
    fun_prop
  have hβ (j : Fin n) :
      Continuous (fun p : BregmanParameter n => p.2.2.1 j) := by
    fun_prop
  have hpi (i j : Fin n) :
      Continuous (fun p : BregmanParameter n => p.2.2.2.1 i j) := by
    have hcoupling : Continuous (fun p : BregmanParameter n =>
        p.2.2.2) :=
      continuous_snd.comp (continuous_snd.comp continuous_snd)
    have hmatrix : Continuous (fun p : BregmanParameter n =>
        p.2.2.2.1) := continuous_subtype_val.comp hcoupling
    exact (continuous_apply j).comp ((continuous_apply i).comp hmatrix)
  apply heps.mul
  apply continuous_finset_sum
  intro i hi
  apply continuous_finset_sum
  intro j hj
  have harg : Continuous (fun p : BregmanParameter n =>
      (p.2.1 i + p.2.2.1 j - C.cost i j) / p.1.1) := by
    exact ((hα i).add (hβ j)).sub continuous_const |>.div heps
      (fun p => p.1.property.ne')
  have hexp : Continuous (fun p : BregmanParameter n =>
      Real.exp ((p.2.1 i + p.2.2.1 j - C.cost i j) / p.1.1)) :=
    Real.continuous_exp.comp harg
  let first : C(BregmanParameter n, PositiveReal) :=
    ContinuousMap.mk
      (fun p => ⟨p.2.2.2.1 i j, p.2.2.2.2 i j⟩)
      ((hpi i j).subtype_mk (fun p => p.2.2.2.2 i j))
  let second : C(BregmanParameter n, PositiveReal) :=
    ContinuousMap.mk
      (fun p => ⟨Real.exp ((p.2.1 i + p.2.2.1 j - C.cost i j) / p.1.1),
        Real.exp_pos _⟩)
      (hexp.subtype_mk (fun p => Real.exp_pos _))
  exact continuous_poissonBregmanPositive.comp
    (ContinuousMap.prodMk first second).continuous

noncomputable def bregmanGapTopCatHom
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)) :
    TopCat.of (BregmanParameter n) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := bregmanGapReadout C
      continuous_toFun := continuous_bregmanGapReadout C }

theorem bregmanGapTopCatHom_apply
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (p : BregmanParameter n) :
    bregmanGapTopCatHom C p = bregmanGapReadout C p :=
  rfl

theorem bregmanGapTopCatHom_nonneg
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (p : BregmanParameter n) :
    0 ≤ bregmanGapTopCatHom C p := by
  rw [bregmanGapTopCatHom_apply]
  unfold bregmanGapReadout
  exact poissonSinkhornBregmanGap_nonneg C p.1.1 p.1.property.le
    p.2.1 p.2.2.1 p.2.2.2.1
    (fun i j => (p.2.2.2.2 i j).le)

end InfoGeometry.Topology.PoissonSinkhornBregmanTopCat
