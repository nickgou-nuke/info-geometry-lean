import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KANFrobeniusGromovWittenBridge

namespace InfoGeometry.Canonical

open scoped BigOperators

abbrev FiniteStructureConstants (dim : ℕ) :=
  Fin dim → Fin dim → Fin dim → ℝ

def tensorWDVVResidual {dim : ℕ}
    (C : FiniteStructureConstants dim) (i j k l : Fin dim) : ℝ :=
  (∑ a : Fin dim, C i j a * C a k l) -
    ∑ a : Fin dim, C j k a * C i a l

theorem continuous_finiteStructureConstantsEntry {dim : ℕ}
    (i j k : Fin dim) :
    Continuous (fun C : FiniteStructureConstants dim => C i j k) := by
  have hi : Continuous (fun C : FiniteStructureConstants dim => C i) :=
    continuous_apply i
  have hij : Continuous (fun C : FiniteStructureConstants dim => C i j) :=
    (continuous_apply j).comp hi
  exact (continuous_apply k).comp hij

theorem continuous_tensorWDVVResidual {dim : ℕ}
    (i j k l : Fin dim) :
    Continuous (fun C : FiniteStructureConstants dim =>
      tensorWDVVResidual C i j k l) := by
  unfold tensorWDVVResidual
  apply Continuous.sub
  · apply continuous_finset_sum
    intro a ha
    exact (continuous_finiteStructureConstantsEntry i j a).mul
      (continuous_finiteStructureConstantsEntry a k l)
  · apply continuous_finset_sum
    intro a ha
    exact (continuous_finiteStructureConstantsEntry j k a).mul
      (continuous_finiteStructureConstantsEntry i a l)

def tensorWDVVLocus (dim : ℕ) : Set (FiniteStructureConstants dim) :=
  {C | ∀ i j k l, tensorWDVVResidual C i j k l = 0}

abbrev FiniteWDVVLocus (dim : ℕ) :=
  {C : FiniteStructureConstants dim // C ∈ tensorWDVVLocus dim}

theorem tensorWDVVLocus_isClosed (dim : ℕ) :
    IsClosed (tensorWDVVLocus dim) := by
  have hset : tensorWDVVLocus dim =
      ⋂ i : Fin dim, ⋂ j : Fin dim, ⋂ k : Fin dim, ⋂ l : Fin dim,
        {C : FiniteStructureConstants dim |
          tensorWDVVResidual C i j k l = 0} := by
    ext C
    simp [tensorWDVVLocus]
  rw [hset]
  exact isClosed_iInter (fun i => isClosed_iInter (fun j =>
    isClosed_iInter (fun k => isClosed_iInter (fun l =>
      (isClosed_singleton : IsClosed ({0} : Set ℝ)).preimage
        (continuous_tensorWDVVResidual i j k l)))))

theorem finiteWDVVSystem_mem_tensorWDVVLocus {dim : ℕ}
    (W : FiniteWDVVSystem dim) :
    W.structureConstants ∈ tensorWDVVLocus dim := by
  intro i j k l
  exact finiteWDVVResidual_eq_zero W i j k l

def finiteWDVVSystemToLocus {dim : ℕ} (W : FiniteWDVVSystem dim) :
    FiniteWDVVLocus dim :=
  ⟨W.structureConstants, finiteWDVVSystem_mem_tensorWDVVLocus W⟩

def prepotentialToWDVVLocus {dim : ℕ}
    (F : GromovWittenPrepotential dim) : FiniteWDVVLocus dim :=
  ⟨F.F3, by
    intro i j k l
    unfold tensorWDVVResidual
    rw [F.wdvv]
    ring⟩

theorem prepotentialToWDVVLocus_val {dim : ℕ}
    (F : GromovWittenPrepotential dim) :
    (prepotentialToWDVVLocus F).1 = F.F3 := rfl

theorem continuous_finiteWDVVLocus_subtypeVal {dim : ℕ} :
    Continuous (Subtype.val : FiniteWDVVLocus dim →
      FiniteStructureConstants dim) :=
  continuous_subtype_val

theorem finiteWDVVLocus_residual_eq_zero {dim : ℕ}
    (C : FiniteWDVVLocus dim) (i j k l : Fin dim) :
    tensorWDVVResidual C.1 i j k l = 0 :=
  C.2 i j k l

end InfoGeometry.Canonical
