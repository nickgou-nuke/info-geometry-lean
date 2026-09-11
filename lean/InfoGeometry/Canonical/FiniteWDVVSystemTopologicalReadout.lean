import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KANFrobeniusGromovWittenBridge

namespace InfoGeometry.Canonical

open scoped BigOperators

instance finiteWDVVSystemTopologicalSpace (dim : ℕ) :
    TopologicalSpace (FiniteWDVVSystem dim) :=
  TopologicalSpace.induced
    (fun W : FiniteWDVVSystem dim => W.structureConstants) inferInstance

def finiteWDVVEntryReadout {dim : ℕ} (i j k : Fin dim) :
    FiniteWDVVSystem dim → ℝ :=
  fun W => W.structureConstants i j k

theorem continuous_finiteWDVVEntryReadout {dim : ℕ}
    (i j k : Fin dim) :
    Continuous (finiteWDVVEntryReadout i j k) := by
  have hC : Continuous
      (fun W : FiniteWDVVSystem dim => W.structureConstants) :=
    continuous_induced_dom
  have hi : Continuous
      (fun W : FiniteWDVVSystem dim => W.structureConstants i) :=
    (continuous_apply i).comp hC
  have hij : Continuous
      (fun W : FiniteWDVVSystem dim => W.structureConstants i j) :=
    (continuous_apply j).comp hi
  exact (continuous_apply k).comp hij

theorem continuous_finiteWDVVResidual {dim : ℕ}
    (i j k l : Fin dim) :
    Continuous (fun W : FiniteWDVVSystem dim =>
      finiteWDVVResidual W i j k l) := by
  unfold finiteWDVVResidual
  apply Continuous.sub
  · apply continuous_finset_sum
    intro a ha
    exact (continuous_finiteWDVVEntryReadout i j a).mul
      (continuous_finiteWDVVEntryReadout a k l)
  · apply continuous_finset_sum
    intro a ha
    exact (continuous_finiteWDVVEntryReadout j k a).mul
      (continuous_finiteWDVVEntryReadout i a l)

theorem finiteWDVVResidual_zeroLocus_isClosed {dim : ℕ}
    (i j k l : Fin dim) :
    IsClosed {W : FiniteWDVVSystem dim |
      finiteWDVVResidual W i j k l = 0} := by
  simpa only [Set.preimage, Set.mem_setOf_eq] using
    (isClosed_singleton : IsClosed ({0} : Set ℝ)).preimage
      (continuous_finiteWDVVResidual i j k l)

end InfoGeometry.Canonical
