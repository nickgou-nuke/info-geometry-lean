import InfoGeometry.Canonical.KANFrobeniusGromovWittenBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Topological readout for finite WDVV residuals

This file adds only the topology of the finite structure-constant space.  It
does not introduce a prepotential, Gromov--Witten invariants, or a gauge
quotient.
-/

namespace InfoGeometry.Canonical

open scoped BigOperators

def finiteWDVVResidualReadout {dim : ℕ}
    (c : Fin dim → Fin dim → Fin dim → ℝ)
    (i j k l : Fin dim) : ℝ :=
  (∑ a : Fin dim, c i j a * c a k l) -
    ∑ a : Fin dim, c j k a * c i a l

theorem finiteWDVVResidual_eq_readout {dim : ℕ}
    (W : FiniteWDVVSystem dim) (i j k l : Fin dim) :
    finiteWDVVResidual W i j k l =
      finiteWDVVResidualReadout W.structureConstants i j k l :=
  rfl

theorem finiteWDVVResidualReadout_continuous {dim : ℕ}
    (i j k l : Fin dim) :
    Continuous (fun c : Fin dim → Fin dim → Fin dim → ℝ =>
      finiteWDVVResidualReadout c i j k l) := by
  unfold finiteWDVVResidualReadout
  fun_prop

def finiteWDVVZeroLocus (dim : ℕ) (i j k l : Fin dim) :
    Set (Fin dim → Fin dim → Fin dim → ℝ) :=
  {c | finiteWDVVResidualReadout c i j k l = 0}

theorem finiteWDVVZeroLocus_isClosed {dim : ℕ}
    (i j k l : Fin dim) :
    IsClosed (finiteWDVVZeroLocus dim i j k l) := by
  change IsClosed
    ((fun c : Fin dim → Fin dim → Fin dim → ℝ =>
      finiteWDVVResidualReadout c i j k l) ⁻¹' ({0} : Set ℝ))
  exact isClosed_singleton.preimage
    (finiteWDVVResidualReadout_continuous i j k l)

theorem finiteWDVVSystem_mem_zeroLocus {dim : ℕ}
    (W : FiniteWDVVSystem dim) (i j k l : Fin dim) :
    W.structureConstants ∈ finiteWDVVZeroLocus dim i j k l := by
  change finiteWDVVResidualReadout W.structureConstants i j k l = 0
  rw [← finiteWDVVResidual_eq_readout W i j k l]
  exact finiteWDVVResidual_eq_zero W i j k l

def finiteWDVVAssociativeLocus (dim : ℕ) :
    Set (Fin dim → Fin dim → Fin dim → ℝ) :=
  {c | ∀ i j k l : Fin dim,
    finiteWDVVResidualReadout c i j k l = 0}

theorem finiteWDVVAssociativeLocus_isClosed {dim : ℕ} :
    IsClosed (finiteWDVVAssociativeLocus dim) := by
  rw [show finiteWDVVAssociativeLocus dim =
      (⋂ i : Fin dim, ⋂ j : Fin dim, ⋂ k : Fin dim, ⋂ l : Fin dim,
        finiteWDVVZeroLocus dim i j k l) by
    ext c
    simp [finiteWDVVAssociativeLocus, finiteWDVVZeroLocus]]
  exact isClosed_iInter (fun i => isClosed_iInter (fun j =>
    isClosed_iInter (fun k => isClosed_iInter (fun l =>
      finiteWDVVZeroLocus_isClosed i j k l))))

theorem finiteWDVVSystem_mem_associativeLocus {dim : ℕ}
    (W : FiniteWDVVSystem dim) :
    W.structureConstants ∈ finiteWDVVAssociativeLocus dim := by
  intro i j k l
  exact finiteWDVVSystem_mem_zeroLocus W i j k l

end InfoGeometry.Canonical
