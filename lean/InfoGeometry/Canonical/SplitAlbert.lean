import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Exceptional.STUDatum

/-!
# Split Albert cubic Jordan carrier

This is the canonical split-Albert owner surface for the Freudenthal route.

It is concrete and proof-carrying:

* the carrier is `Fin 9 → STUCarrier`, hence real dimension `27`;
* the trace pairing, cubic norm, adjoint map, and trilinear polarization are
  defined blockwise from the already-proved STU datum;
* no octonionic Hermitian matrix multiplication is claimed here.

The file is intentionally theorem-first and uses only mathlib plus the repo's
existing STU/Freudenthal proofs.
-/

noncomputable section

namespace SplitAlbert

open scoped BigOperators
open Freudenthal
open STUDatum

/-- A 27-dimensional coordinate carrier for the split Albert route. -/
abbrev SplitAlbertCarrier := Fin 9 → STUCarrier

/-- Blockwise trace pairing on the split Albert route carrier. -/
def splitAlbertTraceBilin :
    SplitAlbertCarrier →ₗ[ℝ] SplitAlbertCarrier →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => ∑ i : Fin 9, stuTraceBilin (x i) (y i)
      map_add' := by
        intro y₁ y₂
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        simp [Finset.mul_sum] }
  map_add' := by
    intro x₁ x₂
    ext y
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    ext y
    simp [Finset.mul_sum]

/-- Unary coordinate trace on the split Albert route carrier. -/
def splitAlbertTrace : SplitAlbertCarrier →ₗ[ℝ] ℝ where
  toFun x := ∑ i : Fin 9, stuTrace (x i)
  map_add' := by
    intro x y
    simp [stuTrace, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c x
    simp [stuTrace, Finset.mul_sum]

@[simp] theorem splitAlbertTrace_apply (x : SplitAlbertCarrier) :
    splitAlbertTrace x = ∑ i : Fin 9, stuTrace (x i) :=
  rfl

/-- The trace-zero subspace of the split Albert route carrier. -/
def splitAlbertTraceZero : Submodule ℝ SplitAlbertCarrier :=
  LinearMap.ker splitAlbertTrace

@[simp] theorem mem_splitAlbertTraceZero (x : SplitAlbertCarrier) :
    x ∈ splitAlbertTraceZero ↔ splitAlbertTrace x = 0 := by
  rfl

/-- A simple coordinate witness with prescribed split-Albert trace. -/
def splitAlbertTraceWitness (r : ℝ) : SplitAlbertCarrier :=
  Pi.single 0 (Pi.single 0 r)

@[simp] theorem splitAlbertTrace_traceWitness (r : ℝ) :
    splitAlbertTrace (splitAlbertTraceWitness r) = r := by
  classical
  have h0 : ∑ x : Fin 9, splitAlbertTraceWitness r x 0 = r := by
    rw [Finset.sum_eq_single 0]
    · simp [splitAlbertTraceWitness]
    · intro x _ hx
      simp [splitAlbertTraceWitness, hx]
    · simp [splitAlbertTraceWitness]
  have h1 : ∑ x : Fin 9, splitAlbertTraceWitness r x 1 = 0 := by
    rw [Finset.sum_eq_single 0]
    · simp [splitAlbertTraceWitness]
    · intro x _ hx
      simp [splitAlbertTraceWitness, hx]
    · simp [splitAlbertTraceWitness]
  have h2 : ∑ x : Fin 9, splitAlbertTraceWitness r x 2 = 0 := by
    rw [Finset.sum_eq_single 0]
    · simp [splitAlbertTraceWitness]
    · intro x _ hx
      simp [splitAlbertTraceWitness, hx]
    · simp [splitAlbertTraceWitness]
  calc
    splitAlbertTrace (splitAlbertTraceWitness r)
        = (∑ x : Fin 9, splitAlbertTraceWitness r x 0)
            + ∑ x : Fin 9, splitAlbertTraceWitness r x 1
            + ∑ x : Fin 9, splitAlbertTraceWitness r x 2 := by
              simp [splitAlbertTrace, stuTrace, Finset.sum_add_distrib]
    _ = r + 0 + 0 := by rw [h0, h1, h2]
    _ = r := by ring

theorem splitAlbertTrace_surjective : Function.Surjective splitAlbertTrace := by
  intro r
  exact ⟨splitAlbertTraceWitness r, splitAlbertTrace_traceWitness r⟩

theorem splitAlbertTrace_range_eq_top : LinearMap.range splitAlbertTrace = ⊤ := by
  exact LinearMap.range_eq_top.2 splitAlbertTrace_surjective

/-- Blockwise cubic norm on the split Albert route carrier. -/
def splitAlbertNormCubic (x : SplitAlbertCarrier) : ℝ :=
  ∑ i : Fin 9, stuNormCubic (x i)

/-- Blockwise quadratic adjoint on the split Albert route carrier. -/
def splitAlbertAdjointQuad (x : SplitAlbertCarrier) : SplitAlbertCarrier :=
  fun i => stuAdjointQuad (x i)

/-- Blockwise symmetric trilinear form on the split Albert route carrier. -/
def splitAlbertNormTrilin :
    SplitAlbertCarrier →ₗ[ℝ] SplitAlbertCarrier →ₗ[ℝ] SplitAlbertCarrier →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => ∑ i : Fin 9, stuNormTrilin (x i) (y i) (z i)
          map_add' := by
            intro z₁ z₂
            simp [Finset.sum_add_distrib]
          map_smul' := by
            intro c z
            simp [Finset.mul_sum] }
      map_add' := by
        intro y₁ y₂
        ext z
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        ext z
        simp [Finset.mul_sum] }
  map_add' := by
    intro x₁ x₂
    ext y z
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    ext y z
    simp [Finset.mul_sum]

/-- The concrete split Albert cubic Jordan structure. -/
def splitAlbertJordan : CubicJordanDatum SplitAlbertCarrier where
  traceBilin := splitAlbertTraceBilin
  trace_comm := by
    intro x y
    simp [splitAlbertTraceBilin]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact STU_Datum.trace_comm (x i) (y i)
  normCubic := splitAlbertNormCubic
  adjointQuad := splitAlbertAdjointQuad
  normTrilin := splitAlbertNormTrilin
  normTrilin_swap₁₂ := by
    intro x y z
    simp [splitAlbertNormTrilin]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact STU_Datum.normTrilin_swap₁₂ (x i) (y i) (z i)
  normTrilin_swap₂₃ := by
    intro x y z
    simp [splitAlbertNormTrilin]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact STU_Datum.normTrilin_swap₂₃ (x i) (y i) (z i)
  normTrilin_self := by
    intro x
    simp [splitAlbertNormTrilin, splitAlbertNormCubic]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact STU_Datum.normTrilin_self (x i)

/-- The split Albert route carrier has real finrank `27`. -/
theorem splitAlbertCarrier_finrank_eq_27 :
    Module.finrank ℝ SplitAlbertCarrier = 27 := by
  simp [SplitAlbertCarrier, STUCarrier, Module.finrank_pi_fintype]

/-- The trace-zero subspace has codimension one. -/
theorem splitAlbertTraceZero_finrank_eq_26 :
    Module.finrank ℝ splitAlbertTraceZero = 26 := by
  have h := LinearMap.finrank_range_add_finrank_ker splitAlbertTrace
  rw [splitAlbertTrace_range_eq_top] at h
  have h' : Module.finrank ℝ (LinearMap.ker splitAlbertTrace) = 26 := by
    apply Nat.succ.inj
    simpa [Nat.succ_eq_add_one, add_comm, splitAlbertCarrier_finrank_eq_27] using h
  simpa [splitAlbertTraceZero] using h'

end SplitAlbert
