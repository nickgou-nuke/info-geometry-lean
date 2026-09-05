import InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
import InfoGeometry.LinearAlgebra.RegularDyadCompression

/-!
# Dyadic compression for the existing regular two-boundary functional

The overlap and weak functional are the existing PR153 definitions. This
file supplies their missing operator compression, without identifying a
regular boundary pair with a density matrix or a positive probability state.
-/

noncomputable section

namespace InfoGeometry.Streaming.TwoBoundaryDyadCompression

open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
open InfoGeometry.LinearAlgebra.RegularDyadCompression

variable {ι : Type*} [Fintype ι]

/-- The existing Dirac pairing as a covector of its second argument. -/
def postCovector (p : RegularBoundaryPair ι) : Module.Dual ℂ (State ι) where
  toFun x := pairing p.post x
  map_add' x y := pairing_add_right p.post x y
  map_smul' c x := by
    simpa only [smul_eq_mul] using pairing_smul_right c p.post x

@[simp] theorem postCovector_apply (p : RegularBoundaryPair ι) (x : State ι) :
    postCovector p x = pairing p.post x := rfl

/-- No second regular-boundary structure is needed. -/
def boundaryDyad (p : RegularBoundaryPair ι) : Operator ι :=
  normalizedDyad p.pre (postCovector p)

@[simp] theorem boundaryDyad_apply (p : RegularBoundaryPair ι) (x : State ι) :
    boundaryDyad p x = (pairing p.post x / overlap p) • p.pre := by
  rw [boundaryDyad, normalizedDyad_apply]
  rfl

@[simp] theorem boundaryDyad_pre (p : RegularBoundaryPair ι) :
    boundaryDyad p p.pre = p.pre :=
  normalizedDyad_self p.pre (postCovector p) p.overlap_ne

/-- The weak-value compression law uses the pre-existing normalized coefficient. -/
theorem boundaryDyad_compression (p : RegularBoundaryPair ι) (A : Operator ι) :
    boundaryDyad p * A * boundaryDyad p = weakValue p A • boundaryDyad p := by
  exact normalizedDyad_compression p.pre (postCovector p) A

theorem boundaryDyad_idempotent (p : RegularBoundaryPair ι) :
    boundaryDyad p * boundaryDyad p = boundaryDyad p :=
  normalizedDyad_idempotent p.pre (postCovector p) p.overlap_ne

theorem boundaryDyad_range (p : RegularBoundaryPair ι) :
    (boundaryDyad p).range = Submodule.span ℂ {p.pre} :=
  normalizedDyad_range p.pre (postCovector p) p.overlap_ne

theorem boundaryDyad_ker (p : RegularBoundaryPair ι) :
    (boundaryDyad p).ker = (postCovector p).ker :=
  normalizedDyad_ker p.pre (postCovector p) p.overlap_ne

@[simp] theorem weakValue_boundaryDyad (p : RegularBoundaryPair ι) :
    weakValue p (boundaryDyad p) = 1 := by
  unfold weakValue numerator
  rw [boundaryDyad_pre]
  exact div_self p.overlap_ne

/-- A proved finite operator decomposition descends by the existing linear map.
The theorem does not assume that only five occupation grades exist. -/
theorem weakValue_finset_sum (p : RegularBoundaryPair ι)
    {κ : Type*} (s : Finset κ) (A : κ → Operator ι) :
    weakValue p (∑ k ∈ s, A k) = ∑ k ∈ s, weakValue p (A k) := by
  exact (weakValueLinear p).map_sum A s

/-- Concrete regular data for which the dyad is not self-adjoint. -/
def obliquePair : RegularBoundaryPair (Fin 2) where
  pre := ![1, 0]
  post := ![1, 1]
  overlap_ne := by norm_num [pairing, Fin.sum_univ_two]

/-- Coordinate readout of an endomorphism in the native basis. -/
def coordinateMatrix [DecidableEq ι] (A : Operator ι) : Matrix ι ι ℂ :=
  fun i j => A (Pi.single j 1) i

theorem obliquePair_matrix : coordinateMatrix (boundaryDyad obliquePair) =
    !![1, 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateMatrix, boundaryDyad_apply, obliquePair, overlap, pairing,
      Fin.sum_univ_two, Pi.single_apply]

/-- A regular normalized dyad need not be a density matrix. -/
theorem obliquePair_not_self_adjoint :
    (coordinateMatrix (boundaryDyad obliquePair))ᴴ ≠
      coordinateMatrix (boundaryDyad obliquePair) := by
  rw [obliquePair_matrix]
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [Matrix.conjTranspose_apply] at h01

end InfoGeometry.Streaming.TwoBoundaryDyadCompression
