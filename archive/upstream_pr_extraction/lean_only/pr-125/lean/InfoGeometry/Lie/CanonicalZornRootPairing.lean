import InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# The native Cartan pairing interface

This owner exposes only the verified Cartan-plane prerequisite for Mathlib's
`RootPairing`: the evaluation perfect pairing between the Cartan dual and the
Cartan plane.  Root indexing, coroots, and reflection stability are deliberately
downstream; they require a kernel-checked adjoint decomposition before
`RootPairing.mk''` can be applied.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornRootPairing

open InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

abbrev Weight := TracelessWeight →ₗ[ℝ] ℝ

instance : Module.Free ℝ TracelessWeight :=
  Module.Free.of_equiv tracelessWeightEquiv

instance : Module.Finite ℝ TracelessWeight :=
  Module.Finite.equiv tracelessWeightEquiv

theorem tracelessWeight_finrank : Module.finrank ℝ TracelessWeight = 2 := by
  rw [← (tracelessWeightEquiv).finrank_eq]
  exact Module.finrank_fin_fun ℝ

def evaluationPairing : Weight →ₗ[ℝ] TracelessWeight →ₗ[ℝ] ℝ :=
  (Module.Dual.eval ℝ TracelessWeight).flip

instance : evaluationPairing.IsPerfPair := by
  unfold evaluationPairing
  exact LinearMap.IsPerfPair.flip inferInstance

@[simp] theorem evaluationPairing_apply (α : Weight) (h : TracelessWeight) :
    evaluationPairing α h = α h := rfl

def coordinateWeights : Fin 2 → Weight
  | 0 => coordWeight 0
  | 1 => coordWeight 1

def coordinateCoroot (i : Fin 2) : TracelessWeight :=
  (2 : ℝ) • tracelessWeightEquiv
    (Pi.single i (1 : ℝ) : Fin 2 → ℝ)

theorem coordinateWeight_apply_coordinateCoroot (i j : Fin 2) :
    coordinateWeights i (coordinateCoroot j) = if i = j then 2 else 0 := by
  fin_cases i
  · by_cases h : j = 0
    · subst j
      simp [coordinateWeights, coordinateCoroot, coordWeight, tracelessWeightEquiv]
    · simp [coordinateWeights, coordinateCoroot, coordWeight, tracelessWeightEquiv, h,
        Ne.symm h]
  · by_cases h : j = 1
    · subst j
      simp [coordinateWeights, coordinateCoroot, coordWeight, tracelessWeightEquiv]
    · simp [coordinateWeights, coordinateCoroot, coordWeight, tracelessWeightEquiv, h,
        Ne.symm h]

theorem coordinateWeights_linearIndependent :
    LinearIndependent ℝ coordinateWeights := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · have h0 := congrArg (fun w : Weight =>
      w (tracelessWeightEquiv (Pi.single 0 (1 : ℝ)))) hg
    simpa [coordinateWeights, coordWeight, tracelessWeightEquiv] using h0
  · have h1 := congrArg (fun w : Weight =>
      w (tracelessWeightEquiv (Pi.single 1 (1 : ℝ)))) hg
    simpa [coordinateWeights, coordWeight, tracelessWeightEquiv] using h1

theorem coordinateWeights_span_top :
    Submodule.span ℝ (Set.range coordinateWeights) = (⊤ : Submodule ℝ Weight) := by
  apply coordinateWeights_linearIndependent.span_eq_top_of_card_eq_finrank
  rw [Subspace.dual_finrank_eq, tracelessWeight_finrank]
  rfl

theorem rootWeights_span_top :
    Submodule.span ℝ (Set.range (rootWeight : Fin 14 → Weight)) = (⊤ : Submodule ℝ Weight) := by
  apply le_antisymm le_top
  rw [← coordinateWeights_span_top]
  apply Submodule.span_le.2
  intro x hx
  rcases hx with ⟨i, rfl⟩
  fin_cases i
  · exact Submodule.subset_span ⟨10, by simp [rootWeight, coordinateWeights]⟩
  · exact Submodule.subset_span ⟨9, by simp [rootWeight, coordinateWeights]⟩

theorem rootWeight_nonzero_injective :
    Function.Injective (fun j : nonzeroIndex => rootWeight j.1) := by
  intro i j hij
  by_contra hne
  exact (rootWeight_injective_on_nonzero i j hne) hij

def rootEmbedding : nonzeroIndex ↪ Weight where
  toFun j := rootWeight j.1
  inj' := rootWeight_nonzero_injective

def shortSimpleCoroot : TracelessWeight :=
  tracelessWeightEquiv (Pi.single 0 (2 : ℝ) + Pi.single 1 (-1 : ℝ))

def longSimpleCoroot : TracelessWeight :=
  tracelessWeightEquiv (Pi.single 0 (-1 : ℝ) + Pi.single 1 (1 : ℝ))

theorem shortSimpleCoroot_pairing_short :
    coordWeight 0 shortSimpleCoroot = 2 := by
  simp [shortSimpleCoroot, coordWeight, tracelessWeightEquiv]

theorem longSimpleCoroot_pairing_long :
    (coordWeight 1 - coordWeight 0) longSimpleCoroot = 2 := by
  simp [longSimpleCoroot, coordWeight, tracelessWeightEquiv]
  norm_num

theorem longSimpleCoroot_pairing_short :
    (coordWeight 0) longSimpleCoroot = -1 := by
  simp [longSimpleCoroot, coordWeight, tracelessWeightEquiv]

theorem shortSimpleCoroot_pairing_long :
    (coordWeight 1 - coordWeight 0) shortSimpleCoroot = -3 := by
  simp [shortSimpleCoroot, coordWeight, tracelessWeightEquiv]
  norm_num

theorem rootWeight_shortSimple_pairing :
    rootWeight 10 shortSimpleCoroot = 2 := by
  simpa [rootWeight] using shortSimpleCoroot_pairing_short

theorem rootWeight_longSimple_pairing :
    rootWeight 1 longSimpleCoroot = 2 := by
  simpa [rootWeight] using longSimpleCoroot_pairing_long

theorem rootWeight_short_long_pairing :
    rootWeight 10 longSimpleCoroot = -1 := by
  simpa [rootWeight] using longSimpleCoroot_pairing_short

theorem rootWeight_long_short_pairing :
    rootWeight 1 shortSimpleCoroot = -3 := by
  simpa [rootWeight] using shortSimpleCoroot_pairing_long

def simpleWeight (i : Fin 2) : Weight :=
  if i = 0 then coordWeight 0 else coordWeight 1 - coordWeight 0

def simpleCoroot (i : Fin 2) : TracelessWeight :=
  if i = 0 then shortSimpleCoroot else longSimpleCoroot

def simpleCartanMatrix : Matrix (Fin 2) (Fin 2) ℝ
  | 0, 0 => 2
  | 0, 1 => -1
  | 1, 0 => -3
  | 1, 1 => 2

theorem simpleWeight_simpleCoroot_pairing (i j : Fin 2) :
    simpleWeight i (simpleCoroot j) =
      simpleCartanMatrix i j := by
  fin_cases i <;> fin_cases j
  · simpa [simpleWeight, simpleCoroot] using shortSimpleCoroot_pairing_short
  · simpa [simpleWeight, simpleCoroot] using longSimpleCoroot_pairing_short
  · simpa [simpleWeight, simpleCoroot] using shortSimpleCoroot_pairing_long
  · simpa [simpleWeight, simpleCoroot] using longSimpleCoroot_pairing_long

theorem simpleWeight_linearIndependent :
    LinearIndependent ℝ simpleWeight := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · have h0 := congrArg (fun w : Weight => w (simpleCoroot 0)) hg
    have h1 := congrArg (fun w : Weight => w (simpleCoroot 1)) hg
    simp [Fin.sum_univ_two, simpleWeight_simpleCoroot_pairing,
      simpleCartanMatrix] at h0 h1
    change g 0 = 0
    nlinarith
  · have h0 := congrArg (fun w : Weight => w (simpleCoroot 0)) hg
    have h1 := congrArg (fun w : Weight => w (simpleCoroot 1)) hg
    simp [Fin.sum_univ_two, simpleWeight_simpleCoroot_pairing,
      simpleCartanMatrix] at h0 h1
    change g 1 = 0
    nlinarith

theorem simpleWeight_span_top :
    Submodule.span ℝ (Set.range simpleWeight) = (⊤ : Submodule ℝ Weight) := by
  apply simpleWeight_linearIndependent.span_eq_top_of_card_eq_finrank
  rw [Subspace.dual_finrank_eq, tracelessWeight_finrank]
  rfl

theorem simpleCoroot_linearIndependent :
    LinearIndependent ℝ simpleCoroot := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · have h0 := congrArg (fun x : TracelessWeight => coordWeight 0 x) hg
    have h1 := congrArg (fun x : TracelessWeight => coordWeight 1 x) hg
    simp [Fin.sum_univ_two, simpleCoroot, coordWeight,
      shortSimpleCoroot, longSimpleCoroot, tracelessWeightEquiv] at h0 h1
    change g 0 = 0
    nlinarith
  · have h0 := congrArg (fun x : TracelessWeight => coordWeight 0 x) hg
    have h1 := congrArg (fun x : TracelessWeight => coordWeight 1 x) hg
    simp [Fin.sum_univ_two, simpleCoroot, coordWeight,
      shortSimpleCoroot, longSimpleCoroot, tracelessWeightEquiv] at h0 h1
    change g 1 = 0
    nlinarith

theorem simpleCoroot_span_top :
    Submodule.span ℝ (Set.range simpleCoroot) =
      (⊤ : Submodule ℝ TracelessWeight) := by
  apply simpleCoroot_linearIndependent.span_eq_top_of_card_eq_finrank
  simpa using tracelessWeight_finrank.symm

def simpleCorootEvaluation : Weight →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun w := fun i => w (simpleCoroot i)
  map_add' w v := by
    funext i
    simp
  map_smul' a w := by
    funext i
    simp

@[simp] theorem simpleCorootEvaluation_apply (w : Weight) (i : Fin 2) :
    simpleCorootEvaluation w i = w (simpleCoroot i) := rfl

theorem simpleCorootEvaluation_injective :
    Function.Injective simpleCorootEvaluation := by
  intro w v h
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℝ (Set.range simpleCoroot) := by
    rw [simpleCoroot_span_top]
    trivial
  have hker : Submodule.span ℝ (Set.range simpleCoroot) ≤
      LinearMap.ker (w - v) := by
    apply Submodule.span_le.2
    rintro x ⟨i, rfl⟩
    change (w - v) (simpleCoroot i) = 0
    apply sub_eq_zero.mpr
    have hii := congrFun h i
    simpa [simpleCorootEvaluation] using hii
  have : (w - v) x = 0 := hker hx
  simpa using sub_eq_zero.mp this

noncomputable def simpleCorootEvaluationEquiv :
    Weight ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearEquiv.ofBijective simpleCorootEvaluation
    ⟨simpleCorootEvaluation_injective,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [Subspace.dual_finrank_eq, tracelessWeight_finrank,
            Module.finrank_fin_fun])).mp
        simpleCorootEvaluation_injective⟩

end InfoGeometry.Lie.CanonicalZornRootPairing
