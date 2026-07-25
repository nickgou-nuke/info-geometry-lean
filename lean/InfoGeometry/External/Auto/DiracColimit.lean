import Mathlib.Tactic
import Mathlib.Analysis.CStarAlgebra.Spectrum

noncomputable section

namespace InfoGeometry.Canonical.DiracColimit

open Complex

/--
Abstract inductive tower of finite-dimensional stages and Dirac operators.
- `emb n` : `Stage n ⟶ Stage (n+1)` is an isometric inclusion of stages.
- `D n`   : self-adjoint Dirac-type operator on stage `n`.
- `hD_comm` : compatibility of consecutive operators across the tower.
-/
structure DiracColimitData where
  Stage : ℕ → Type*
  [hNorm : ∀ n, NormedAddCommGroup (Stage n)]
  [hIP : ∀ n, InnerProductSpace ℂ (Stage n)]
  [hCS : ∀ n, CompleteSpace (Stage n)]
  emb : ∀ n, Stage n →ₗᵢ[ℂ] Stage (n + 1)
  D : ∀ n, Stage n →L[ℂ] Stage n
  hD_selfAdj : ∀ n, IsSelfAdjoint (D n)
  hD_comm : ∀ n,
    (D (n + 1)).comp (emb n).toContinuousLinearMap =
      (emb n).toContinuousLinearMap.comp (D n)

attribute [instance] DiracColimitData.hNorm DiracColimitData.hIP DiracColimitData.hCS

/--
Data specifying a categorical limit object for the tower.
- `inc n` gives the level-wise inclusion into the Hilbert limit space.
- `hPair` is the concrete colimit condition: every pair of limit vectors can
  be pulled back to a common finite stage.
- `hInc` enforces compatibility of level embeddings (`inc (n+1) ∘ emb n = inc n`).
- `hDlim_compat` enforces compatibility of the direct-limit Dirac operator.
-/
structure DiracColimitLimit (S : DiracColimitData) where
  Hlim : Type*
  [hNorm : NormedAddCommGroup Hlim]
  [hIP : InnerProductSpace ℂ Hlim]
  [hCS : CompleteSpace Hlim]
  inc : ∀ n, S.Stage n →ₗᵢ[ℂ] Hlim
  hPair : ∀ x y : Hlim, ∃ n u v, x = (inc n) u ∧ y = (inc n) v
  hInc : ∀ n,
      (inc (n + 1)).toContinuousLinearMap.comp (S.emb n).toContinuousLinearMap =
      (inc n).toContinuousLinearMap
  Dlim : Hlim →L[ℂ] Hlim
  hDlim_compat : ∀ n,
    Dlim.comp (inc n).toContinuousLinearMap =
      (inc n).toContinuousLinearMap.comp (S.D n)

attribute [instance] DiracColimitLimit.hNorm DiracColimitLimit.hIP DiracColimitLimit.hCS

/--
Self-adjointness of the direct-limit Dirac operator from stagewise self-adjointness
and colimit compatibility assumptions.
-/
theorem dirac_colimit_selfAdjoint
    (S : DiracColimitData)
    (L : DiracColimitLimit S) : IsSelfAdjoint L.Dlim := by
  refine (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 ?_
  intro x y
  rcases L.hPair x y with ⟨n, u, v, rfl, rfl⟩
  have hCompV :
      L.Dlim (L.inc n v) = (L.inc n) (S.D n v) := by
    simpa using congrArg (fun T => T v) (L.hDlim_compat n)
  have hCompU :
      L.Dlim (L.inc n u) = (L.inc n) (S.D n u) := by
    simpa using congrArg (fun T => T u) (L.hDlim_compat n)
  calc
    inner ℂ (L.Dlim (L.inc n u)) (L.inc n v)
        = inner ℂ ((L.inc n) (S.D n u)) (L.inc n v) := by simpa [hCompU]
    _ = inner ℂ (S.D n u) v := by
          simpa using (L.inc n).inner_map_map (S.D n u) v
    _ = inner ℂ u (S.D n v) := (S.hD_selfAdj n).isSymmetric u v
    _ = inner ℂ (L.inc n u) ((L.inc n) (S.D n v)) := by
          simpa using (L.inc n).inner_map_map u (S.D n v) |>.symm
    _ = inner ℂ (L.inc n u) (L.Dlim (L.inc n v)) := by simpa [hCompV]

/-- Corollary: spectrum of `Dlim` is real-valued.
This is the operator-theoretic Hilbert-Pólya shadow used in the narrative.
-/
theorem dirac_colimit_spectrum_is_real
    (S : DiracColimitData)
    (L : DiracColimitLimit S)
    (z : ℂ)
    (hz : z ∈ spectrum ℂ L.Dlim) :
    z.im = 0 := by
  exact (dirac_colimit_selfAdjoint S L).im_eq_zero_of_mem_spectrum hz

/--
A compact transport package used by other layers:
any colimit-constructed spectral argument can be discharged by pointing at
`dirac_colimit_spectrum_is_real`.
-/
theorem dirac_colimit_reality_chain
    (S : DiracColimitData)
    (L : DiracColimitLimit S)
    (z : ℂ)
    (hSpec : z ∈ spectrum ℂ L.Dlim) :
    z.im = 0 :=
  dirac_colimit_spectrum_is_real S L z hSpec

/--
Concrete one-mode tower: every finite stage is `ℂ`, every bonding map is the
identity isometry, and every finite Dirac operator is the identity operator.

This is the smallest genuine instantiation of the abstract colimit hypotheses.
It does not claim to be the full Clifford/Cuntz tower; it proves the interface
is constructible by an actual Lean object.
-/
def oneModeDiracData : DiracColimitData where
  Stage := fun _ => ℂ
  emb := fun _ => LinearIsometry.id
  D := fun _ => ContinuousLinearMap.id ℂ ℂ
  hD_selfAdj := by
    intro n
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    simp
  hD_comm := by
    intro n
    ext
    rfl

/-- The corresponding concrete one-mode colimit. -/
def oneModeDiracLimit : DiracColimitLimit oneModeDiracData where
  Hlim := ℂ
  inc := fun _ => LinearIsometry.id
  hPair := by
    intro x y
    exact ⟨0, x, y, rfl, rfl⟩
  hInc := by
    intro n
    ext
    rfl
  Dlim := ContinuousLinearMap.id ℂ ℂ
  hDlim_compat := by
    intro n
    ext
    rfl

/-- Concrete discharge of the colimit self-adjointness theorem. -/
theorem oneMode_dirac_colimit_selfAdjoint :
    IsSelfAdjoint oneModeDiracLimit.Dlim :=
  dirac_colimit_selfAdjoint oneModeDiracData oneModeDiracLimit

/-- Spectrum-reality corollary for the concrete one-mode colimit. -/
theorem oneMode_dirac_colimit_spectrum_is_real
    (z : ℂ)
    (hz : z ∈ spectrum ℂ oneModeDiracLimit.Dlim) :
    z.im = 0 :=
  dirac_colimit_spectrum_is_real oneModeDiracData oneModeDiracLimit z hz

end InfoGeometry.Canonical.DiracColimit
