import InfoGeometry.KK.DiracFredholmIndex
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.AnalyticalIndexCore
import InfoGeometry.Meta.Architecture
import Mathlib.Algebra.Lie.OfAssociative

open scoped InnerProductSpace

/-!
# InfoGeometry.KK.KasparovCycle

Repo-internal legacy compatibility surface for the bounded KK presentation.

The primitive owner is the real split-Krein Dirac/Fredholm module carried by
`RealSplitKreinKasparovCycle` and developed directly in
`DiracFredholmModule`/`DiracFredholmIndex`. This file keeps the old
`KasparovCycle` names only as an explicitly isolated representation layer for
remaining in-repo consumers.

- `@[rep_depth krein]` declarations are local bounded compatibility owners.
- `@[rep_depth transport]` declarations are transport/invariance wrappers that
  compare the local KK presentation with canonical analytical-index families.
-/

namespace InfoGeometry.KK

open InfoGeometry.Krein

/-- Legacy bounded KK label for the primitive real split-Krein carrier. -/
@[rep_depth krein]
abbrev KasparovCycle := RealSplitKreinKasparovCycle

namespace RealSplitKreinKasparovCycle

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/-- Forget only the canonical naming bridge and retain the legacy KK label. -/
@[rep_depth krein]
abbrev toKasparovCycle
    (X : RealSplitKreinKasparovCycle A B H) : KasparovCycle A B H :=
  X

/--
Finite-dimensional analytical index of the primitive bounded real split-Krein
Dirac/Fredholm module.
-/
@[rep_depth krein]
noncomputable def finiteAnalyticalIndex
    [FiniteDimensional ℝ H]
    (X : RealSplitKreinKasparovCycle A B H) : ℤ :=
  X.analyticalIndex (X.chiralFredholmSurfaceOfFiniteAmbient)

/--
The legacy finite-dimensional KK index agrees with the canonical finite model.
-/
@[rep_depth transport, simp] theorem finiteAnalyticalIndex_eq_canonical
    [FiniteDimensional ℝ H]
    (X : RealSplitKreinKasparovCycle A B H) :
    X.finiteAnalyticalIndex =
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
        X.F.toLinearMap
        (KreinGradedModule.gradeCLM (H := H)).toLinearMap := by
  have hPlus :
      InfoGeometry.Canonical.AnalyticalIndex.chiralKernelSlicePlus
          X.F.toLinearMap
          (KreinGradedModule.gradeCLM (H := H)).toLinearMap
        =
      RealSplitKreinKasparovCycle.chiralKernelSlicePlus X := by
    simp [InfoGeometry.Canonical.AnalyticalIndex.chiralKernelSlicePlus,
      InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorPlus,
      RealSplitKreinKasparovCycle.chiralKernelSlicePlus,
      RealSplitKreinKasparovCycle.diracOperator,
      RealSplitKreinKasparovCycle.chiralProjectorPlus,
      KreinGradedModule.gradeProjPlus, one_div]
  have hMinus :
      InfoGeometry.Canonical.AnalyticalIndex.chiralKernelSliceMinus
          X.F.toLinearMap
          (KreinGradedModule.gradeCLM (H := H)).toLinearMap
        =
      RealSplitKreinKasparovCycle.chiralKernelSliceMinus X := by
    simp [InfoGeometry.Canonical.AnalyticalIndex.chiralKernelSliceMinus,
      InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorMinus,
      RealSplitKreinKasparovCycle.chiralKernelSliceMinus,
      RealSplitKreinKasparovCycle.diracOperator,
      RealSplitKreinKasparovCycle.chiralProjectorMinus,
      KreinGradedModule.gradeProjMinus, one_div]
  unfold RealSplitKreinKasparovCycle.finiteAnalyticalIndex
  rw [RealSplitKreinKasparovCycle.analyticalIndex_eq_finrank_chiralKernelDifference (X := X)]
  unfold InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
  rw [hPlus, hMinus]

end RealSplitKreinKasparovCycle

namespace KasparovCycle

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/-- Legacy compatibility name for the positive chiral defect sector. -/
@[rep_depth krein]
noncomputable abbrev chiralKernelSlicePlus
    (X : KasparovCycle A B H) : Submodule ℝ H :=
  RealSplitKreinKasparovCycle.chiralKernelSlicePlus X

/-- Legacy compatibility name for the negative chiral defect sector. -/
@[rep_depth krein]
noncomputable abbrev chiralKernelSliceMinus
    (X : KasparovCycle A B H) : Submodule ℝ H :=
  RealSplitKreinKasparovCycle.chiralKernelSliceMinus X

/-- Legacy finite-dimensional KK analytical index, implemented by the primitive owner. -/
@[rep_depth krein]
noncomputable abbrev analyticalIndex
    [FiniteDimensional ℝ H]
    (X : KasparovCycle A B H) : ℤ :=
  X.finiteAnalyticalIndex

@[rep_depth krein, simp] theorem analyticalIndex_eq_finiteAnalyticalIndex
    [FiniteDimensional ℝ H]
    (X : KasparovCycle A B H) :
    X.analyticalIndex = X.finiteAnalyticalIndex := rfl

end KasparovCycle

section LocalCompatibility

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]
variable (X : KasparovCycle A B H)

/-- Lemma `comm_compact_lie`. -/
@[rep_depth krein]
lemma comm_compact_lie (a : A) : IsCompactEnd H ⁅X.F, X.π a⁆ := by
  simpa [Ring.lie_def] using X.comm_compact a

/-- Lemma `superComm_compact_of_even_rep`. -/
@[rep_depth krein]
lemma superComm_compact_of_even_rep
    (_hπ_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (X.π a))
    (a : A) :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) X.F (X.π a)) := by
  exact X.superComm_pi_compact a

/--
NON-VACUOUS SPECTRAL BRIDGE:
If `F² = 1`, the finite-dimensional analytical index is constructively zero.
-/
@[rep_depth krein]
theorem index_bridge_spectral_zero [FiniteDimensional ℝ H]
    (hF : X.F * X.F = 1) :
    X.analyticalIndex = 0 := by
  have hSq : ∀ x : H, X.F (X.F x) = x := by
    intro x
    simpa using DFunLike.congr_fun hF x
  have hKer : LinearMap.ker X.F.toLinearMap = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    calc
      x = X.F (X.F x) := by symm; exact hSq x
      _ = X.F (X.F y) := by exact congrArg X.F hxy
      _ = y := hSq y
  have hSlicePlus :
      RealSplitKreinKasparovCycle.chiralKernelSlicePlus X = ⊥ := by
    unfold RealSplitKreinKasparovCycle.chiralKernelSlicePlus
    rw [hKer]
    simp
  have hSliceMinus :
      RealSplitKreinKasparovCycle.chiralKernelSliceMinus X = ⊥ := by
    unfold RealSplitKreinKasparovCycle.chiralKernelSliceMinus
    rw [hKer]
    simp
  unfold KasparovCycle.analyticalIndex RealSplitKreinKasparovCycle.finiteAnalyticalIndex
  rw [RealSplitKreinKasparovCycle.analyticalIndex_eq_finrank_chiralKernelDifference (X := X)]
  rw [hSlicePlus, hSliceMinus]
  simp

/--
The constant Dirac/grading family determined by a spectral bounded primitive
phase has invariant analytical index.
-/
@[rep_depth transport]
theorem index_bridge_spectral [FiniteDimensional ℝ H] :
    InfoGeometry.Canonical.AnalyticalIndex.IndexInvariantAlong
      (fun _ : ℝ => X.F.toLinearMap)
      (fun _ : ℝ => (KreinGradedModule.gradeCLM (H := H)).toLinearMap) := by
  intro s
  simp

/--
For a spectral primitive bounded phase (`F² = 1`), the constant Dirac/grading
family has zero analytical index at every point.
-/
@[rep_depth transport]
theorem index_bridge_spectral_zero_family [FiniteDimensional ℝ H]
    (hF : X.F * X.F = 1) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
        ((fun _ : ℝ => X.F.toLinearMap) s)
        ((fun _ : ℝ => (KreinGradedModule.gradeCLM (H := H)).toLinearMap) s)
        = 0 := by
  intro s
  calc
    InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
        ((fun _ : ℝ => X.F.toLinearMap) s)
        ((fun _ : ℝ => (KreinGradedModule.gradeCLM (H := H)).toLinearMap) s)
      =
        InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
          X.F.toLinearMap
          (KreinGradedModule.gradeCLM (H := H)).toLinearMap := by
            simp
    _ = X.analyticalIndex := by
          simp [KasparovCycle.analyticalIndex]
    _ = 0 := index_bridge_spectral_zero X hF

/--
Frontier materialization (candidate 1):
the spectral bridge yields explicit zero-index transport from the primitive seed.
-/
@[rep_depth transport]
theorem auto_index_bridge_spectral_from_seed_1 [FiniteDimensional ℝ H]
    (hF : X.F * X.F = 1) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
        ((fun _ : ℝ => X.F.toLinearMap) s)
        ((fun _ : ℝ => (KreinGradedModule.gradeCLM (H := H)).toLinearMap) s)
        = 0 := by
  intro s
  exact index_bridge_spectral_zero_family X hF s

/--
Transport the primitive finite-dimensional analytical index through any path
whose analytical index is already known to be invariant and whose baseline
agrees with the bounded Dirac/Fredholm data.
-/
@[rep_depth transport]
theorem analyticalIndex_eq_of_indexInvariantAlong [FiniteDimensional ℝ H]
    (D Γ : ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (hD0 : D 0 = X.F.toLinearMap)
    (hΓ0 : Γ 0 = (KreinGradedModule.gradeCLM (H := H)).toLinearMap)
    (hInv : InfoGeometry.Canonical.AnalyticalIndex.IndexInvariantAlong D Γ) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D s) (Γ s) =
        X.analyticalIndex := by
  intro s
  calc
    InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D s) (Γ s)
        =
          InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D 0) (Γ 0) := hInv s
    _ = InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
          X.F.toLinearMap
          (KreinGradedModule.gradeCLM (H := H)).toLinearMap := by
          rw [hD0, hΓ0]
    _ = X.analyticalIndex := by
          simp [KasparovCycle.analyticalIndex]

/--
Conjugacy-specialized transport of the primitive bounded analytical index.
-/
@[rep_depth transport]
theorem analyticalIndex_eq_of_conjugacy [FiniteDimensional ℝ H]
    (D Γ : ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (eFlow : ℝ → H ≃ₗ[ℝ] H)
    (hD0 : D 0 = X.F.toLinearMap)
    (hΓ0 : Γ 0 = (KreinGradedModule.gradeCLM (H := H)).toLinearMap)
    (hConj : InfoGeometry.Canonical.AnalyticalIndex.ChiralConjugacyAlong D Γ eFlow) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D s) (Γ s) =
        X.analyticalIndex := by
  exact analyticalIndex_eq_of_indexInvariantAlong
    (X := X)
    (D := D)
    (Γ := Γ)
    hD0
    hΓ0
    (InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_conjugacy
      (D := D) (Γ := Γ) (eFlow := eFlow) hConj)

/--
Modular/Clifford-transport specialization of the primitive bounded analytical
index bridge.
-/
@[rep_depth transport]
theorem analyticalIndex_eq_of_modularCliffordTransport [FiniteDimensional ℝ H]
    (D Γ : ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    {ι : Type*}
    (σ : ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (clAct : ι → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (unit : ι)
    (hD0 : D 0 = X.F.toLinearMap)
    (hΓ0 : Γ 0 = (KreinGradedModule.gradeCLM (H := H)).toLinearMap)
    (hTrans :
      InfoGeometry.Canonical.AnalyticalIndex.ChiralSliceModularCliffordTransportAlong
        (D := D) (Γ := Γ) σ clAct unit) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D s) (Γ s) =
        X.analyticalIndex := by
  exact analyticalIndex_eq_of_indexInvariantAlong
    (X := X)
    (D := D)
    (Γ := Γ)
    hD0
    hΓ0
    (InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_modularCliffordTransport
      (D := D) (Γ := Γ) (σ := σ) (clAct := clAct) (unit := unit) hTrans)

end LocalCompatibility

end InfoGeometry.KK
