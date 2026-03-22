import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.Canonical.AnalyticalIndex
import Mathlib.Algebra.Lie.OfAssociative

open scoped InnerProductSpace

namespace InfoGeometry.KK

open InfoGeometry.Krein

open InfoGeometry.Canonical.AnalyticalIndex

/--
Compatibility bounded Kasparov-cycle interface over a graded Krein module.

This is a forgetful compatibility layer relative to the richer primitive real
split-Krein cycle surface. It keeps only the bounded odd phase and the algebra
compactness axioms needed by the current KK facade.
-/
structure KasparovCycle
    (A B H : Type*)
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] where
  /-- Left representation of `A`. -/
  π : A →ₐ[ℝ] EndH H
  /-- Secondary representation of `B` (right-action refinement can be layered later). -/
  ρ : B →ₐ[ℝ] EndH H
  /-- Bounded odd phase / Fredholm operator. -/
  F : EndH H
  /-- Oddness with respect to the grading involution. -/
  F_odd : KreinGradedModule.IsOdd (H := H) F
  /-- Krein skew-adjointness of `F` (corresponds to Hilbert self-adjointness for odd operators). -/
  F_skewAdj : KreinSpace.IsKreinSkewAdjoint (H := H) F
  /-- `F² - 1` is compact. -/
  F_sq_one_compact : IsCompactEnd H (F * F - (1 : EndH H))
  /-- Graded commutator condition (even algebra reps => ordinary commutator). -/
  comm_compact : ∀ a : A, IsCompactEnd H (F * (π a) - (π a) * F)

namespace RealSplitKreinKasparovCycle

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/-- Forget the split-`Cl(1,1)` data and keep the bounded KK compatibility surface. -/
noncomputable def toKasparovCycle
    (X : RealSplitKreinKasparovCycle A B H) :
    KasparovCycle A B H where
  π := X.π
  ρ := X.ρ
  F := X.F
  F_odd := X.F_odd
  F_skewAdj := X.F_skewAdj
  F_sq_one_compact := X.F_sq_one_compact
  comm_compact := X.comm_compact

end RealSplitKreinKasparovCycle

section
variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]
variable (X : KasparovCycle A B H)

/--
The analytical index of a finite-dimensional Kasparov cycle.
The odd operator F acts as the Dirac operator for the index calculation.
-/
noncomputable def KasparovCycle.analyticalIndex [FiniteDimensional ℝ H] : ℤ :=
  InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
    X.F.toLinearMap
    (KreinGradedModule.gradeCLM (H := H)).toLinearMap

/-- Lemma `comm_compact_lie`. -/
lemma comm_compact_lie (a : A) : IsCompactEnd H ⁅X.F, X.π a⁆ := by
  simpa [Ring.lie_def] using X.comm_compact a

/-- Lemma `superComm_compact_of_even_rep`. -/
lemma superComm_compact_of_even_rep
    (hπ_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (X.π a))
    (a : A) :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) X.F (X.π a)) := by
  have hsuper :
      KreinGradedModule.superComm (H := H) X.F (X.π a)
        = KreinGradedModule.comm (H := H) X.F (X.π a) :=
    KreinGradedModule.superComm_odd_even (H := H) X.F_odd (hπ_even a)
  rw [hsuper]
  simpa [KreinGradedModule.comm] using X.comm_compact a

/--
NON-VACUOUS SPECTRAL BRIDGE:
If `F² = 1`, the analytical index is constructively zero.
This replaces the thin invariance statement with a direct derivation from 
the operator identity.
-/
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
      chiralKernelSlicePlus X.F.toLinearMap (KreinGradedModule.gradeCLM (H := H)).toLinearMap = ⊥ := by
    unfold chiralKernelSlicePlus
    rw [hKer]
    simp
  have hSliceMinus :
      chiralKernelSliceMinus X.F.toLinearMap (KreinGradedModule.gradeCLM (H := H)).toLinearMap = ⊥ := by
    unfold chiralKernelSliceMinus
    rw [hKer]
    simp
  unfold KasparovCycle.analyticalIndex analyticalIndex
  rw [hSlicePlus, hSliceMinus]
  simp

/--
The constant Dirac/grading family determined by a spectral Kasparov phase
has invariant (zero) analytical index.
-/
theorem index_bridge_spectral [FiniteDimensional ℝ H] :
    InfoGeometry.Canonical.AnalyticalIndex.IndexInvariantAlong
      (fun _ : ℝ => X.F.toLinearMap)
      (fun _ : ℝ => (KreinGradedModule.gradeCLM (H := H)).toLinearMap) := by
  intro s
  simp

/--
REFINED SPECTRAL INDEX BRIDGE:
For a spectral Kasparov phase (F² = 1), the constant Dirac/grading family
has zero analytical index at every point, derived from the constructive
spectral bridge.
-/
theorem index_bridge_spectral_zero_family [FiniteDimensional ℝ H]
    (hF : X.F * X.F = 1) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
        ((fun _ : ℝ => X.F.toLinearMap) s)
        ((fun _ : ℝ => (KreinGradedModule.gradeCLM (H := H)).toLinearMap) s)
        = 0 := by
  intro s
  simp only
  exact index_bridge_spectral_zero X hF

/--
Frontier materialization (candidate 1):
the spectral bridge yields explicit zero-index transport from the Kasparov seed.
-/
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
Transport the KK analytical index through any path whose analytical index is
already known to be invariant and whose baseline agrees with the Kasparov data.
-/
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
          rfl

/--
Conjugacy-specialized transport of the KK analytical index.
-/
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
Modular/Clifford-transport specialization of the KK analytical index bridge.
-/
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

end

end InfoGeometry.KK
