import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.RicciMongeAmpere
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Topology.LocallyConstant.Basic
set_option linter.unnecessarySimpa false

open scoped TensorProduct

/-
This file formalizes a finite-dimensional kernel-slice asymmetry model for a
Dirac/grading pair. The split maps

`P₊ = (1/2) (Id + Γ)`, `P₋ = (1/2) (Id - Γ)`

are defined without imposing grading axioms. Under the additional Bott-Dirac
hypotheses `Γ ∘ Γ = Id` and `D ∘ Γ + Γ ∘ D = 0` (packaged in the Bott-Dirac
layer as `IsInvolutiveGrading Γ` and `IsChiralDirac D Γ` when the ambient space
is normed), they recover the usual projector/odd-Dirac interpretation.
-/

namespace InfoGeometry.Canonical.AnalyticalIndex

open InfoGeometry.Krein
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.RicciMongeAmpere

section Core

variable {V : Type*}
  [AddCommGroup V] [Module ℝ V]

/--
Formal positive chiral-splitting map `P₊ = (1/2)(Id + Γ)`.

If `Γ` satisfies `IsInvolutiveGrading`, then this becomes an idempotent
projector onto the positive grading sector.
-/
noncomputable def chiralProjectorPlus (Γ : Endomorphism V) : Endomorphism V :=
  ((1 / 2 : ℝ) • ((LinearMap.id : Endomorphism V) + Γ))

/--
Formal negative chiral-splitting map `P₋ = (1/2)(Id - Γ)`.

If `Γ` satisfies `IsInvolutiveGrading`, then this becomes an idempotent
projector onto the negative grading sector.
-/
noncomputable def chiralProjectorMinus (Γ : Endomorphism V) : Endomorphism V :=
  ((1 / 2 : ℝ) • ((LinearMap.id : Endomorphism V) - Γ))

/-- Formal positive chiral component `D⁺ := D ∘ P₊`. -/
noncomputable def chiralPartPlus (D Γ : Endomorphism V) : Endomorphism V :=
  D.comp (chiralProjectorPlus Γ)

/-- Formal negative chiral component `D⁻ := D ∘ P₋`. -/
noncomputable def chiralPartMinus (D Γ : Endomorphism V) : Endomorphism V :=
  D.comp (chiralProjectorMinus Γ)

/--
Formal positive kernel slice `ker(D) ∩ Im(P₊)`.

Under `IsInvolutiveGrading Γ` and `IsChiralDirac D Γ`, this is the usual
positive chiral kernel sector.
-/
noncomputable def chiralKernelSlicePlus (D Γ : Endomorphism V) : Submodule ℝ V :=
  LinearMap.ker D ⊓ LinearMap.range (chiralProjectorPlus Γ)

/--
Formal negative kernel slice `ker(D) ∩ Im(P₋)`.

Under `IsInvolutiveGrading Γ` and `IsChiralDirac D Γ`, this is the usual
negative chiral kernel sector.
-/
noncomputable def chiralKernelSliceMinus (D Γ : Endomorphism V) : Submodule ℝ V :=
  LinearMap.ker D ⊓ LinearMap.range (chiralProjectorMinus Γ)

/--
Finite-dimensional formal analytical-index model:
`Index(D) = dim(ker(D) ∩ Im(P₊)) - dim(ker(D) ∩ Im(P₋))`.

With `IsInvolutiveGrading Γ` and `IsChiralDirac D Γ`, this matches the usual
chiral kernel-asymmetry formula.
-/
noncomputable def analyticalIndex [FiniteDimensional ℝ V] (D Γ : Endomorphism V) : ℤ :=
  (Module.finrank ℝ (chiralKernelSlicePlus D Γ) : ℤ) -
    (Module.finrank ℝ (chiralKernelSliceMinus D Γ) : ℤ)

/-- Formal chiral-splitting identity: `D⁺ + D⁻ = D`. -/
lemma chiralPartPlus_add_chiralPartMinus (D Γ : Endomorphism V) :
    chiralPartPlus D Γ + chiralPartMinus D Γ = D := by
  ext v
  rw [show (chiralPartPlus D Γ + chiralPartMinus D Γ) v
        = D ((chiralProjectorPlus Γ + chiralProjectorMinus Γ) v) by
          simp [chiralPartPlus, chiralPartMinus, map_add]]
  have hproj :
      (chiralProjectorPlus Γ + chiralProjectorMinus Γ) v = v := by
    calc
      (chiralProjectorPlus Γ + chiralProjectorMinus Γ) v
          = (1 / 2 : ℝ) • (((LinearMap.id : Endomorphism V) + Γ) v) +
              (1 / 2 : ℝ) • (((LinearMap.id : Endomorphism V) - Γ) v) := by
                simp [chiralProjectorPlus, chiralProjectorMinus]
      _ = (1 / 2 : ℝ) •
            ((((LinearMap.id : Endomorphism V) + Γ) v) +
              (((LinearMap.id : Endomorphism V) - Γ) v)) := by
              rw [← smul_add]
      _ = (1 / 2 : ℝ) • (v + v) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • v := by
            simpa using (add_smul (1 / 2 : ℝ) (1 / 2 : ℝ) v).symm
      _ = (1 : ℝ) • v := by norm_num
      _ = v := by simp
  simp [hproj]

/--
Under `Γ ∘ Γ = Id`, `P₊` is an idempotent projector.
-/
lemma chiralProjectorPlus_comp_self_of_square_eq_id
    (Γ : Endomorphism V)
    (hΓSq : Γ.comp Γ = (LinearMap.id : Endomorphism V)) :
    (chiralProjectorPlus Γ).comp (chiralProjectorPlus Γ) = chiralProjectorPlus Γ := by
  ext v
  have hΓv : Γ (Γ v) = v := by
    have h := congrArg (fun T : Endomorphism V => T v) hΓSq
    simpa [LinearMap.comp_apply] using h
  have hSum :
      (v + Γ v) + (Γ v + v) = (2 : ℝ) • (v + Γ v) := by
    simpa [two_smul, smul_add, add_assoc, add_left_comm, add_comm]
  calc
    ((chiralProjectorPlus Γ).comp (chiralProjectorPlus Γ)) v
        = (1 / 2 : ℝ) • (((1 / 2 : ℝ) • (v + Γ v)) + ((1 / 2 : ℝ) • (Γ v + v))) := by
            simp [chiralProjectorPlus, LinearMap.comp_apply, map_add, map_smul, hΓv]
    _ = (1 / 2 : ℝ) • ((1 / 2 : ℝ) • ((v + Γ v) + (Γ v + v))) := by
          rw [← smul_add]
    _ = (1 / 2 : ℝ) • ((1 / 2 : ℝ) • ((2 : ℝ) • (v + Γ v))) := by rw [hSum]
    _ = (((1 / 2 : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ))) : ℝ) • (v + Γ v) := by
          simp [smul_smul]
    _ = (1 / 2 : ℝ) • (v + Γ v) := by norm_num
    _ = chiralProjectorPlus Γ v := by simp [chiralProjectorPlus]

/--
Under `Γ ∘ Γ = Id`, `P₋` is an idempotent projector.
-/
lemma chiralProjectorMinus_comp_self_of_square_eq_id
    (Γ : Endomorphism V)
    (hΓSq : Γ.comp Γ = (LinearMap.id : Endomorphism V)) :
    (chiralProjectorMinus Γ).comp (chiralProjectorMinus Γ) = chiralProjectorMinus Γ := by
  ext v
  have hΓv : Γ (Γ v) = v := by
    have h := congrArg (fun T : Endomorphism V => T v) hΓSq
    simpa [LinearMap.comp_apply] using h
  have hDiff :
      (v - Γ v) - (Γ v - v) = (2 : ℝ) • (v - Γ v) := by
    simp [sub_eq_add_neg, two_smul, smul_add, add_assoc, add_left_comm, add_comm]
  calc
    ((chiralProjectorMinus Γ).comp (chiralProjectorMinus Γ)) v
        = (1 / 2 : ℝ) • (((1 / 2 : ℝ) • (v - Γ v)) - ((1 / 2 : ℝ) • (Γ v - v))) := by
            simp [chiralProjectorMinus, LinearMap.comp_apply, map_sub, map_smul, hΓv]
    _ = (1 / 2 : ℝ) • ((1 / 2 : ℝ) • ((v - Γ v) - (Γ v - v))) := by
          rw [← smul_sub]
    _ = (1 / 2 : ℝ) • ((1 / 2 : ℝ) • ((2 : ℝ) • (v - Γ v))) := by rw [hDiff]
    _ = (((1 / 2 : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ))) : ℝ) • (v - Γ v) := by
          simp [smul_smul]
    _ = (1 / 2 : ℝ) • (v - Γ v) := by norm_num
    _ = chiralProjectorMinus Γ v := by simp [chiralProjectorMinus]

/--
If `D ∘ Γ + Γ ∘ D = 0`, then `D` carries the positive split into the negative
split: `D ∘ P₊ = P₋ ∘ D`.
-/
lemma chiralPartPlus_eq_projectorMinus_comp_of_anticommute
    (D Γ : Endomorphism V)
    (hAnti : D.comp Γ + Γ.comp D = 0) :
    chiralPartPlus D Γ = (chiralProjectorMinus Γ).comp D := by
  ext v
  have hAntiV : D (Γ v) + Γ (D v) = 0 := by
    have h := congrArg (fun T : Endomorphism V => T v) hAnti
    simpa [LinearMap.comp_apply, LinearMap.add_apply] using h
  have hDΓ : D (Γ v) = -Γ (D v) := by
    exact eq_neg_of_add_eq_zero_left hAntiV
  calc
    chiralPartPlus D Γ v = (1 / 2 : ℝ) • (D v + D (Γ v)) := by
      simp [chiralPartPlus, chiralProjectorPlus, LinearMap.comp_apply, map_add, map_smul]
    _ = (1 / 2 : ℝ) • (D v - Γ (D v)) := by rw [hDΓ, sub_eq_add_neg]
    _ = ((chiralProjectorMinus Γ).comp D) v := by
      simp [chiralProjectorMinus, LinearMap.comp_apply]

/--
If `D ∘ Γ + Γ ∘ D = 0`, then `D` carries the negative split into the positive
split: `D ∘ P₋ = P₊ ∘ D`.
-/
lemma chiralPartMinus_eq_projectorPlus_comp_of_anticommute
    (D Γ : Endomorphism V)
    (hAnti : D.comp Γ + Γ.comp D = 0) :
    chiralPartMinus D Γ = (chiralProjectorPlus Γ).comp D := by
  ext v
  have hAntiV : D (Γ v) + Γ (D v) = 0 := by
    have h := congrArg (fun T : Endomorphism V => T v) hAnti
    simpa [LinearMap.comp_apply, LinearMap.add_apply] using h
  have hDΓ : D (Γ v) = -Γ (D v) := by
    exact eq_neg_of_add_eq_zero_left hAntiV
  calc
    chiralPartMinus D Γ v = (1 / 2 : ℝ) • (D v - D (Γ v)) := by
      simp [chiralPartMinus, chiralProjectorMinus, LinearMap.comp_apply, map_sub, map_smul]
    _ = (1 / 2 : ℝ) • (D v + Γ (D v)) := by rw [hDΓ, sub_eq_add_neg, neg_neg]
    _ = ((chiralProjectorPlus Γ).comp D) v := by
      simp [chiralProjectorPlus, LinearMap.comp_apply]

/--
If both chiral parts coincide, the corresponding Dirac endomorphisms coincide.

This is exactly the identity `D = D ∘ P₊ + D ∘ P₋` with `P₊ + P₋ = Id`.
-/
lemma dirac_eq_of_chiralParts_eq
    (D Γ D' Γ' : Endomorphism V)
    (hplus : chiralPartPlus D Γ = chiralPartPlus D' Γ')
    (hminus : chiralPartMinus D Γ = chiralPartMinus D' Γ') :
    D = D' := by
  calc
    D = chiralPartPlus D Γ + chiralPartMinus D Γ := by
      symm
      exact chiralPartPlus_add_chiralPartMinus (D := D) (Γ := Γ)
    _ = chiralPartPlus D' Γ' + chiralPartMinus D' Γ' := by
      rw [hplus, hminus]
    _ = D' := chiralPartPlus_add_chiralPartMinus (D := D') (Γ := Γ')

/-- Lemma `analyticalIndex_eq_of_chiralParts_eq`. -/
lemma analyticalIndex_eq_of_chiralParts_eq
    [FiniteDimensional ℝ V]
    (D Γ D' Γ' : Endomorphism V)
    (hplus : chiralPartPlus D Γ = chiralPartPlus D' Γ')
    (hminus : chiralPartMinus D Γ = chiralPartMinus D' Γ')
    (hRangePlus :
      LinearMap.range (chiralProjectorPlus Γ) = LinearMap.range (chiralProjectorPlus Γ'))
    (hRangeMinus :
      LinearMap.range (chiralProjectorMinus Γ) = LinearMap.range (chiralProjectorMinus Γ')) :
    analyticalIndex D Γ = analyticalIndex D' Γ' := by
  have hD : D = D' := dirac_eq_of_chiralParts_eq D Γ D' Γ' hplus hminus
  subst hD
  unfold analyticalIndex chiralKernelSlicePlus chiralKernelSliceMinus
  rw [hRangePlus, hRangeMinus]

/-- Index invariance along a parameterized Dirac/grading family. -/
def IndexInvariantAlong [FiniteDimensional ℝ V] (D Γ : ℝ → Endomorphism V) : Prop :=
  ∀ s : ℝ, analyticalIndex (D s) (Γ s) = analyticalIndex (D 0) (Γ 0)

/--
Deformation data for index invariance: each chiral kernel slice at time `s` is
linearly equivalent to the baseline slice at `0`.
-/
def ChiralSliceIsoAlong [FiniteDimensional ℝ V] (D Γ : ℝ → Endomorphism V) : Prop :=
  (∀ s : ℝ,
      Nonempty
        ((chiralKernelSlicePlus (D s) (Γ s)) ≃ₗ[ℝ]
          (chiralKernelSlicePlus (D 0) (Γ 0))))
    ∧
  (∀ s : ℝ,
      Nonempty
        ((chiralKernelSliceMinus (D s) (Γ s)) ≃ₗ[ℝ]
          (chiralKernelSliceMinus (D 0) (Γ 0))))

/--
Algebraic deformation bridge:
if the positive/negative chiral slice dimensions are constant along the path,
then each slice is linearly equivalent to the baseline slice.
-/
theorem chiralSliceIsoAlong_of_const_finrank
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hPlus :
      ∀ s t : ℝ,
        Module.finrank ℝ (chiralKernelSlicePlus (D s) (Γ s)) =
          Module.finrank ℝ (chiralKernelSlicePlus (D t) (Γ t)))
    (hMinus :
      ∀ s t : ℝ,
        Module.finrank ℝ (chiralKernelSliceMinus (D s) (Γ s)) =
          Module.finrank ℝ (chiralKernelSliceMinus (D t) (Γ t))) :
    ChiralSliceIsoAlong D Γ := by
  refine ⟨?_, ?_⟩
  · intro s
    exact ⟨LinearEquiv.ofFinrankEq
      (chiralKernelSlicePlus (D s) (Γ s))
      (chiralKernelSlicePlus (D 0) (Γ 0))
      (hPlus s 0)⟩
  · intro s
    exact ⟨LinearEquiv.ofFinrankEq
      (chiralKernelSliceMinus (D s) (Γ s))
      (chiralKernelSliceMinus (D 0) (Γ 0))
      (hMinus s 0)⟩

/--
No-zero-crossing hypothesis on chiral kernel dimensions along a path.

This is the analytic frontier assumption needed to prevent kernel jumps:
continuity and grading anticommutation alone do not force this.
-/
def ChiralNoZeroCrossingAlong [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V) : Prop :=
  (∀ s t : ℝ,
      Module.finrank ℝ (chiralKernelSlicePlus (D s) (Γ s)) =
        Module.finrank ℝ (chiralKernelSlicePlus (D t) (Γ t)))
    ∧
  (∀ s t : ℝ,
      Module.finrank ℝ (chiralKernelSliceMinus (D s) (Γ s)) =
        Module.finrank ℝ (chiralKernelSliceMinus (D t) (Γ t)))

/--
Local no-zero-crossing condition at scale `s0`:
there is an open neighborhood where both chiral kernel finranks are fixed to
their value at `s0`.
-/
def ChiralNoZeroCrossingNear [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V) (s0 : ℝ) : Prop :=
  ∃ U : Set ℝ,
    IsOpen U ∧
    s0 ∈ U ∧
    (∀ s : ℝ, s ∈ U →
      Module.finrank ℝ (chiralKernelSlicePlus (D s) (Γ s)) =
        Module.finrank ℝ (chiralKernelSlicePlus (D s0) (Γ s0))) ∧
    (∀ s : ℝ, s ∈ U →
      Module.finrank ℝ (chiralKernelSliceMinus (D s) (Γ s)) =
        Module.finrank ℝ (chiralKernelSliceMinus (D s0) (Γ s0)))

/--
No-zero-eigenvalue-crossing near `s0`:
in an open neighborhood of `s0`, the Dirac endomorphism stays bijective.

This is the finite-dimensional zero-spectral-gap-at-origin condition.
-/
def ChiralNoZeroEigenCrossingNear [FiniteDimensional ℝ V]
    (D : ℝ → Endomorphism V) (s0 : ℝ) : Prop :=
  ∃ U : Set ℝ,
    IsOpen U ∧
    s0 ∈ U ∧
    (∀ s : ℝ, s ∈ U → Function.Bijective (D s))

/--
No-zero-eigenvalue-crossing implies local no-zero-crossing of chiral slice
dimensions.

This is the trivial-kernel branch of the local gap argument: bijectivity forces
`ker(D s) = 0`, so both chiral kernel slices vanish throughout the
neighborhood.
-/
theorem chiralNoZeroCrossingNear_of_noZeroEigenCrossingNear
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (s0 : ℝ)
    (hNoEig : ChiralNoZeroEigenCrossingNear D s0) :
    ChiralNoZeroCrossingNear D Γ s0 := by
  rcases hNoEig with ⟨U, hUOpen, hs0U, hBij⟩
  refine ⟨U, hUOpen, hs0U, ?_, ?_⟩
  · intro s hsU
    have hKerEqBot : LinearMap.ker (D s) = ⊥ := by
      exact LinearMap.ker_eq_bot.mpr (hBij s hsU).1
    have hKerEqBot0 : LinearMap.ker (D s0) = ⊥ := by
      exact LinearMap.ker_eq_bot.mpr (hBij s0 hs0U).1
    have hPlusZero :
        Module.finrank ℝ (chiralKernelSlicePlus (D s) (Γ s)) = 0 := by
      unfold chiralKernelSlicePlus
      rw [hKerEqBot]
      simp
    have hPlusZero0 :
        Module.finrank ℝ (chiralKernelSlicePlus (D s0) (Γ s0)) = 0 := by
      unfold chiralKernelSlicePlus
      rw [hKerEqBot0]
      simp
    exact hPlusZero.trans hPlusZero0.symm
  · intro s hsU
    have hKerEqBot : LinearMap.ker (D s) = ⊥ := by
      exact LinearMap.ker_eq_bot.mpr (hBij s hsU).1
    have hKerEqBot0 : LinearMap.ker (D s0) = ⊥ := by
      exact LinearMap.ker_eq_bot.mpr (hBij s0 hs0U).1
    have hMinusZero :
        Module.finrank ℝ (chiralKernelSliceMinus (D s) (Γ s)) = 0 := by
      unfold chiralKernelSliceMinus
      rw [hKerEqBot]
      simp
    have hMinusZero0 :
        Module.finrank ℝ (chiralKernelSliceMinus (D s0) (Γ s0)) = 0 := by
      unfold chiralKernelSliceMinus
      rw [hKerEqBot0]
      simp
    exact hMinusZero.trans hMinusZero0.symm

/--
Analytic frontier theorem (gap form):
if every scale has a neighborhood with no chiral zero crossing, then the pair
of chiral finranks is locally constant along the path.
-/
theorem chiralSlice_finrank_locallyConstant_of_gap
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hGap : ∀ s : ℝ, ChiralNoZeroCrossingNear D Γ s) :
    IsLocallyConstant
      (fun s : ℝ =>
        ( Module.finrank ℝ (chiralKernelSlicePlus (D s) (Γ s))
        , Module.finrank ℝ (chiralKernelSliceMinus (D s) (Γ s)) )) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s0
  rcases hGap s0 with ⟨U, hUOpen, hs0U, hPlusConst, hMinusConst⟩
  filter_upwards [hUOpen.mem_nhds hs0U] with s hsU
  exact Prod.ext (hPlusConst s hsU) (hMinusConst s hsU)

/--
Global no-zero-crossing along `ℝ` from the local gap condition.

Since `ℝ` is preconnected, local constancy of the finrank pair forces global
constancy.
-/
theorem chiralNoZeroCrossingAlong_of_gap
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hGap : ∀ s : ℝ, ChiralNoZeroCrossingNear D Γ s) :
    ChiralNoZeroCrossingAlong D Γ := by
  let f : ℝ → ℕ × ℕ := fun s =>
    ( Module.finrank ℝ (chiralKernelSlicePlus (D s) (Γ s))
    , Module.finrank ℝ (chiralKernelSliceMinus (D s) (Γ s)) )
  have hfLoc : IsLocallyConstant f :=
    chiralSlice_finrank_locallyConstant_of_gap (D := D) (Γ := Γ) hGap
  refine ⟨?_, ?_⟩
  · intro s t
    exact congrArg Prod.fst (hfLoc.apply_eq_of_preconnectedSpace s t)
  · intro s t
    exact congrArg Prod.snd (hfLoc.apply_eq_of_preconnectedSpace s t)

/-!
Theorem-level closure for slice transport currently requires the explicit
no-zero-crossing condition (constant `±` chiral-slice dimensions).

The stronger analytic theorem deriving this from continuity, grading, and a
spectral-gap condition is a separate frontier result.
-/
theorem chiralSliceIsoAlong_of_noZeroCrossing
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hNoCross : ChiralNoZeroCrossingAlong D Γ) :
    ChiralSliceIsoAlong D Γ := by
  rcases hNoCross with ⟨hPlus, hMinus⟩
  exact chiralSliceIsoAlong_of_const_finrank
    (D := D) (Γ := Γ) hPlus hMinus

/--
Topological invariance route in two proved steps:
gap neighborhood `⇒` global no-zero-crossing `⇒` chiral slice isomorphism.
-/
theorem chiralSliceIsoAlong_of_gap
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hGap : ∀ s : ℝ, ChiralNoZeroCrossingNear D Γ s) :
    ChiralSliceIsoAlong D Γ := by
  exact chiralSliceIsoAlong_of_noZeroCrossing
    (D := D) (Γ := Γ)
    (hNoCross := chiralNoZeroCrossingAlong_of_gap (D := D) (Γ := Γ) hGap)

/--
Direct zero-eigenvalue-crossing route:
local bijectivity of `D(s)` along the path implies chiral-slice transport
invariance.
-/
theorem chiralSliceIsoAlong_of_noZeroEigenCrossing
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hNoEig : ∀ s : ℝ, ChiralNoZeroEigenCrossingNear D s) :
    ChiralSliceIsoAlong D Γ := by
  apply chiralSliceIsoAlong_of_gap (D := D) (Γ := Γ)
  intro s
  exact chiralNoZeroCrossingNear_of_noZeroEigenCrossingNear
    (D := D) (Γ := Γ) (s0 := s) (hNoEig := hNoEig s)

/--
Path-level no-zero-eigenvalue-crossing closure:
chiral-slice isomorphism is derived via the no-zero-eigenvalue-crossing route.

This is not a continuity-only theorem: the local gap hypothesis is the precise
analytic protection condition currently formalized.
-/
theorem chiralSliceIsoAlong_of_noZeroEigenCrossing_path
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hNoEig : ∀ s : ℝ, ChiralNoZeroEigenCrossingNear D s) :
    ChiralSliceIsoAlong D Γ := by
  exact chiralSliceIsoAlong_of_noZeroEigenCrossing (D := D) (Γ := Γ) hNoEig

/--
Conjugacy data for a Dirac/grading family along a transport flow of linear
equivalences.
-/
def ChiralConjugacyAlong [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (eFlow : ℝ → V ≃ₗ[ℝ] V) : Prop :=
  (∀ s : ℝ, (D 0).comp (eFlow s).toLinearMap = (eFlow s).toLinearMap.comp (D s)) ∧
    (∀ s : ℝ, (Γ 0).comp (eFlow s).toLinearMap = (eFlow s).toLinearMap.comp (Γ s))

/-- Conjugacy transports kernels exactly along a linear equivalence. -/
lemma map_ker_eq_of_conjugacy
    (Ds D0 : Endomorphism V)
    (e : V ≃ₗ[ℝ] V)
    (hConj : D0.comp e.toLinearMap = e.toLinearMap.comp Ds) :
    (LinearMap.ker Ds).map e.toLinearMap = LinearMap.ker D0 := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨x, hx, rfl⟩
    change D0 (e x) = 0
    have hConjX : D0 (e x) = e (Ds x) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj x)
    rw [hConjX, hx, map_zero]
  · intro hv
    refine ⟨e.symm v, ?_, by simp⟩
    have hConjX : D0 (e (e.symm v)) = e (Ds (e.symm v)) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj (e.symm v))
    have hImageZero : e (Ds (e.symm v)) = 0 := by
      calc
        e (Ds (e.symm v)) = D0 (e (e.symm v)) := by simpa using hConjX.symm
        _ = D0 v := by simp
        _ = 0 := hv
    exact e.injective (by simpa using hImageZero)

/-- Conjugacy transports ranges exactly along a linear equivalence. -/
lemma map_range_eq_of_conjugacy
    (Ps P0 : Endomorphism V)
    (e : V ≃ₗ[ℝ] V)
    (hConj : P0.comp e.toLinearMap = e.toLinearMap.comp Ps) :
    (LinearMap.range Ps).map e.toLinearMap = LinearMap.range P0 := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨x, hx, rfl⟩
    rcases hx with ⟨y, rfl⟩
    refine ⟨e y, ?_⟩
    have hConjY : P0 (e y) = e (Ps y) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj y)
    simpa [hConjY]
  · intro hv
    rcases hv with ⟨x, rfl⟩
    refine ⟨Ps (e.symm x), ?_, ?_⟩
    · exact ⟨e.symm x, rfl⟩
    · have hConjX : P0 (e (e.symm x)) = e (Ps (e.symm x)) := by
        simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj (e.symm x))
      simpa using hConjX.symm

/-- Chiral projector `P₊` respects grading conjugacy. -/
lemma chiralProjectorPlus_comp_of_conjugacy
    (Γs Γ0 : Endomorphism V)
    (e : V ≃ₗ[ℝ] V)
    (hConj : Γ0.comp e.toLinearMap = e.toLinearMap.comp Γs) :
    (chiralProjectorPlus Γ0).comp e.toLinearMap =
      e.toLinearMap.comp (chiralProjectorPlus Γs) := by
  ext v
  have hConjV : Γ0 (e v) = e (Γs v) := by
    simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj v)
  simp [chiralProjectorPlus, LinearMap.comp_apply, hConjV, map_add, map_smul]

/-- Chiral projector `P₋` respects grading conjugacy. -/
lemma chiralProjectorMinus_comp_of_conjugacy
    (Γs Γ0 : Endomorphism V)
    (e : V ≃ₗ[ℝ] V)
    (hConj : Γ0.comp e.toLinearMap = e.toLinearMap.comp Γs) :
    (chiralProjectorMinus Γ0).comp e.toLinearMap =
      e.toLinearMap.comp (chiralProjectorMinus Γs) := by
  ext v
  have hConjV : Γ0 (e v) = e (Γs v) := by
    simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj v)
  simp [chiralProjectorMinus, LinearMap.comp_apply, hConjV, map_sub, map_smul]

/-- Conjugacy transports the positive chiral kernel slice exactly. -/
lemma map_chiralKernelSlicePlus_eq_of_conjugacy
    (D Γ : ℝ → Endomorphism V)
    (s : ℝ)
    (e : V ≃ₗ[ℝ] V)
    (hD : (D 0).comp e.toLinearMap = e.toLinearMap.comp (D s))
    (hΓ : (Γ 0).comp e.toLinearMap = e.toLinearMap.comp (Γ s)) :
    (chiralKernelSlicePlus (D s) (Γ s)).map e.toLinearMap =
      chiralKernelSlicePlus (D 0) (Γ 0) := by
  unfold chiralKernelSlicePlus
  calc
    (LinearMap.ker (D s) ⊓ LinearMap.range (chiralProjectorPlus (Γ s))).map e.toLinearMap
        =
      (LinearMap.ker (D s)).map e.toLinearMap ⊓
        (LinearMap.range (chiralProjectorPlus (Γ s))).map e.toLinearMap := by
          simpa using
            (Submodule.map_inf (f := e.toLinearMap)
              (p := LinearMap.ker (D s))
              (q := LinearMap.range (chiralProjectorPlus (Γ s)))
              e.injective)
    _ = LinearMap.ker (D 0) ⊓ LinearMap.range (chiralProjectorPlus (Γ 0)) := by
      rw [map_ker_eq_of_conjugacy (Ds := D s) (D0 := D 0) (e := e) hD,
        map_range_eq_of_conjugacy
          (Ps := chiralProjectorPlus (Γ s))
          (P0 := chiralProjectorPlus (Γ 0))
          (e := e)
          (chiralProjectorPlus_comp_of_conjugacy
            (Γs := Γ s) (Γ0 := Γ 0) (e := e) hΓ)]

/-- Conjugacy transports the negative chiral kernel slice exactly. -/
lemma map_chiralKernelSliceMinus_eq_of_conjugacy
    (D Γ : ℝ → Endomorphism V)
    (s : ℝ)
    (e : V ≃ₗ[ℝ] V)
    (hD : (D 0).comp e.toLinearMap = e.toLinearMap.comp (D s))
    (hΓ : (Γ 0).comp e.toLinearMap = e.toLinearMap.comp (Γ s)) :
    (chiralKernelSliceMinus (D s) (Γ s)).map e.toLinearMap =
      chiralKernelSliceMinus (D 0) (Γ 0) := by
  unfold chiralKernelSliceMinus
  calc
    (LinearMap.ker (D s) ⊓ LinearMap.range (chiralProjectorMinus (Γ s))).map e.toLinearMap
        =
      (LinearMap.ker (D s)).map e.toLinearMap ⊓
        (LinearMap.range (chiralProjectorMinus (Γ s))).map e.toLinearMap := by
          simpa using
            (Submodule.map_inf (f := e.toLinearMap)
              (p := LinearMap.ker (D s))
              (q := LinearMap.range (chiralProjectorMinus (Γ s)))
              e.injective)
    _ = LinearMap.ker (D 0) ⊓ LinearMap.range (chiralProjectorMinus (Γ 0)) := by
      rw [map_ker_eq_of_conjugacy (Ds := D s) (D0 := D 0) (e := e) hD,
        map_range_eq_of_conjugacy
          (Ps := chiralProjectorMinus (Γ s))
          (P0 := chiralProjectorMinus (Γ 0))
          (e := e)
          (chiralProjectorMinus_comp_of_conjugacy
            (Γs := Γ s) (Γ0 := Γ 0) (e := e) hΓ)]

/--
Conjugacy-to-iso bridge: if `D(s), Γ(s)` are conjugate to the baseline by a
linear-equivalence flow, then both chiral kernel slices are linearly equivalent
to their baseline slices.
-/
theorem chiralSliceIsoAlong_of_conjugacy
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (eFlow : ℝ → V ≃ₗ[ℝ] V)
    (hConj : ChiralConjugacyAlong D Γ eFlow) :
    ChiralSliceIsoAlong D Γ := by
  rcases hConj with ⟨hDConj, hΓConj⟩
  refine ⟨?_, ?_⟩
  · intro s
    let e := eFlow s
    let eMap :
        (chiralKernelSlicePlus (D s) (Γ s)) ≃ₗ[ℝ]
          ((chiralKernelSlicePlus (D s) (Γ s)).map e.toLinearMap) :=
      Submodule.equivMapOfInjective
        (f := e.toLinearMap) (i := e.injective)
        (p := chiralKernelSlicePlus (D s) (Γ s))
    have hMap :
        (chiralKernelSlicePlus (D s) (Γ s)).map e.toLinearMap =
          chiralKernelSlicePlus (D 0) (Γ 0) :=
      map_chiralKernelSlicePlus_eq_of_conjugacy
        (D := D) (Γ := Γ) (s := s) (e := e) (hD := hDConj s) (hΓ := hΓConj s)
    exact ⟨eMap.trans (LinearEquiv.ofEq _ _ hMap)⟩
  · intro s
    let e := eFlow s
    let eMap :
        (chiralKernelSliceMinus (D s) (Γ s)) ≃ₗ[ℝ]
          ((chiralKernelSliceMinus (D s) (Γ s)).map e.toLinearMap) :=
      Submodule.equivMapOfInjective
        (f := e.toLinearMap) (i := e.injective)
        (p := chiralKernelSliceMinus (D s) (Γ s))
    have hMap :
        (chiralKernelSliceMinus (D s) (Γ s)).map e.toLinearMap =
          chiralKernelSliceMinus (D 0) (Γ 0) :=
      map_chiralKernelSliceMinus_eq_of_conjugacy
        (D := D) (Γ := Γ) (s := s) (e := e) (hD := hDConj s) (hΓ := hΓConj s)
    exact ⟨eMap.trans (LinearEquiv.ofEq _ _ hMap)⟩

/--
Modular-flow / Clifford-bundle transport hypothesis for the chiral kernel slices.

At each scale `s`, transport by `σ s` and Clifford action `clAct ℓ` sends the
`±` chiral kernel slice at `s` to the baseline slice at `0`. The designated
`unit` Clifford label acts as identity. The stronger `∀ ℓ` transport data is
stored for higher-level capstone packaging, while the basic deformation bridge
only uses the `unit` branch.
-/
def ChiralSliceModularCliffordTransportAlong
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι) : Prop :=
  clAct unit = LinearMap.id ∧
    (∀ s : ℝ, Function.Injective (σ s)) ∧
    (∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSlicePlus (D s) (Γ s)).map ((clAct ℓ).comp (σ s))
        = chiralKernelSlicePlus (D 0) (Γ 0)) ∧
    (∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSliceMinus (D s) (Γ s)).map ((clAct ℓ).comp (σ s))
        = chiralKernelSliceMinus (D 0) (Γ 0))

/--
Unit-transport bridge: the distinguished Clifford branch already suffices to
transport the chiral slices to the baseline.
-/
theorem chiralSliceIsoAlong_of_modularCliffordUnitTransport
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι)
    (hUnit : clAct unit = LinearMap.id)
    (hσInj : ∀ s : ℝ, Function.Injective (σ s))
    (hPlusUnitMap : ∀ s : ℝ,
      (chiralKernelSlicePlus (D s) (Γ s)).map ((clAct unit).comp (σ s))
        = chiralKernelSlicePlus (D 0) (Γ 0))
    (hMinusUnitMap : ∀ s : ℝ,
      (chiralKernelSliceMinus (D s) (Γ s)).map ((clAct unit).comp (σ s))
        = chiralKernelSliceMinus (D 0) (Γ 0)) :
    ChiralSliceIsoAlong D Γ := by
  refine ⟨?_, ?_⟩
  · intro s
    let f : Endomorphism V := (clAct unit).comp (σ s)
    have hf : Function.Injective f := by
      intro x y hxy
      have hxy' : (σ s) x = (σ s) y := by
        simpa [f, hUnit] using hxy
      exact hσInj s hxy'
    let eMap :
        (chiralKernelSlicePlus (D s) (Γ s)) ≃ₗ[ℝ]
          ((chiralKernelSlicePlus (D s) (Γ s)).map f) :=
      Submodule.equivMapOfInjective
        (f := f) (i := hf) (p := chiralKernelSlicePlus (D s) (Γ s))
    have hEq :
        (chiralKernelSlicePlus (D s) (Γ s)).map f
          = chiralKernelSlicePlus (D 0) (Γ 0) := by
      simpa [f] using hPlusUnitMap s
    exact ⟨eMap.trans (LinearEquiv.ofEq _ _ hEq)⟩
  · intro s
    let f : Endomorphism V := (clAct unit).comp (σ s)
    have hf : Function.Injective f := by
      intro x y hxy
      have hxy' : (σ s) x = (σ s) y := by
        simpa [f, hUnit] using hxy
      exact hσInj s hxy'
    let eMap :
        (chiralKernelSliceMinus (D s) (Γ s)) ≃ₗ[ℝ]
          ((chiralKernelSliceMinus (D s) (Γ s)).map f) :=
      Submodule.equivMapOfInjective
        (f := f) (i := hf) (p := chiralKernelSliceMinus (D s) (Γ s))
    have hEq :
        (chiralKernelSliceMinus (D s) (Γ s)).map f
          = chiralKernelSliceMinus (D 0) (Γ 0) := by
      simpa [f] using hMinusUnitMap s
    exact ⟨eMap.trans (LinearEquiv.ofEq _ _ hEq)⟩

/--
Transport-to-iso bridge: modular/Clifford transport of the chiral slices yields
the deformation-style slice isomorphisms used by index invariance.
-/
theorem chiralSliceIsoAlong_of_modularCliffordTransport
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι)
    (hTrans : ChiralSliceModularCliffordTransportAlong (D := D) (Γ := Γ) σ clAct unit) :
    ChiralSliceIsoAlong D Γ := by
  rcases hTrans with ⟨hUnit, hσInj, hPlusMap, hMinusMap⟩
  exact chiralSliceIsoAlong_of_modularCliffordUnitTransport
    (D := D) (Γ := Γ) (σ := σ) (clAct := clAct) (unit := unit)
    hUnit hσInj (fun s => hPlusMap s unit) (fun s => hMinusMap s unit)

/--
Slice-transport invariance implies analytical-index invariance.
-/
theorem indexInvariantAlong_of_chiralSliceIsoAlong
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hIso : ChiralSliceIsoAlong D Γ) :
    IndexInvariantAlong D Γ := by
  intro s
  rcases hIso.1 s with ⟨ePlus⟩
  rcases hIso.2 s with ⟨eMinus⟩
  have hPlusFinrank :
      Module.finrank ℝ (chiralKernelSlicePlus (D s) (Γ s)) =
        Module.finrank ℝ (chiralKernelSlicePlus (D 0) (Γ 0)) :=
    ePlus.finrank_eq
  have hMinusFinrank :
      Module.finrank ℝ (chiralKernelSliceMinus (D s) (Γ s)) =
        Module.finrank ℝ (chiralKernelSliceMinus (D 0) (Γ 0)) :=
    eMinus.finrank_eq
  unfold analyticalIndex
  simp [hPlusFinrank, hMinusFinrank]

/--
Index invariance as a direct consequence of no zero-eigenvalue crossing.
-/
theorem indexInvariantAlong_of_noZeroEigenCrossing
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hNoEig : ∀ s : ℝ, ChiralNoZeroEigenCrossingNear D s) :
    IndexInvariantAlong D Γ := by
  exact indexInvariantAlong_of_chiralSliceIsoAlong
    (D := D) (Γ := Γ)
    (chiralSliceIsoAlong_of_noZeroEigenCrossing (D := D) (Γ := Γ) hNoEig)

/--
Path-level no-zero-eigenvalue-crossing index invariance:
obtained from no-zero-eigenvalue crossing along the path.
-/
theorem indexInvariantAlong_of_noZeroEigenCrossing_path
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hNoEig : ∀ s : ℝ, ChiralNoZeroEigenCrossingNear D s) :
    IndexInvariantAlong D Γ := by
  exact indexInvariantAlong_of_noZeroEigenCrossing (D := D) (Γ := Γ) hNoEig

/-- Index invariance from flow-conjugacy of the Dirac/grading family. -/
theorem indexInvariantAlong_of_conjugacy
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (eFlow : ℝ → V ≃ₗ[ℝ] V)
    (hConj : ChiralConjugacyAlong D Γ eFlow) :
    IndexInvariantAlong D Γ := by
  exact indexInvariantAlong_of_chiralSliceIsoAlong
    (D := D) (Γ := Γ)
    (chiralSliceIsoAlong_of_conjugacy (D := D) (Γ := Γ) (eFlow := eFlow) hConj)

/--
Direct deformation invariance route:
modular-flow / Clifford-bundle transport of chiral slices implies analytical
index invariance along the full family.
-/
theorem indexInvariantAlong_of_modularCliffordTransport
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι)
    (hTrans : ChiralSliceModularCliffordTransportAlong (D := D) (Γ := Γ) σ clAct unit) :
    IndexInvariantAlong D Γ := by
  exact indexInvariantAlong_of_chiralSliceIsoAlong
    (D := D) (Γ := Γ)
    (chiralSliceIsoAlong_of_modularCliffordTransport
      (D := D) (Γ := Γ) (σ := σ) (clAct := clAct) (unit := unit) hTrans)

/--
Direct primitive-hypothesis form of modular/Clifford transport invariance:
no bundled transport witness is required.
-/
theorem indexInvariantAlong_of_modularCliffordTransport_components
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι)
    (hUnit : clAct unit = LinearMap.id)
    (hσInj : ∀ s : ℝ, Function.Injective (σ s))
    (hPlusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSlicePlus (D s) (Γ s)).map ((clAct ℓ).comp (σ s))
        = chiralKernelSlicePlus (D 0) (Γ 0))
    (hMinusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSliceMinus (D s) (Γ s)).map ((clAct ℓ).comp (σ s))
        = chiralKernelSliceMinus (D 0) (Γ 0)) :
    IndexInvariantAlong D Γ := by
  exact indexInvariantAlong_of_modularCliffordTransport
    (D := D) (Γ := Γ) (σ := σ) (clAct := clAct) (unit := unit)
    (hTrans := ⟨hUnit, hσInj, hPlusMap, hMinusMap⟩)

end Core

section Bott

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
Formal global split map on the Bott tensor space: `Γ_bott = Γ₁ ⊗ Γₙ`.

When the tensor factors satisfy the corresponding grading hypotheses, this is
the global Bott grading.
-/
def globalGrading (Γ1 : Endomorphism E) (Γn : Endomorphism F) :
    Endomorphism (E ⊗[ℝ] F) :=
  TensorProduct.map Γ1 Γn

/--
Formal analytical index of the Bott-Dirac operator with the chosen tensor split
map.
-/
noncomputable def bottAnalyticalIndex
    [FiniteDimensional ℝ (E ⊗[ℝ] F)]
    (D1 Γ1 : Endomorphism E) (Dn Γn : Endomorphism F) : ℤ :=
  analyticalIndex (bottDirac D1 Γ1 Dn) (globalGrading Γ1 Γn)

/--
`Cl(1,1)` specialization of the formal global split map.

This is a genuine global grading when the second factor carries the appropriate
grading structure.
-/
noncomputable def cl11GlobalGrading (Γn : Endomorphism F) :
    Endomorphism (DoubledSpace E ⊗[ℝ] F) :=
  globalGrading (cl11Grading (E := E)) Γn

/-- `Cl(1,1)` specialization of the formal Bott analytical index. -/
noncomputable def cl11BottAnalyticalIndex
    [FiniteDimensional ℝ (DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : Endomorphism F) : ℤ :=
  analyticalIndex
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn)
    (cl11GlobalGrading (E := E) Γn)

end Bott

section Laplacian

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Vanishing condition for the split Bott Laplacian term. -/
def Cl11BottLaplacianZero (Dn : Endomorphism F) : Prop :=
  cl11BottLaplacian (E := E) Dn = 0

/-- Theorem `cl11_bottDirac_sq_eq_zero_of_laplacian_zero`. -/
theorem cl11_bottDirac_sq_eq_zero_of_laplacian_zero
    (Dn : Endomorphism F)
    (hZero : Cl11BottLaplacianZero (E := E) Dn) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn) = 0 := by
  exact (cl11_bottDirac_sq_eq_cl11BottLaplacian (E := E) (F := F) (Dn := Dn)).trans hZero

end Laplacian

section CoupledInvariant

variable (n : Nat)
variable {X V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/--
Coupled invariant package:
thermodynamic Sinkhorn control, scalar-Ricci fixed-point collapse, and
analytical index invariance along a Dirac/grading family.
-/
def SinkhornRicciIndexInvariant
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V) : Prop :=
  (∀ k : Nat, ∀ label : PermMode n → CliffordLabel,
    trajectoryLyapunovNext n T.traj k ≤ trajectoryLyapunov n T.traj k ∧
      trajectorySelectedRoutingEpsilon n T (k + 1) label ≤ 1)
    ∧ (∀ s : ℝ, flow s = 0)
    ∧ IndexInvariantAlong D Γ

/--
Canonical constructor for the coupled invariant package from its three proved
components.
-/
theorem sinkhornRicciIndexInvariant_of_components
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (hSinkhorn : ∀ k : Nat, ∀ label : PermMode n → CliffordLabel,
      trajectoryLyapunovNext n T.traj k ≤ trajectoryLyapunov n T.traj k ∧
        trajectorySelectedRoutingEpsilon n T (k + 1) label ≤ 1)
    (hRicciZero : ∀ s : ℝ, flow s = 0)
    (hIndex : IndexInvariantAlong D Γ) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  exact ⟨hSinkhorn, hRicciZero, hIndex⟩

/--
Derived constructor using modular-flow / Clifford-bundle transport hypotheses
for the chiral slices.
-/
theorem sinkhornRicciIndexInvariant_of_modularCliffordTransport_state_hypotheses
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hTrans :
      ChiralSliceModularCliffordTransportAlong (D := D) (Γ := Γ) σ clAct unit) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  refine sinkhornRicciIndexInvariant_of_components
    (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
    ?_ ?_ ?_
  · intro k label
    exact sinkhorn_dynamics_step_control (n := n) T k label
  · exact normalizedKaehlerRicci_fixedpoint_eq_zero
      (E := X) flow hNorm hFixed
  · exact indexInvariantAlong_of_modularCliffordTransport
      (D := D) (Γ := Γ) (σ := σ) (clAct := clAct) (unit := unit) hTrans

/--
Primitive-hypothesis form of the coupled Sinkhorn/Ricci/index invariant:
modular/Clifford transport is supplied as explicit component equalities.
-/
theorem sinkhornRicciIndexInvariant_of_modularCliffordTransport_components_state_hypotheses
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hUnit : clAct unit = LinearMap.id)
    (hσInj : ∀ s : ℝ, Function.Injective (σ s))
    (hPlusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSlicePlus (D s) (Γ s)).map ((clAct ℓ).comp (σ s))
        = chiralKernelSlicePlus (D 0) (Γ 0))
    (hMinusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSliceMinus (D s) (Γ s)).map ((clAct ℓ).comp (σ s))
        = chiralKernelSliceMinus (D 0) (Γ 0)) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  refine sinkhornRicciIndexInvariant_of_components
    (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
    ?_ ?_ ?_
  · intro k label
    exact sinkhorn_dynamics_step_control (n := n) T k label
  · exact normalizedKaehlerRicci_fixedpoint_eq_zero
      (E := X) flow hNorm hFixed
  · exact indexInvariantAlong_of_modularCliffordTransport_components
      (D := D) (Γ := Γ) (σ := σ) (clAct := clAct) (unit := unit)
      hUnit hσInj hPlusMap hMinusMap

/--
Derived constructor using primitive flow-conjugacy hypotheses:
the Dirac/grading family is transported to baseline by linear equivalences.
-/
theorem sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (eFlow : ℝ → V ≃ₗ[ℝ] V)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hConj : ChiralConjugacyAlong D Γ eFlow) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  refine sinkhornRicciIndexInvariant_of_components
    (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
    ?_ ?_ ?_
  · intro k label
    exact sinkhorn_dynamics_step_control (n := n) T k label
  · exact normalizedKaehlerRicci_fixedpoint_eq_zero
      (E := X) flow hNorm hFixed
  · exact indexInvariantAlong_of_conjugacy
      (D := D) (Γ := Γ) (eFlow := eFlow) hConj

end CoupledInvariant

section KMSCapstone

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
Explicit thermodynamic KMS capstone package:
exact KMS closure at each next step.
-/
def SinkhornKMSCapstone
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornKMSClosure n T K ω β

/-- Lemma `SinkhornKMSCapstone`. -/
lemma SinkhornKMSCapstone.kmsState
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : SinkhornKMSCapstone n T K ω β) :
    SinkhornKMSClosure n T K ω β :=
  hCap

/--
Constructive iterate specialization from closure (primary closure-first form).
-/
theorem sinkhornIterate_sinkhornKMSCapstone_of_closure
    (M0 : SinkhornMatrix n)
    (hrow : ∀ M : SinkhornMatrix n, HasPositiveRowSums n M)
    (hcol : ∀ M : SinkhornMatrix n, HasPositiveColSums n M)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hClosure : SinkhornKMSClosure n
      (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β) :
    SinkhornKMSCapstone n (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β := by
  exact hClosure

end KMSCapstone

section FullCapstone

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Fth] [InnerProductSpace ℝ Fth] [CompleteSpace Fth]

/--
Full capstone package:
thermodynamic/KMS control + geometric fixed-point collapse + index invariance.
-/
def FullThermoGeoIndexCapstone
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornRicciIndexInvariant n T flow D Γ ∧
    SinkhornKMSCapstone n T.traj K ω β

/--
Canonical constructor for the full capstone package from the two state-level
components.
-/
theorem fullThermoGeoIndexCapstone_of_states
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hGeoAlg : SinkhornRicciIndexInvariant n T flow D Γ)
    (hClosure : SinkhornKMSClosure n T.traj K ω β) :
    FullThermoGeoIndexCapstone n T flow D Γ K ω β := by
  exact ⟨hGeoAlg, hClosure⟩

/-- Lemma `FullThermoGeoIndexCapstone`. -/
lemma FullThermoGeoIndexCapstone.geometricAlgebraicState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : FullThermoGeoIndexCapstone n T flow D Γ K ω β) :
    SinkhornRicciIndexInvariant n T flow D Γ :=
  hCap.1

/-- Lemma `FullThermoGeoIndexCapstone`. -/
lemma FullThermoGeoIndexCapstone.thermodynamicKMSState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : FullThermoGeoIndexCapstone n T flow D Γ K ω β) :
    SinkhornKMSClosure n T.traj K ω β :=
  hCap.2

end FullCapstone

section UnifiedNaming

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Fth] [InnerProductSpace ℝ Fth] [CompleteSpace Fth]

/--
Unified thermodynamic state naming used by higher-level synthesis modules.
-/
abbrev ThermodynamicKMSState
    (T : DoublyStochasticSinkhornTrajectory n)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornKMSClosure n T.traj K ω β

/--
Unified geometric-algebraic state naming used by higher-level synthesis modules.
-/
abbrev GeometricAlgebraicState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V) : Prop :=
  SinkhornRicciIndexInvariant n T flow D Γ

/--
Unified full capstone naming used by higher-level synthesis modules.
-/
abbrev ThermoGeoIndexCapstoneState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  FullThermoGeoIndexCapstone n T flow D Γ K ω β

end UnifiedNaming

end InfoGeometry.Canonical.AnalyticalIndex
