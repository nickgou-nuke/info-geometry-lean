import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.ChiralAnomaly
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
This file formalizes the chiral analytical-index trunk: chiral projectors,
kernel slices, index invariance under transport/conjugacy, and the Bott/Cl(1,1)
specializations built from that core.
-/

namespace InfoGeometry.Canonical.AnalyticalIndex

open InfoGeometry.Krein
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.ChiralAnomaly

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

section Cartan

open InfoGeometry.Canonical.BogoliubovTransport

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Exact doubled-space linear equivalence carried by the local Cartan exponential
`KRotation t = exp(tK)`.
-/
noncomputable def KRotationLE (t : ℝ) : DoubledSpace E ≃ₗ[ℝ] DoubledSpace E :=
  LinearEquiv.ofLinear
    (KRotation (E := E) t).toLinearMap
    (KRotation (E := E) (-t)).toLinearMap
    (by
      apply LinearMap.ext
      intro x
      change KRotation (E := E) t (KRotation (E := E) (-t) x) = x
      have hInv :
          KRotation (E := E) t * KRotation (E := E) (-t)
            = (1 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
        simpa using (KRotation_add (E := E) t (-t)).symm
      exact congrArg (fun f : DoubledSpace E →L[ℝ] DoubledSpace E => f x) hInv)
    (by
      apply LinearMap.ext
      intro x
      change KRotation (E := E) (-t) (KRotation (E := E) t x) = x
      have hInv :
          KRotation (E := E) (-t) * KRotation (E := E) t
            = (1 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
        simpa using (KRotation_add (E := E) (-t) t).symm
      exact congrArg (fun f : DoubledSpace E →L[ℝ] DoubledSpace E => f x) hInv)

@[simp] lemma KRotationLE_apply (t : ℝ) (x : DoubledSpace E) :
    KRotationLE (E := E) t x = KRotation (E := E) t x := rfl

@[simp] lemma KRotationLE_symm_apply (t : ℝ) (x : DoubledSpace E) :
    (KRotationLE (E := E) t).symm x = KRotation (E := E) (-t) x := rfl

/--
Exact Cartan exponential transport of an endomorphism:
`A(t) = exp(-tK) A exp(tK)`.
-/
noncomputable def cartanConjugate
    (A : Endomorphism (DoubledSpace E)) (t : ℝ) :
    Endomorphism (DoubledSpace E) :=
  (KRotationLE (E := E) t).symm.toLinearMap.comp
    (A.comp (KRotationLE (E := E) t).toLinearMap)

/--
The exact Cartan exponential transport `A(t) = exp(-tK) A exp(tK)` is
conjugate to the baseline seed by `exp(tK)`.
-/
theorem cartanConjugate_comp_KRotationLE
    (A : Endomorphism (DoubledSpace E)) (t : ℝ) :
    A.comp (KRotationLE (E := E) t).toLinearMap =
      (KRotationLE (E := E) t).toLinearMap.comp (cartanConjugate (E := E) A t) := by
  apply LinearMap.ext
  intro x
  change A ((KRotationLE (E := E) t) x) =
    (KRotationLE (E := E) t) ((KRotationLE (E := E) t).symm (A ((KRotationLE (E := E) t) x)))
  exact ((KRotationLE (E := E) t).apply_symm_apply (A ((KRotationLE (E := E) t) x))).symm

@[simp] theorem cartanConjugate_zero
    (A : Endomorphism (DoubledSpace E)) :
    cartanConjugate (E := E) A 0 = A := by
  apply LinearMap.ext
  intro x
  simp [cartanConjugate]

/--
Exact Cartan exponential transport furnishes a chiral conjugacy family on the
doubled carrier. The only local coordinate is the exponential time parameter.
-/
theorem chiralConjugacyAlong_of_cartanConjugate
    [FiniteDimensional ℝ (DoubledSpace E)]
    (D0 Γ0 : Endomorphism (DoubledSpace E)) :
    ChiralConjugacyAlong
      (fun t => cartanConjugate (E := E) D0 t)
      (fun t => cartanConjugate (E := E) Γ0 t)
      (fun t => KRotationLE (E := E) t) := by
  constructor
  · intro t
    simpa using cartanConjugate_comp_KRotationLE (E := E) D0 t
  · intro t
    simpa using cartanConjugate_comp_KRotationLE (E := E) Γ0 t

/--
Analytical-index invariance along the exact local Cartan exponential corridor.
-/
theorem indexInvariantAlong_of_cartanConjugate
    [FiniteDimensional ℝ (DoubledSpace E)]
    (D0 Γ0 : Endomorphism (DoubledSpace E)) :
    IndexInvariantAlong
      (fun t => cartanConjugate (E := E) D0 t)
      (fun t => cartanConjugate (E := E) Γ0 t) := by
  exact indexInvariantAlong_of_conjugacy
    (D := fun t => cartanConjugate (E := E) D0 t)
    (Γ := fun t => cartanConjugate (E := E) Γ0 t)
    (eFlow := fun t => KRotationLE (E := E) t)
    (hConj := chiralConjugacyAlong_of_cartanConjugate (E := E) D0 Γ0)

/--
Pointwise analytical-index invariance along exact Cartan exponential transport.
-/
theorem analyticalIndex_eq_zero_time_of_cartanConjugate
    [FiniteDimensional ℝ (DoubledSpace E)]
    (D0 Γ0 : Endomorphism (DoubledSpace E))
    (t : ℝ) :
    analyticalIndex
      (cartanConjugate (E := E) D0 t)
      (cartanConjugate (E := E) Γ0 t)
      =
    analyticalIndex D0 Γ0 := by
  simpa using indexInvariantAlong_of_cartanConjugate (E := E) D0 Γ0 t

end Cartan

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
  globalGrading ((InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)).eps.toLinearMap) Γn

/-- Pointwise action formula for the lifted `Cl(1,1)` global grading. -/
theorem cl11GlobalGrading_apply_tmul
    (Γn : Endomorphism F) (u : DoubledSpace E) (v : F) :
    cl11GlobalGrading (E := E) Γn (u ⊗ₜ[ℝ] v)
      = spectral_epsilon (E := E) u ⊗ₜ[ℝ] Γn v := by
  simp [cl11GlobalGrading, globalGrading, TensorProduct.map_tmul]

/--
Exact lifted chiral law for the `Cl(1,1)` Bott root:
if the second-factor Dirac/grading pair anticommutes, then the lifted
`cl11BottDirac` anticommutes with the lifted global grading.
-/
theorem cl11BottDirac_comp_cl11GlobalGrading_add_cl11GlobalGrading_comp_cl11BottDirac
    (Dn Γn : Endomorphism F)
    (hAnti : IsChiralDirac (E := F) Dn Γn) :
    (cl11BottDirac (E := E) Dn).comp (cl11GlobalGrading (E := E) Γn)
      + (cl11GlobalGrading (E := E) Γn).comp (cl11BottDirac (E := E) Dn)
      = 0 := by
  ext u v
  have hAntiEval : Dn (Γn v) + Γn (Dn v) = 0 := by
    have h := congrArg (fun T : Endomorphism F => T v) hAnti
    simpa [IsChiralDirac, LinearMap.comp_apply, LinearMap.add_apply] using h
  simp [LinearMap.comp_apply, LinearMap.add_apply, cl11BottDirac_apply_tmul,
    cl11GlobalGrading_apply_tmul]
  have hCrossVec :
      WithLp.toLp (2 : ENNReal) (-WithLp.snd u, WithLp.fst u)
        =
      -WithLp.toLp (2 : ENNReal) (WithLp.snd u, -WithLp.fst u) := by
    apply DoubledSpace.ext <;> simp
  have hCross :
      WithLp.toLp (2 : ENNReal) (WithLp.snd u, -WithLp.fst u) ⊗ₜ[ℝ] Γn v
        +
      WithLp.toLp (2 : ENNReal) (-WithLp.snd u, WithLp.fst u) ⊗ₜ[ℝ] Γn v
        = 0 := by
    rw [hCrossVec]
    simp [TensorProduct.neg_tmul]
  have hCross' :
      WithLp.toLp (2 : ENNReal) (-WithLp.snd u, WithLp.fst u) ⊗ₜ[ℝ] Γn v
        +
      WithLp.toLp (2 : ENNReal) (WithLp.snd u, -WithLp.fst u) ⊗ₜ[ℝ] Γn v
        = 0 := by
    simpa [add_comm] using hCross
  have hMain :
      WithLp.toLp (2 : ENNReal) (WithLp.fst u, WithLp.snd u) ⊗ₜ[ℝ] Dn (Γn v)
        +
      WithLp.toLp (2 : ENNReal) (WithLp.fst u, WithLp.snd u) ⊗ₜ[ℝ] Γn (Dn v)
        = 0 := by
    rw [← TensorProduct.tmul_add]
    simp [hAntiEval]
  calc
    WithLp.toLp (2 : ENNReal) (-WithLp.snd u, WithLp.fst u) ⊗ₜ[ℝ] Γn v
        +
      WithLp.toLp (2 : ENNReal) (WithLp.fst u, WithLp.snd u) ⊗ₜ[ℝ] Dn (Γn v)
        +
      (WithLp.toLp (2 : ENNReal) (WithLp.snd u, -WithLp.fst u) ⊗ₜ[ℝ] Γn v
        +
      WithLp.toLp (2 : ENNReal) (WithLp.fst u, WithLp.snd u) ⊗ₜ[ℝ] Γn (Dn v))
        =
      (WithLp.toLp (2 : ENNReal) (-WithLp.snd u, WithLp.fst u) ⊗ₜ[ℝ] Γn v
        +
      WithLp.toLp (2 : ENNReal) (WithLp.snd u, -WithLp.fst u) ⊗ₜ[ℝ] Γn v)
        +
      (WithLp.toLp (2 : ENNReal) (WithLp.fst u, WithLp.snd u) ⊗ₜ[ℝ] Dn (Γn v)
        +
      WithLp.toLp (2 : ENNReal) (WithLp.fst u, WithLp.snd u) ⊗ₜ[ℝ] Γn (Dn v)) := by
          ac_rfl
    _ = 0 + 0 := by rw [hCross', hMain]
    _ = 0 := by simp

/-- `Cl(1,1)` specialization of the formal Bott analytical index. -/
noncomputable def cl11BottAnalyticalIndex
    [FiniteDimensional ℝ (DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : Endomorphism F) : ℤ :=
  analyticalIndex
    (cl11BottDirac (E := E) Dn)
    (cl11GlobalGrading (E := E) Γn)

/--
Exact conjugacy law for the lifted `Cl(1,1)` global grading:
conjugacy of the second-factor grading is preserved by the Bott tensor lift.
-/
theorem cl11GlobalGrading_comp_tensor_eq_tensor_comp_cl11GlobalGrading
    (Γ0 Γs e : Endomorphism F)
    (hConj : Γ0.comp e = e.comp Γs) :
    (cl11GlobalGrading (E := E) Γ0).comp
      (TensorProduct.map (LinearMap.id : Endomorphism (DoubledSpace E)) e)
      =
    (TensorProduct.map (LinearMap.id : Endomorphism (DoubledSpace E)) e).comp
      (cl11GlobalGrading (E := E) Γs) := by
  ext u v
  simp [cl11GlobalGrading, globalGrading, TensorProduct.map_tmul, LinearMap.comp_apply]
  have hEval : Γ0 (e v) = e (Γs v) := by
    have h := congrArg (fun T : Endomorphism F => T v) hConj
    simpa [LinearMap.comp_apply] using h
  rw [hEval]

/--
The lifted projective involution `J` on the doubled-space factor transports the
lifted global grading to the sign-twisted second-factor grading.
-/
theorem cl11GlobalGrading_comp_tensor_modular_j_eq_tensor_comp_cl11GlobalGrading_neg
    (Γ0 Γs e : Endomorphism F)
    (hConj : Γ0.comp e = e.comp Γs) :
    (cl11GlobalGrading (E := E) Γ0).comp
      (TensorProduct.map (modular_jLE E).toLinearMap e)
      =
    (TensorProduct.map (modular_jLE E).toLinearMap e).comp
      (cl11GlobalGrading (E := E) (-Γs)) := by
  ext u v
  have hEval : Γ0 (e v) = e (Γs v) := by
    have h := congrArg (fun T : Endomorphism F => T v) hConj
    simpa [LinearMap.comp_apply] using h
  have hSign :
      WithLp.toLp (2 : ENNReal) (WithLp.snd u, -WithLp.fst u)
        =
      -WithLp.toLp (2 : ENNReal) (-WithLp.snd u, WithLp.fst u) := by
    apply DoubledSpace.ext <;> simp
  simp [LinearMap.comp_apply, TensorProduct.map_tmul, cl11GlobalGrading_apply_tmul,
    modular_jLE, hEval]
  rw [hSign]
  simp [TensorProduct.neg_tmul, TensorProduct.tmul_neg]

/--
Functorial `Cl(1,1)` lift of chiral conjugacy:
conjugacy of the second-factor Dirac/grading family induces conjugacy of the
lifted Bott-Dirac/global-grading family.
-/
theorem chiralConjugacyAlong_cl11Bott
    [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ (DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : ℝ → Endomorphism F)
    (eFlow : ℝ → F ≃ₗ[ℝ] F)
    (hConj : ChiralConjugacyAlong Dn Γn eFlow) :
    ChiralConjugacyAlong
      (fun s => cl11BottDirac (E := E) (Dn s))
      (fun s => cl11GlobalGrading (E := E) (Γn s))
      (fun s => TensorProduct.congr (LinearEquiv.refl ℝ (DoubledSpace E)) (eFlow s)) := by
  constructor
  · intro s
    have hTensor :
        (TensorProduct.congr (LinearEquiv.refl ℝ (DoubledSpace E)) (eFlow s)).toLinearMap =
          TensorProduct.map (LinearMap.id : Endomorphism (DoubledSpace E)) (eFlow s).toLinearMap := by
      ext u v
      simp [TensorProduct.congr, LinearEquiv.refl]
    rw [hTensor]
    exact cl11BottDirac_comp_tensor_eq_tensor_comp_cl11BottDirac
      (E := E) (Dn 0) (Dn s) (eFlow s).toLinearMap (hConj.1 s)
  · intro s
    have hTensor :
        (TensorProduct.congr (LinearEquiv.refl ℝ (DoubledSpace E)) (eFlow s)).toLinearMap =
          TensorProduct.map (LinearMap.id : Endomorphism (DoubledSpace E)) (eFlow s).toLinearMap := by
      ext u v
      simp [TensorProduct.congr, LinearEquiv.refl]
    rw [hTensor]
    exact cl11GlobalGrading_comp_tensor_eq_tensor_comp_cl11GlobalGrading
      (E := E) (Γ0 := Γn 0) (Γs := Γn s) (e := (eFlow s).toLinearMap) (hConj := hConj.2 s)

/--
Analytical-index invariance for the `Cl(1,1)` Bott lift:
base-space chiral conjugacy is enough to keep the lifted Bott analytical index
fixed along the full family.
-/
theorem cl11BottIndexInvariantAlong_of_conjugacy
    [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ (DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : ℝ → Endomorphism F)
    (eFlow : ℝ → F ≃ₗ[ℝ] F)
    (hConj : ChiralConjugacyAlong Dn Γn eFlow) :
    IndexInvariantAlong
      (fun s => cl11BottDirac (E := E) (Dn s))
      (fun s => cl11GlobalGrading (E := E) (Γn s)) := by
  exact indexInvariantAlong_of_conjugacy
    (D := fun s => cl11BottDirac (E := E) (Dn s))
    (Γ := fun s => cl11GlobalGrading (E := E) (Γn s))
    (eFlow := fun s => TensorProduct.congr (LinearEquiv.refl ℝ (DoubledSpace E)) (eFlow s))
    (hConj := chiralConjugacyAlong_cl11Bott
      (E := E) (F := F) (Dn := Dn) (Γn := Γn) (eFlow := eFlow) hConj)

/--
The projective involution `J` on doubled-space rays lifts to an exact Bott
conjugacy jump from `(D, Γ)` to `(-D, -Γ)` on the `Cl(1,1)` tensor module.
-/
theorem chiralConjugacyAlong_cl11BottJump_of_projectiveJ
    [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ (DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : Endomorphism F) :
    ChiralConjugacyAlong
      (fun s => if s = 0 then cl11BottDirac (E := E) Dn else cl11BottDirac (E := E) (-Dn))
      (fun s => if s = 0 then cl11GlobalGrading (E := E) Γn else cl11GlobalGrading (E := E) (-Γn))
      (fun s =>
        if s = 0 then LinearEquiv.refl ℝ (DoubledSpace E ⊗[ℝ] F)
        else TensorProduct.congr (modular_jLE E) (LinearEquiv.refl ℝ F)) := by
  constructor
  · intro s
    by_cases hs : s = 0
    · simp [hs]
    · simpa [hs] using
        (InfoGeometry.Canonical.BottDirac.cl11BottDirac_comp_tensor_modular_j_eq_tensor_comp_cl11BottDirac_neg
          (E := E) (Dn := Dn) (Dn' := Dn) (e := LinearMap.id)
          (by ext x; simp))
  · intro s
    by_cases hs : s = 0
    · simp [hs]
    · simpa [hs] using
        (cl11GlobalGrading_comp_tensor_modular_j_eq_tensor_comp_cl11GlobalGrading_neg
          (E := E) (Γ0 := Γn) (Γs := Γn) (e := LinearMap.id)
          (by ext x; simp))

/--
Exact `J`-transport on the Bott root preserves the analytical index under the
sign-twist `(D, Γ) ↦ (-D, -Γ)`.
-/
theorem cl11BottAnalyticalIndex_eq_neg_of_projectiveJ
    [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ (DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : Endomorphism F) :
    cl11BottAnalyticalIndex (E := E) Dn Γn
      =
    cl11BottAnalyticalIndex (E := E) (-Dn) (-Γn) := by
  have hInv := indexInvariantAlong_of_conjugacy
    (D := fun s => if s = 0 then cl11BottDirac (E := E) Dn else cl11BottDirac (E := E) (-Dn))
    (Γ := fun s => if s = 0 then cl11GlobalGrading (E := E) Γn else cl11GlobalGrading (E := E) (-Γn))
    (eFlow := fun s =>
      if s = 0 then LinearEquiv.refl ℝ (DoubledSpace E ⊗[ℝ] F)
      else TensorProduct.congr (modular_jLE E) (LinearEquiv.refl ℝ F))
    (hConj := chiralConjugacyAlong_cl11BottJump_of_projectiveJ
      (E := E) (F := F) (Dn := Dn) (Γn := Γn))
  have h1 : (1 : ℝ) ≠ 0 := by norm_num
  simpa [cl11BottAnalyticalIndex, h1] using (hInv 1).symm

/--
Pointwise `Cl(1,1)` Bott analytical-index invariance:
base-space chiral conjugacy identifies each lifted Bott index with the
baseline index at `0`.
-/
theorem cl11BottAnalyticalIndex_eq_zero_time_of_conjugacy
    [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ (DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : ℝ → Endomorphism F)
    (eFlow : ℝ → F ≃ₗ[ℝ] F)
    (hConj : ChiralConjugacyAlong Dn Γn eFlow)
    (s : ℝ) :
    cl11BottAnalyticalIndex (E := E) (Dn s) (Γn s) =
      cl11BottAnalyticalIndex (E := E) (Dn 0) (Γn 0) := by
  exact cl11BottIndexInvariantAlong_of_conjugacy
    (E := E) (F := F) (Dn := Dn) (Γn := Γn) (eFlow := eFlow) hConj s

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
    (cl11BottDirac (E := E) Dn).comp
      (cl11BottDirac (E := E) Dn) = 0 := by
  exact (cl11_bottDirac_sq_eq_cl11BottLaplacian (E := E) (F := F) (Dn := Dn)).trans hZero

/--
Explicit `Cl(1,1)` Bott-square vanishing criterion:
if the second-factor Dirac operator squares to `-Id`, then the split Bott-Dirac
operator is nilpotent of order two.
-/
theorem cl11_bottDirac_sq_eq_zero_of_dirac_sq_eq_neg_id
    (Dn : Endomorphism F)
    (hDnSq : Dn.comp Dn = -(LinearMap.id : Endomorphism F)) :
    (cl11BottDirac (E := E) Dn).comp
      (cl11BottDirac (E := E) Dn) = 0 := by
  rw [cl11_bottDirac_sq_eq_tensor_id_add_tensor_dirac_sq (E := E) (F := F) (Dn := Dn)]
  rw [hDnSq]
  have hTensorNegId :
      TensorProduct.map
          (LinearMap.id : Endomorphism (DoubledSpace E))
          (-(LinearMap.id : Endomorphism F))
        =
      -(LinearMap.id : Endomorphism (DoubledSpace E ⊗[ℝ] F)) := by
    ext u v
    simp [TensorProduct.map_tmul, TensorProduct.tmul_neg]
  rw [hTensorNegId]
  simp

end Laplacian

end InfoGeometry.Canonical.AnalyticalIndex
