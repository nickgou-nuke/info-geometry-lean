import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Canonical.Clifford
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Singular.Drazin
import InfoGeometry.Meta.Architecture

/-!
# Einstein Universe: Singular Regularization
Integrating Drazin and Moore-Penrose inverses for degenerate metrics.
-/

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace InfoGeometry.Canonical

variable {R : Type*} [Ring R] [StarRing R]

/-- Canonical Moore-Penrose inverse predicate (re-export alias). -/
abbrev IsMoorePenroseInverse (a b : R) : Prop :=
  InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse a b

/-- Canonical Drazin inverse predicate (re-export alias). -/
abbrev IsDrazinInverse (a b : R) (k : ℕ) : Prop :=
  InfoGeometry.Canonical.Drazin.IsDrazinInverse a b k

/-!
## Positive adjoint-square boundary

This is the Lean-native analogue of the bounded-operator theorem shape that an
adjoint square is positive.  The roots are mathlib's positive-operator API for
continuous linear maps; this section only exposes the canonical info-geometry
operator boundary.
-/

section PositiveAdjointSquare

open InnerProductSpace ContinuousLinearMap
open scoped InnerProduct ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
variable [CompleteSpace E] [CompleteSpace F]

/-- The Gram operator `S† ∘L S` is positive. -/
@[rep_depth krein]
theorem adjoint_comp_self_isPositive (S : E →L[𝕜] F) :
    (S† ∘L S).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self S

/-- In endomorphism notation, `A† * A` is positive. -/
@[rep_depth krein]
theorem star_mul_self_isPositive (A : E →L[𝕜] E) :
    (star A * A).IsPositive := by
  simpa [star_eq_adjoint, ContinuousLinearMap.mul_def] using
    (ContinuousLinearMap.isPositive_adjoint_comp_self A)

/-- The final-space Gram operator `A * A†` is positive. -/
@[rep_depth krein]
theorem mul_star_self_isPositive (A : E →L[𝕜] E) :
    (A * star A).IsPositive := by
  simpa [star_eq_adjoint, ContinuousLinearMap.mul_def] using
    (ContinuousLinearMap.isPositive_self_comp_adjoint A)

end PositiveAdjointSquare

/--
The "Einstein Anomaly"
Defined as the commutator of the Geometric (MP) and Spectral (Drazin) projectors.
-/
def EinsteinAnomaly (a b_mp b_dr : R) : R :=
  let P_MP := a * b_mp
  let P_D  := a * b_dr
  P_MP * P_D - P_D * P_MP

/--
Theorem: Chiral/Einstein Anomaly Skew-Adjointness
The anomaly, defined as the commutator between the Geometric and Spectral projectors,
is strictly skew-adjoint when both projectors are self-adjoint.
-/
theorem einsteinAnomaly_skew_adjoint (a b_mp b_dr : R) (k : ℕ)
    (h_mp : IsMoorePenroseInverse a b_mp)
    (_h_dr : IsDrazinInverse a b_dr k)
    (h_dr_star : star (a * b_dr) = a * b_dr) :
    star (EinsteinAnomaly a b_mp b_dr) =
      - (EinsteinAnomaly a b_mp b_dr) := by
  unfold EinsteinAnomaly
  simp only [star_sub, star_mul, h_mp.ab_star, h_dr_star]
  rw [neg_sub]

/-!
## Constructive Nondegenerate Existence

For invertible (`IsUnit`) elements, generalized inverses are constructively
realized by the ordinary inverse.
-/

/--
Constructive Moore-Penrose inverse existence in the nondegenerate case.
If `a` is invertible, `a⁻¹` satisfies the Moore-Penrose axioms.
-/
theorem exists_moorePenroseInverse_of_isUnit
    (a : R) (ha : IsUnit a) :
    ∃ b : R, IsMoorePenroseInverse a b := by
  rcases ha with ⟨u, rfl⟩
  refine ⟨↑u⁻¹, ?_⟩
  constructor <;> simp

/--
Constructive Drazin inverse existence in the nondegenerate case.
If `a` is invertible, `a⁻¹` is a Drazin inverse with index `k = 0`.
-/
theorem exists_drazinInverse_of_isUnit
    {S : Type*} [Ring S]
    (a : S) (ha : IsUnit a) :
    ∃ b : S, IsDrazinInverse a b 0 := by
  rcases ha with ⟨u, rfl⟩
  refine ⟨↑u⁻¹, ?_⟩
  constructor <;> simp

/--
Constructive Moore-Penrose inverse existence in the degenerate projector case.
If `a` is a self-adjoint idempotent, then `a` is its own Moore-Penrose inverse.
-/
theorem exists_moorePenroseInverse_of_selfAdjoint_idempotent
    (a : R)
    (ha_idem : a * a = a)
    (ha_star : star a = a) :
    ∃ b : R, IsMoorePenroseInverse a b := by
  refine ⟨a, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      a * a * a = (a * a) * a := by simp [mul_assoc]
      _ = a * a := by simpa [ha_idem]
      _ = a := ha_idem
  · calc
      a * a * a = (a * a) * a := by simp [mul_assoc]
      _ = a * a := by simpa [ha_idem]
      _ = a := ha_idem
  · calc
      star (a * a) = star a * star a := by simpa using star_mul a a
      _ = a * a := by simpa [ha_star]
  · calc
      star (a * a) = star a * star a := by simpa using star_mul a a
      _ = a * a := by simpa [ha_star]

/--
Constructive Drazin inverse existence in the degenerate projector case.
If `a` is idempotent, then `a` is its own Drazin inverse with index `k = 1`.
-/
theorem exists_drazinInverse_of_idempotent
    {S : Type*} [Ring S]
    (a : S)
    (ha_idem : a * a = a) :
    ∃ b : S, IsDrazinInverse a b 1 := by
  refine ⟨a, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp
  · calc
      a * a * a = (a * a) * a := by simp [mul_assoc]
      _ = a * a := by simpa [ha_idem]
      _ = a := ha_idem
  · calc
      a ^ (1 + 1) * a = (a * a) * a := by simp [pow_succ, mul_assoc]
      _ = a * a := by simpa [ha_idem]
      _ = a := ha_idem
      _ = a ^ 1 := by simp

/--
Joint constructive generalized-inverse package in the projector case.
For self-adjoint idempotent `a`, the same witness `a` satisfies both
Moore-Penrose and Drazin (`k = 1`) axioms.
-/
theorem exists_regularization_pair_of_selfAdjoint_idempotent
    (a : R)
    (ha_idem : a * a = a)
    (ha_star : star a = a) :
    ∃ b : R, IsMoorePenroseInverse a b ∧ IsDrazinInverse a b 1 := by
  refine ⟨a, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        a * a * a = (a * a) * a := by simp [mul_assoc]
        _ = a * a := by simpa [ha_idem]
        _ = a := ha_idem
    · calc
        a * a * a = (a * a) * a := by simp [mul_assoc]
        _ = a * a := by simpa [ha_idem]
        _ = a := ha_idem
    · calc
        star (a * a) = star a * star a := by simpa using star_mul a a
        _ = a * a := by simpa [ha_star]
    · calc
        star (a * a) = star a * star a := by simpa using star_mul a a
        _ = a * a := by simpa [ha_star]
  · refine ⟨?_, ?_, ?_⟩
    · simp
    · calc
        a * a * a = (a * a) * a := by simp [mul_assoc]
        _ = a * a := by simpa [ha_idem]
        _ = a := ha_idem
    · calc
        a ^ (1 + 1) * a = (a * a) * a := by simp [pow_succ, mul_assoc]
        _ = a * a := by simpa [ha_idem]
        _ = a := ha_idem
        _ = a ^ 1 := by simp

/--
Joint constructive generalized-inverse package in the nondegenerate case.
The same inverse witness simultaneously satisfies Moore-Penrose and Drazin (`k=0`).
-/
theorem exists_regularization_pair_of_isUnit
    (a : R) (ha : IsUnit a) :
    ∃ b : R, IsMoorePenroseInverse a b ∧ IsDrazinInverse a b 0 := by
  rcases ha with ⟨u, rfl⟩
  refine ⟨↑u⁻¹, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  · refine ⟨?_, ?_, ?_⟩ <;> simp

@[simp] theorem EinsteinAnomaly_eq_zero_of_regularization_pair
    (a b : R)
    (_h_mp : IsMoorePenroseInverse a b)
    (_h_dr : IsDrazinInverse a b 0) :
    EinsteinAnomaly a b b = 0 := by
  unfold EinsteinAnomaly
  simp

@[simp] theorem EinsteinAnomaly_eq_zero_of_selfAdjoint_idempotent
    (a : R)
    (ha_idem : a * a = a)
    (ha_star : star a = a) :
    EinsteinAnomaly a a a = 0 := by
  unfold EinsteinAnomaly
  simp [ha_idem]


/-!
## Endomorphism Constructive Existence

Provable constructive existence results for finite-dimensional endomorphisms
in the nondegenerate (`IsUnit`) regime.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Constructive Moore-Penrose inverse existence for nondegenerate endomorphisms.
-/
theorem exists_moorePenroseInverse_endomorphism_of_isUnit
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E)
    (hA : IsUnit A) :
    ∃ (B : E →L[ℝ] E), IsMoorePenroseInverse A B := by
  exact exists_moorePenroseInverse_of_isUnit (a := A) hA

/--
Constructive Drazin inverse existence for nondegenerate endomorphisms.
-/
theorem exists_drazinInverse_endomorphism_of_isUnit
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E)
    (hA : IsUnit A) :
    ∃ (k : ℕ) (B : E →L[ℝ] E), IsDrazinInverse A B k := by
  refine ⟨0, ?_⟩
  rcases exists_drazinInverse_of_isUnit (a := A) hA with ⟨B, hB⟩
  exact ⟨B, hB⟩

/--
Global constructive Drazin inverse existence in finite dimensions.

This closes the canonical Drazin layer by importing the Fitting-based constructive
existence theorem from `InfoGeometry.Singular.Drazin` and translating it to
the canonical predicate.
-/
theorem exists_drazinInverse_global
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) :
    ∃ (k : ℕ) (B : E →L[ℝ] E), IsDrazinInverse A B k := by
  rcases InfoGeometry.Singular.Drazin.exists_drazinInverse_global
      (K := ℝ) (V := E) (A := A.toLinearMap) with ⟨k, Blin, hDlin⟩
  let B : E →L[ℝ] E := LinearMap.toContinuousLinearMap Blin
  have hCommLin : A.toLinearMap * B.toLinearMap = B.toLinearMap * A.toLinearMap := by
    simpa [B] using hDlin.2.1
  have hIdemLin : B.toLinearMap * A.toLinearMap * B.toLinearMap = B.toLinearMap := by
    simpa [B] using hDlin.1
  have hPowLin : A.toLinearMap ^ (k + 1) * B.toLinearMap = A.toLinearMap ^ k := by
    simpa [B] using hDlin.2.2.symm
  refine ⟨k, B, InfoGeometry.Canonical.Drazin.IsDrazinInverse.mk
    (hcomm := ?_) (hidempotent := ?_) (hpower := ?_)⟩
  · ext x
    simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) hCommLin
  · ext x
    simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) hIdemLin
  ·
    have hPowCont : (A ^ (k + 1) * B).toLinearMap = (A ^ k).toLinearMap := by
      change (ContinuousLinearMap.toLinearMapRingHom : (E →L[ℝ] E) →+* (E →ₗ[ℝ] E))
          (A ^ (k + 1) * B) =
        (ContinuousLinearMap.toLinearMapRingHom : (E →L[ℝ] E) →+* (E →ₗ[ℝ] E))
          (A ^ k)
      simpa [map_mul, map_pow, B] using hPowLin
    have hPow' : A ^ (k + 1) * B = ((A ^ k).toLinearMap).toContinuousLinearMap :=
      (ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap
          (g := A ^ (k + 1) * B) (f := (A ^ k).toLinearMap)).1 hPowCont
    have hRoundTrip : ((A ^ k).toLinearMap).toContinuousLinearMap = A ^ k := by
      exact (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap
        (f := (A ^ k).toLinearMap) (g := A ^ k)).2 rfl
    exact hPow'.trans hRoundTrip

/--
Closed-range constructive Moore-Penrose inverse existence on real Hilbert spaces.

Construction: invert `A` continuously on `ker(A)ᗮ`, using the closed-range
Banach inverse theorem, and kill `range(A)ᗮ`.
-/
theorem exists_moorePenroseInverse_of_closedRange_with_projectors
    (A : E →L[ℝ] E)
    (hClosedRange : IsClosed (A.range : Set E)) :
    ∃ (B : E →L[ℝ] E),
      IsMoorePenroseInverse A B ∧
      A * B = A.range.starProjection ∧
      B * A = A.kerᗮ.starProjection := by
  let K : Submodule ℝ E := A.kerᗮ
  let R : Submodule ℝ E := A.range
  letI : CompleteSpace R := hClosedRange.completeSpace_coe

  let AresCLM : K →L[ℝ] R :=
    (A.comp K.subtypeL).codRestrict R (by
      intro x
      exact ⟨x.1, rfl⟩)

  have hAres_injective : Function.Injective AresCLM := by
    intro x y hxy
    apply Subtype.ext
    have hval : A (x : E) = A y := congrArg Subtype.val hxy
    have hker : ((x - y : K) : E) ∈ A.ker := by
      change A ((x - y : K) : E) = 0
      simpa [map_sub, hval]
    have horth : ((x - y : K) : E) ∈ A.kerᗮ := by
      simpa [K] using (x - y : K).2
    have hbot : ((x - y : K) : E) ∈ (⊥ : Submodule ℝ E) := by
      have : ((x - y : K) : E) ∈ A.ker ⊓ A.kerᗮ := ⟨hker, horth⟩
      simpa [Submodule.inf_orthogonal_eq_bot] using this
    simpa [sub_eq_zero] using hbot

  have hKorth_eq_ker : Kᗮ = A.ker := by
    simpa [K] using (A.ker.orthogonal_orthogonal : A.kerᗮᗮ = A.ker)

  have hA_on_Kproj : ∀ x : E, A ((K.orthogonalProjection x : K) : E) = A x := by
    intro x
    have hsplit : K.starProjection x + Kᗮ.starProjection x = x :=
      K.starProjection_add_starProjection_orthogonal x
    have hkerOrthPart_mem : Kᗮ.starProjection x ∈ Kᗮ := by
      change ((Kᗮ.orthogonalProjection x : Kᗮ) : E) ∈ Kᗮ
      exact (Kᗮ.orthogonalProjection x).2
    have hkerPart_mem : Kᗮ.starProjection x ∈ A.ker := by
      simpa [hKorth_eq_ker] using hkerOrthPart_mem
    have hkerPart_zero : A (Kᗮ.starProjection x) = 0 := by
      simpa [LinearMap.mem_ker] using hkerPart_mem
    have hAx :
        A (K.starProjection x) + A (Kᗮ.starProjection x) = A x := by
      simpa [map_add] using congrArg A hsplit
    have hAx' : A (K.starProjection x) = A x := by
      calc
        A (K.starProjection x) = A (K.starProjection x) + A (Kᗮ.starProjection x) := by
          rw [hkerPart_zero, add_zero]
        _ = A x := hAx
    change A (K.starProjection x) = A x
    exact hAx'

  have hAres_surjective : Function.Surjective AresCLM := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, hx⟩
    refine ⟨K.orthogonalProjection x, ?_⟩
    apply Subtype.ext
    calc
      A ((K.orthogonalProjection x : K) : E) = A x := hA_on_Kproj x
      _ = y := hx

  have hAres_ker : AresCLM.ker = ⊥ :=
    LinearMap.ker_eq_bot.2 hAres_injective
  have hAres_range : AresCLM.range = ⊤ :=
    LinearMap.range_eq_top.2 hAres_surjective

  let e : K ≃L[ℝ] R :=
    ContinuousLinearEquiv.ofBijective AresCLM hAres_ker hAres_range
  let eCLM : K →L[ℝ] R := e.toContinuousLinearMap
  let eSymm : R →L[ℝ] K := e.symm.toContinuousLinearMap
  let B : E →L[ℝ] E := K.subtypeL.comp (eSymm.comp R.orthogonalProjection)

  have he_id : eCLM.comp eSymm = ContinuousLinearMap.id ℝ R := by
    ext r
    simp [eCLM, eSymm]

  have hsymm_id : eSymm.comp eCLM = ContinuousLinearMap.id ℝ K := by
    ext k
    simp [eCLM, eSymm]

  have hAcompSubtype : A.comp K.subtypeL = R.subtypeL.comp eCLM := by
    ext k
    simp [eCLM, e, AresCLM]

  have hAB : A.comp B = R.starProjection := by
    ext x
    have hAstep := DFunLike.congr_fun hAcompSubtype (eSymm (R.orthogonalProjection x))
    calc
      A (B x) = R.subtypeL (eCLM (eSymm (R.orthogonalProjection x))) := by
        simpa [B, ContinuousLinearMap.comp_apply] using hAstep
      _ = R.subtypeL ((eCLM.comp eSymm) (R.orthogonalProjection x)) := by
        rfl
      _ = R.subtypeL ((ContinuousLinearMap.id ℝ R) (R.orthogonalProjection x)) := by
        rw [DFunLike.congr_fun he_id (R.orthogonalProjection x)]
      _ = R.starProjection x := by
        rfl

  have hprojA : R.orthogonalProjection.comp A = eCLM.comp K.orthogonalProjection := by
    ext x
    have hAx_mem : A x ∈ R := by
      exact ⟨x, rfl⟩
    have hleft : ((R.orthogonalProjection.comp A) x : E) = A x := by
      simpa using congrArg Subtype.val
        (R.orthogonalProjection_mem_subspace_eq_self ⟨A x, hAx_mem⟩)
    have hright0 :
        ((eCLM.comp K.orthogonalProjection) x : E) =
          A ((K.orthogonalProjection x : K) : E) := by
      simp [ContinuousLinearMap.comp_apply, eCLM, e, AresCLM]
    have hright : ((eCLM.comp K.orthogonalProjection) x : E) = A x := by
      exact hright0.trans (hA_on_Kproj x)
    exact hleft.trans hright.symm

  have hBA : B.comp A = K.starProjection := by
    ext x
    have hprojAx :
        R.orthogonalProjection (A x) = eCLM (K.orthogonalProjection x) := by
      simpa [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hprojA x
    have hsymmAx :
        eSymm (eCLM (K.orthogonalProjection x)) =
          (ContinuousLinearMap.id ℝ K) (K.orthogonalProjection x) := by
      simpa [ContinuousLinearMap.comp_apply] using
        DFunLike.congr_fun hsymm_id (K.orthogonalProjection x)
    calc
      B (A x) = K.subtypeL (eSymm (R.orthogonalProjection (A x))) := by
        rfl
      _ = K.subtypeL (eSymm (eCLM (K.orthogonalProjection x))) := by
        rw [hprojAx]
      _ = K.subtypeL ((ContinuousLinearMap.id ℝ K) (K.orthogonalProjection x)) := by
        rw [hsymmAx]
      _ = K.starProjection x := by
        rfl

  have hBmem : ∀ x : E, B x ∈ K := by
    intro x
    simpa [B] using (eSymm (R.orthogonalProjection x)).2

  have haba : A * B * A = A := by
    ext x
    have hxR : A x ∈ R := ⟨x, rfl⟩
    have hproj : R.starProjection (A x) = A x :=
      (R.starProjection_eq_self_iff).2 hxR
    calc
      ((A * B * A) x) = (A.comp B) (A x) := by
        simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
      _ = R.starProjection (A x) := by
        simpa [hAB]
      _ = A x := hproj

  have hbab : B * A * B = B := by
    ext x
    have hproj : K.starProjection (B x) = B x :=
      (K.starProjection_eq_self_iff).2 (hBmem x)
    calc
      ((B * A * B) x) = (B.comp A) (B x) := by
        simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
      _ = K.starProjection (B x) := by
        simpa [hBA]
      _ = B x := hproj

  have habstar : star (A * B) = A * B := by
    have hstarR : star R.starProjection = R.starProjection := by
      simpa [IsSelfAdjoint] using
        (isSelfAdjoint_starProjection R : IsSelfAdjoint R.starProjection)
    calc
      star (A * B) = star R.starProjection := by
        simpa [ContinuousLinearMap.mul_def, hAB]
      _ = R.starProjection := hstarR
      _ = A * B := by
        simpa [ContinuousLinearMap.mul_def, hAB]

  have hbastar : star (B * A) = B * A := by
    have hstarK : star K.starProjection = K.starProjection := by
      simpa [IsSelfAdjoint] using
        (isSelfAdjoint_starProjection K : IsSelfAdjoint K.starProjection)
    calc
      star (B * A) = star K.starProjection := by
        simpa [ContinuousLinearMap.mul_def, hBA]
      _ = K.starProjection := hstarK
      _ = B * A := by
        simpa [ContinuousLinearMap.mul_def, hBA]

  exact ⟨B, ⟨⟨haba, hbab, habstar, hbastar⟩,
    by simpa [R, ContinuousLinearMap.mul_def] using hAB,
    by simpa [K, ContinuousLinearMap.mul_def] using hBA⟩⟩

/--
Global constructive Moore-Penrose inverse existence on finite-dimensional
real Hilbert spaces.

Construction: invert `A` on `ker(A)ᗮ`, kill `range(A)ᗮ`.
-/
theorem exists_moorePenroseInverse_global_with_projectors
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) :
    ∃ (B : E →L[ℝ] E),
      IsMoorePenroseInverse A B ∧
      A * B = A.range.starProjection ∧
      B * A = A.kerᗮ.starProjection := by
  let K : Submodule ℝ E := A.kerᗮ
  let R : Submodule ℝ E := A.range

  let Ares : K →ₗ[ℝ] R :=
    { toFun := fun x => ⟨A x.1, ⟨x.1, rfl⟩⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro c x
        ext
        simp }

  have hAres_injective : Function.Injective Ares := by
    intro x y hxy
    apply Subtype.ext
    have hval : A (x : E) = A y := congrArg Subtype.val hxy
    have hker : ((x - y : K) : E) ∈ A.ker := by
      change A ((x - y : K) : E) = 0
      simpa [map_sub, hval]
    have horth : ((x - y : K) : E) ∈ A.kerᗮ := by
      simpa [K] using (x - y : K).2
    have hbot : ((x - y : K) : E) ∈ (⊥ : Submodule ℝ E) := by
      have : ((x - y : K) : E) ∈ A.ker ⊓ A.kerᗮ := ⟨hker, horth⟩
      simpa [Submodule.inf_orthogonal_eq_bot] using this
    simpa [sub_eq_zero] using hbot

  have hKorth_eq_ker : Kᗮ = A.ker := by
    simpa [K] using (A.ker.orthogonal_orthogonal : A.kerᗮᗮ = A.ker)

  have hA_on_Kproj : ∀ x : E, A ((K.orthogonalProjection x : K) : E) = A x := by
    intro x
    have hsplit : K.starProjection x + Kᗮ.starProjection x = x :=
      K.starProjection_add_starProjection_orthogonal x
    have hkerOrthPart_mem : Kᗮ.starProjection x ∈ Kᗮ := by
      change ((Kᗮ.orthogonalProjection x : Kᗮ) : E) ∈ Kᗮ
      exact (Kᗮ.orthogonalProjection x).2
    have hkerPart_mem : Kᗮ.starProjection x ∈ A.ker := by
      simpa [hKorth_eq_ker] using hkerOrthPart_mem
    have hkerPart_zero : A (Kᗮ.starProjection x) = 0 := by
      simpa [LinearMap.mem_ker] using hkerPart_mem
    have hAx :
        A (K.starProjection x) + A (Kᗮ.starProjection x) = A x := by
      simpa [map_add] using congrArg A hsplit
    have hAx' : A (K.starProjection x) = A x := by
      calc
        A (K.starProjection x) = A (K.starProjection x) + A (Kᗮ.starProjection x) := by
          rw [hkerPart_zero, add_zero]
        _ = A x := hAx
    change A (K.starProjection x) = A x
    exact hAx'

  have hAres_surjective : Function.Surjective Ares := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, hx⟩
    refine ⟨K.orthogonalProjection x, ?_⟩
    apply Subtype.ext
    calc
      A ((K.orthogonalProjection x : K) : E) = A x := hA_on_Kproj x
      _ = y := hx

  let e : K ≃ₗ[ℝ] R := LinearEquiv.ofBijective Ares ⟨hAres_injective, hAres_surjective⟩
  let eCLM : K →L[ℝ] R := LinearMap.toContinuousLinearMap e.toLinearMap
  let eSymm : R →L[ℝ] K := LinearMap.toContinuousLinearMap e.symm.toLinearMap
  let B : E →L[ℝ] E := K.subtypeL.comp (eSymm.comp R.orthogonalProjection)

  have he_id : eCLM.comp eSymm = ContinuousLinearMap.id ℝ R := by
    ext r
    simp [eCLM, eSymm]

  have hsymm_id : eSymm.comp eCLM = ContinuousLinearMap.id ℝ K := by
    ext k
    simp [eCLM, eSymm]

  have hAcompSubtype : A.comp K.subtypeL = R.subtypeL.comp eCLM := by
    ext k
    simp [eCLM, e, Ares]

  have hAB : A.comp B = R.starProjection := by
    ext x
    have hAstep := DFunLike.congr_fun hAcompSubtype (eSymm (R.orthogonalProjection x))
    calc
      A (B x) = R.subtypeL (eCLM (eSymm (R.orthogonalProjection x))) := by
        simpa [B, ContinuousLinearMap.comp_apply] using hAstep
      _ = R.subtypeL ((eCLM.comp eSymm) (R.orthogonalProjection x)) := by
        rfl
      _ = R.subtypeL ((ContinuousLinearMap.id ℝ R) (R.orthogonalProjection x)) := by
        rw [DFunLike.congr_fun he_id (R.orthogonalProjection x)]
      _ = R.starProjection x := by
        rfl

  have hprojA : R.orthogonalProjection.comp A = eCLM.comp K.orthogonalProjection := by
    ext x
    have hAx_mem : A x ∈ R := by
      exact ⟨x, rfl⟩
    have hleft : ((R.orthogonalProjection.comp A) x : E) = A x := by
      simpa using congrArg Subtype.val
        (R.orthogonalProjection_mem_subspace_eq_self ⟨A x, hAx_mem⟩)
    have hright0 :
        ((eCLM.comp K.orthogonalProjection) x : E) =
          A ((K.orthogonalProjection x : K) : E) := by
      simp [ContinuousLinearMap.comp_apply, eCLM, e, Ares]
    have hright : ((eCLM.comp K.orthogonalProjection) x : E) = A x := by
      exact hright0.trans (hA_on_Kproj x)
    exact hleft.trans hright.symm

  have hBA : B.comp A = K.starProjection := by
    ext x
    have hprojAx :
        R.orthogonalProjection (A x) = eCLM (K.orthogonalProjection x) := by
      simpa [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hprojA x
    have hsymmAx :
        eSymm (eCLM (K.orthogonalProjection x)) =
          (ContinuousLinearMap.id ℝ K) (K.orthogonalProjection x) := by
      simpa [ContinuousLinearMap.comp_apply] using
        DFunLike.congr_fun hsymm_id (K.orthogonalProjection x)
    calc
      B (A x) = K.subtypeL (eSymm (R.orthogonalProjection (A x))) := by
        rfl
      _ = K.subtypeL (eSymm (eCLM (K.orthogonalProjection x))) := by
        rw [hprojAx]
      _ = K.subtypeL ((ContinuousLinearMap.id ℝ K) (K.orthogonalProjection x)) := by
        rw [hsymmAx]
      _ = K.starProjection x := by
        rfl

  have hBmem : ∀ x : E, B x ∈ K := by
    intro x
    simpa [B] using (eSymm (R.orthogonalProjection x)).2

  have haba : A * B * A = A := by
    ext x
    have hxR : A x ∈ R := ⟨x, rfl⟩
    have hproj : R.starProjection (A x) = A x :=
      (R.starProjection_eq_self_iff).2 hxR
    calc
      ((A * B * A) x) = (A.comp B) (A x) := by
        simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
      _ = R.starProjection (A x) := by
        simpa [hAB]
      _ = A x := hproj

  have hbab : B * A * B = B := by
    ext x
    have hproj : K.starProjection (B x) = B x :=
      (K.starProjection_eq_self_iff).2 (hBmem x)
    calc
      ((B * A * B) x) = (B.comp A) (B x) := by
        simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
      _ = K.starProjection (B x) := by
        simpa [hBA]
      _ = B x := hproj

  have habstar : star (A * B) = A * B := by
    have hstarR : star R.starProjection = R.starProjection := by
      simpa [IsSelfAdjoint] using
        (isSelfAdjoint_starProjection R : IsSelfAdjoint R.starProjection)
    calc
      star (A * B) = star R.starProjection := by
        simpa [ContinuousLinearMap.mul_def, hAB]
      _ = R.starProjection := hstarR
      _ = A * B := by
        simpa [ContinuousLinearMap.mul_def, hAB]

  have hbastar : star (B * A) = B * A := by
    have hstarK : star K.starProjection = K.starProjection := by
      simpa [IsSelfAdjoint] using
        (isSelfAdjoint_starProjection K : IsSelfAdjoint K.starProjection)
    calc
      star (B * A) = star K.starProjection := by
        simpa [ContinuousLinearMap.mul_def, hBA]
      _ = K.starProjection := hstarK
      _ = B * A := by
        simpa [ContinuousLinearMap.mul_def, hBA]

  exact ⟨B, ⟨⟨haba, hbab, habstar, hbastar⟩,
    by simpa [R, ContinuousLinearMap.mul_def] using hAB,
    by simpa [K, ContinuousLinearMap.mul_def] using hBA⟩⟩

/--
Global constructive Moore-Penrose inverse existence on finite-dimensional
real Hilbert spaces.

Construction: invert `A` on `ker(A)ᗮ`, kill `range(A)ᗮ`.
-/
theorem exists_moorePenroseInverse_global
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) :
    ∃ (B : E →L[ℝ] E), IsMoorePenroseInverse A B := by
  rcases exists_moorePenroseInverse_global_with_projectors (A := A) with
    ⟨B, hMP, _hAB, _hBA⟩
  exact ⟨B, hMP⟩

attribute [rep_depth krein]
  IsMoorePenroseInverse
  IsDrazinInverse
  EinsteinAnomaly
  einsteinAnomaly_skew_adjoint
  exists_moorePenroseInverse_of_isUnit
  exists_drazinInverse_of_isUnit
  exists_moorePenroseInverse_of_selfAdjoint_idempotent
  exists_drazinInverse_of_idempotent
  exists_regularization_pair_of_selfAdjoint_idempotent
  exists_regularization_pair_of_isUnit
  EinsteinAnomaly_eq_zero_of_regularization_pair
  EinsteinAnomaly_eq_zero_of_selfAdjoint_idempotent
  exists_moorePenroseInverse_endomorphism_of_isUnit
  exists_drazinInverse_endomorphism_of_isUnit
  exists_drazinInverse_global
  exists_moorePenroseInverse_of_closedRange_with_projectors
  exists_moorePenroseInverse_global_with_projectors
  exists_moorePenroseInverse_global

end InfoGeometry.Canonical

