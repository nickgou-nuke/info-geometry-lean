/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.Product
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.KK.CompactOperatorBridge
import InfoGeometry.KK.ClNNFredholmBridge
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

namespace InfoGeometry.KK

open InfoGeometry.Krein

/-- Finite-dimensional base space for concrete KK test models. -/
abbrev FinModelE (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- Doubled finite-dimensional carrier with canonical Krein and grading instances. -/
abbrev FinModelH (n : ℕ) : Type := HilbertDoubled (FinModelE n)

variable (n : ℕ)

/-- Canonical split Cl(1,1) action on the doubled finite-dimensional carrier. -/
noncomputable def finModelCl11Action :
    InfoGeometry.Quantum.RealSplitCl11Action (FinModelH n) :=
  InfoGeometry.Quantum.RealSplitCl11Action.ofContinuousLinearEquiv
    (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := FinModelE n))
    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := FinModelE n))

/-- Concrete bounded Kasparov cycle test model on the doubled finite-dimensional carrier. -/
noncomputable def trivialKasparovCycle : KasparovCycle ℝ ℝ (FinModelH n) where
  cl11 := finModelCl11Action n
  π := Algebra.ofId ℝ (EndH (FinModelH n))
  ρ := Algebra.ofId ℝ (EndH (FinModelH n))
  π_even := by
    intro a
    apply ContinuousLinearMap.ext
    intro x
    change KreinGradedModule.gradeCLM (H := FinModelH n) (a • KreinGradedModule.gradeCLM (H := FinModelH n) x) = a • x
    rw [map_smul]
    congr 1
    exact (KreinGradedModule.grade_invol (H := FinModelH n) x)
  ρ_even := by
    intro b
    apply ContinuousLinearMap.ext
    intro x
    change KreinGradedModule.gradeCLM (H := FinModelH n) (b • KreinGradedModule.gradeCLM (H := FinModelH n) x) = b • x
    rw [map_smul]
    congr 1
    exact (KreinGradedModule.grade_invol (H := FinModelH n) x)
  F := 0
  F_odd := by
    unfold KreinGradedModule.IsOdd KreinGradedModule.gradeConj
    simp
  F_skewAdj := by
    simp [KreinSpace.IsKreinSkewAdjoint]
  F_sq_one_compact := by
    simpa using (isCompactEnd_of_finiteDimensional
      (H := FinModelH n) (A := (-(1 : EndH (FinModelH n)))))
  comm_compact := by
    intro a
    simpa using (isCompactEnd_zero (H := FinModelH n))
  superComm_eps_compact := by
    simp
    exact isCompactEnd_zero (H := FinModelH n)
  superComm_J_compact := by
    simp
    exact isCompactEnd_zero (H := FinModelH n)

/-- End-to-end concrete product packaging for the trivial finite-dimensional test cycle. -/
noncomputable def trivialKasparovProductData :
    KasparovProductData
      ℝ ℝ ℝ
      (FinModelH n) (FinModelH n) (FinModelH n)
      (trivialKasparovCycle n) (trivialKasparovCycle n) :=
  trivialKasparovCycle n

@[simp] lemma trivialKasparovProductData_F :
    (trivialKasparovProductData n).F = 0 := rfl

section NontrivialFiniteDimWitnesses

open InfoGeometry.KK.ClNNFredholmBridge
open InfoGeometry.KK.FiniteTensorProduct
open scoped TensorProduct InfoGeometry.KK.FiniteTensorProduct

/-- Standard `90°` rotation `(x₀, x₁) ↦ (-x₁, x₀)` on `FinModelE 2`. -/
noncomputable def rot90E2 : EndH (FinModelE 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then -(x.ofLp 1) else x.ofLp 0)
      map_add' := fun x y => by
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext i
        fin_cases i <;> simp [add_comm]
      map_smul' := fun r x => by
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext i
        fin_cases i <;> simp }

@[simp] lemma rot90E2_apply (x : FinModelE 2) (i : Fin 2) :
    (rot90E2 x).ofLp i = if i = 0 then -(x.ofLp 1) else x.ofLp 0 := rfl

lemma rot90E2_sq : rot90E2 * rot90E2 = -1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext i
  fin_cases i <;> simp [mul_apply_eq_comp]

lemma rot90E2_adjoint : ContinuousLinearMap.adjoint rot90E2 = -rot90E2 := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
  simp only [neg_apply, PiLp.inner_apply, Fin.sum_univ_two, rot90E2_apply,
    RCLike.inner_apply, conj_trivial]
  norm_num
  ring

/-- Rank-1 coordinate projection `(x₀, x₁) ↦ (x₀, 0)` on `FinModelE 2`. -/
noncomputable def proj0E2 : EndH (FinModelE 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then x.ofLp 0 else 0)
      map_add' := fun x y => by
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext i
        fin_cases i <;> simp
      map_smul' := fun r x => by
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        ext i
        fin_cases i <;> simp }

@[simp] lemma proj0E2_apply (x : FinModelE 2) (i : Fin 2) :
    (proj0E2 x).ofLp i = if i = 0 then x.ofLp 0 else 0 := rfl

/-- Standard first basis vector `e₀ = (1, 0)` in `FinModelE 2`. -/
noncomputable def e0E2 : FinModelE 2 :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)

/-- Standard second basis vector `e₁ = (0, 1)` in `FinModelE 2`. -/
noncomputable def e1E2 : FinModelE 2 :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1)

@[simp] lemma e0E2_ofLp (i : Fin 2) :
    e0E2.ofLp i = if i = 0 then (1 : ℝ) else 0 := rfl

@[simp] lemma e1E2_ofLp (i : Fin 2) :
    e1E2.ofLp i = if i = 0 then (0 : ℝ) else 1 := rfl

lemma rot90E2_e0 : rot90E2 e0E2 = e1E2 := by
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext i
  fin_cases i <;> simp

lemma proj0E2_e0 : proj0E2 e0E2 = e0E2 := by
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext i
  fin_cases i <;> simp

lemma proj0E2_e1 : proj0E2 e1E2 = 0 := by
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext i
  fin_cases i <;> simp

/-- Diagonal bounded-operator lift `EndH E →ₐ[ℝ] EndH (HilbertDoubled E)`. -/
noncomputable def diagHilbertDoubledAlgHom {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    EndH E →ₐ[ℝ] EndH (HilbertDoubled E) where
  toFun T := conjugateDoubledEnd (E := E) (diagDoubledAlgHom (E := E) T)
  map_one' := by
    rw [map_one]
    exact conjugateDoubledEnd_id (E := E)
  map_mul' S T := by
    rw [map_mul]
    exact conjugateDoubledEnd_comp (E := E) _ _
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    simp [conjugateDoubledEnd]
  map_add' S T := by
    apply ContinuousLinearMap.ext
    intro x
    simp [conjugateDoubledEnd]
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro x
    simp [conjugateDoubledEnd, Algebra.algebraMap_eq_smul_one]

/-- Off-diagonal doubled operator `(x, y) ↦ (B y, -B x)` on `DoubledSpace E`. -/
noncomputable def doubledOffDiagSkew {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : EndH E) : EndH (DoubledSpace E) where
  toFun u := to_doubled (B (WithLp.snd u)) (-(B (WithLp.fst u)))
  map_add' u v := by
    apply DoubledSpace.ext <;> simp [map_add]
    abel
  map_smul' r u := by
    apply DoubledSpace.ext <;> simp [map_smul, smul_neg]
  cont := by
    exact (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := E) (β := E)).comp
      ((B.continuous.comp (WithLp.continuous_snd (p := (2 : ENNReal)) (α := E) (β := E))).prodMk
        (continuous_neg.comp
          (B.continuous.comp (WithLp.continuous_fst (p := (2 : ENNReal)) (α := E) (β := E)))))

@[simp] lemma doubledOffDiagSkew_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : EndH E) (u : DoubledSpace E) :
    doubledOffDiagSkew B u = to_doubled (B (WithLp.snd u)) (-(B (WithLp.fst u))) := rfl

private lemma doubledOffDiagSkew_kreinInner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {B : EndH E} (hB : ContinuousLinearMap.adjoint B = -B) (u v : DoubledSpace E) :
    KreinSpace.kreinInner (doubledOffDiagSkew B u) v +
      KreinSpace.kreinInner u (doubledOffDiagSkew B v) = 0 := by
  have hB' : ∀ a b : E, ⟪B a, b⟫_ℝ = -⟪a, B b⟫_ℝ := by
    intro a b
    rw [← ContinuousLinearMap.adjoint_inner_right, hB, neg_apply, inner_neg_right]
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> rfl
  have hv : v = to_doubled (WithLp.fst v) (WithLp.snd v) := by
    apply DoubledSpace.ext <;> rfl
  nth_rw 2 [hu]
  nth_rw 1 [hv]
  nth_rw 2 [hv]
  rw [doubledOffDiagSkew_apply, doubledOffDiagSkew_apply,
    kreinInner_to_doubled, kreinInner_to_doubled]
  simp only [snd_to_doubled, inner_neg_left, inner_neg_right, hB']
  ring

/--
Nontrivial finite-dimensional `RealSplitKreinKasparovCycle` witness on `FinModelH 2`
with `F ≠ 0`, `F * F = 1`, `IsOdd F`, `IsKreinSkewAdjoint F`, and `[F, π a] ≠ 0`,
contrasting with `trivialKasparovCycle` (`F = 0`).
-/
noncomputable def nontrivialKasparovCycle :
    RealSplitKreinKasparovCycle (EndH (FinModelE 2)) ℝ (FinModelH 2) where
  cl11 := finModelCl11Action 2
  π := diagHilbertDoubledAlgHom (E := FinModelE 2)
  ρ := Algebra.ofId ℝ (EndH (FinModelH 2))
  π_even := fun a => by
    unfold KreinGradedModule.IsEven KreinGradedModule.gradeConj
    rw [hilbertDoubled_default_grade_eq_jCLM]
    apply ContinuousLinearMap.ext
    intro u
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    change KreinSpace.jCLM (H := FinModelH 2)
        (diagHilbertDoubledAlgHom a (KreinSpace.jCLM (H := FinModelH 2) u)) =
      diagHilbertDoubledAlgHom a u
    rw [← conjugateDoubledEnd_spectral_epsilon_jCLM]
    change ((conjugateDoubledEnd (E := FinModelE 2) (spectral_epsilon (E := FinModelE 2))).comp
        ((conjugateDoubledEnd (E := FinModelE 2) (diagDoubledAlgHom a)).comp
          (conjugateDoubledEnd (E := FinModelE 2) (spectral_epsilon (E := FinModelE 2))))) u =
      conjugateDoubledEnd (E := FinModelE 2) (diagDoubledAlgHom a) u
    rw [← conjugateDoubledEnd_comp, ← conjugateDoubledEnd_comp]
    congr 2
    apply ContinuousLinearMap.ext
    intro d
    apply DoubledSpace.ext <;> simp [spectral_epsilon, diagDoubledAlgHom]
  ρ_even := fun b => by
    unfold KreinGradedModule.IsEven KreinGradedModule.gradeConj
    apply ContinuousLinearMap.ext
    intro x
    change KreinGradedModule.gradeCLM (H := FinModelH 2)
        (b • KreinGradedModule.gradeCLM (H := FinModelH 2) x) = b • x
    rw [map_smul, KreinGradedModule.gradeCLM_apply, KreinGradedModule.gradeCLM_apply,
      KreinGradedModule.grade_invol]
  F := conjugateDoubledEnd (E := FinModelE 2) (doubledOffDiagSkew rot90E2)
  F_odd := by
    unfold KreinGradedModule.IsOdd KreinGradedModule.gradeConj
    rw [hilbertDoubled_default_grade_eq_jCLM, ← conjugateDoubledEnd_spectral_epsilon_jCLM]
    rw [← conjugateDoubledEnd_comp, ← conjugateDoubledEnd_comp]
    apply ContinuousLinearMap.ext
    intro u
    change conjugateDoubledEnd (E := FinModelE 2) _ u =
      -(conjugateDoubledEnd (E := FinModelE 2) (doubledOffDiagSkew rot90E2) u)
    apply (HilbertDoubled.toDoubledContinuousLinearEquiv (E := FinModelE 2)).injective
    apply DoubledSpace.ext <;>
      simp [conjugateDoubledEnd, spectral_epsilon, doubledOffDiagSkew]
  F_skewAdj := by
    rw [KreinSpace.isKreinSkewAdjoint_iff]
    intro u v
    have hIso : ∀ w₁ w₂ : FinModelH 2,
        KreinSpace.kreinInner w₁ w₂ =
          KreinSpace.kreinInner
            ((HilbertDoubled.toDoubledContinuousLinearEquiv (E := FinModelE 2)) w₁)
            ((HilbertDoubled.toDoubledContinuousLinearEquiv (E := FinModelE 2)) w₂) :=
      fun _ _ => rfl
    rw [hIso, hIso]
    exact doubledOffDiagSkew_kreinInner rot90E2_adjoint _ _
  F_sq_one_compact := isCompactEnd_of_finiteDimensional (H := FinModelH 2) _
  comm_compact := fun _ => isCompactEnd_of_finiteDimensional (H := FinModelH 2) _
  superComm_eps_compact := isCompactEnd_of_finiteDimensional (H := FinModelH 2) _
  superComm_J_compact := isCompactEnd_of_finiteDimensional (H := FinModelH 2) _

theorem nontrivialKasparovCycle_F_sq :
    nontrivialKasparovCycle.F * nontrivialKasparovCycle.F = 1 := by
  change conjugateDoubledEnd (E := FinModelE 2) (doubledOffDiagSkew rot90E2) *
      conjugateDoubledEnd (E := FinModelE 2) (doubledOffDiagSkew rot90E2) = 1
  change (conjugateDoubledEnd (E := FinModelE 2) (doubledOffDiagSkew rot90E2)).comp
      (conjugateDoubledEnd (E := FinModelE 2) (doubledOffDiagSkew rot90E2)) =
    ContinuousLinearMap.id ℝ (FinModelH 2)
  rw [← conjugateDoubledEnd_comp]
  have hsq : (doubledOffDiagSkew rot90E2).comp (doubledOffDiagSkew rot90E2) =
      ContinuousLinearMap.id ℝ (DoubledSpace (FinModelE 2)) := by
    apply ContinuousLinearMap.ext
    intro d
    have hrot : ∀ x : FinModelE 2, rot90E2 (rot90E2 x) = -x := fun x => by
      simpa [mul_apply_eq_comp] using congrArg (fun T : EndH (FinModelE 2) => T x) rot90E2_sq
    apply DoubledSpace.ext <;> simp [hrot]
  rw [hsq]
  exact conjugateDoubledEnd_id (E := FinModelE 2)

theorem nontrivialKasparovCycle_F_ne_zero :
    nontrivialKasparovCycle.F ≠ 0 := by
  intro h0
  have h1 := congrArg (fun T : EndH (FinModelH 2) =>
    WithLp.fst ((HilbertDoubled.toDoubledContinuousLinearEquiv (E := FinModelE 2))
      (T ((HilbertDoubled.ofDoubledContinuousLinearEquiv (E := FinModelE 2))
        (to_doubled (0 : FinModelE 2) e0E2))))) h0
  have h2 : rot90E2 e0E2 = 0 := by
    simpa [nontrivialKasparovCycle, conjugateDoubledEnd] using h1
  rw [rot90E2_e0] at h2
  have hcoord := congrArg (fun x : FinModelE 2 => x.ofLp 1) h2
  simp at hcoord

theorem nontrivialKasparovCycle_comm_ne_zero :
    nontrivialKasparovCycle.F * nontrivialKasparovCycle.π proj0E2 -
      nontrivialKasparovCycle.π proj0E2 * nontrivialKasparovCycle.F ≠ 0 := by
  intro h0
  let v : FinModelH 2 :=
    (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := FinModelE 2))
      (to_doubled (0 : FinModelE 2) e0E2)
  have h1 := congrArg (fun T : EndH (FinModelH 2) =>
    WithLp.fst ((HilbertDoubled.toDoubledContinuousLinearEquiv (E := FinModelE 2)) (T v))) h0
  have hval : rot90E2 (proj0E2 e0E2) - proj0E2 (rot90E2 e0E2) = 0 := by
    simpa [nontrivialKasparovCycle, v, conjugateDoubledEnd, diagHilbertDoubledAlgHom,
      diagDoubledAlgHom, mul_apply_eq_comp] using h1
  rw [proj0E2_e0, rot90E2_e0, proj0E2_e1, sub_zero] at hval
  have hcoord := congrArg (fun x : FinModelE 2 => x.ofLp 1) hval
  simp at hcoord

theorem nontrivialKasparovCycle_analyticalIndex_eq_zero :
    (nontrivialKasparovCycle.toKasparovCycle).analyticalIndex = 0 :=
  index_bridge_spectral_zero nontrivialKasparovCycle nontrivialKasparovCycle_F_sq

/--
Nontrivial `RealSplitKreinKasparovCycle` witness on M3.2's non-collapsing
`SplitDoubledSpace (FinModelE 2)` carrier (`gradeCLM = splitDoubledModularJ`,
`jCLM = splitDoubledSpectralEpsilon`), also satisfying `F ≠ 0`, `F * F = 1`,
and `[F, π proj0E2] ≠ 0`.
-/
noncomputable def nontrivialSplitKasparovCycle :
    RealSplitKreinKasparovCycle (EndH (FinModelE 2)) ℝ (SplitDoubledSpace (FinModelE 2)) where
  cl11 := SplitDoubledSpace.splitDoubledCl11Action (E := FinModelE 2)
  π := diagSplitDoubledAlgHom (E := FinModelE 2)
  ρ := Algebra.ofId ℝ (EndH (SplitDoubledSpace (FinModelE 2)))
  π_even := diagSplitDoubledAlgHom_isEven (E := FinModelE 2)
  ρ_even := (clSplitStageCycle 1).ρ_even
  F := SplitDoubledSpace.conjEnd (E := FinModelE 2) (doubledOffDiagSkew rot90E2)
  F_odd := by
    unfold KreinGradedModule.IsOdd KreinGradedModule.gradeConj
    apply ContinuousLinearMap.ext
    intro u
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;>
      simp [SplitDoubledSpace.gradeCLM_eq_splitDoubledModularJ,
        SplitDoubledSpace.splitDoubledModularJ, modular_j_apply]
  F_skewAdj := by
    rw [KreinSpace.isKreinSkewAdjoint_iff]
    intro u v
    have hIso : ∀ w₁ w₂ : SplitDoubledSpace (FinModelE 2),
        KreinSpace.kreinInner w₁ w₂ = KreinSpace.kreinInner w₁.toDoubled w₂.toDoubled :=
      fun _ _ => rfl
    rw [hIso, hIso]
    exact doubledOffDiagSkew_kreinInner rot90E2_adjoint u.toDoubled v.toDoubled
  F_sq_one_compact := isCompactEnd_of_finiteDimensional (H := SplitDoubledSpace (FinModelE 2)) _
  comm_compact := fun _ =>
    isCompactEnd_of_finiteDimensional (H := SplitDoubledSpace (FinModelE 2)) _
  superComm_eps_compact :=
    isCompactEnd_of_finiteDimensional (H := SplitDoubledSpace (FinModelE 2)) _
  superComm_J_compact :=
    isCompactEnd_of_finiteDimensional (H := SplitDoubledSpace (FinModelE 2)) _

theorem nontrivialSplitKasparovCycle_F_sq :
    nontrivialSplitKasparovCycle.F * nontrivialSplitKasparovCycle.F = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  have hrot : ∀ x : FinModelE 2, rot90E2 (rot90E2 x) = -x := fun x => by
    simpa [mul_apply_eq_comp] using congrArg (fun T : EndH (FinModelE 2) => T x) rot90E2_sq
  apply SplitDoubledSpace.ext
  apply DoubledSpace.ext <;>
    simp [nontrivialSplitKasparovCycle, mul_apply_eq_comp, hrot]

theorem nontrivialSplitKasparovCycle_F_ne_zero :
    nontrivialSplitKasparovCycle.F ≠ 0 := by
  intro h0
  have h1 := congrArg (fun T : EndH (SplitDoubledSpace (FinModelE 2)) =>
    WithLp.fst (T ⟨to_doubled (0 : FinModelE 2) e0E2⟩).toDoubled) h0
  have h2 : rot90E2 e0E2 = 0 := by simpa [nontrivialSplitKasparovCycle] using h1
  rw [rot90E2_e0] at h2
  have hcoord := congrArg (fun x : FinModelE 2 => x.ofLp 1) h2
  simp at hcoord

theorem nontrivialSplitKasparovCycle_comm_ne_zero :
    nontrivialSplitKasparovCycle.F * nontrivialSplitKasparovCycle.π proj0E2 -
      nontrivialSplitKasparovCycle.π proj0E2 * nontrivialSplitKasparovCycle.F ≠ 0 := by
  intro h0
  let v : SplitDoubledSpace (FinModelE 2) := ⟨to_doubled (0 : FinModelE 2) e0E2⟩
  have h1 := congrArg (fun T : EndH (SplitDoubledSpace (FinModelE 2)) =>
    WithLp.fst (T v).toDoubled) h0
  have hval : rot90E2 (proj0E2 e0E2) - proj0E2 (rot90E2 e0E2) = 0 := by
    change rot90E2 (proj0E2 e0E2) - proj0E2 (rot90E2 e0E2) = 0 at h1
    exact h1
  rw [proj0E2_e0, rot90E2_e0, proj0E2_e1, sub_zero] at hval
  have hcoord := congrArg (fun x : FinModelE 2 => x.ofLp 1) hval
  simp at hcoord

/-- Chiral-asymmetric operator `(x, y) ↦ (B (x + y), -B (x + y))` on `DoubledSpace E`. -/
noncomputable def doubledChiralSkew {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : EndH E) : EndH (DoubledSpace E) where
  toFun u :=
    to_doubled (B (WithLp.fst u + WithLp.snd u)) (-(B (WithLp.fst u + WithLp.snd u)))
  map_add' u v := by
    apply DoubledSpace.ext <;>
      simp only [fst_to_doubled, snd_to_doubled, WithLp.add_fst, WithLp.add_snd,
        ← map_add, ← neg_add]
    · congr 1; abel
    · congr 2; abel
  map_smul' r u := by
    apply DoubledSpace.ext <;>
      simp [WithLp.smul_fst, WithLp.smul_snd, map_smul, smul_add, smul_neg]
  cont := by
    have hsum : Continuous (fun u : DoubledSpace E => WithLp.fst u + WithLp.snd u) :=
      (WithLp.continuous_fst (p := (2 : ENNReal)) (α := E) (β := E)).add
        (WithLp.continuous_snd (p := (2 : ENNReal)) (α := E) (β := E))
    exact (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := E) (β := E)).comp
      ((B.continuous.comp hsum).prodMk (continuous_neg.comp (B.continuous.comp hsum)))

@[simp] lemma doubledChiralSkew_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : EndH E) (u : DoubledSpace E) :
    doubledChiralSkew B u =
      to_doubled (B (WithLp.fst u + WithLp.snd u)) (-(B (WithLp.fst u + WithLp.snd u))) := rfl

private lemma doubledChiralSkew_kreinInner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {B : EndH E} (hB : ContinuousLinearMap.adjoint B = -B) (u v : DoubledSpace E) :
    KreinSpace.kreinInner (doubledChiralSkew B u) v +
      KreinSpace.kreinInner u (doubledChiralSkew B v) = 0 := by
  have hB' : ∀ a b : E, ⟪B a, b⟫_ℝ = -⟪a, B b⟫_ℝ := by
    intro a b
    rw [← ContinuousLinearMap.adjoint_inner_right, hB, neg_apply, inner_neg_right]
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> rfl
  have hv : v = to_doubled (WithLp.fst v) (WithLp.snd v) := by
    apply DoubledSpace.ext <;> rfl
  nth_rw 2 [hu]
  nth_rw 1 [hv]
  nth_rw 2 [hv]
  rw [doubledChiralSkew_apply, doubledChiralSkew_apply,
    kreinInner_to_doubled, kreinInner_to_doubled]
  simp only [snd_to_doubled, inner_neg_left, inner_neg_right, map_add,
    inner_add_left, inner_add_right, hB']
  ring

/--
Nonzero-analytical-index `RealSplitKreinKasparovCycle` witness on
`SplitDoubledSpace (FinModelE 2)`: `F(x, y) := (rot90E2 (x + y), -rot90E2 (x + y))`
vanishes identically on `H₋ = {(x, -x)}` and has trivial kernel on `H₊ = {(x, x)}`,
yielding `analyticalIndex = -2 ≠ 0`.
-/
noncomputable def nontrivialChiralIndexCycle :
    RealSplitKreinKasparovCycle (EndH (FinModelE 2)) ℝ (SplitDoubledSpace (FinModelE 2)) where
  cl11 := SplitDoubledSpace.splitDoubledCl11Action (E := FinModelE 2)
  π := diagSplitDoubledAlgHom (E := FinModelE 2)
  ρ := Algebra.ofId ℝ (EndH (SplitDoubledSpace (FinModelE 2)))
  π_even := diagSplitDoubledAlgHom_isEven (E := FinModelE 2)
  ρ_even := (clSplitStageCycle 1).ρ_even
  F := SplitDoubledSpace.conjEnd (E := FinModelE 2) (doubledChiralSkew rot90E2)
  F_odd := by
    unfold KreinGradedModule.IsOdd KreinGradedModule.gradeConj
    apply ContinuousLinearMap.ext
    intro u
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;>
      simp only [SplitDoubledSpace.gradeCLM_eq_splitDoubledModularJ,
        SplitDoubledSpace.splitDoubledModularJ, SplitDoubledSpace.conjEnd_apply,
        doubledChiralSkew_apply, modular_j_apply, fst_to_doubled, snd_to_doubled,
        ContinuousLinearMap.comp_apply, neg_apply, SplitDoubledSpace.toDoubled_neg,
        WithLp.neg_fst, WithLp.neg_snd, neg_neg] <;>
      rw [add_comm]
  F_skewAdj := by
    rw [KreinSpace.isKreinSkewAdjoint_iff]
    intro u v
    have hIso : ∀ w₁ w₂ : SplitDoubledSpace (FinModelE 2),
        KreinSpace.kreinInner w₁ w₂ = KreinSpace.kreinInner w₁.toDoubled w₂.toDoubled :=
      fun _ _ => rfl
    rw [hIso, hIso]
    exact doubledChiralSkew_kreinInner rot90E2_adjoint u.toDoubled v.toDoubled
  F_sq_one_compact := isCompactEnd_of_finiteDimensional (H := SplitDoubledSpace (FinModelE 2)) _
  comm_compact := fun _ =>
    isCompactEnd_of_finiteDimensional (H := SplitDoubledSpace (FinModelE 2)) _
  superComm_eps_compact :=
    isCompactEnd_of_finiteDimensional (H := SplitDoubledSpace (FinModelE 2)) _
  superComm_J_compact :=
    isCompactEnd_of_finiteDimensional (H := SplitDoubledSpace (FinModelE 2)) _

theorem nontrivialChiralIndexCycle_analyticalIndex_eq :
    (nontrivialChiralIndexCycle.toKasparovCycle).analyticalIndex = -2 := by
  have hrot_inj : Function.Injective rot90E2 := by
    intro x y hxy
    have hsq : ∀ z : FinModelE 2, rot90E2 (rot90E2 z) = -z := fun z => by
      simpa [mul_apply_eq_comp] using congrArg (fun T : EndH (FinModelE 2) => T z) rot90E2_sq
    have hneg := congrArg rot90E2 hxy
    rw [hsq, hsq] at hneg
    exact neg_inj.mp hneg
  have hPlus : RealSplitKreinKasparovCycle.chiralKernelSlicePlus nontrivialChiralIndexCycle = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rcases hu with ⟨huKer, ⟨w, rfl⟩⟩
    change nontrivialChiralIndexCycle.F
        (KreinGradedModule.gradeProjPlus (H := SplitDoubledSpace (FinModelE 2)) w) = 0 at huKer
    have hEqFst :
        rot90E2 (WithLp.fst
            ((KreinGradedModule.gradeProjPlus (H := SplitDoubledSpace (FinModelE 2)) w).toDoubled) +
          WithLp.snd
            ((KreinGradedModule.gradeProjPlus (H := SplitDoubledSpace (FinModelE 2)) w).toDoubled)) =
          0 := by
      simpa [nontrivialChiralIndexCycle, doubledChiralSkew] using
        congrArg (fun z : SplitDoubledSpace (FinModelE 2) => WithLp.fst z.toDoubled) huKer
    have hGp :
        WithLp.fst ((KreinGradedModule.gradeProjPlus (H := SplitDoubledSpace (FinModelE 2)) w).toDoubled) =
          (2 : ℝ)⁻¹ • (WithLp.fst w.toDoubled + WithLp.snd w.toDoubled) ∧
        WithLp.snd ((KreinGradedModule.gradeProjPlus (H := SplitDoubledSpace (FinModelE 2)) w).toDoubled) =
          (2 : ℝ)⁻¹ • (WithLp.fst w.toDoubled + WithLp.snd w.toDoubled) := by
      constructor <;>
        simp [KreinGradedModule.gradeProjPlus, SplitDoubledSpace.gradeCLM_eq_splitDoubledModularJ,
          SplitDoubledSpace.splitDoubledModularJ, modular_j_apply, WithLp.add_fst, WithLp.add_snd,
          WithLp.smul_fst, WithLp.smul_snd, add_comm]
    rw [hGp.1, hGp.2, ← two_smul ℝ, smul_smul, show (2 : ℝ) * (2 : ℝ)⁻¹ = 1 by norm_num,
      one_smul] at hEqFst
    have hSumZero : WithLp.fst w.toDoubled + WithLp.snd w.toDoubled = 0 := by
      apply hrot_inj
      simpa using hEqFst
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext
    · simp [hGp.1, hSumZero]
    · simp [hGp.2, hSumZero]
  have hMinus :
      RealSplitKreinKasparovCycle.chiralKernelSliceMinus nontrivialChiralIndexCycle =
        LinearMap.range
          (KreinGradedModule.gradeProjMinus (H := SplitDoubledSpace (FinModelE 2))).toLinearMap := by
    refine inf_eq_right.mpr ?_
    rintro u ⟨w, rfl⟩
    change nontrivialChiralIndexCycle.F
        (KreinGradedModule.gradeProjMinus (H := SplitDoubledSpace (FinModelE 2)) w) = 0
    have hGm :
        WithLp.fst ((KreinGradedModule.gradeProjMinus (H := SplitDoubledSpace (FinModelE 2)) w).toDoubled) +
          WithLp.snd ((KreinGradedModule.gradeProjMinus (H := SplitDoubledSpace (FinModelE 2)) w).toDoubled) =
          0 := by
      simp [KreinGradedModule.gradeProjMinus, SplitDoubledSpace.gradeCLM_eq_splitDoubledModularJ,
        SplitDoubledSpace.splitDoubledModularJ, modular_j_apply, WithLp.sub_fst, WithLp.sub_snd,
        WithLp.smul_fst, WithLp.smul_snd, ← smul_add]
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext
    · simp only [nontrivialChiralIndexCycle, SplitDoubledSpace.conjEnd_apply,
        doubledChiralSkew_apply, fst_to_doubled]
      rw [hGm, map_zero]
      rfl
    · simp only [nontrivialChiralIndexCycle, SplitDoubledSpace.conjEnd_apply,
        doubledChiralSkew_apply, snd_to_doubled]
      rw [hGm, map_zero, neg_zero]
      rfl
  let eMinus :
      FinModelE 2 ≃ₗ[ℝ]
        LinearMap.range
          (KreinGradedModule.gradeProjMinus (H := SplitDoubledSpace (FinModelE 2))).toLinearMap :=
    { toFun := fun x =>
        ⟨⟨to_doubled x (-x)⟩,
          ⟨⟨to_doubled ((2 : ℝ) • x) 0⟩, by
            apply SplitDoubledSpace.ext
            apply DoubledSpace.ext <;>
              simp [KreinGradedModule.gradeProjMinus,
                SplitDoubledSpace.gradeCLM_eq_splitDoubledModularJ,
                SplitDoubledSpace.splitDoubledModularJ, modular_j_apply, WithLp.sub_fst,
                WithLp.sub_snd, WithLp.smul_fst, WithLp.smul_snd, smul_smul]⟩⟩
      invFun := fun u => WithLp.fst u.1.toDoubled
      left_inv := fun x => by simp
      right_inv := fun u => by
        rcases u with ⟨u, w, hw⟩
        apply Subtype.ext
        have hu :
            WithLp.fst u.toDoubled + WithLp.snd u.toDoubled = 0 := by
          rw [← hw]
          simp [KreinGradedModule.gradeProjMinus,
            SplitDoubledSpace.gradeCLM_eq_splitDoubledModularJ,
            SplitDoubledSpace.splitDoubledModularJ, modular_j_apply, WithLp.sub_fst,
            WithLp.sub_snd, WithLp.smul_fst, WithLp.smul_snd, ← smul_add]
        have hsnd : WithLp.snd u.toDoubled = -(WithLp.fst u.toDoubled) :=
          eq_neg_of_add_eq_zero_right hu
        apply SplitDoubledSpace.ext
        apply DoubledSpace.ext
        · rfl
        · exact hsnd.symm
      map_add' := fun x y => by
        apply Subtype.ext
        apply SplitDoubledSpace.ext
        apply DoubledSpace.ext <;> simp [WithLp.add_fst, WithLp.add_snd]
        abel
      map_smul' := fun r x => by
        apply Subtype.ext
        apply SplitDoubledSpace.ext
        apply DoubledSpace.ext <;> simp [WithLp.smul_fst, WithLp.smul_snd, smul_neg] }
  have hFinrankMinus :
      Module.finrank ℝ
          (LinearMap.range
            (KreinGradedModule.gradeProjMinus (H := SplitDoubledSpace (FinModelE 2))).toLinearMap) =
        2 := by
    rw [← eMinus.finrank_eq]
    exact finrank_euclideanSpace_fin
  unfold KasparovCycle.analyticalIndex RealSplitKreinKasparovCycle.finiteAnalyticalIndex
  rw [RealSplitKreinKasparovCycle.analyticalIndex_eq_finrank_chiralKernelDifference]
  rw [hPlus, hMinus, finrank_bot, hFinrankMinus]
  norm_num

/-- Scalar-algebra restriction of `nontrivialKasparovCycle` for tensor-product pairing over `B = ℝ`. -/
noncomputable def nontrivialScalarKasparovCycle :
    RealSplitKreinKasparovCycle ℝ ℝ (FinModelH 2) where
  cl11 := nontrivialKasparovCycle.cl11
  π := Algebra.ofId ℝ (EndH (FinModelH 2))
  ρ := nontrivialKasparovCycle.ρ
  π_even := nontrivialKasparovCycle.ρ_even
  ρ_even := nontrivialKasparovCycle.ρ_even
  F := nontrivialKasparovCycle.F
  F_odd := nontrivialKasparovCycle.F_odd
  F_skewAdj := nontrivialKasparovCycle.F_skewAdj
  F_sq_one_compact := nontrivialKasparovCycle.F_sq_one_compact
  comm_compact := fun r => by
    have hcomm :
        nontrivialKasparovCycle.F * Algebra.ofId ℝ (EndH (FinModelH 2)) r -
          Algebra.ofId ℝ (EndH (FinModelH 2)) r * nontrivialKasparovCycle.F = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      change nontrivialKasparovCycle.F (r • x) - r • nontrivialKasparovCycle.F x = 0
      simp [map_smul]
    rw [hcomm]
    exact isCompactEnd_zero (H := FinModelH 2)
  superComm_eps_compact := nontrivialKasparovCycle.superComm_eps_compact
  superComm_J_compact := nontrivialKasparovCycle.superComm_J_compact

/--
Concrete `BUCKET 2` finite-dimensional `KasparovProductData` witness applying
`FiniteTensorProduct.finiteDimTensorProduct` to `nontrivialKasparovCycle` and
`nontrivialScalarKasparovCycle`, with `F₁₂ ≠ 0` and `F₁₂ * F₁₂ = 1`.
-/
noncomputable def nontrivialKasparovProductData :
    KasparovProductData
      (EndH (FinModelE 2)) ℝ ℝ
      (FinModelH 2) (FinModelH 2) (FinModelH 2 ⊗[ℝ] FinModelH 2)
      nontrivialKasparovCycle nontrivialScalarKasparovCycle :=
  FiniteTensorProduct.finiteDimTensorProduct
    nontrivialKasparovCycle nontrivialScalarKasparovCycle
    (by
      unfold KreinGradedModule.IsEven KreinGradedModule.gradeConj
      rw [hilbertDoubled_default_grade_eq_jCLM]
      apply ContinuousLinearMap.ext
      intro u
      change KreinSpace.jCLM (H := FinModelH 2)
          (KreinSpace.jCLM (H := FinModelH 2) (KreinSpace.jCLM (H := FinModelH 2) u)) =
        KreinSpace.jCLM (H := FinModelH 2) u
      rw [KreinSpace.jCLM_apply, KreinSpace.jCLM_apply, KreinSpace.J_invol])

theorem nontrivialKasparovProductData_F_sq :
    nontrivialKasparovProductData.F * nontrivialKasparovProductData.F = 1 :=
  FiniteTensorProduct.finiteDimTensorPhase_sq_eq_one_of_sq_one
    nontrivialKasparovCycle nontrivialScalarKasparovCycle
    nontrivialKasparovCycle_F_sq nontrivialKasparovCycle_F_sq

theorem nontrivialKasparovProductData_F_ne_zero :
    nontrivialKasparovProductData.F ≠ 0 := by
  intro h0
  let v₀ : FinModelH 2 :=
    (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := FinModelE 2))
      (to_doubled (0 : FinModelE 2) e0E2)
  have hsq := nontrivialKasparovProductData_F_sq
  rw [h0, zero_mul] at hsq
  have hvec : (0 : FinModelH 2 ⊗[ℝ] FinModelH 2) = v₀ ⊗ₜ[ℝ] v₀ := by
    have hpt := congrArg (fun T : EndH (FinModelH 2 ⊗[ℝ] FinModelH 2) =>
      T (v₀ ⊗ₜ[ℝ] v₀)) hsq
    simpa using hpt
  have hInner := congrArg (fun z : FinModelH 2 ⊗[ℝ] FinModelH 2 =>
    inner (𝕜 := ℝ) z (v₀ ⊗ₜ[ℝ] v₀)) hvec
  rw [inner_zero_left, TensorProduct.inner_tmul] at hInner
  have hv0 : 0 < inner (𝕜 := ℝ) v₀ v₀ := by
    refine real_inner_self_pos.mpr ?_
    intro hv
    have hfst := congrArg (fun w : FinModelH 2 =>
      (WithLp.snd ((HilbertDoubled.toDoubledContinuousLinearEquiv (E := FinModelE 2)) w)).ofLp 0)
      hv
    simp [v₀] at hfst
  exact ne_of_lt (mul_pos hv0 hv0) hInner

end NontrivialFiniteDimWitnesses

end InfoGeometry.KK
