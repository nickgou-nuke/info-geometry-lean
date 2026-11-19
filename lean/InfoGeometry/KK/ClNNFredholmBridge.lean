/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.KK.CompactOperatorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Canonical.SplitCliffordTowerUnification
import InfoGeometry.Krein.RealDoubledHilbertBridge
import InfoGeometry.Krein.RealDoubledOperatorAdjointTransport
import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace GradedTensorProduct

/-!
# InfoGeometry.KK.ClNNFredholmBridge

Bridge from the split `Cl(n,n)` Clifford tower (`Clsplit n`) to the bounded
real split-Krein Fredholm/Kasparov layer:
1. Preserves the first-step `Cl(1,1)` atom identifications (`section FirstStep`).
2. Introduces the non-aliased carrier `SplitDoubledSpace E` (`structure`, not `abbrev`)
   whose default `KreinSpace` (`jCLM` = transported `spectral_epsilon`) and
   `KreinGradedModule` (`gradeCLM` = transported `modular_j`) instances do not
   collapse under `HilbertDoubled`/`NeutralSpace` type-aliasing.
3. Constructs arbitrary finite-stage `Clsplit n` representations and
   `RealSplitKreinKasparovCycle` objects on `StageKreinH n := SplitDoubledSpace (StageVec n)`
   via M2's `SplitCliffordTowerUnification` (`clSplitEquivClTowerReal`,
   `clTowerEquivMatrix`), together with the graded-tensor successor action
   `clSplitDoubledSuccRep n` via `clsplit_succ_equiv n` and explicit `n = 0, 1, 2`
   stage characterizations.
4. Proves isometric Krein carrier transport (`eH : H ≃ₗᵢ[ℝ] H'`) for
   `kreinInner`, `kreinAdjoint`, `RealSplitCl11Action`, and
   `RealSplitKreinKasparovCycle`, including `SplitDoubledSpace.toDoubledLIE`.
5. Classifies and proves non-tautological operator distinctness across
   `DoubledSpace E`, `SplitDoubledSpace E`, `StageKreinH n`, and
   `HilbertDoubled E` (both the collapsed default `instKreinGradedModuleNeutral`
   realization and the unmasked `instKreinGradedModuleHilbertDoubled` realization).
-/

namespace InfoGeometry.KK.ClNNFredholmBridge

open InfoGeometry.KK
open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.CliffordTower
open InfoGeometry.Canonical.SplitCliffordTowerUnification
  (clSplitEquivClTowerReal clTowerEquivMatrix splitZeroEquivReal)

attribute [local instance] InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis.instAlgebraClTower

section FirstStep

variable {A B E : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

@[rep_depth operator] theorem
    RealSplitKreinKasparovCycle.firstStep_leftGenerator_eq_cl11Rep
    (X : RealSplitKreinKasparovCycle A B (DoubledSpace E))
    (hcl11 : X.cl11 = doubledSpaceCl11Action (E := E)) :
    X.cl11.J
      = InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)) := by
  simpa [hcl11] using doubledSpaceCl11Action_J_eq_cl11Rep_leftGenerator (E := E)

@[rep_depth operator] theorem
    RealSplitKreinKasparovCycle.firstStep_rightGenerator_eq_cl11Rep
    (X : RealSplitKreinKasparovCycle A B (DoubledSpace E))
    (hcl11 : X.cl11 = doubledSpaceCl11Action (E := E)) :
    X.K
      = InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) := by
  simpa [RealSplitKreinKasparovCycle.K, hcl11] using
    doubledSpaceCl11Action_K_eq_cl11Rep_rightGenerator (E := E)

@[rep_depth operator] theorem
    RealSplitKreinKasparovCycle.firstStep_pseudoscalar_eq_cl11Rep
    (X : RealSplitKreinKasparovCycle A B (DoubledSpace E))
    (hcl11 : X.cl11 = doubledSpaceCl11Action (E := E)) :
    X.cl11.eps
      = InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)
            * CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) := by
  simpa [hcl11] using doubledSpaceCl11Action_eps_eq_cl11Rep_pseudoscalar (E := E)

end FirstStep

section SplitDoubledCarrier

/-- Dedicated non-aliased carrier wrapper around `DoubledSpace E`. Because it is a
`structure` (not an `abbrev`), its default `KreinSpace` (`jCLM` = transported
`spectral_epsilon`) and `KreinGradedModule` (`gradeCLM` = transported `modular_j`)
instances cannot be overridden by `NeutralSpace E`. -/
@[ext]
structure SplitDoubledSpace (E : Type*) where
  toDoubled : DoubledSpace E

namespace SplitDoubledSpace

section AlgebraicInstances

variable {E : Type*}

lemma toDoubled_injective :
    Function.Injective (toDoubled : SplitDoubledSpace E → DoubledSpace E) :=
  fun u v h => by cases u; cases v; cases h; rfl

section NormedGroup

variable [NormedAddCommGroup E]

instance : Add (SplitDoubledSpace E) := ⟨fun u v => ⟨u.toDoubled + v.toDoubled⟩⟩
instance : Zero (SplitDoubledSpace E) := ⟨⟨0⟩⟩
instance : Neg (SplitDoubledSpace E) := ⟨fun u => ⟨-u.toDoubled⟩⟩
instance : Sub (SplitDoubledSpace E) := ⟨fun u v => ⟨u.toDoubled - v.toDoubled⟩⟩
instance : SMul ℕ (SplitDoubledSpace E) := ⟨fun n u => ⟨n • u.toDoubled⟩⟩
instance : SMul ℤ (SplitDoubledSpace E) := ⟨fun z u => ⟨z • u.toDoubled⟩⟩

@[simp] lemma toDoubled_zero : (0 : SplitDoubledSpace E).toDoubled = 0 := rfl
@[simp] lemma toDoubled_add (u v : SplitDoubledSpace E) :
    (u + v).toDoubled = u.toDoubled + v.toDoubled := rfl
@[simp] lemma toDoubled_neg (u : SplitDoubledSpace E) :
    (-u).toDoubled = -u.toDoubled := rfl
@[simp] lemma toDoubled_sub (u v : SplitDoubledSpace E) :
    (u - v).toDoubled = u.toDoubled - v.toDoubled := rfl

noncomputable instance : AddCommGroup (SplitDoubledSpace E) :=
  Function.Injective.addCommGroup toDoubled toDoubled_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Additive equivalence `SplitDoubledSpace E ≃+ DoubledSpace E`. -/
noncomputable def toDoubledAddEquiv : SplitDoubledSpace E ≃+ DoubledSpace E where
  toFun := toDoubled
  invFun := mk
  left_inv u := by cases u; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

noncomputable instance : NormedAddCommGroup (SplitDoubledSpace E) :=
  NormedAddCommGroup.induced (SplitDoubledSpace E) (DoubledSpace E)
    toDoubledAddEquiv (AddEquiv.injective _)

@[simp] lemma norm_eq (u : SplitDoubledSpace E) : ‖u‖ = ‖u.toDoubled‖ := rfl

end NormedGroup

end AlgebraicInstances

section HilbertAndKreinInstances

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

instance : SMul ℝ (SplitDoubledSpace E) := ⟨fun r u => ⟨r • u.toDoubled⟩⟩

omit [CompleteSpace E] in
@[simp] lemma toDoubled_smul (r : ℝ) (u : SplitDoubledSpace E) :
    (r • u).toDoubled = r • u.toDoubled := rfl

noncomputable instance : Module ℝ (SplitDoubledSpace E) :=
  Function.Injective.module ℝ toDoubledAddEquiv.toAddMonoidHom toDoubled_injective
    (fun _ _ => rfl)

noncomputable instance : Inner ℝ (SplitDoubledSpace E) where
  inner u v := ⟪u.toDoubled, v.toDoubled⟫_ℝ

omit [CompleteSpace E] in
@[simp] lemma inner_eq (u v : SplitDoubledSpace E) :
    ⟪u, v⟫_ℝ = ⟪u.toDoubled, v.toDoubled⟫_ℝ := rfl

noncomputable instance : InnerProductSpace ℝ (SplitDoubledSpace E) where
  norm_smul_le r u := by
    change ‖r • u.toDoubled‖ ≤ ‖r‖ * ‖u.toDoubled‖
    exact norm_smul_le r u.toDoubled
  norm_sq_eq_re_inner u := by
    change ‖u.toDoubled‖ ^ 2 = RCLike.re ⟪u.toDoubled, u.toDoubled⟫_ℝ
    exact norm_sq_eq_re_inner u.toDoubled
  conj_inner_symm u v := by
    change starRingEnd ℝ ⟪v.toDoubled, u.toDoubled⟫_ℝ = ⟪u.toDoubled, v.toDoubled⟫_ℝ
    exact inner_conj_symm (𝕜 := ℝ) u.toDoubled v.toDoubled
  add_left u v w := by
    change ⟪u.toDoubled + v.toDoubled, w.toDoubled⟫_ℝ =
      ⟪u.toDoubled, w.toDoubled⟫_ℝ + ⟪v.toDoubled, w.toDoubled⟫_ℝ
    exact inner_add_left u.toDoubled v.toDoubled w.toDoubled
  smul_left u v r := by
    change ⟪r • u.toDoubled, v.toDoubled⟫_ℝ =
      (starRingEnd ℝ) r * ⟪u.toDoubled, v.toDoubled⟫_ℝ
    simpa using real_inner_smul_left u.toDoubled v.toDoubled r

/-- Uniform equivalence `SplitDoubledSpace E ≃ᵤ DoubledSpace E` induced by `toDoubled`. -/
noncomputable def toDoubledUniformEquiv : SplitDoubledSpace E ≃ᵤ DoubledSpace E where
  toEquiv := toDoubledAddEquiv.toEquiv
  uniformContinuous_toFun := uniformContinuous_iff_le_comap.mpr le_rfl
  uniformContinuous_invFun := uniformContinuous_comap' uniformContinuous_id

noncomputable instance : CompleteSpace (SplitDoubledSpace E) :=
  (completeSpace_congr (toDoubledUniformEquiv (E := E)).isUniformEmbedding).mpr inferInstance

/-- Canonical linear isometry equivalence `SplitDoubledSpace E ≃ₗᵢ[ℝ] DoubledSpace E`. -/
noncomputable def toDoubledLIE : SplitDoubledSpace E ≃ₗᵢ[ℝ] DoubledSpace E where
  toFun := toDoubled
  invFun := mk
  left_inv u := by cases u; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- Canonical linear isometry equivalence `DoubledSpace E ≃ₗᵢ[ℝ] SplitDoubledSpace E`. -/
noncomputable def ofDoubledLIE : DoubledSpace E ≃ₗᵢ[ℝ] SplitDoubledSpace E :=
  (toDoubledLIE (E := E)).symm

omit [CompleteSpace E] in
@[simp] lemma toDoubledLIE_apply (u : SplitDoubledSpace E) :
    toDoubledLIE (E := E) u = u.toDoubled := rfl

omit [CompleteSpace E] in
@[simp] lemma ofDoubledLIE_apply (d : DoubledSpace E) :
    ofDoubledLIE (E := E) d = ⟨d⟩ := rfl

noncomputable instance instFiniteDimensional [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (SplitDoubledSpace E) :=
  (ofDoubledLIE (E := E)).toLinearEquiv.finiteDimensional

instance instNontrivial [Nontrivial E] : Nontrivial (SplitDoubledSpace E) :=
  (ofDoubledLIE (E := E)).injective.nontrivial

/-- Conjugation of bounded operators from `DoubledSpace E` onto `SplitDoubledSpace E`. -/
noncomputable def conjEnd (T : EndH (DoubledSpace E)) : EndH (SplitDoubledSpace E) :=
  (ofDoubledLIE (E := E)).conjStarAlgEquiv T

@[simp] lemma conjEnd_apply (T : EndH (DoubledSpace E)) (u : SplitDoubledSpace E) :
    conjEnd (E := E) T u = ⟨T u.toDoubled⟩ := rfl

lemma conjEnd_injective : Function.Injective (conjEnd (E := E)) :=
  (ofDoubledLIE (E := E)).conjStarAlgEquiv.injective

/-- Transported fundamental symmetry `spectral_epsilon` on `SplitDoubledSpace E`. -/
noncomputable def splitDoubledSpectralEpsilon : EndH (SplitDoubledSpace E) :=
  conjEnd (E := E) (spectral_epsilon (E := E))

/-- Transported modular swap `modular_j` on `SplitDoubledSpace E`. -/
noncomputable def splitDoubledModularJ : EndH (SplitDoubledSpace E) :=
  conjEnd (E := E) (modular_j (E := E))

/-- Transported real complex structure `complex_i = modular_j ∘ spectral_epsilon` on
`SplitDoubledSpace E`. -/
noncomputable def splitDoubledComplexI : EndH (SplitDoubledSpace E) :=
  conjEnd (E := E) (complex_i (E := E))

noncomputable instance : KreinSpace (SplitDoubledSpace E) where
  J := (toDoubledLIE (E := E)).trans ((KreinSpace.J (H := DoubledSpace E)).trans (ofDoubledLIE (E := E)))
  J_invol u := by
    apply SplitDoubledSpace.ext
    exact KreinSpace.J_invol (H := DoubledSpace E) u.toDoubled
  J_selfAdj u v := by
    exact KreinSpace.J_selfAdj (H := DoubledSpace E) u.toDoubled v.toDoubled

@[simp] lemma jCLM_eq_splitDoubledSpectralEpsilon :
    KreinSpace.jCLM (H := SplitDoubledSpace E) = splitDoubledSpectralEpsilon (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply SplitDoubledSpace.ext
  change (KreinSpace.J (H := DoubledSpace E)) u.toDoubled = spectral_epsilon (E := E) u.toDoubled
  rw [← KreinSpace.jCLM_apply, InfoGeometry.Krein.jCLM_eq_spectral_epsilon]

noncomputable instance : KreinGradedModule (SplitDoubledSpace E) where
  grade :=
    { toFun := fun u => ⟨modular_j (E := E) u.toDoubled⟩
      invFun := fun u => ⟨modular_j (E := E) u.toDoubled⟩
      left_inv := fun u => by
        apply SplitDoubledSpace.ext
        apply DoubledSpace.ext <;> simp [modular_j_apply]
      right_inv := fun u => by
        apply SplitDoubledSpace.ext
        apply DoubledSpace.ext <;> simp [modular_j_apply]
      map_add' := fun u v => by
        apply SplitDoubledSpace.ext
        simp [map_add]
      map_smul' := fun r u => by
        apply SplitDoubledSpace.ext
        simp [map_smul]
      norm_map' := fun u => by
        change ‖modular_j (E := E) u.toDoubled‖ = ‖u.toDoubled‖
        have hsq : ‖modular_j (E := E) u.toDoubled‖ ^ 2 = ‖u.toDoubled‖ ^ 2 := by
          rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
          simp [modular_j_apply, add_comm]
        nlinarith [norm_nonneg (modular_j (E := E) u.toDoubled), norm_nonneg u.toDoubled, hsq] }
  grade_invol u := by
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;> simp [modular_j_apply]
  grade_selfAdj u v := by
    change ⟪modular_j (E := E) u.toDoubled, v.toDoubled⟫_ℝ =
      ⟪u.toDoubled, modular_j (E := E) v.toDoubled⟫_ℝ
    simp [modular_j_apply, WithLp.prod_inner_apply, add_comm]

@[simp] lemma gradeCLM_eq_splitDoubledModularJ :
    KreinGradedModule.gradeCLM (H := SplitDoubledSpace E) = splitDoubledModularJ (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- Canonical real split `Cl(1,1)` action on `SplitDoubledSpace E` transported from
`doubledSpaceCl11Action` via `ofDoubledLIE`. -/
noncomputable def splitDoubledCl11Action : RealSplitCl11Action (SplitDoubledSpace E) :=
  RealSplitCl11Action.ofContinuousLinearEquiv
    (ofDoubledLIE (E := E)).toContinuousLinearEquiv
    (doubledSpaceCl11Action (E := E))

@[simp] lemma splitDoubledCl11Action_J :
    (splitDoubledCl11Action (E := E)).J = splitDoubledModularJ (E := E) := rfl

@[simp] lemma splitDoubledCl11Action_eps :
    (splitDoubledCl11Action (E := E)).eps = splitDoubledSpectralEpsilon (E := E) := rfl

@[simp] lemma splitDoubledCl11Action_K :
    (splitDoubledCl11Action (E := E)).K = splitDoubledComplexI (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply SplitDoubledSpace.ext
  rfl

end HilbertAndKreinInstances

end SplitDoubledSpace

end SplitDoubledCarrier

section SplitTowerStages

/-- Stage-`n` finite-dimensional Euclidean Hilbert carrier of dimension `2^n`. -/
abbrev StageVec (n : ℕ) : Type := EuclideanSpace ℝ (Fin (2 ^ n))

/-- Stage-`n` graded double-real Krein Hilbert carrier `SplitDoubledSpace (StageVec n)`.
Its default `KreinSpace` (`jCLM = splitDoubledSpectralEpsilon`) and `KreinGradedModule`
(`gradeCLM = splitDoubledModularJ`) instances are uniquely synthesized without `NeutralSpace`
type aliasing. -/
abbrev StageKreinH (n : ℕ) : Type := SplitDoubledSpace (StageVec n)

/-- Real algebra equivalence identifying `M_{2^n}(ℝ)` with bounded operators `EndH (StageVec n)`. -/
noncomputable def matrixToStageEnd (n : ℕ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ ≃ₐ[ℝ] EndH (StageVec n) where
  toFun M := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)
  invFun f := Matrix.toEuclideanLin.symm f.toLinearMap
  left_inv M := by
    change Matrix.toEuclideanLin.symm (Matrix.toEuclideanLin M) = M
    exact Matrix.toEuclideanLin.symm_apply_apply M
  right_inv f := by
    apply ContinuousLinearMap.ext
    intro v
    change Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm f.toLinearMap) v = f v
    rw [Matrix.toEuclideanLin.apply_symm_apply]
    rfl
  map_mul' A B := by
    apply ContinuousLinearMap.ext
    intro v
    change Matrix.toEuclideanLin (A * B) v =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v)
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro v
    change Matrix.toEuclideanLin (A + B) v =
      Matrix.toEuclideanLin A v + Matrix.toEuclideanLin B v
    simp [map_add]
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro v
    change Matrix.toEuclideanLin (algebraMap ℝ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) r) v =
      r • v
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    simp [Matrix.toEuclideanLin, Algebra.algebraMap_eq_smul_one]

/-- Stage-`n` faithful `Clsplit n` algebra equivalence onto `EndH (StageVec n)` via M2's
`clSplitEquivClTowerReal` and `clTowerEquivMatrix`. -/
noncomputable def clSplitToStageEnd (n : ℕ) :
    Clsplit n ≃ₐ[ℝ] EndH (StageVec n) :=
  ((clSplitEquivClTowerReal n).trans (clTowerEquivMatrix ℝ n)).trans (matrixToStageEnd n)

/-- Diagonal bounded-operator lift `EndH E →ₐ[ℝ] EndH (SplitDoubledSpace E)` sending
`T` to `(x, ξ) ↦ (T x, T ξ)`. -/
noncomputable def diagSplitDoubledAlgHom {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    EndH E →ₐ[ℝ] EndH (SplitDoubledSpace E) where
  toFun T :=
    { toFun := fun u =>
        ⟨to_doubled (T (WithLp.fst u.toDoubled)) (T (WithLp.snd u.toDoubled))⟩
      map_add' := fun u v => by
        apply SplitDoubledSpace.ext
        apply DoubledSpace.ext <;> simp [map_add]
      map_smul' := fun c u => by
        apply SplitDoubledSpace.ext
        apply DoubledSpace.ext <;> simp [map_smul]
      cont := by
        refine (SplitDoubledSpace.ofDoubledLIE (E := E)).continuous.comp ?_
        exact (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := E) (β := E)).comp
          ((T.continuous.comp
              ((WithLp.continuous_fst (p := (2 : ENNReal)) (α := E) (β := E)).comp
                (SplitDoubledSpace.toDoubledLIE (E := E)).continuous)).prodMk
            (T.continuous.comp
              ((WithLp.continuous_snd (p := (2 : ENNReal)) (α := E) (β := E)).comp
                (SplitDoubledSpace.toDoubledLIE (E := E)).continuous))) }
  map_one' := by
    apply ContinuousLinearMap.ext
    intro u
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;> simp
  map_mul' S T := by
    apply ContinuousLinearMap.ext
    intro u
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;> rfl
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro u
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;> simp
  map_add' S T := by
    apply ContinuousLinearMap.ext
    intro u
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext
    · change WithLp.fst (to_doubled ((S + T) (WithLp.fst u.toDoubled))
          ((S + T) (WithLp.snd u.toDoubled))) =
        WithLp.fst (to_doubled (S (WithLp.fst u.toDoubled)) (S (WithLp.snd u.toDoubled)) +
          to_doubled (T (WithLp.fst u.toDoubled)) (T (WithLp.snd u.toDoubled)))
      simp [WithLp.add_fst]
    · change WithLp.snd (to_doubled ((S + T) (WithLp.fst u.toDoubled))
          ((S + T) (WithLp.snd u.toDoubled))) =
        WithLp.snd (to_doubled (S (WithLp.fst u.toDoubled)) (S (WithLp.snd u.toDoubled)) +
          to_doubled (T (WithLp.fst u.toDoubled)) (T (WithLp.snd u.toDoubled)))
      simp [WithLp.add_snd]
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro u
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;> simp [Algebra.algebraMap_eq_smul_one]

lemma diagSplitDoubledAlgHom_injective {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    Function.Injective (diagSplitDoubledAlgHom (E := E)) := by
  intro S T hST
  apply ContinuousLinearMap.ext
  intro x
  have hpt := congrArg (fun f : EndH (SplitDoubledSpace E) =>
    WithLp.fst (f ⟨to_doubled x (0 : E)⟩).toDoubled) hST
  change S x = T x at hpt
  exact hpt

lemma diagSplitDoubledAlgHom_isEven {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (T : EndH E) :
    KreinGradedModule.IsEven (H := SplitDoubledSpace E) (diagSplitDoubledAlgHom (E := E) T) := by
  unfold KreinGradedModule.IsEven KreinGradedModule.gradeConj
  apply ContinuousLinearMap.ext
  intro u
  apply SplitDoubledSpace.ext
  apply DoubledSpace.ext
  · change WithLp.fst (modular_j (to_doubled (T (WithLp.fst (modular_j u.toDoubled)))
        (T (WithLp.snd (modular_j u.toDoubled))))) =
      T (WithLp.fst u.toDoubled)
    simp [modular_j_apply]
  · change WithLp.snd (modular_j (to_doubled (T (WithLp.fst (modular_j u.toDoubled)))
        (T (WithLp.snd (modular_j u.toDoubled))))) =
      T (WithLp.snd u.toDoubled)
    simp [modular_j_apply]

/-- Faithful representation of `Clsplit n` on the graded double-real Krein carrier `StageKreinH n`. -/
noncomputable def clSplitStageRep (n : ℕ) :
    Clsplit n →ₐ[ℝ] EndH (StageKreinH n) :=
  (diagSplitDoubledAlgHom (E := StageVec n)).comp (clSplitToStageEnd n).toAlgHom

theorem clSplitStageRep_injective (n : ℕ) :
    Function.Injective (clSplitStageRep n) :=
  (diagSplitDoubledAlgHom_injective (E := StageVec n)).comp
    (clSplitToStageEnd n).injective

/-- Stage-`n` `RealSplitKreinKasparovCycle` hosting `Clsplit n` (via `clSplitToStageEnd n`)
alongside `splitDoubledCl11Action` on `StageKreinH n`. Under default typeclass synthesis,
`gradeCLM = cl11.J` and `jCLM = cl11.eps`, so `gradeCLM ≠ jCLM` and `gradeCLM ≠ cl11.eps`. -/
noncomputable def clSplitStageCycle (n : ℕ) :
    RealSplitKreinKasparovCycle (EndH (StageVec n)) ℝ (StageKreinH n) where
  cl11 := SplitDoubledSpace.splitDoubledCl11Action (E := StageVec n)
  π := diagSplitDoubledAlgHom (E := StageVec n)
  ρ := Algebra.ofId ℝ (EndH (StageKreinH n))
  π_even := diagSplitDoubledAlgHom_isEven (E := StageVec n)
  ρ_even := fun r => by
    unfold KreinGradedModule.IsEven KreinGradedModule.gradeConj
    apply ContinuousLinearMap.ext
    intro u
    have hcomp : (KreinGradedModule.gradeCLM (H := StageKreinH n)).comp
        (KreinGradedModule.gradeCLM (H := StageKreinH n)) =
        ContinuousLinearMap.id ℝ (StageKreinH n) :=
      KreinGradedModule.gradeCLM_comp_self
    change KreinGradedModule.gradeCLM (H := StageKreinH n)
        (r • KreinGradedModule.gradeCLM (H := StageKreinH n) u) = r • u
    rw [map_smul]
    have hgg : KreinGradedModule.gradeCLM (H := StageKreinH n)
        (KreinGradedModule.gradeCLM (H := StageKreinH n) u) = u :=
      congrArg (fun f : EndH (StageKreinH n) => f u) hcomp
    rw [hgg]
  F := 0
  F_odd := by simp [KreinGradedModule.IsOdd]
  F_skewAdj := by simp [KreinSpace.IsKreinSkewAdjoint]
  F_sq_one_compact := isCompactEnd_of_finiteDimensional _
  comm_compact := fun _ => by simp [isCompactEnd_zero]
  superComm_eps_compact := by simp [isCompactEnd_zero]
  superComm_J_compact := by simp [isCompactEnd_zero]

@[simp] theorem clSplitStageCycle_pi_comp_clSplitToStageEnd (n : ℕ) (x : Clsplit n) :
    (clSplitStageCycle n).π (clSplitToStageEnd n x) = clSplitStageRep n x := rfl

theorem clSplitStageCycle_gradeCLM_eq_J (n : ℕ) :
    KreinGradedModule.gradeCLM (H := StageKreinH n) = (clSplitStageCycle n).cl11.J := by
  simp [clSplitStageCycle]

theorem clSplitStageCycle_jCLM_eq_eps (n : ℕ) :
    KreinSpace.jCLM (H := StageKreinH n) = (clSplitStageCycle n).cl11.eps := by
  simp [clSplitStageCycle]

/-- Diagonal bounded-operator lift `EndH E →ₐ[ℝ] EndH (DoubledSpace E)`. -/
noncomputable def diagDoubledAlgHom {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    EndH E →ₐ[ℝ] EndH (DoubledSpace E) where
  toFun T :=
    { toFun := fun u => to_doubled (T (WithLp.fst u)) (T (WithLp.snd u))
      map_add' := fun u v => by
        apply DoubledSpace.ext <;> simp [map_add]
      map_smul' := fun c u => by
        apply DoubledSpace.ext <;> simp [map_smul]
      cont := by
        exact (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := E) (β := E)).comp
          ((T.continuous.comp
            (WithLp.continuous_fst (p := (2 : ENNReal)) (α := E) (β := E))).prodMk
           (T.continuous.comp
            (WithLp.continuous_snd (p := (2 : ENNReal)) (α := E) (β := E)))) }
  map_one' := by
    apply ContinuousLinearMap.ext; intro u; apply DoubledSpace.ext <;> simp
  map_mul' S T := by
    apply ContinuousLinearMap.ext; intro u; apply DoubledSpace.ext <;> rfl
  map_zero' := by
    apply ContinuousLinearMap.ext; intro u; apply DoubledSpace.ext <;> simp
  map_add' S T := by
    apply ContinuousLinearMap.ext; intro u; apply DoubledSpace.ext <;> simp
  commutes' r := by
    apply ContinuousLinearMap.ext; intro u; apply DoubledSpace.ext <;> simp [Algebra.algebraMap_eq_smul_one]

/-- Parity-twisted tail action of `Clsplit n` on `DoubledSpace (StageVec n)`:
`b ↦ ((x, ξ) ↦ (ρ_n b x, ρ_n (involute b) ξ))`. -/
noncomputable def tailDoubledRep (n : ℕ) :
    Clsplit n →ₐ[ℝ] EndH (DoubledSpace (StageVec n)) where
  toFun b :=
    { toFun := fun u =>
        to_doubled
          (clSplitToStageEnd n b (WithLp.fst u))
          (clSplitToStageEnd n (CliffordAlgebra.involute b) (WithLp.snd u))
      map_add' := fun u v => by
        apply DoubledSpace.ext <;> simp [map_add]
      map_smul' := fun c u => by
        apply DoubledSpace.ext <;> simp [map_smul]
      cont := by
        exact (WithLp.prod_continuous_toLp (p := (2 : ENNReal))
            (α := StageVec n) (β := StageVec n)).comp
          (((clSplitToStageEnd n b).continuous.comp
            (WithLp.continuous_fst (p := (2 : ENNReal))
              (α := StageVec n) (β := StageVec n))).prodMk
           ((clSplitToStageEnd n (CliffordAlgebra.involute b)).continuous.comp
            (WithLp.continuous_snd (p := (2 : ENNReal))
              (α := StageVec n) (β := StageVec n)))) }
  map_one' := by
    apply ContinuousLinearMap.ext; intro u; apply DoubledSpace.ext <;> simp
  map_mul' a b := by
    apply ContinuousLinearMap.ext; intro u; apply DoubledSpace.ext
    · simp [map_mul]
    · simp [map_mul]
  map_zero' := by
    apply ContinuousLinearMap.ext; intro u; apply DoubledSpace.ext <;> simp
  map_add' a b := by
    apply ContinuousLinearMap.ext; intro u; apply DoubledSpace.ext <;> simp [map_add]
  commutes' r := by
    apply ContinuousLinearMap.ext; intro u; apply DoubledSpace.ext <;>
      simp [Algebra.algebraMap_eq_smul_one]

private lemma diagDoubledAlgHom_comm_cl11Rep {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : EndH E) (x : CliffordAlgebra InfoGeometry.Clifford.splitQ11) :
    diagDoubledAlgHom T * InfoGeometry.Krein.cl11Rep (E := E) x =
      InfoGeometry.Krein.cl11Rep (E := E) x * diagDoubledAlgHom T := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      rw [AlgHom.commutes, Algebra.commutes]
  | ι v =>
      rw [InfoGeometry.Krein.cl11Rep_ι_apply]
      apply ContinuousLinearMap.ext
      intro u
      apply DoubledSpace.ext <;>
        simp [diagDoubledAlgHom, InfoGeometry.Krein.cl11RepLin,
          WithLp.add_fst, WithLp.add_snd, WithLp.smul_fst, WithLp.smul_snd,
          modular_j_apply, complex_i_apply]
  | add a b ha hb =>
      rw [map_add, mul_add, add_mul, ha, hb]
  | mul a b ha hb =>
      rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]

private lemma cl11Rep_involute {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : CliffordAlgebra InfoGeometry.Clifford.splitQ11) :
    InfoGeometry.Krein.cl11Rep (E := E) (CliffordAlgebra.involute x) =
      spectral_epsilon (E := E) * InfoGeometry.Krein.cl11Rep (E := E) x *
        spectral_epsilon (E := E) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      have heps : spectral_epsilon (E := E) * spectral_epsilon (E := E) = 1 :=
        spectral_epsilon_involution E
      rw [CliffordAlgebra.involute.commutes, AlgHom.commutes, ← Algebra.commutes, mul_assoc,
        heps, mul_one]
  | ι v =>
      rw [CliffordAlgebra.involute_ι, map_neg, InfoGeometry.Krein.cl11Rep_ι_apply]
      apply ContinuousLinearMap.ext
      intro u
      apply DoubledSpace.ext <;>
        (simp [InfoGeometry.Krein.cl11RepLin, WithLp.add_fst, WithLp.add_snd,
          WithLp.smul_fst, WithLp.smul_snd, modular_j_apply, complex_i_apply]; try abel)
  | add a b ha hb =>
      rw [map_add, map_add, ha, hb, map_add, mul_add, add_mul]
  | mul a b ha hb =>
      have heps : spectral_epsilon (E := E) * spectral_epsilon (E := E) = 1 :=
        spectral_epsilon_involution E
      rw [map_mul, map_mul, ha, hb, map_mul]
      calc
        spectral_epsilon * InfoGeometry.Krein.cl11Rep (E := E) a * spectral_epsilon *
            (spectral_epsilon * InfoGeometry.Krein.cl11Rep (E := E) b * spectral_epsilon)
            = spectral_epsilon * InfoGeometry.Krein.cl11Rep (E := E) a *
                (spectral_epsilon * spectral_epsilon) *
                (InfoGeometry.Krein.cl11Rep (E := E) b * spectral_epsilon) := by
              simp only [mul_assoc]
        _ = spectral_epsilon *
              (InfoGeometry.Krein.cl11Rep (E := E) a * InfoGeometry.Krein.cl11Rep (E := E) b) *
              spectral_epsilon := by
              rw [heps, mul_one]
              simp only [mul_assoc]

private lemma tailDoubledRep_even_eq (n : ℕ) (b : Clsplit n)
    (hb : CliffordAlgebra.involute b = b) :
    tailDoubledRep n b = diagDoubledAlgHom (clSplitToStageEnd n b) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [tailDoubledRep, diagDoubledAlgHom, hb]

private lemma tailDoubledRep_odd_eq (n : ℕ) (b : Clsplit n)
    (hb : CliffordAlgebra.involute b = -b) :
    tailDoubledRep n b = diagDoubledAlgHom (clSplitToStageEnd n b) * spectral_epsilon := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [tailDoubledRep, diagDoubledAlgHom, hb, map_neg]

private lemma cl11Rep_comm_eps_of_even {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : CliffordAlgebra InfoGeometry.Clifford.splitQ11)
    (hx : x ∈ CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 0) :
    InfoGeometry.Krein.cl11Rep (E := E) x * spectral_epsilon (E := E) =
      spectral_epsilon (E := E) * InfoGeometry.Krein.cl11Rep (E := E) x := by
  have heps : spectral_epsilon (E := E) * spectral_epsilon (E := E) = 1 :=
    spectral_epsilon_involution E
  have hinvx := cl11Rep_involute (E := E) x
  rw [CliffordAlgebra.involute_eq_of_mem_even hx] at hinvx
  calc
    InfoGeometry.Krein.cl11Rep (E := E) x * spectral_epsilon
        = (spectral_epsilon * InfoGeometry.Krein.cl11Rep (E := E) x *
            spectral_epsilon) * spectral_epsilon := by rw [← hinvx]
    _ = spectral_epsilon * InfoGeometry.Krein.cl11Rep (E := E) x *
          (spectral_epsilon * spectral_epsilon) := by simp only [mul_assoc]
    _ = spectral_epsilon * InfoGeometry.Krein.cl11Rep (E := E) x := by rw [heps, mul_one]

private lemma cl11Rep_anticomm_eps_of_odd {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : CliffordAlgebra InfoGeometry.Clifford.splitQ11)
    (hx : x ∈ CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 1) :
    InfoGeometry.Krein.cl11Rep (E := E) x * spectral_epsilon (E := E) =
      -(spectral_epsilon (E := E) * InfoGeometry.Krein.cl11Rep (E := E) x) := by
  have heps : spectral_epsilon (E := E) * spectral_epsilon (E := E) = 1 :=
    spectral_epsilon_involution E
  have hinvx := cl11Rep_involute (E := E) x
  rw [CliffordAlgebra.involute_eq_of_mem_odd hx, map_neg] at hinvx
  have hneg : -(InfoGeometry.Krein.cl11Rep (E := E) x * spectral_epsilon) =
      spectral_epsilon * InfoGeometry.Krein.cl11Rep (E := E) x := by
    have hstep : -(InfoGeometry.Krein.cl11Rep (E := E) x * spectral_epsilon (E := E)) =
        (-InfoGeometry.Krein.cl11Rep (E := E) x) * spectral_epsilon (E := E) :=
      (ContinuousLinearMap.neg_comp _ _).symm
    rw [hstep, hinvx]
    calc
      spectral_epsilon * InfoGeometry.Krein.cl11Rep (E := E) x * spectral_epsilon *
          spectral_epsilon
          = spectral_epsilon * InfoGeometry.Krein.cl11Rep (E := E) x *
              (spectral_epsilon * spectral_epsilon) := by simp only [mul_assoc]
      _ = spectral_epsilon * InfoGeometry.Krein.cl11Rep (E := E) x := by rw [heps, mul_one]
  exact neg_eq_iff_eq_neg.mp hneg

private lemma cl11Rep_tailDoubledRep_supercommute (n : ℕ) {i j : ZMod 2}
    (x : CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 i)
    (b : CliffordAlgebra.evenOdd (Qsplit n) j) :
    InfoGeometry.Krein.cl11Rep (E := StageVec n) x * tailDoubledRep n b =
      (-1 : ℤˣ) ^ (j * i) •
        (tailDoubledRep n b * InfoGeometry.Krein.cl11Rep (E := StageVec n) x) := by
  fin_cases i <;> fin_cases j
  · change InfoGeometry.Krein.cl11Rep (E := StageVec n) x * tailDoubledRep n b =
      (-1 : ℤˣ) ^ (0 : ZMod 2) •
        (tailDoubledRep n b * InfoGeometry.Krein.cl11Rep (E := StageVec n) x)
    rw [uzpow_zero, one_smul,
      tailDoubledRep_even_eq n b (CliffordAlgebra.involute_eq_of_mem_even b.property)]
    exact (diagDoubledAlgHom_comm_cl11Rep (clSplitToStageEnd n b) x).symm
  · change InfoGeometry.Krein.cl11Rep (E := StageVec n) x * tailDoubledRep n b =
      (-1 : ℤˣ) ^ (0 : ZMod 2) •
        (tailDoubledRep n b * InfoGeometry.Krein.cl11Rep (E := StageVec n) x)
    rw [uzpow_zero, one_smul,
      tailDoubledRep_odd_eq n b (CliffordAlgebra.involute_eq_of_mem_odd b.property)]
    have hcomm_eps := cl11Rep_comm_eps_of_even (E := StageVec n) x.1 x.property
    calc
      InfoGeometry.Krein.cl11Rep (E := StageVec n) x *
          (diagDoubledAlgHom (clSplitToStageEnd n b) * spectral_epsilon)
          = (InfoGeometry.Krein.cl11Rep (E := StageVec n) x *
              diagDoubledAlgHom (clSplitToStageEnd n b)) * spectral_epsilon := by rw [mul_assoc]
      _ = (diagDoubledAlgHom (clSplitToStageEnd n b) *
              InfoGeometry.Krein.cl11Rep (E := StageVec n) x) *
            spectral_epsilon := by rw [diagDoubledAlgHom_comm_cl11Rep]
      _ = diagDoubledAlgHom (clSplitToStageEnd n b) *
            (InfoGeometry.Krein.cl11Rep (E := StageVec n) x * spectral_epsilon) := by rw [mul_assoc]
      _ = (diagDoubledAlgHom (clSplitToStageEnd n b) * spectral_epsilon) *
            InfoGeometry.Krein.cl11Rep (E := StageVec n) x := by rw [hcomm_eps, ← mul_assoc]
  · change InfoGeometry.Krein.cl11Rep (E := StageVec n) x * tailDoubledRep n b =
      (-1 : ℤˣ) ^ (0 : ZMod 2) •
        (tailDoubledRep n b * InfoGeometry.Krein.cl11Rep (E := StageVec n) x)
    rw [uzpow_zero, one_smul,
      tailDoubledRep_even_eq n b (CliffordAlgebra.involute_eq_of_mem_even b.property)]
    exact (diagDoubledAlgHom_comm_cl11Rep (clSplitToStageEnd n b) x).symm
  · change InfoGeometry.Krein.cl11Rep (E := StageVec n) x * tailDoubledRep n b =
      (-1 : ℤˣ) ^ (1 : ZMod 2) •
        (tailDoubledRep n b * InfoGeometry.Krein.cl11Rep (E := StageVec n) x)
    rw [uzpow_one, Units.neg_smul, one_smul,
      tailDoubledRep_odd_eq n b (CliffordAlgebra.involute_eq_of_mem_odd b.property)]
    have hanti_eps := cl11Rep_anticomm_eps_of_odd (E := StageVec n) x.1 x.property
    have hneg_mul : ∀ A B : EndH (DoubledSpace (StageVec n)),
        A * (-B) = -(A * B) := fun A B => ContinuousLinearMap.comp_neg A B
    calc
      InfoGeometry.Krein.cl11Rep (E := StageVec n) x *
          (diagDoubledAlgHom (clSplitToStageEnd n b) * spectral_epsilon)
          = (InfoGeometry.Krein.cl11Rep (E := StageVec n) x *
              diagDoubledAlgHom (clSplitToStageEnd n b)) * spectral_epsilon := by rw [mul_assoc]
      _ = (diagDoubledAlgHom (clSplitToStageEnd n b) *
              InfoGeometry.Krein.cl11Rep (E := StageVec n) x) *
            spectral_epsilon := by rw [diagDoubledAlgHom_comm_cl11Rep]
      _ = diagDoubledAlgHom (clSplitToStageEnd n b) *
            (InfoGeometry.Krein.cl11Rep (E := StageVec n) x * spectral_epsilon) := by rw [mul_assoc]
      _ = -((diagDoubledAlgHom (clSplitToStageEnd n b) * spectral_epsilon) *
            InfoGeometry.Krein.cl11Rep (E := StageVec n) x) := by
          rw [hanti_eps, hneg_mul, mul_assoc]

/-- Stage-`(n+1)` algebra representation `Clsplit (n + 1) →ₐ[ℝ] EndH (DoubledSpace (StageVec n))`
built from `clsplit_succ_equiv n` (`Cl(1,1) ᵍ⊗ Clsplit n`) and `cl11Rep` / `tailDoubledRep`. -/
noncomputable def clSplitDoubledSuccRep (n : ℕ) :
    Clsplit (n + 1) →ₐ[ℝ] EndH (DoubledSpace (StageVec n)) :=
  (GradedTensorProduct.lift
    (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
    (CliffordAlgebra.evenOdd (Qsplit n))
    (InfoGeometry.Krein.cl11Rep (E := StageVec n)) (tailDoubledRep n)
    (fun {_ _} x b => cl11Rep_tailDoubledRep_supercommute n x b)).comp
      (clsplit_succ_equiv n).toAlgHom

@[simp] theorem clSplitDoubledSuccRep_head (n : ℕ) (v : ℝ × ℝ) :
    clSplitDoubledSuccRep n (CliffordAlgebra.ι (Qsplit (n + 1)) (v, (0 : SplitSpace n))) =
      InfoGeometry.Krein.cl11Rep (E := StageVec n)
        (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 v) := by
  change (GradedTensorProduct.lift
      (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
      (CliffordAlgebra.evenOdd (Qsplit n))
      (InfoGeometry.Krein.cl11Rep (E := StageVec n)) (tailDoubledRep n)
      (fun {_ _} x b => cl11Rep_tailDoubledRep_supercommute n x b))
    ((CliffordAlgebra.prodEquiv InfoGeometry.CliffordTower.Q11 (Qsplit n))
      (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Q11.prod (Qsplit n)) (v, 0))) = _
  rw [CliffordAlgebra.prodEquiv_apply, CliffordAlgebra.ofProd_ι_mk]
  simp [GradedTensorProduct.lift_tmul]

@[simp] theorem clSplitDoubledSuccRep_tail (n : ℕ) (w : SplitSpace n) :
    clSplitDoubledSuccRep n (CliffordAlgebra.ι (Qsplit (n + 1)) ((0 : ℝ × ℝ), w)) =
      tailDoubledRep n (CliffordAlgebra.ι (Qsplit n) w) := by
  change (GradedTensorProduct.lift
      (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
      (CliffordAlgebra.evenOdd (Qsplit n))
      (InfoGeometry.Krein.cl11Rep (E := StageVec n)) (tailDoubledRep n)
      (fun {_ _} x b => cl11Rep_tailDoubledRep_supercommute n x b))
    ((CliffordAlgebra.prodEquiv InfoGeometry.CliffordTower.Q11 (Qsplit n))
      (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Q11.prod (Qsplit n)) (0, w))) = _
  rw [CliffordAlgebra.prodEquiv_apply, CliffordAlgebra.ofProd_ι_mk]
  simp [GradedTensorProduct.lift_tmul]

/-- Stage `n = 0`: `Clsplit 0` is commutative (`≅ ℝ`), so `clSplitStageRep 0` has commutative image. -/
theorem clSplitStageZero_comm (x y : Clsplit 0) :
    clSplitStageRep 0 x * clSplitStageRep 0 y =
      clSplitStageRep 0 y * clSplitStageRep 0 x := by
  have hxy : x * y = y * x := by
    apply splitZeroEquivReal.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  rw [← map_mul (clSplitStageRep 0), hxy, map_mul (clSplitStageRep 0)]

/-- Stage `n = 1`: `clSplitDoubledSuccRep 0` matches the `FirstStep` `cl11Rep` generators
(`J`, `K`, `eps`) on `DoubledSpace (StageVec 0)`. -/
theorem clSplitOne_matches_firstStep {A B : Type*}
    [NormedRing A] [NormedRing B] [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [KreinGradedModule (DoubledSpace (StageVec 0))]
    (X : RealSplitKreinKasparovCycle A B (DoubledSpace (StageVec 0)))
    (hcl11 : X.cl11 = doubledSpaceCl11Action (E := StageVec 0)) :
    clSplitDoubledSuccRep 0 (CliffordAlgebra.ι (Qsplit 1) ((1, 0), (0 : SplitSpace 0))) =
        X.cl11.J ∧
    clSplitDoubledSuccRep 0 (CliffordAlgebra.ι (Qsplit 1) ((0, 1), (0 : SplitSpace 0))) =
        X.K ∧
    clSplitDoubledSuccRep 0
        (CliffordAlgebra.ι (Qsplit 1) ((1, 0), (0 : SplitSpace 0)) *
         CliffordAlgebra.ι (Qsplit 1) ((0, 1), (0 : SplitSpace 0))) =
        X.cl11.eps := by
  refine ⟨?_, ?_, ?_⟩
  · rw [clSplitDoubledSuccRep_head]
    exact (RealSplitKreinKasparovCycle.firstStep_leftGenerator_eq_cl11Rep X hcl11).symm
  · rw [clSplitDoubledSuccRep_head]
    exact (RealSplitKreinKasparovCycle.firstStep_rightGenerator_eq_cl11Rep X hcl11).symm
  · rw [map_mul, clSplitDoubledSuccRep_head, clSplitDoubledSuccRep_head,
      ← map_mul (InfoGeometry.Krein.cl11Rep (E := StageVec 0))]
    exact (RealSplitKreinKasparovCycle.firstStep_pseudoscalar_eq_cl11Rep X hcl11).symm

private lemma add_self_eq_zero_end {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : V →L[ℝ] V} (h : A + A = 0) : A = 0 := by
  ext v
  have hv := congrArg (fun T : V →L[ℝ] V => T v) h
  simp only [add_apply, zero_apply] at hv
  have h2 : (2 : ℝ) • A v = 0 := by simpa [two_smul] using hv
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

private lemma add_self_eq_zero_cl2 {A : Clsplit 2} (h : A + A = 0) : A = 0 := by
  have h2 : (2 : ℝ) • A = 0 := by simpa [two_smul] using h
  rw [← one_smul ℝ A, show (1 : ℝ) = (2 : ℝ)⁻¹ * 2 by norm_num, mul_smul, h2, smul_zero]

/-- Stage `n = 2`: genuine noncommutativity between the head (`Cl(1,1)`) and tail (`Clsplit 1`)
generators inside `Clsplit 2` on both `clSplitStageRep 2` and `clSplitDoubledSuccRep 1`. -/
theorem clSplitStageTwo_noncomm :
    let e₁ : Clsplit 2 := CliffordAlgebra.ι (Qsplit 2) ((1, 0), (0 : SplitSpace 1))
    let e₂ : Clsplit 2 := CliffordAlgebra.ι (Qsplit 2) ((0, 0), ((1, 0), (0 : SplitSpace 0)))
    clSplitStageRep 2 e₁ * clSplitStageRep 2 e₂ ≠
      clSplitStageRep 2 e₂ * clSplitStageRep 2 e₁ ∧
    clSplitDoubledSuccRep 1 e₁ * clSplitDoubledSuccRep 1 e₂ ≠
      clSplitDoubledSuccRep 1 e₂ * clSplitDoubledSuccRep 1 e₁ := by
  intro e₁ e₂
  have he12 : e₁ * e₁ = 1 := by
    rw [CliffordAlgebra.ι_sq_scalar]
    have hq : Qsplit 2 ((1, 0), (0 : SplitSpace 1)) = 1 := by
      simp [Qsplit]
    rw [hq, map_one]
  have he22 : e₂ * e₂ = 1 := by
    rw [CliffordAlgebra.ι_sq_scalar]
    have hq : Qsplit 2 ((0, 0), ((1, 0), (0 : SplitSpace 0))) = 1 := by
      simp [Qsplit]
    rw [hq, map_one]
  have hanti : e₁ * e₂ + e₂ * e₁ = 0 := by
    rw [CliffordAlgebra.ι_mul_ι_add_swap]
    have hpolar : QuadraticMap.polar (Qsplit 2) ((1, 0), (0 : SplitSpace 1))
        ((0, 0), ((1, 0), (0 : SplitSpace 0))) = 0 := by
      simp [QuadraticMap.polar, Qsplit]
    rw [hpolar, map_zero]
  have hprod_sq : (e₁ * e₂) * (e₁ * e₂) = -1 := by
    have hswap : e₂ * e₁ = -(e₁ * e₂) := eq_neg_of_add_eq_zero_right hanti
    calc
      (e₁ * e₂) * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ := by simp only [mul_assoc]
      _ = e₁ * (-(e₁ * e₂)) * e₂ := by rw [hswap]
      _ = -((e₁ * e₁) * (e₂ * e₂)) := by simp only [mul_neg, neg_mul, mul_assoc]
      _ = -1 := by rw [he12, he22, mul_one]
  have he1e2_ne : e₁ * e₂ ≠ e₂ * e₁ := by
    intro hcomm
    have hadd : e₁ * e₂ + e₁ * e₂ = 0 := by
      calc
        e₁ * e₂ + e₁ * e₂ = e₁ * e₂ + e₂ * e₁ := by rw [hcomm]
        _ = 0 := hanti
    have hzero : e₁ * e₂ = 0 := add_self_eq_zero_cl2 hadd
    have hneg1 : (0 : Clsplit 2) = -1 := by
      calc
        (0 : Clsplit 2) = (e₁ * e₂) * (e₁ * e₂) := by rw [hzero, mul_zero]
        _ = -1 := hprod_sq
    have h10 : (1 : Clsplit 2) = 0 := by
      simpa using congrArg Neg.neg hneg1.symm
    exact one_ne_zero h10
  refine ⟨?_, ?_⟩
  · rw [← map_mul (clSplitStageRep 2), ← map_mul (clSplitStageRep 2)]
    exact fun h => he1e2_ne (clSplitStageRep_injective 2 h)
  · intro hcomm
    have hsq_neg1 : (clSplitDoubledSuccRep 1 (e₁ * e₂)) *
        (clSplitDoubledSuccRep 1 (e₁ * e₂)) = -1 := by
      rw [← map_mul (clSplitDoubledSuccRep 1), hprod_sq, map_neg, map_one]
    have hanti_rep : clSplitDoubledSuccRep 1 e₁ * clSplitDoubledSuccRep 1 e₂ +
        clSplitDoubledSuccRep 1 e₂ * clSplitDoubledSuccRep 1 e₁ = 0 := by
      rw [← map_mul (clSplitDoubledSuccRep 1), ← map_mul (clSplitDoubledSuccRep 1),
        ← map_add, hanti, map_zero]
    have hadd : clSplitDoubledSuccRep 1 e₁ * clSplitDoubledSuccRep 1 e₂ +
        clSplitDoubledSuccRep 1 e₁ * clSplitDoubledSuccRep 1 e₂ = 0 := by
      calc
        clSplitDoubledSuccRep 1 e₁ * clSplitDoubledSuccRep 1 e₂ +
            clSplitDoubledSuccRep 1 e₁ * clSplitDoubledSuccRep 1 e₂
            = clSplitDoubledSuccRep 1 e₁ * clSplitDoubledSuccRep 1 e₂ +
                clSplitDoubledSuccRep 1 e₂ * clSplitDoubledSuccRep 1 e₁ := by rw [hcomm]
        _ = 0 := hanti_rep
    have hzero : clSplitDoubledSuccRep 1 e₁ * clSplitDoubledSuccRep 1 e₂ = 0 :=
      add_self_eq_zero_end hadd
    rw [map_mul (clSplitDoubledSuccRep 1), hzero, mul_zero] at hsq_neg1
    have h10 : (1 : EndH (DoubledSpace (StageVec 1))) = 0 := by
      rw [← neg_neg (1 : EndH (DoubledSpace (StageVec 1))), ← hsq_neg1, neg_zero]
    let v : DoubledSpace (StageVec 1) :=
      to_doubled (WithLp.toLp 2 (fun _ : Fin (2 ^ 1) => (1 : ℝ))) 0
    have hv := congrArg (fun T : EndH (DoubledSpace (StageVec 1)) =>
      (WithLp.fst (T v)).ofLp 0) h10
    change (1 : ℝ) = 0 at hv
    exact one_ne_zero hv

end SplitTowerStages

section IsometricKreinTransport

variable {H H' : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]
variable [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H'] [KreinSpace H']

lemma kreinInner_preserve_iff_intertwine_J (eH : H ≃ₗᵢ[ℝ] H') :
    (∀ u v : H, KreinSpace.kreinInner (eH u) (eH v) = KreinSpace.kreinInner u v) ↔
      (∀ x : H, KreinSpace.J (eH x) = eH (KreinSpace.J x)) := by
  constructor
  · intro h x
    apply ext_inner_right ℝ
    intro y'
    obtain ⟨y, rfl⟩ := eH.surjective y'
    calc
      ⟪KreinSpace.J (eH x), eH y⟫_ℝ
          = KreinSpace.kreinInner (eH x) (eH y) := rfl
      _ = KreinSpace.kreinInner x y := h x y
      _ = ⟪KreinSpace.J x, y⟫_ℝ := rfl
      _ = ⟪eH (KreinSpace.J x), eH y⟫_ℝ := (eH.inner_map_map _ _).symm
  · intro heJ u v
    calc
      KreinSpace.kreinInner (eH u) (eH v)
          = ⟪KreinSpace.J (eH u), eH v⟫_ℝ := rfl
      _ = ⟪eH (KreinSpace.J u), eH v⟫_ℝ := by rw [heJ]
      _ = ⟪KreinSpace.J u, v⟫_ℝ := eH.inner_map_map _ _
      _ = KreinSpace.kreinInner u v := rfl

theorem kreinInner_transport_isometry (eH : H ≃ₗᵢ[ℝ] H')
    (heJ : ∀ x : H, KreinSpace.J (eH x) = eH (KreinSpace.J x)) (u v : H) :
    KreinSpace.kreinInner (eH u) (eH v) = KreinSpace.kreinInner u v :=
  (kreinInner_preserve_iff_intertwine_J eH).mpr heJ u v

theorem kreinAdjoint_transport_isometry (eH : H ≃ₗᵢ[ℝ] H')
    (he_inner : ∀ u v : H, KreinSpace.kreinInner (eH u) (eH v) = KreinSpace.kreinInner u v)
    (A : EndH H) :
    eH.conjStarAlgEquiv (KreinSpace.kreinAdjoint A) =
      KreinSpace.kreinAdjoint (eH.conjStarAlgEquiv A) := by
  have heJ : ∀ x : H, KreinSpace.J (eH x) = eH (KreinSpace.J x) :=
    (kreinInner_preserve_iff_intertwine_J eH).mp he_inner
  have hjCLM : eH.conjStarAlgEquiv (KreinSpace.jCLM (H := H)) =
      KreinSpace.jCLM (H := H') := by
    apply ContinuousLinearMap.ext
    intro y'
    obtain ⟨x, rfl⟩ := eH.surjective y'
    change eH (KreinSpace.J (eH.symm (eH x))) = KreinSpace.J (eH x)
    simp [heJ]
  exact InfoGeometry.Krein.StarHomAdjointTransport.map_bounded_kreinAdjoint
    eH.conjStarAlgEquiv.toStarAlgHom (Or.inl hjCLM) A

theorem isKreinSelfAdjoint_transport_isometry (eH : H ≃ₗᵢ[ℝ] H')
    (he_inner : ∀ u v : H, KreinSpace.kreinInner (eH u) (eH v) = KreinSpace.kreinInner u v)
    {A : EndH H} (hA : KreinSpace.IsKreinSelfAdjoint A) :
    KreinSpace.IsKreinSelfAdjoint (eH.conjStarAlgEquiv A) := by
  unfold KreinSpace.IsKreinSelfAdjoint
  rw [← kreinAdjoint_transport_isometry eH he_inner A, hA]

theorem isKreinSkewAdjoint_transport_isometry (eH : H ≃ₗᵢ[ℝ] H')
    (he_inner : ∀ u v : H, KreinSpace.kreinInner (eH u) (eH v) = KreinSpace.kreinInner u v)
    {A : EndH H} (hA : KreinSpace.IsKreinSkewAdjoint A) :
    KreinSpace.IsKreinSkewAdjoint (eH.conjStarAlgEquiv A) := by
  unfold KreinSpace.IsKreinSkewAdjoint
  rw [← kreinAdjoint_transport_isometry eH he_inner A, hA, map_neg]

/-- Transport a `RealSplitCl11Action` along a linear isometry equivalence `eH : H ≃ₗᵢ[ℝ] H'`. -/
noncomputable def RealSplitCl11Action.transportOfLinearIsometryEquiv
    (eH : H ≃ₗᵢ[ℝ] H') (X : RealSplitCl11Action H) :
    RealSplitCl11Action H' :=
  RealSplitCl11Action.ofContinuousLinearEquiv eH.toContinuousLinearEquiv X

private lemma conjStarAlgEquiv_gradeConj {H₀ H₀' : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [KreinSpace H₀] [KreinGradedModule H₀]
    [NormedAddCommGroup H₀'] [InnerProductSpace ℝ H₀'] [CompleteSpace H₀']
    [KreinSpace H₀'] [KreinGradedModule H₀']
    (eH : H₀ ≃ₗᵢ[ℝ] H₀')
    (he_grade : ∀ x : H₀, KreinGradedModule.grade (eH x) = eH (KreinGradedModule.grade x))
    (A : EndH H₀) :
    eH.conjStarAlgEquiv (KreinGradedModule.gradeConj (H := H₀) A) =
      KreinGradedModule.gradeConj (H := H₀') (eH.conjStarAlgEquiv A) := by
  apply ContinuousLinearMap.ext
  intro y'
  obtain ⟨x, rfl⟩ := eH.surjective y'
  have hsymm : ∀ z : H₀', KreinGradedModule.grade (eH.symm z) =
      eH.symm (KreinGradedModule.grade z) := by
    intro z
    apply eH.injective
    rw [eH.apply_symm_apply, ← he_grade, eH.apply_symm_apply]
  change eH (KreinGradedModule.grade (A (KreinGradedModule.grade (eH.symm (eH x))))) =
    KreinGradedModule.grade (eH (A (eH.symm (KreinGradedModule.grade (eH x)))))
  simp [he_grade]

private lemma isCompactEnd_conjStarAlgEquiv {H₀ H₀' : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₀'] [InnerProductSpace ℝ H₀'] [CompleteSpace H₀']
    (eH : H₀ ≃ₗᵢ[ℝ] H₀') {A : EndH H₀} (hA : IsCompactEnd H₀ A) :
    IsCompactEnd H₀' (eH.conjStarAlgEquiv A) := by
  change IsCompactOperator
    ((eH.toLinearIsometry.toContinuousLinearMap.comp
      (A.comp eH.symm.toLinearIsometry.toContinuousLinearMap)) : H₀' → H₀')
  exact (hA.comp_clm eH.symm.toLinearIsometry.toContinuousLinearMap).clm_comp
    eH.toLinearIsometry.toContinuousLinearMap

/-- Transport a `RealSplitKreinKasparovCycle` along a grading- and Krein-preserving linear
isometry equivalence `eH : H ≃ₗᵢ[ℝ] H'`. -/
noncomputable def RealSplitKreinKasparovCycle.transportOfLinearIsometryEquiv
    {A B : Type*} [NormedRing A] [NormedRing B] [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [KreinGradedModule H] [KreinGradedModule H']
    (eH : H ≃ₗᵢ[ℝ] H')
    (he_inner : ∀ u v : H, KreinSpace.kreinInner (eH u) (eH v) = KreinSpace.kreinInner u v)
    (he_grade : ∀ x : H, KreinGradedModule.grade (eH x) = eH (KreinGradedModule.grade x))
    (X : RealSplitKreinKasparovCycle A B H) :
    RealSplitKreinKasparovCycle A B H' where
  cl11 := RealSplitCl11Action.transportOfLinearIsometryEquiv eH X.cl11
  π := eH.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgHom.comp X.π
  ρ := eH.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgHom.comp X.ρ
  π_even a := by
    unfold KreinGradedModule.IsEven
    change KreinGradedModule.gradeConj (H := H') (eH.conjStarAlgEquiv (X.π a)) =
      eH.conjStarAlgEquiv (X.π a)
    rw [← conjStarAlgEquiv_gradeConj eH he_grade, X.π_even a]
  ρ_even b := by
    unfold KreinGradedModule.IsEven
    change KreinGradedModule.gradeConj (H := H') (eH.conjStarAlgEquiv (X.ρ b)) =
      eH.conjStarAlgEquiv (X.ρ b)
    rw [← conjStarAlgEquiv_gradeConj eH he_grade, X.ρ_even b]
  F := eH.conjStarAlgEquiv X.F
  F_odd := by
    unfold KreinGradedModule.IsOdd
    rw [← conjStarAlgEquiv_gradeConj eH he_grade, X.F_odd, map_neg]
  F_skewAdj := isKreinSkewAdjoint_transport_isometry eH he_inner X.F_skewAdj
  F_sq_one_compact := by
    have hmap : eH.conjStarAlgEquiv X.F * eH.conjStarAlgEquiv X.F - (1 : EndH H') =
        eH.conjStarAlgEquiv (X.F * X.F - (1 : EndH H)) := by
      rw [map_sub, map_mul, map_one]
    rw [hmap]
    exact isCompactEnd_conjStarAlgEquiv eH X.F_sq_one_compact
  comm_compact a := by
    have hmap : eH.conjStarAlgEquiv X.F *
          (eH.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgHom.comp X.π) a -
          (eH.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgHom.comp X.π) a *
            eH.conjStarAlgEquiv X.F =
        eH.conjStarAlgEquiv (X.F * X.π a - X.π a * X.F) := by
      change eH.conjStarAlgEquiv X.F * eH.conjStarAlgEquiv (X.π a) -
          eH.conjStarAlgEquiv (X.π a) * eH.conjStarAlgEquiv X.F =
        eH.conjStarAlgEquiv (X.F * X.π a - X.π a * X.F)
      rw [← map_mul, ← map_mul, ← map_sub]
    rw [hmap]
    exact isCompactEnd_conjStarAlgEquiv eH (X.comm_compact a)
  superComm_eps_compact := by
    have h_even_part : ∀ T : EndH H,
        KreinGradedModule.evenPart (H := H') (eH.conjStarAlgEquiv T) =
          eH.conjStarAlgEquiv (KreinGradedModule.evenPart (H := H) T) := by
      intro T
      unfold KreinGradedModule.evenPart
      rw [map_smul, map_add, conjStarAlgEquiv_gradeConj eH he_grade]
    have h_odd_part : ∀ T : EndH H,
        KreinGradedModule.oddPart (H := H') (eH.conjStarAlgEquiv T) =
          eH.conjStarAlgEquiv (KreinGradedModule.oddPart (H := H) T) := by
      intro T
      unfold KreinGradedModule.oddPart
      rw [map_smul, map_sub, conjStarAlgEquiv_gradeConj eH he_grade]
    have h_eps : (RealSplitCl11Action.transportOfLinearIsometryEquiv eH X.cl11).eps =
        eH.conjStarAlgEquiv X.cl11.eps := rfl
    have h_super :
        KreinGradedModule.superComm (H := H') (eH.conjStarAlgEquiv X.F)
          (RealSplitCl11Action.transportOfLinearIsometryEquiv eH X.cl11).eps =
        eH.conjStarAlgEquiv (KreinGradedModule.superComm (H := H) X.F X.cl11.eps) := by
      rw [h_eps]
      unfold KreinGradedModule.superComm KreinGradedModule.comm KreinGradedModule.anticomm
      rw [h_even_part X.F, h_even_part X.cl11.eps, h_odd_part X.F, h_odd_part X.cl11.eps]
      simp only [map_add, map_sub, map_mul]
    rw [h_super]
    exact isCompactEnd_conjStarAlgEquiv eH X.superComm_eps_compact
  superComm_J_compact := by
    have h_even_part : ∀ T : EndH H,
        KreinGradedModule.evenPart (H := H') (eH.conjStarAlgEquiv T) =
          eH.conjStarAlgEquiv (KreinGradedModule.evenPart (H := H) T) := by
      intro T
      unfold KreinGradedModule.evenPart
      rw [map_smul, map_add, conjStarAlgEquiv_gradeConj eH he_grade]
    have h_odd_part : ∀ T : EndH H,
        KreinGradedModule.oddPart (H := H') (eH.conjStarAlgEquiv T) =
          eH.conjStarAlgEquiv (KreinGradedModule.oddPart (H := H) T) := by
      intro T
      unfold KreinGradedModule.oddPart
      rw [map_smul, map_sub, conjStarAlgEquiv_gradeConj eH he_grade]
    have h_J : (RealSplitCl11Action.transportOfLinearIsometryEquiv eH X.cl11).J =
        eH.conjStarAlgEquiv X.cl11.J := rfl
    have h_super :
        KreinGradedModule.superComm (H := H') (eH.conjStarAlgEquiv X.F)
          (RealSplitCl11Action.transportOfLinearIsometryEquiv eH X.cl11).J =
        eH.conjStarAlgEquiv (KreinGradedModule.superComm (H := H) X.F X.cl11.J) := by
      rw [h_J]
      unfold KreinGradedModule.superComm KreinGradedModule.comm KreinGradedModule.anticomm
      rw [h_even_part X.F, h_even_part X.cl11.J, h_odd_part X.F, h_odd_part X.cl11.J]
      simp only [map_add, map_sub, map_mul]
    rw [h_super]
    exact isCompactEnd_conjStarAlgEquiv eH X.superComm_J_compact

/-- `SplitDoubledSpace.toDoubledLIE : SplitDoubledSpace E ≃ₗᵢ[ℝ] DoubledSpace E` intertwines
the Krein fundamental symmetry `J`. -/
theorem splitDoubled_toDoubledLIE_intertwines_J {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : SplitDoubledSpace E) :
    KreinSpace.J (SplitDoubledSpace.toDoubledLIE (E := E) u) =
      SplitDoubledSpace.toDoubledLIE (E := E) (KreinSpace.J u) := rfl

/-- `SplitDoubledSpace.toDoubledLIE` preserves the indefinite Krein inner product. -/
theorem splitDoubled_toDoubledLIE_kreinInner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u v : SplitDoubledSpace E) :
    KreinSpace.kreinInner (SplitDoubledSpace.toDoubledLIE (E := E) u)
        (SplitDoubledSpace.toDoubledLIE (E := E) v) =
      KreinSpace.kreinInner u v :=
  kreinInner_transport_isometry (SplitDoubledSpace.toDoubledLIE (E := E))
    (splitDoubled_toDoubledLIE_intertwines_J (E := E)) u v

/-- `SplitDoubledSpace.toDoubledLIE` intertwines `kreinAdjoint`. -/
theorem splitDoubled_toDoubledLIE_kreinAdjoint {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : EndH (SplitDoubledSpace E)) :
    (SplitDoubledSpace.toDoubledLIE (E := E)).conjStarAlgEquiv (KreinSpace.kreinAdjoint A) =
      KreinSpace.kreinAdjoint ((SplitDoubledSpace.toDoubledLIE (E := E)).conjStarAlgEquiv A) :=
  kreinAdjoint_transport_isometry (SplitDoubledSpace.toDoubledLIE (E := E))
    (splitDoubled_toDoubledLIE_kreinInner (E := E)) A

end IsometricKreinTransport

section OperatorDistinctness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem doubledSpace_jCLM_eq_spectral_epsilon :
    KreinSpace.jCLM (H := DoubledSpace E) = spectral_epsilon (E := E) :=
  InfoGeometry.Krein.jCLM_eq_spectral_epsilon (E := E)

/-- On `DoubledSpace E` (`[Nontrivial E]`), `KreinSpace.jCLM = spectral_epsilon`, and the four
operators `{id, KreinSpace.jCLM (= spectral_epsilon), modular_j, complex_i}` are pairwise
distinct. (`DoubledSpace E` carries no global `KreinGradedModule` instance.) -/
theorem doubledSpace_cl11_operators_distinct [Nontrivial E] :
    ContinuousLinearMap.id ℝ (DoubledSpace E) ≠ KreinSpace.jCLM (H := DoubledSpace E) ∧
    ContinuousLinearMap.id ℝ (DoubledSpace E) ≠ modular_j (E := E) ∧
    ContinuousLinearMap.id ℝ (DoubledSpace E) ≠ complex_i (E := E) ∧
    KreinSpace.jCLM (H := DoubledSpace E) ≠ modular_j (E := E) ∧
    KreinSpace.jCLM (H := DoubledSpace E) ≠ complex_i (E := E) ∧
    modular_j (E := E) ≠ complex_i (E := E) ∧
    spectral_epsilon (E := E) ≠ ContinuousLinearMap.id ℝ (DoubledSpace E) ∧
    spectral_epsilon (E := E) ≠ modular_j (E := E) ∧
    spectral_epsilon (E := E) ≠ complex_i (E := E) := by
  have h := InfoGeometry.Krein.doubledSpace_operators_pairwise_distinct (E := E)
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, ?_, ?_, ?_⟩
  · rw [← doubledSpace_jCLM_eq_spectral_epsilon (E := E)]; exact h.1.symm
  · exact InfoGeometry.Krein.spectral_epsilon_ne_modular_j (E := E)
  · exact InfoGeometry.Krein.spectral_epsilon_ne_complex_i (E := E)

private lemma conjEnd_ne_of_ne {T₁ T₂ : EndH (DoubledSpace E)} (h : T₁ ≠ T₂) :
    SplitDoubledSpace.conjEnd (E := E) T₁ ≠ SplitDoubledSpace.conjEnd (E := E) T₂ :=
  fun hEq => h (SplitDoubledSpace.conjEnd_injective (E := E) hEq)

private lemma conjEnd_ne_id_of_ne {T : EndH (DoubledSpace E)}
    (h : T ≠ ContinuousLinearMap.id ℝ (DoubledSpace E)) :
    SplitDoubledSpace.conjEnd (E := E) T ≠
      ContinuousLinearMap.id ℝ (SplitDoubledSpace E) := by
  intro hEq
  apply h
  apply SplitDoubledSpace.conjEnd_injective (E := E)
  rw [hEq]
  change ContinuousLinearMap.id ℝ (SplitDoubledSpace E) =
    (SplitDoubledSpace.ofDoubledLIE (E := E)).conjStarAlgEquiv (1 : EndH (DoubledSpace E))
  rw [map_one]
  rfl

/-- On `SplitDoubledSpace E` under **default** typeclass synthesis (no `letI` override),
`jCLM = splitDoubledCl11Action.eps = splitDoubledSpectralEpsilon` and
`gradeCLM = splitDoubledCl11Action.J = splitDoubledModularJ`, and all four operators
`{id, jCLM (= eps), gradeCLM (= J), K (= splitDoubledComplexI)}` are pairwise distinct. -/
theorem splitDoubledSpace_operators_distinct [Nontrivial E] :
    KreinSpace.jCLM (H := SplitDoubledSpace E) =
      (SplitDoubledSpace.splitDoubledCl11Action (E := E)).eps ∧
    KreinGradedModule.gradeCLM (H := SplitDoubledSpace E) =
      (SplitDoubledSpace.splitDoubledCl11Action (E := E)).J ∧
    KreinGradedModule.gradeCLM (H := SplitDoubledSpace E) ≠
      KreinSpace.jCLM (H := SplitDoubledSpace E) ∧
    KreinGradedModule.gradeCLM (H := SplitDoubledSpace E) ≠
      (SplitDoubledSpace.splitDoubledCl11Action (E := E)).eps ∧
    KreinGradedModule.gradeCLM (H := SplitDoubledSpace E) ≠
      (SplitDoubledSpace.splitDoubledCl11Action (E := E)).K ∧
    KreinGradedModule.gradeCLM (H := SplitDoubledSpace E) ≠
      ContinuousLinearMap.id ℝ (SplitDoubledSpace E) ∧
    KreinSpace.jCLM (H := SplitDoubledSpace E) ≠
      (SplitDoubledSpace.splitDoubledCl11Action (E := E)).J ∧
    KreinSpace.jCLM (H := SplitDoubledSpace E) ≠
      (SplitDoubledSpace.splitDoubledCl11Action (E := E)).K ∧
    KreinSpace.jCLM (H := SplitDoubledSpace E) ≠
      ContinuousLinearMap.id ℝ (SplitDoubledSpace E) ∧
    (SplitDoubledSpace.splitDoubledCl11Action (E := E)).J ≠
      (SplitDoubledSpace.splitDoubledCl11Action (E := E)).K ∧
    (SplitDoubledSpace.splitDoubledCl11Action (E := E)).eps ≠
      (SplitDoubledSpace.splitDoubledCl11Action (E := E)).K ∧
    (SplitDoubledSpace.splitDoubledCl11Action (E := E)).K ≠
      ContinuousLinearMap.id ℝ (SplitDoubledSpace E) := by
  have h := doubledSpace_cl11_operators_distinct (E := E)
  have hj_eq : KreinSpace.jCLM (H := SplitDoubledSpace E) =
      SplitDoubledSpace.splitDoubledSpectralEpsilon (E := E) :=
    SplitDoubledSpace.jCLM_eq_splitDoubledSpectralEpsilon (E := E)
  have hg_eq : KreinGradedModule.gradeCLM (H := SplitDoubledSpace E) =
      SplitDoubledSpace.splitDoubledModularJ (E := E) :=
    SplitDoubledSpace.gradeCLM_eq_splitDoubledModularJ (E := E)
  have hK_eq : (SplitDoubledSpace.splitDoubledCl11Action (E := E)).K =
      SplitDoubledSpace.splitDoubledComplexI (E := E) :=
    SplitDoubledSpace.splitDoubledCl11Action_K (E := E)
  have hmod_eps : SplitDoubledSpace.splitDoubledModularJ (E := E) ≠
      SplitDoubledSpace.splitDoubledSpectralEpsilon (E := E) :=
    conjEnd_ne_of_ne h.2.2.2.2.2.2.2.1.symm
  have hmod_K : SplitDoubledSpace.splitDoubledModularJ (E := E) ≠
      SplitDoubledSpace.splitDoubledComplexI (E := E) :=
    conjEnd_ne_of_ne h.2.2.2.2.2.1
  have heps_K : SplitDoubledSpace.splitDoubledSpectralEpsilon (E := E) ≠
      SplitDoubledSpace.splitDoubledComplexI (E := E) :=
    conjEnd_ne_of_ne h.2.2.2.2.2.2.2.2
  have hmod_id : SplitDoubledSpace.splitDoubledModularJ (E := E) ≠
      ContinuousLinearMap.id ℝ (SplitDoubledSpace E) :=
    conjEnd_ne_id_of_ne h.2.1.symm
  have heps_id : SplitDoubledSpace.splitDoubledSpectralEpsilon (E := E) ≠
      ContinuousLinearMap.id ℝ (SplitDoubledSpace E) :=
    conjEnd_ne_id_of_ne h.2.2.2.2.2.2.1
  have hK_id : SplitDoubledSpace.splitDoubledComplexI (E := E) ≠
      ContinuousLinearMap.id ℝ (SplitDoubledSpace E) :=
    conjEnd_ne_id_of_ne h.2.2.1.symm
  refine ⟨hj_eq, hg_eq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg_eq, hj_eq]; exact hmod_eps
  · rw [hg_eq, SplitDoubledSpace.splitDoubledCl11Action_eps]; exact hmod_eps
  · rw [hg_eq, hK_eq]; exact hmod_K
  · rw [hg_eq]; exact hmod_id
  · rw [hj_eq, SplitDoubledSpace.splitDoubledCl11Action_J]; exact hmod_eps.symm
  · rw [hj_eq, hK_eq]; exact heps_K
  · rw [hj_eq]; exact heps_id
  · rw [SplitDoubledSpace.splitDoubledCl11Action_J, hK_eq]; exact hmod_K
  · rw [SplitDoubledSpace.splitDoubledCl11Action_eps, hK_eq]; exact heps_K
  · rw [hK_eq]; exact hK_id

/-- Default-instance operator distinctness on `clSplitStageCycle n` (`StageKreinH n`):
with zero `letI` overrides, `gradeCLM = cl11.J`, `jCLM = cl11.eps`, and `{id, jCLM (= eps),
gradeCLM (= J), K}` are pairwise distinct for every stage `n : ℕ`. -/
theorem clSplitStageCycle_operators_distinct (n : ℕ) :
    KreinGradedModule.gradeCLM (H := StageKreinH n) = (clSplitStageCycle n).cl11.J ∧
    KreinSpace.jCLM (H := StageKreinH n) = (clSplitStageCycle n).cl11.eps ∧
    KreinGradedModule.gradeCLM (H := StageKreinH n) ≠ KreinSpace.jCLM (H := StageKreinH n) ∧
    KreinGradedModule.gradeCLM (H := StageKreinH n) ≠ (clSplitStageCycle n).cl11.eps ∧
    KreinGradedModule.gradeCLM (H := StageKreinH n) ≠ (clSplitStageCycle n).K ∧
    KreinGradedModule.gradeCLM (H := StageKreinH n) ≠ ContinuousLinearMap.id ℝ (StageKreinH n) ∧
    (clSplitStageCycle n).cl11.J ≠ (clSplitStageCycle n).cl11.eps ∧
    (clSplitStageCycle n).cl11.J ≠ (clSplitStageCycle n).K ∧
    (clSplitStageCycle n).cl11.eps ≠ (clSplitStageCycle n).K := by
  have hpos : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
  have : Nonempty (Fin (2 ^ n)) := ⟨⟨0, hpos⟩⟩
  have hs := splitDoubledSpace_operators_distinct (E := StageVec n)
  refine ⟨hs.2.1, hs.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · have hJ : (clSplitStageCycle n).cl11.J =
        (SplitDoubledSpace.splitDoubledCl11Action (E := StageVec n)).J := rfl
    have heps : (clSplitStageCycle n).cl11.eps =
        (SplitDoubledSpace.splitDoubledCl11Action (E := StageVec n)).eps := rfl
    rw [hJ, heps, ← hs.2.1, ← hs.1]
    exact hs.2.2.1
  · exact hs.2.2.2.2.2.2.2.2.2.1
  · exact hs.2.2.2.2.2.2.2.2.2.2.1

/-- Non-tautological five-operator separation on a `RealSplitKreinKasparovCycle` over
`DoubledSpace E` (`[Nontrivial E]`): whenever the supplied `[KreinGradedModule (DoubledSpace E)]`
grading `Γ = gradeCLM` is distinct from `id`, `X.cl11.J (= modular_j)`, `X.cl11.eps (= jCLM =
spectral_epsilon)`, and `X.K (= complex_i)`, all five operators
`{id, jCLM (= X.cl11.eps = spectral_epsilon), X.cl11.J (= modular_j), X.K (= complex_i), gradeCLM}`
are pairwise distinct (10 inequalities, with `jCLM = X.cl11.eps = spectral_epsilon` documented
explicitly). -/
theorem doubledSpace_cycle_five_operators_distinct {A B : Type*}
    [NormedRing A] [NormedRing B] [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [KreinGradedModule (DoubledSpace E)] [Nontrivial E]
    (X : RealSplitKreinKasparovCycle A B (DoubledSpace E))
    (hcl11 : X.cl11 = doubledSpaceCl11Action (E := E))
    (hΓ_id : KreinGradedModule.gradeCLM (H := DoubledSpace E) ≠
      ContinuousLinearMap.id ℝ (DoubledSpace E))
    (hΓ_J : KreinGradedModule.gradeCLM (H := DoubledSpace E) ≠ X.cl11.J)
    (hΓ_eps : KreinGradedModule.gradeCLM (H := DoubledSpace E) ≠ X.cl11.eps)
    (hΓ_K : KreinGradedModule.gradeCLM (H := DoubledSpace E) ≠ X.K) :
    KreinSpace.jCLM (H := DoubledSpace E) = X.cl11.eps ∧
    ContinuousLinearMap.id ℝ (DoubledSpace E) ≠ KreinSpace.jCLM (H := DoubledSpace E) ∧
    ContinuousLinearMap.id ℝ (DoubledSpace E) ≠ X.cl11.J ∧
    ContinuousLinearMap.id ℝ (DoubledSpace E) ≠ X.K ∧
    ContinuousLinearMap.id ℝ (DoubledSpace E) ≠ KreinGradedModule.gradeCLM (H := DoubledSpace E) ∧
    KreinSpace.jCLM (H := DoubledSpace E) ≠ X.cl11.J ∧
    KreinSpace.jCLM (H := DoubledSpace E) ≠ X.K ∧
    KreinSpace.jCLM (H := DoubledSpace E) ≠ KreinGradedModule.gradeCLM (H := DoubledSpace E) ∧
    X.cl11.J ≠ X.K ∧
    X.cl11.J ≠ KreinGradedModule.gradeCLM (H := DoubledSpace E) ∧
    X.K ≠ KreinGradedModule.gradeCLM (H := DoubledSpace E) := by
  have h4 := doubledSpace_cl11_operators_distinct (E := E)
  have hJ : X.cl11.J = modular_j (E := E) := by simp [hcl11]
  have heps : X.cl11.eps = spectral_epsilon (E := E) := by simp [hcl11]
  have hK : X.K = complex_i (E := E) := by simp [RealSplitKreinKasparovCycle.K, hcl11]
  have hj_eps : KreinSpace.jCLM (H := DoubledSpace E) = X.cl11.eps := by
    rw [doubledSpace_jCLM_eq_spectral_epsilon, heps]
  refine ⟨hj_eps, h4.1, ?_, ?_, hΓ_id.symm, ?_, ?_, ?_, ?_, hΓ_J.symm, hΓ_K.symm⟩
  · rw [hJ]; exact h4.2.1
  · rw [hK]; exact h4.2.2.1
  · rw [hJ]; exact h4.2.2.2.1
  · rw [hK]; exact h4.2.2.2.2.1
  · rw [hj_eps]; exact hΓ_eps.symm
  · rw [hJ, hK]; exact h4.2.2.2.2.2.1

/-- Honest realization note for `HilbertDoubled E`: because `HilbertDoubled E` and `NeutralSpace E`
are both `abbrev` for `ULift (DoubledSpace E)`, Lean's default synthesized `KreinGradedModule`
instance on `HilbertDoubled E` is `instKreinGradedModuleNeutral`, whose `gradeCLM` collapses to
`KreinSpace.jCLM`. Use `SplitDoubledSpace E` (`StageKreinH n`) when canonical `gradeCLM = modular_j`
under default synthesis is required. -/
theorem hilbertDoubled_default_grade_eq_jCLM :
    KreinGradedModule.gradeCLM (H := HilbertDoubled E) =
      KreinSpace.jCLM (H := HilbertDoubled E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply (NeutralSpace.rotation45ToHilbert (E := E)).injective
  have hgr : NeutralSpace.rotation45ToHilbert (E := E)
      (KreinGradedModule.gradeCLM (H := HilbertDoubled E) u) =
      hilbertSwapCLM (E := E) (NeutralSpace.rotation45ToHilbert (E := E) u) :=
    InfoGeometry.Krein.rotation45_gradeCLM_neutral_apply (E := E) u
  rw [hgr]
  rcases u with ⟨d⟩
  rcases hdx : WithLp.ofLp d with ⟨x, ξ⟩
  have hd : d = to_doubled x ξ := by
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    simpa [to_doubled] using hdx
  apply HilbertDoubled.ext
  apply DoubledSpace.ext
  · simp [hd, HilbertDoubled.toLp, hilbertSwapCLM_apply, sub_eq_add_neg]
  · simp [hd, HilbertDoubled.toLp, hilbertSwapCLM_apply, sub_eq_add_neg]

/-- On `HilbertDoubled E` (`[Nontrivial E]`), without any `letI` masking, the explicit
`instKreinGradedModuleHilbertDoubled` grading `gradeCLM` equals `hilbertSwapCLM`, and
`{id, jCLM, instKreinGradedModuleHilbertDoubled.gradeCLM (= hilbertSwapCLM), hilbertComplexI}`
are pairwise distinct. (Compare `hilbertDoubled_default_grade_eq_jCLM` for the default
`instKreinGradedModuleNeutral` realization.) -/
theorem hilbertDoubled_operators_distinct [Nontrivial E] :
    @KreinGradedModule.gradeCLM (HilbertDoubled E) _ _ _ _
        (instKreinGradedModuleHilbertDoubled (E := E)) = hilbertSwapCLM (E := E) ∧
    ContinuousLinearMap.id ℝ (HilbertDoubled E) ≠ KreinSpace.jCLM (H := HilbertDoubled E) ∧
    ContinuousLinearMap.id ℝ (HilbertDoubled E) ≠ hilbertSwapCLM (E := E) ∧
    ContinuousLinearMap.id ℝ (HilbertDoubled E) ≠ hilbertComplexI (E := E) ∧
    KreinSpace.jCLM (H := HilbertDoubled E) ≠ hilbertSwapCLM (E := E) ∧
    KreinSpace.jCLM (H := HilbertDoubled E) ≠ hilbertComplexI (E := E) ∧
    hilbertSwapCLM (E := E) ≠ hilbertComplexI (E := E) ∧
    KreinSpace.jCLM (H := HilbertDoubled E) ≠
      @KreinGradedModule.gradeCLM (HilbertDoubled E) _ _ _ _
        (instKreinGradedModuleHilbertDoubled (E := E)) ∧
    @KreinGradedModule.gradeCLM (HilbertDoubled E) _ _ _ _
        (instKreinGradedModuleHilbertDoubled (E := E)) ≠ hilbertComplexI (E := E) ∧
    @KreinGradedModule.gradeCLM (HilbertDoubled E) _ _ _ _
        (instKreinGradedModuleHilbertDoubled (E := E)) ≠
      ContinuousLinearMap.id ℝ (HilbertDoubled E) := by
  have h4 := doubledSpace_cl11_operators_distinct (E := E)
  have h_id_j : ContinuousLinearMap.id ℝ (HilbertDoubled E) ≠
      KreinSpace.jCLM (H := HilbertDoubled E) := by
    intro h
    apply h4.1
    apply ContinuousLinearMap.ext
    intro u
    have hpt := congrArg (fun T : EndH (HilbertDoubled E) =>
      HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)
        (T (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E) u))) h
    simpa [toDoubled_jCLM_apply, doubledSpace_jCLM_eq_spectral_epsilon] using hpt
  have h_id_swap : ContinuousLinearMap.id ℝ (HilbertDoubled E) ≠ hilbertSwapCLM (E := E) := by
    intro h
    apply h4.2.1
    apply ContinuousLinearMap.ext
    intro u
    have hpt := congrArg (fun T : EndH (HilbertDoubled E) =>
      HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)
        (T (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E) u))) h
    simpa [toDoubled_hilbertSwapCLM_apply] using hpt
  have h_id_I : ContinuousLinearMap.id ℝ (HilbertDoubled E) ≠ hilbertComplexI (E := E) := by
    intro h
    apply h4.2.2.1
    apply ContinuousLinearMap.ext
    intro u
    have hpt := congrArg (fun T : EndH (HilbertDoubled E) =>
      HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)
        (T (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E) u))) h
    simpa [toDoubled_hilbertComplexI_apply] using hpt
  have hj_swap : KreinSpace.jCLM (H := HilbertDoubled E) ≠ hilbertSwapCLM (E := E) := by
    intro h
    apply h4.2.2.2.1
    apply ContinuousLinearMap.ext
    intro u
    have hpt := congrArg (fun T : EndH (HilbertDoubled E) =>
      HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)
        (T (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E) u))) h
    simpa [toDoubled_jCLM_apply, toDoubled_hilbertSwapCLM_apply,
      doubledSpace_jCLM_eq_spectral_epsilon] using hpt
  have hj_I : KreinSpace.jCLM (H := HilbertDoubled E) ≠ hilbertComplexI (E := E) := by
    intro h
    apply h4.2.2.2.2.1
    apply ContinuousLinearMap.ext
    intro u
    have hpt := congrArg (fun T : EndH (HilbertDoubled E) =>
      HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)
        (T (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E) u))) h
    simpa [toDoubled_jCLM_apply, toDoubled_hilbertComplexI_apply,
      doubledSpace_jCLM_eq_spectral_epsilon] using hpt
  have hswap_I : hilbertSwapCLM (E := E) ≠ hilbertComplexI (E := E) := by
    intro h
    apply h4.2.2.2.2.2.1
    apply ContinuousLinearMap.ext
    intro u
    have hpt := congrArg (fun T : EndH (HilbertDoubled E) =>
      HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)
        (T (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E) u))) h
    simpa [toDoubled_hilbertSwapCLM_apply, toDoubled_hilbertComplexI_apply] using hpt
  have hgrade_eq :
      @KreinGradedModule.gradeCLM (HilbertDoubled E) _ _ _ _
        (instKreinGradedModuleHilbertDoubled (E := E)) = hilbertSwapCLM (E := E) := rfl
  refine ⟨hgrade_eq, h_id_j, h_id_swap, h_id_I, hj_swap, hj_I, hswap_I, ?_, ?_, ?_⟩
  · rw [hgrade_eq]; exact hj_swap
  · rw [hgrade_eq]; exact hswap_I
  · rw [hgrade_eq]; exact h_id_swap.symm

end OperatorDistinctness

end InfoGeometry.KK.ClNNFredholmBridge
