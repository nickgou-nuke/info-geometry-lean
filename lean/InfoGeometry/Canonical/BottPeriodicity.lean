import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Clifford.Grading
import InfoGeometry.Clifford.Lift
import InfoGeometry.Clifford.Relations
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Clifford.SplitQ11Equivariance
import InfoGeometry.Clifford.SplitQ11PhaseFlip
import InfoGeometry.Clifford.SplitQ11Projectors
import InfoGeometry.Krein.Superphysics
import InfoGeometry.Clifford.Tower
import InfoGeometry.Quantum.RealSplitClifford
import Mathlib.LinearAlgebra.TensorProduct.Basic
set_option linter.unnecessarySimpa false

open scoped TensorProduct

namespace BottPeriodicity

open InfoGeometry.Krein
open InfoGeometry.Quantum

local notation "Q11" => InfoGeometry.CliffordTower.Q11
local notation "SplitSpace" => InfoGeometry.CliffordTower.SplitSpace
local notation "Qsplit" => InfoGeometry.CliffordTower.Qsplit
local notation "Clsplit" => InfoGeometry.CliffordTower.Clsplit
local notation "clsplit_succ_equiv" => InfoGeometry.CliffordTower.clsplit_succ_equiv

section TensorLift

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Tensor product of two doubled spaces. -/
abbrev DoubledTensor (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :=
  DoubledSpace E ⊗[ℝ] DoubledSpace F

/--
Lift `modular_j` to the tensor product via `TensorProduct.map`.
-/
noncomputable def tensorModularJ : DoubledTensor E F →ₗ[ℝ] DoubledTensor E F :=
  TensorProduct.map (modular_j (E := E)).toLinearMap (modular_j (E := F)).toLinearMap

/--
Lift `spectral_epsilon` to the tensor product via `TensorProduct.map`.
-/
noncomputable def tensorSpectralEpsilon : DoubledTensor E F →ₗ[ℝ] DoubledTensor E F :=
  TensorProduct.map (spectral_epsilon (E := E)).toLinearMap (spectral_epsilon (E := F)).toLinearMap

@[simp] lemma tensorModularJ_tmul (u : DoubledSpace E) (v : DoubledSpace F) :
    tensorModularJ (E := E) (F := F) (u ⊗ₜ[ℝ] v)
      = modular_j (E := E) u ⊗ₜ[ℝ] modular_j (E := F) v := by
  simp [tensorModularJ]

@[simp] lemma tensorSpectralEpsilon_tmul (u : DoubledSpace E) (v : DoubledSpace F) :
    tensorSpectralEpsilon (E := E) (F := F) (u ⊗ₜ[ℝ] v)
      = spectral_epsilon (E := E) u ⊗ₜ[ℝ] spectral_epsilon (E := F) v := by
  simp [tensorSpectralEpsilon]

@[simp] lemma tensorModularJ_comp_tmul (u : DoubledSpace E) (v : DoubledSpace F) :
    ((tensorModularJ (E := E) (F := F)).comp (tensorModularJ (E := E) (F := F)))
      (u ⊗ₜ[ℝ] v)
      = u ⊗ₜ[ℝ] v := by
  have hu' : WithLp.toLp (2 : ENNReal) (WithLp.fst u, WithLp.snd u) = u := by
    change WithLp.toLp (2 : ENNReal) (WithLp.ofLp u) = u
    exact WithLp.toLp_ofLp (p := (2 : ENNReal)) u
  have hv' : WithLp.toLp (2 : ENNReal) (WithLp.fst v, WithLp.snd v) = v := by
    change WithLp.toLp (2 : ENNReal) (WithLp.ofLp v) = v
    exact WithLp.toLp_ofLp (p := (2 : ENNReal)) v
  simpa [tensorModularJ, LinearMap.comp_apply, modular_j, hu', hv']

@[simp] lemma tensorSpectralEpsilon_comp_tmul (u : DoubledSpace E) (v : DoubledSpace F) :
    ((tensorSpectralEpsilon (E := E) (F := F)).comp
      (tensorSpectralEpsilon (E := E) (F := F)))
      (u ⊗ₜ[ℝ] v)
      = u ⊗ₜ[ℝ] v := by
  have hu' : WithLp.toLp (2 : ENNReal) (WithLp.fst u, WithLp.snd u) = u := by
    change WithLp.toLp (2 : ENNReal) (WithLp.ofLp u) = u
    exact WithLp.toLp_ofLp (p := (2 : ENNReal)) u
  have hv' : WithLp.toLp (2 : ENNReal) (WithLp.fst v, WithLp.snd v) = v := by
    change WithLp.toLp (2 : ENNReal) (WithLp.ofLp v) = v
    exact WithLp.toLp_ofLp (p := (2 : ENNReal)) v
  simpa [tensorSpectralEpsilon, LinearMap.comp_apply, spectral_epsilon, hu', hv']

end TensorLift

section BottStep

/-- Bott-step target graded tensor algebra in the split tower. -/
abbrev BottTensor (n : ℕ) :=
  CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)

/--
One-step Bott periodicity isomorphism in the split tower:
`Clsplit (n+1) ≃ BottTensor n`.
-/
noncomputable abbrev bottStepEquiv (n : ℕ) : Clsplit (n + 1) ≃ₐ[ℝ] BottTensor n :=
  clsplit_succ_equiv n

/--
Explicit generator injection into the Bott tensor side:
`v ↦ bottStepEquiv (ι v)`.
-/
noncomputable def bottGeneratorInjection (n : ℕ) :
    SplitSpace (n + 1) →ₗ[ℝ] BottTensor n where
  toFun v := bottStepEquiv n (CliffordAlgebra.ι (Qsplit (n + 1)) v)
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro a x
    simp

@[simp] lemma bottGeneratorInjection_apply (n : ℕ) (x : ℝ × ℝ) (xs : SplitSpace n) :
    bottGeneratorInjection n (x, xs)
      = (CliffordAlgebra.ι Q11 x) ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n))
        + (1 : CliffordAlgebra Q11) ᵍ⊗ₜ (CliffordAlgebra.ι (Qsplit n) xs) := by
  change CliffordAlgebra.ofProd Q11 (Qsplit n)
      (CliffordAlgebra.ι (Q11.prod (Qsplit n)) (x, xs))
    = (CliffordAlgebra.ι Q11 x) ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n))
      + (1 : CliffordAlgebra Q11) ᵍ⊗ₜ (CliffordAlgebra.ι (Qsplit n) xs)
  rw [CliffordAlgebra.ofProd_ι_mk (Q₁ := Q11) (Q₂ := Qsplit n) x xs]

@[simp] lemma bottStepEquiv_symm_left_generator (n : ℕ) (x : ℝ × ℝ) :
    (bottStepEquiv n).symm
      ((CliffordAlgebra.ι Q11 x) ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)))
      = CliffordAlgebra.ι (Qsplit (n + 1)) (x, (0 : SplitSpace n)) := by
  change CliffordAlgebra.toProd Q11 (Qsplit n)
      ((CliffordAlgebra.ι Q11 x) ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)))
    = CliffordAlgebra.ι (Q11.prod (Qsplit n)) (x, (0 : SplitSpace n))
  simp

@[simp] lemma bottStepEquiv_symm_right_generator (n : ℕ) (xs : SplitSpace n) :
    (bottStepEquiv n).symm
      ((1 : CliffordAlgebra Q11) ᵍ⊗ₜ (CliffordAlgebra.ι (Qsplit n) xs))
      = CliffordAlgebra.ι (Qsplit (n + 1)) ((0 : ℝ × ℝ), xs) := by
  change CliffordAlgebra.toProd Q11 (Qsplit n)
      ((1 : CliffordAlgebra Q11) ᵍ⊗ₜ (CliffordAlgebra.ι (Qsplit n) xs))
    = CliffordAlgebra.ι (Q11.prod (Qsplit n)) ((0 : ℝ × ℝ), xs)
  simp

/-- Named alias for one-step Bott periodicity in this framework. -/
noncomputable abbrev bott_step_periodicity (n : ℕ) :
    Clsplit (n + 1) ≃ₐ[ℝ] BottTensor n :=
  bottStepEquiv n

end BottStep

section FirstBottSeed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[simp] theorem bottGeneratorInjection_zero_left :
    bottGeneratorInjection 0 ((1, 0), (0 : SplitSpace 0))
      = (CliffordAlgebra.ι Q11 (1, 0)) ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit 0)) := by
  rw [bottGeneratorInjection_apply]
  have hzero : CliffordAlgebra.ι (Qsplit 0) (0 : SplitSpace 0) = 0 := by
    simpa using (LinearMap.map_zero (CliffordAlgebra.ι (Qsplit 0)))
  rw [hzero]
  simp

@[simp] theorem bottGeneratorInjection_zero_right :
    bottGeneratorInjection 0 ((0, 1), (0 : SplitSpace 0))
      = (CliffordAlgebra.ι Q11 (0, 1)) ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit 0)) := by
  rw [bottGeneratorInjection_apply]
  have hzero : CliffordAlgebra.ι (Qsplit 0) (0 : SplitSpace 0) = 0 := by
    simpa using (LinearMap.map_zero (CliffordAlgebra.ι (Qsplit 0)))
  rw [hzero]
  simp

/--
The packaged doubled-space split action is the concrete `Q11` seed consumed by the
first Bott step on the left generator.
-/
theorem firstBottStep_consumes_doubledSpaceCl11Action_J :
    (doubledSpaceCl11Action (E := E)).J
      = InfoGeometry.Krein.cl11Rep (E := E) (CliffordAlgebra.ι Q11 (1, 0)) ∧
    bottGeneratorInjection 0 ((1, 0), (0 : SplitSpace 0))
      = (CliffordAlgebra.ι Q11 (1, 0)) ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit 0)) := by
  constructor
  · simpa using (doubledSpaceCl11Action_J_eq_cl11Rep_leftGenerator (E := E))
  · exact bottGeneratorInjection_zero_left

/--
The packaged doubled-space split action is the concrete `Q11` seed consumed by the
first Bott step on the right generator.
-/
theorem firstBottStep_consumes_doubledSpaceCl11Action_K :
    (doubledSpaceCl11Action (E := E)).K
      = InfoGeometry.Krein.cl11Rep (E := E) (CliffordAlgebra.ι Q11 (0, 1)) ∧
    bottGeneratorInjection 0 ((0, 1), (0 : SplitSpace 0))
      = (CliffordAlgebra.ι Q11 (0, 1)) ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit 0)) := by
  constructor
  · simpa using (doubledSpaceCl11Action_K_eq_cl11Rep_rightGenerator (E := E))
  · exact bottGeneratorInjection_zero_right

end FirstBottSeed

section CompanionInjection

/--
Companion tensor target in the order `Cl(Qsplit n) ⊗ Cl(Q11)`,
matching the textbook pattern `v ↦ v ⊗ ε`, `w ↦ 1 ⊗ w`.
-/
abbrev CompanionTensor (n : ℕ) :=
  CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] CliffordAlgebra.evenOdd Q11

/--
Canonical graded algebra injection from the product Clifford algebra:
`Cl(Qsplit n ⊕ Q11) → Cl(Qsplit n) ⊗ Cl(Q11)`.
-/
noncomputable abbrev gradedProdInjection (n : ℕ) :
    CliffordAlgebra ((Qsplit n).prod Q11) →ₐ[ℝ] CompanionTensor n :=
  CliffordAlgebra.ofProd (Q₁ := Qsplit n) (Q₂ := Q11)

/-- Chosen split `Cl(1,1)` grading element used in the pattern layer. -/
noncomputable def cl11GradeEpsilon : CliffordAlgebra Q11 :=
  CliffordAlgebra.ι Q11 (1, 0)

/--
Old-space generator map in companion pattern form: `v ↦ ι(v) ⊗ ε`.
-/
noncomputable def oldGeneratorTensorEpsilon
    (n : ℕ) (ε : CliffordAlgebra Q11) :
    SplitSpace n →ₗ[ℝ] CompanionTensor n where
  toFun v := (CliffordAlgebra.ι (Qsplit n) v) ᵍ⊗ₜ ε
  map_add' := by
    intro x y
    simp [GradedTensorProduct.tmul, TensorProduct.add_tmul]
  map_smul' := by
    intro a x
    rw [LinearMap.map_smul]
    show
      GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit n)) (CliffordAlgebra.evenOdd Q11)
          (((a • (CliffordAlgebra.ι (Qsplit n) x)) ⊗ₜ[ℝ] ε)) =
        (RingHom.id ℝ) a •
          GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit n))
            (CliffordAlgebra.evenOdd Q11)
            (((CliffordAlgebra.ι (Qsplit n) x) ⊗ₜ[ℝ] ε))
    calc
      GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit n)) (CliffordAlgebra.evenOdd Q11)
          (((a • (CliffordAlgebra.ι (Qsplit n) x)) ⊗ₜ[ℝ] ε))
        = GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit n)) (CliffordAlgebra.evenOdd Q11)
            (a • ((CliffordAlgebra.ι (Qsplit n) x) ⊗ₜ[ℝ] ε)) := by
              congr 1
      _ = (RingHom.id ℝ) a •
            GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit n))
              (CliffordAlgebra.evenOdd Q11)
              (((CliffordAlgebra.ι (Qsplit n) x) ⊗ₜ[ℝ] ε)) := by
              exact LinearEquiv.map_smul
                (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd (Qsplit n))
                  (CliffordAlgebra.evenOdd Q11))
                a (((CliffordAlgebra.ι (Qsplit n) x) ⊗ₜ[ℝ] ε))

/--
New-space generator map in companion pattern form: `w ↦ 1 ⊗ ι(w)`.
-/
noncomputable def newGeneratorTensorOne (n : ℕ) :
    (ℝ × ℝ) →ₗ[ℝ] CompanionTensor n where
  toFun w := (1 : CliffordAlgebra (Qsplit n)) ᵍ⊗ₜ (CliffordAlgebra.ι Q11 w)
  map_add' := by
    intro x y
    simp [GradedTensorProduct.tmul, TensorProduct.tmul_add]
  map_smul' := by
    intro a x
    simp [GradedTensorProduct.tmul, TensorProduct.tmul_smul]

/--
Companion linear pattern map:
`(v,w) ↦ (ι(v) ⊗ ε) + (1 ⊗ ι(w))`.
-/
noncomputable def twistedGeneratorPattern
    (n : ℕ) (ε : CliffordAlgebra Q11) :
    SplitSpace n × (ℝ × ℝ) →ₗ[ℝ] CompanionTensor n :=
  LinearMap.coprod (oldGeneratorTensorEpsilon n ε) (newGeneratorTensorOne n)

@[simp] lemma twistedGeneratorPattern_apply
    (n : ℕ) (ε : CliffordAlgebra Q11) (v : SplitSpace n) (w : ℝ × ℝ) :
    twistedGeneratorPattern n ε (v, w)
      = (CliffordAlgebra.ι (Qsplit n) v) ᵍ⊗ₜ ε
          + (1 : CliffordAlgebra (Qsplit n)) ᵍ⊗ₜ (CliffordAlgebra.ι Q11 w) := by
  simp [twistedGeneratorPattern, oldGeneratorTensorEpsilon, newGeneratorTensorOne]

/--
Generator formula for the canonical graded product injection (`ofProd`):
`(v,w) ↦ ι(v) ⊗ 1 + 1 ⊗ ι(w)`.
-/
@[simp] lemma gradedProdInjection_on_generator
    (n : ℕ) (v : SplitSpace n) (w : ℝ × ℝ) :
    gradedProdInjection n (CliffordAlgebra.ι ((Qsplit n).prod Q11) (v, w))
      = (CliffordAlgebra.ι (Qsplit n) v) ᵍ⊗ₜ (1 : CliffordAlgebra Q11)
          + (1 : CliffordAlgebra (Qsplit n)) ᵍ⊗ₜ (CliffordAlgebra.ι Q11 w) := by
  simp [gradedProdInjection]

/--
Companion matching theorem (unit-`ε` case):
the canonical graded `AlgHom` injection agrees with the explicit pattern map
when `ε = 1`.
-/
@[simp] theorem gradedProdInjection_matches_pattern_unit
    (n : ℕ) (v : SplitSpace n) (w : ℝ × ℝ) :
    gradedProdInjection n (CliffordAlgebra.ι ((Qsplit n).prod Q11) (v, w))
      = twistedGeneratorPattern n (1 : CliffordAlgebra Q11) (v, w) := by
  simp [twistedGeneratorPattern_apply]

end CompanionInjection

end BottPeriodicity
