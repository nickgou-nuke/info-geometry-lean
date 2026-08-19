import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.Canonical.SouriauOnsagerBKMBridge
import InfoGeometry.Canonical.SouriauOnsagerBKMFilteredColimit

/-!
# Raw matrix trace tower interface

The matrix stages have a canonical normalized trace, positivity lemmas, and a
native successor embedding between the different matrix sizes.  This owner
derives the filtered maps and trace compatibility from that embedding.  It does
not invent an order on matrix algebras in order to coerce the raw functional
into the `State` type.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixTraceTower

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open CategoryTheory CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix
open SouriauOnsagerBKM

open scoped Kronecker

/-! ### Concrete noncommutative successor map

The standard index `Fin (2^n)` is related to the tensor index of the
Kronecker product by an explicit finite equivalence.  The successor map below
is therefore the matrix-algebra embedding `A ↦ A ⊗ I₂`, transported through
that equivalence.  No order structure on the full matrix carrier is used.
-/

noncomputable def stageIndexEquiv (n : ℕ) :
    (Fin (2 ^ n) × Fin 2) ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (by simp [pow_succ, Nat.mul_comm]))

noncomputable def concreteStep (n : ℕ) :
    MatrixStage n →⋆ₐ[ℂ] MatrixStage (n + 1) where
  toFun A := (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n))
    (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
  map_one' := by
    simp
  map_mul' A B := by
    have hkr : (A * B) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) =
        (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
      simpa using (Matrix.mul_kronecker_mul A B
        (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ))
    rw [hkr]
    exact (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)).map_mul _ _
  map_zero' := by
    simp
  map_add' A B := by
    change (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n))
      ((A + B) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = _
    rw [Matrix.add_kronecker]
    exact (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)).map_add _ _
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp [Matrix.smul_kronecker]
  map_star' A := by
    ext i j
    simp only [Matrix.reindexAlgEquiv, Matrix.star_apply]
    cases hi : (stageIndexEquiv n).symm i with
    | mk i₁ i₂ =>
      cases hj : (stageIndexEquiv n).symm j with
      | mk j₁ j₂ =>
        fin_cases i₂ <;> fin_cases j₂ <;>
          simp [hi, hj, Matrix.star_apply]

@[simp] theorem concreteStep_star (n : ℕ) (A : MatrixStage n) :
    concreteStep n (star A) = star (concreteStep n A) := by
  exact (concreteStep n).map_star' A

lemma trace_reindex {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommSemiring R]
    (e : m ≃ n) (A : Matrix m m R) :
    Matrix.trace ((Matrix.reindexAlgEquiv R R e) A) = Matrix.trace A := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.reindexAlgEquiv]
  change (∑ x : n, A (e.symm x) (e.symm x)) = ∑ i : m, A i i
  exact Equiv.sum_comp e.symm (fun i : m => A i i)

lemma concreteStep_trace (n : ℕ) (A : MatrixStage n) :
    Matrix.trace (concreteStep n A) = 2 * Matrix.trace A := by
  change Matrix.trace ((Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n))
    (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) = _
  rw [trace_reindex, Matrix.trace_kronecker]
  simp
  ring

theorem concreteStep_injective (n : ℕ) :
    Function.Injective (concreteStep n) := by
  intro A B hAB
  ext i j
  let e := stageIndexEquiv n
  have hentry := congrArg
    (fun M : MatrixStage (n + 1) => M (e (i, 0)) (e (j, 0))) hAB
  simpa [concreteStep, e, Matrix.reindexAlgEquiv] using hentry

/-- Successor maps and preservation of the normalized matrix trace. -/
abbrev StepFamily := ∀ n, MatrixStage n →⋆ₐ[ℂ] MatrixStage (n + 1)

/-! `Data` is retained as a compatibility alias for existing colimit owners.
The trace evidence is packaged separately below, so raw filtered maps do not
carry an artificial state or order structure. -/
abbrev Data := StepFamily

structure TraceCompatibleData where
  step : StepFamily
  trace_compatible :
    ∀ n A, matrixTraceState (n + 1) (step n A) = matrixTraceState n A

/-! The abstract interface now has a concrete noncommutative matrix instance.
The only scalar calculation here is normalization of the genuine matrix
trace; positivity and the algebra map are supplied by the matrix owners
above, not by an artificial order on matrices. -/

theorem concrete_trace_compatible (n : ℕ) (A : MatrixStage n) :
    matrixTraceState (n + 1) (concreteStep n A) = matrixTraceState n A := by
  dsimp [matrixTraceState, matrixTraceFunctional]
  rw [concreteStep_trace]
  rw [pow_succ]
  field_simp [show (2 : ℂ) ^ n ≠ 0 by norm_num]

def concreteTraceCompatibleData : TraceCompatibleData where
  step := concreteStep
  trace_compatible := concrete_trace_compatible

/-- Iterate the supplied successor embedding along a proof `i ≤ j`. -/
def map (T : Data) {i j : ℕ} (hij : i ≤ j) :
    MatrixStage i →⋆ₐ[ℂ] MatrixStage j :=
  Nat.leRecOn hij
    (fun {k} (f : MatrixStage i →⋆ₐ[ℂ] MatrixStage k) =>
      (T k).comp f)
    (StarAlgHom.id ℂ (MatrixStage i))

@[simp] theorem map_id (T : Data) (i : ℕ) :
    map T (le_refl i) = StarAlgHom.id ℂ (MatrixStage i) := by
  dsimp [map]
  exact Nat.leRecOn_self (C := fun k => MatrixStage i →⋆ₐ[ℂ] MatrixStage k)
    (StarAlgHom.id ℂ (MatrixStage i))

theorem map_succ (T : Data) {i j : ℕ} (hij : i ≤ j) :
    map T (Nat.le.step hij) = (T j).comp (map T hij) := by
  dsimp [map]
  exact Nat.leRecOn_succ (C := fun k => MatrixStage i →⋆ₐ[ℂ] MatrixStage k)
    hij (StarAlgHom.id ℂ (MatrixStage i))

theorem map_comp (T : Data) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (map T hjk).comp (map T hij) = map T (le_trans hij hjk) := by
  induction hjk with
  | refl =>
      rw [map_id T]
      simp
  | step hjm ih =>
      rw [map_succ T hjm, map_succ T (le_trans hij hjm),
        StarAlgHom.comp_assoc, ih]

theorem trace_compatible (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    {i j : ℕ} (hij : i ≤ j) (A : MatrixStage i) :
    matrixTraceState j (map T hij A) = matrixTraceState i A := by
  induction hij with
  | refl =>
      simp
  | step hjm ih =>
      rw [map_succ T hjm]
      change matrixTraceState _ (T _ (map T hjm A)) = _
      rw [hT, ih]

/-! The concrete tower is exposed directly as a filtered family of
`StarAlgHom`s.  These are the actual categorical coherence laws used by a
later colimit owner; no state or order structure is smuggled in here. -/

def concreteMap {i j : ℕ} (hij : i ≤ j) :
    MatrixStage i →⋆ₐ[ℂ] MatrixStage j :=
  map concreteStep hij

@[simp] theorem concreteMap_succ_step (n : ℕ) :
    concreteMap (Nat.le_succ n) = concreteStep n := by
  simpa [concreteMap] using (map_succ concreteStep (le_refl n))

theorem concreteMap_injective {i j : ℕ} (hij : i ≤ j) :
    Function.Injective (concreteMap hij) := by
  induction hij with
  | refl =>
      intro A B hAB
      change (map concreteStep (le_refl _)) A =
        (map concreteStep (le_refl _)) B at hAB
      rw [map_id concreteStep] at hAB
      exact hAB
  | step hjm ih =>
      intro A B hAB
      apply ih
      apply concreteStep_injective _
      change map concreteStep (Nat.le.step hjm) A =
        map concreteStep (Nat.le.step hjm) B at hAB
      rw [map_succ concreteStep hjm] at hAB
      exact hAB

@[simp] theorem concreteMap_id (i : ℕ) :
    concreteMap (le_refl i) = StarAlgHom.id ℂ (MatrixStage i) := by
  exact map_id concreteStep i

theorem concreteMap_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (concreteMap hjk).comp (concreteMap hij) = concreteMap (le_trans hij hjk) := by
  exact map_comp concreteStep hij hjk

theorem concreteMap_trace {i j : ℕ} (hij : i ≤ j) (A : MatrixStage i) :
    matrixTraceState j (concreteMap hij A) = matrixTraceState i A := by
  exact trace_compatible concreteStep concrete_trace_compatible hij A

@[simp] theorem concreteMap_star {i j : ℕ} (hij : i ≤ j) (A : MatrixStage i) :
    concreteMap hij (star A) = star (concreteMap hij A) := by
  exact (concreteMap hij).map_star' A

/-! ### Categorical filtered colimit of the raw matrix tower

The colimit below is a genuine `ModuleCat ℂ` colimit of the supplied
noncommutative matrix embeddings.  No order structure on matrices is used;
the trace functional remains a separate compatible family of scalar maps.
-/

def moduleDiagram (T : Data) : ℕ ⥤ ModuleCat ℂ where
  obj n := ModuleCat.of ℂ (MatrixStage n)
  map f := ModuleCat.ofHom
    ((map T (leOfHom f)).toAlgHom.toLinearMap)
  map_id n := by
    apply ModuleCat.hom_ext
    change (map T (le_refl n)).toAlgHom.toLinearMap = LinearMap.id
    rw [map_id T]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    change
      (map T (le_trans (leOfHom f) (leOfHom g))).toAlgHom.toLinearMap =
        ((map T (leOfHom g)).toAlgHom.toLinearMap).comp
          ((map T (leOfHom f)).toAlgHom.toLinearMap)
    have h := congrArg
      (fun e : MatrixStage _ →⋆ₐ[ℂ] MatrixStage _ => e.toAlgHom.toLinearMap)
      (map_comp T (leOfHom f) (leOfHom g)).symm
    simpa [StarAlgHom.comp_apply, AlgHom.comp_apply, LinearMap.comp_apply] using h

abbrev traceColimit (T : Data) : Type :=
  (colimit (moduleDiagram T) : ModuleCat ℂ)

/-- The linear carrier is also exposed with its native filtered-colimit certificate. -/
def traceColimit_isColimit (T : Data) :
    IsColimit (colimit.cocone (moduleDiagram T)) := by
  exact colimit.isColimit (moduleDiagram T)

def traceColimitInclusion (T : Data) (n : ℕ) :
    MatrixStage n →ₗ[ℂ] traceColimit T :=
  (colimit.ι (moduleDiagram T) n).hom

def traceCocone (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A) :
    Cocone (moduleDiagram T) where
  pt := ModuleCat.of ℂ ℂ
  ι :=
    { app := fun n => ModuleCat.ofHom (matrixTraceFunctional n)
      naturality := by
        intro m n f
        apply ModuleCat.hom_ext
        ext A
        change matrixTraceFunctional n (map T (leOfHom f) A) =
          matrixTraceFunctional m A
        simpa [matrixTraceState] using
          trace_compatible T hT (leOfHom f) A }

def traceColimitFunctional (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A) :
    traceColimit T →ₗ[ℂ] ℂ :=
  (colimit.desc (moduleDiagram T) (traceCocone T hT)).hom

theorem traceColimitFunctional_inclusion (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    (n : ℕ)
    (A : MatrixStage n) :
    traceColimitFunctional T hT (traceColimitInclusion T n A) =
      matrixTraceFunctional n A := by
  have h := colimit.ι_desc (traceCocone T hT) n
  exact congrArg (fun f => f A) h

/-- The colimit trace readout is normalized on every canonical stage unit. -/
theorem traceColimitFunctional_inclusion_one (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    (n : ℕ) :
    traceColimitFunctional T hT (traceColimitInclusion T n (1 : MatrixStage n)) = 1 := by
  rw [traceColimitFunctional_inclusion T hT]
  exact matrixTraceState_one n

/- The descended trace retains finite cyclicity on every canonical stage. -/
theorem traceColimitFunctional_inclusion_mul_comm
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    (n : ℕ) (A B : MatrixStage n) :
    traceColimitFunctional T hT
        (traceColimitInclusion T n (A * B)) =
      traceColimitFunctional T hT
        (traceColimitInclusion T n (B * A)) := by
  rw [traceColimitFunctional_inclusion T hT,
    traceColimitFunctional_inclusion T hT]
  exact matrixTraceState_mul_comm n A B

/- The descended trace preserves the involution on every finite stage. -/
theorem traceColimitFunctional_inclusion_star (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    (n : ℕ) (A : MatrixStage n) :
    star (traceColimitFunctional T hT (traceColimitInclusion T n A)) =
      traceColimitFunctional T hT (traceColimitInclusion T n (star A)) := by
  rw [traceColimitFunctional_inclusion T hT,
    traceColimitFunctional_inclusion T hT]
  exact matrixTraceState_star n A

/- The colimit readout retains the finite positive-real-part shadow on `A* A`. -/
theorem traceColimitFunctional_inclusion_star_mul_self_nonneg
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    (n : ℕ) (A : MatrixStage n) :
    0 ≤
      (traceColimitFunctional T hT
        (traceColimitInclusion T n (star A * A))).re := by
  rw [traceColimitFunctional_inclusion T hT]
  exact matrixTraceState_realPart_star_mul_self_nonneg n A

/-- The compatible normalized trace is the unique linear readout on the
colimit with the prescribed finite-stage values. -/
theorem traceColimitFunctional_unique (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    (f : traceColimit T →ₗ[ℂ] ℂ)
    (hf : ∀ (n : ℕ) (A : MatrixStage n),
      f (traceColimitInclusion T n A) = matrixTraceFunctional n A) :
    f = traceColimitFunctional T hT := by
  have hhom :
      ModuleCat.ofHom f = ModuleCat.ofHom (traceColimitFunctional T hT) := by
    apply colimit.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext A
    change f (traceColimitInclusion T n A) =
      traceColimitFunctional T hT (traceColimitInclusion T n A)
    rw [hf n A, traceColimitFunctional_inclusion T hT]
  exact congrArg
    (fun g : ModuleCat.of ℂ (traceColimit T) ⟶ ModuleCat.of ℂ ℂ => g.hom) hhom

theorem traceColimitInclusion_transition
    (T : Data) {m n : ℕ} (hmn : m ≤ n) (A : MatrixStage m) :
    traceColimitInclusion T n (map T hmn A) =
      traceColimitInclusion T m A := by
  have h := (colimit.cocone (moduleDiagram T)).w (homOfLE hmn)
  exact congrArg (fun f => f A) h

/-! The same concrete matrix tower is exposed through the filtered linear
system owner used by the operatorial BKM transport.  The transition maps are
the existing star-algebra maps viewed as linear maps; no new coefficient-level
embedding is introduced. -/

def concreteFilteredDirectSystem :
    FilteredColimit.DirectInductiveSystem ℂ ℕ
      (fun n => MatrixStage n) where
  f := fun {i j} hij => (concreteMap hij).toAlgHom.toLinearMap
  f_id := by
    intro i
    apply LinearMap.ext
    intro A
    change concreteMap (le_refl i) A = A
    rw [concreteMap_id]
    rfl
  f_comp := by
    intro i j k hij hjk
    apply LinearMap.ext
    intro A
    have h := congrArg
      (fun f : MatrixStage i →⋆ₐ[ℂ] MatrixStage k => f A)
      (concreteMap_comp hij hjk)
    simpa [StarAlgHom.comp_apply] using h

def concreteTraceInductiveCocone :
    FilteredColimit.InductiveCocone ℂ concreteFilteredDirectSystem
      (traceColimit concreteStep) := by
  refine ⟨fun n => traceColimitInclusion concreteStep n, ?_⟩
  intro i j hij
  apply LinearMap.ext
  intro A
  change traceColimitInclusion concreteStep j
      (concreteMap hij A) = traceColimitInclusion concreteStep i A
  exact traceColimitInclusion_transition concreteStep hij A

/-! Operator-stage realization of the same tower.  The matrix coordinate
equivalence is used only to transport the already-owned transition maps and
the already-owned trace cocone. -/

def operatorToMatrixLinearMap (n : ℕ) :
    FiniteOperatorAlgebra (2 ^ n) →ₗ[ℂ] MatrixStage n where
  toFun := matrixOfOp
  map_add' := by
    intro A B
    exact matrixOfOp_add A B
  map_smul' := by
    intro c A
    exact matrixOfOp_complex_smul c A

lemma matrixOp_smul (n : ℕ) (c : ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    CblinfunMatrix.matrixOp (c • M) =
      c • CblinfunMatrix.matrixOp M := by
  apply CblinfunMatrix.matrixOfOp_injective
  simp only [CblinfunMatrix.matrixOfOp_matrixOp, matrixOfOp_complex_smul]

lemma matrixOp_add {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix κ ι ℂ) :
    CblinfunMatrix.matrixOp (M + N) =
      CblinfunMatrix.matrixOp M + CblinfunMatrix.matrixOp N := by
  apply matrixOfOp_injective
  simp [matrixOfOp_add]

/-! ### The same finite tower in operator coordinates

The operator presentation is transported through the already-owned finite
matrix coordinate equivalence.  This keeps the noncommutative operator
carrier and the concrete matrix colimit tied to the same transition maps.
-/

def operatorBond {i j : ℕ} (hij : i ≤ j) :
    FiniteOperatorAlgebra (2 ^ i) →ₗ[ℂ] FiniteOperatorAlgebra (2 ^ j) where
  toFun A := CblinfunMatrix.matrixOp (concreteMap hij (matrixOfOp A))
  map_add' := by
    intro A B
    rw [matrixOfOp_add, map_add, matrixOp_add]
  map_smul' := by
    intro c A
    change CblinfunMatrix.matrixOp (concreteMap hij (matrixOfOp (c • A))) =
      c • CblinfunMatrix.matrixOp (concreteMap hij (matrixOfOp A))
    rw [matrixOfOp_complex_smul, map_smul, matrixOp_smul]

theorem operatorBond_matrixOfOp {i j : ℕ} (hij : i ≤ j)
    (A : FiniteOperatorAlgebra (2 ^ i)) :
    matrixOfOp (operatorBond hij A) =
      concreteMap hij (matrixOfOp A) := by
  simp [operatorBond]

def concreteOperatorFilteredDirectSystem :
    @FilteredColimit.DirectInductiveSystem ℂ _ ℕ _
      (fun n => FiniteOperatorAlgebra (2 ^ n))
      (fun _ => ContinuousLinearMap.addCommGroup)
      (fun _ => ContinuousLinearMap.module) where
  f := fun {i j} hij => operatorBond hij
  f_id := by
    intro i
    apply LinearMap.ext
    intro A
    apply matrixOfOp_injective
    rw [operatorBond_matrixOfOp, concreteMap_id]
    rfl
  f_comp := by
    intro i j k hij hjk
    apply LinearMap.ext
    intro A
    apply matrixOfOp_injective
    change matrixOfOp (operatorBond hjk (operatorBond hij A)) = _
    rw [operatorBond_matrixOfOp, operatorBond_matrixOfOp,
      operatorBond_matrixOfOp]
    exact congrArg (fun f => f (matrixOfOp A))
      (concreteMap_comp hij hjk)

def concreteOperatorTraceInductiveCocone :
    FilteredColimit.InductiveCocone ℂ
      concreteOperatorFilteredDirectSystem
      (traceColimit concreteStep) := by
  refine ⟨fun n =>
    (traceColimitInclusion concreteStep n).comp (operatorToMatrixLinearMap n), ?_⟩
  intro i j hij
  apply LinearMap.ext
  intro A
  change traceColimitInclusion concreteStep j
      (matrixOfOp (operatorBond hij A)) =
    traceColimitInclusion concreteStep i (matrixOfOp A)
  rw [operatorBond_matrixOfOp]
  exact traceColimitInclusion_transition concreteStep hij (matrixOfOp A)

/-! ### Finite operator and BKM readouts on the concrete colimit -/

theorem traceColimitFunctional_inclusion_matrixOfOp
    (n : ℕ) (A : FiniteOperatorAlgebra (2 ^ n)) :
    traceColimitFunctional concreteStep concrete_trace_compatible
        (traceColimitInclusion concreteStep n (matrixOfOp A)) =
      (1 / (2 ^ n : ℂ)) * finiteOperatorTrace A := by
  rw [traceColimitFunctional_inclusion]
  rfl

theorem maximallyMixed_bkm_kernel_identity
    (n : ℕ) (s : ℝ) :
    (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : FiniteOperatorAlgebra (2 ^ n)) s
        (1 : FiniteOperatorAlgebra (2 ^ n)) = 1 := by
  rw [FaithfulDensityOperator.kuboMoriKernelFunctional_apply]
  exact FaithfulDensityOperator.kuboMoriIntegrand_one_one
    (maximallyMixedFaithfulDensityPowTwo n) s

theorem maximallyMixed_bkm_kernel_eq_normalized_trace
    (n : ℕ) (s : ℝ) (B : FiniteOperatorAlgebra (2 ^ n)) :
    (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : FiniteOperatorAlgebra (2 ^ n)) s B =
      (1 / (2 ^ n : ℂ)) * finiteOperatorTrace B := by
  rw [FaithfulDensityOperator.kuboMoriKernelFunctional_apply]
  unfold FaithfulDensityOperator.kuboMoriIntegrand
  simp only [star_one, mul_one]
  rw [← (maximallyMixedFaithfulDensityPowTwo n).rpow_add]
  have hs : s + (1 - s) = 1 := by ring
  rw [hs, (maximallyMixedFaithfulDensityPowTwo n).rpow_one]
  change finiteOperatorTrace
    (((1 / (2 ^ n : ℝ)) • (1 : FiniteOperatorAlgebra (2 ^ n))) * B) = _
  unfold finiteOperatorTrace
  change Matrix.trace (matrixOfOp
    (((1 / (2 ^ n : ℝ)) • (1 : FiniteOperatorAlgebra (2 ^ n))).comp B)) = _
  rw [matrixOfOp_comp, matrixOfOp_real_smul]
  have h_one : matrixOfOp (1 : FiniteOperatorAlgebra (2 ^ n)) =
      (1 : MatrixStage n) := by
    change matrixOfOp
        (ContinuousLinearMap.id ℂ (FiniteHilbertSpace (2 ^ n))) = 1
    exact matrixOfOp_id
  rw [h_one, Matrix.smul_mul, one_mul, Matrix.trace_smul]
  simp [smul_eq_mul]

theorem traceColimitFunctional_inclusion_bkm
    (n : ℕ) (s : ℝ) (B : FiniteOperatorAlgebra (2 ^ n)) :
    traceColimitFunctional concreteStep concrete_trace_compatible
        (traceColimitInclusion concreteStep n (matrixOfOp B)) =
      (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : FiniteOperatorAlgebra (2 ^ n)) s B := by
  rw [traceColimitFunctional_inclusion_matrixOfOp,
    maximallyMixed_bkm_kernel_eq_normalized_trace]

theorem maximallyMixed_bkm_kernel_compatible
    {i j : ℕ} (hij : i ≤ j) (s : ℝ)
    (B : FiniteOperatorAlgebra (2 ^ i)) :
    (maximallyMixedFaithfulDensityPowTwo j).kuboMoriKernelFunctional
        (1 : FiniteOperatorAlgebra (2 ^ j)) s (operatorBond hij B) =
      (maximallyMixedFaithfulDensityPowTwo i).kuboMoriKernelFunctional
        (1 : FiniteOperatorAlgebra (2 ^ i)) s B := by
  rw [maximallyMixed_bkm_kernel_eq_normalized_trace,
    maximallyMixed_bkm_kernel_eq_normalized_trace]
  unfold finiteOperatorTrace
  rw [operatorBond_matrixOfOp]
  simpa [matrixTraceState, finiteOperatorTrace] using
    (concreteMap_trace hij (matrixOfOp B))

theorem concreteOperator_bkm_colimit_descent
    (s : ℝ) (n : ℕ) :
    (traceColimitFunctional concreteStep concrete_trace_compatible).comp
        ((traceColimitInclusion concreteStep n).comp
          (operatorToMatrixLinearMap n)) =
      (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : FiniteOperatorAlgebra (2 ^ n)) s := by
  ext B
  exact traceColimitFunctional_inclusion_bkm n s B

theorem concreteOperator_bkm_dual_inverse_transition
    (s : ℝ) {i j : ℕ} (hij : i ≤ j) :
    FilteredColimit.InductiveCocone.dualInverseTransition
        concreteOperatorFilteredDirectSystem hij
        (InfoGeometry.Canonical.SouriauOnsagerBKMFilteredColimit.stageKernel
          (fun n => 2 ^ n)
          (fun n => maximallyMixedFaithfulDensityPowTwo n)
          (fun _ => (1 : FiniteOperatorAlgebra _)) s j) =
      InfoGeometry.Canonical.SouriauOnsagerBKMFilteredColimit.stageKernel
        (fun n => 2 ^ n)
        (fun n => maximallyMixedFaithfulDensityPowTwo n)
        (fun _ => (1 : FiniteOperatorAlgebra _)) s i := by
  refine
    InfoGeometry.Canonical.SouriauOnsagerBKMFilteredColimit.stageKernel_compatible_of_colimit_descent
      (dim := fun n => 2 ^ n)
      (sys := concreteOperatorFilteredDirectSystem)
      (D := fun n => maximallyMixedFaithfulDensityPowTwo n)
      (A := fun _ => (1 : FiniteOperatorAlgebra _))
      (s := s)
      (cocone := concreteOperatorTraceInductiveCocone)
      (Phi := traceColimitFunctional concreteStep concrete_trace_compatible)
      ?_ hij
  intro n
  exact concreteOperator_bkm_colimit_descent s n

theorem concreteOperator_bkm_colimit_readout_independent
    (s : ℝ) {i j : ℕ} (hij : i ≤ j)
    (B : FiniteOperatorAlgebra (2 ^ i)) :
    traceColimitFunctional concreteStep concrete_trace_compatible
        (traceColimitInclusion concreteStep j
          (matrixOfOp (operatorBond hij B))) =
      (maximallyMixedFaithfulDensityPowTwo i).kuboMoriKernelFunctional
        (1 : FiniteOperatorAlgebra (2 ^ i)) s B := by
  exact
    InfoGeometry.Canonical.SouriauOnsagerBKMFilteredColimit.stageKernel_colimit_readout_independent
      (dim := fun n => 2 ^ n)
      (sys := concreteOperatorFilteredDirectSystem)
      (D := fun n => maximallyMixedFaithfulDensityPowTwo n)
      (A := fun _ => (1 : FiniteOperatorAlgebra _))
      (s := s)
      (cocone := concreteOperatorTraceInductiveCocone)
      (Phi := traceColimitFunctional concreteStep concrete_trace_compatible)
      (hdesc := by
        intro n
        exact concreteOperator_bkm_colimit_descent s n)
      hij B

theorem traceColimitFunctional_inclusion_bkm_identity
    (n : ℕ) (s : ℝ) :
    traceColimitFunctional concreteStep concrete_trace_compatible
        (traceColimitInclusion concreteStep n
          (matrixOfOp (1 : FiniteOperatorAlgebra (2 ^ n)))) =
      (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : FiniteOperatorAlgebra (2 ^ n)) s
        (1 : FiniteOperatorAlgebra (2 ^ n)) := by
  have hmat :
      matrixOfOp (1 : FiniteOperatorAlgebra (2 ^ n)) =
        (1 : MatrixStage n) := by
    change matrixOfOp
        (ContinuousLinearMap.id ℂ (FiniteHilbertSpace (2 ^ n))) = 1
    exact matrixOfOp_id
  rw [hmat, traceColimitFunctional_inclusion]
  change matrixTraceState n (1 : MatrixStage n) = _
  rw [matrixTraceState_one]
  exact (maximallyMixed_bkm_kernel_identity n s).symm

end InfoGeometry.Canonical.CuntzMatrixTraceTower
