import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Tactic

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
abbrev Data := ∀ n, MatrixStage n →⋆ₐ[ℂ] MatrixStage (n + 1)

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
      simpa using hAB
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

end InfoGeometry.Canonical.CuntzMatrixTraceTower
