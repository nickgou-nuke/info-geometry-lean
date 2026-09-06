import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
import InfoGeometry.Canonical.CuntzMatrixTraceTower

/-!
# Native star-algebra transition maps on BitWord matrix stages

The concrete matrix tower is owned by the native `Fin (2^n)` stages.  This
bridge transports its genuine `StarAlgHom` successor maps back across the
finite index equivalences to the `BitWord n` matrix carriers.  It therefore
provides a categorical transition system without treating a coefficient
formula as an algebra homomorphism by fiat.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge

open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

private def starAlgHomOfEquiv {A B : Type*} [Semiring A] [Semiring B]
    [StarRing A] [StarRing B] [Algebra ℂ A] [Algebra ℂ B]
    (e : A ≃⋆ₐ[ℂ] B)
    (hcomm : ∀ r : ℂ, e (algebraMap ℂ A r) = algebraMap ℂ B r) :
    A →⋆ₐ[ℂ] B where
  toFun := e
  map_one' := e.map_one
  map_mul' := e.map_mul
  map_zero' := e.map_zero
  map_add' := e.map_add
  commutes' := by
    intro r
    exact hcomm r
  map_star' := by
    intro a
    exact map_star e a

def bitWordDyadicStarEmbedding (n : ℕ) :
    BitWordMatrixStage n →⋆ₐ[ℂ] BitWordMatrixStage (n + 1) :=
  starAlgHomOfEquiv (bitWordStageStarAlgEquiv (n + 1)).symm (by
      intro r
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      simp) |>.comp
    ((concreteStep n).comp
      (starAlgHomOfEquiv (bitWordStageStarAlgEquiv n) (by
        intro r
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        simp)))

@[simp] theorem bitWordDyadicStarEmbedding_apply
    (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordDyadicStarEmbedding n A =
      (bitWordStageStarAlgEquiv (n + 1)).symm
        (concreteStep n (bitWordStageStarAlgEquiv n A)) := by
  rfl

@[simp] theorem bitWordDyadicStarEmbedding_map_one (n : ℕ) :
    bitWordDyadicStarEmbedding n (1 : BitWordMatrixStage n) = 1 := by
  exact (bitWordDyadicStarEmbedding n).map_one

@[simp] theorem bitWordDyadicStarEmbedding_map_mul
    (n : ℕ) (A B : BitWordMatrixStage n) :
    bitWordDyadicStarEmbedding n (A * B) =
      bitWordDyadicStarEmbedding n A * bitWordDyadicStarEmbedding n B := by
  exact (bitWordDyadicStarEmbedding n).map_mul A B

@[simp] theorem bitWordDyadicStarEmbedding_map_star
    (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordDyadicStarEmbedding n (star A) =
      star (bitWordDyadicStarEmbedding n A) := by
  exact map_star (bitWordDyadicStarEmbedding n) A

theorem bitWordDyadicStarEmbedding_trace_compatible
    (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordMatrixTraceFunctional (n + 1)
        (bitWordDyadicStarEmbedding n A) =
      bitWordMatrixTraceFunctional n A := by
  rw [bitWordDyadicStarEmbedding_apply,
    bitWordStageTrace_transport, bitWordStageTrace_transport]
  simp only [StarAlgEquiv.apply_symm_apply]
  change matrixTraceState (n + 1)
      (concreteStep n (bitWordStageStarAlgEquiv n A)) =
    matrixTraceState n (bitWordStageStarAlgEquiv n A)
  exact concrete_trace_compatible n (bitWordStageStarAlgEquiv n A)

abbrev BitWordStarData :=
  ∀ n, BitWordMatrixStage n →⋆ₐ[ℂ] BitWordMatrixStage (n + 1)

def bitWordStarMap (T : BitWordStarData) {i j : ℕ} (hij : i ≤ j) :
    BitWordMatrixStage i →⋆ₐ[ℂ] BitWordMatrixStage j :=
  Nat.leRecOn hij
    (fun {k} (f : BitWordMatrixStage i →⋆ₐ[ℂ] BitWordMatrixStage k) =>
      (T k).comp f)
    (StarAlgHom.id ℂ (BitWordMatrixStage i))

@[simp] theorem bitWordStarMap_id (T : BitWordStarData) (i : ℕ) :
    bitWordStarMap T (le_refl i) =
      StarAlgHom.id ℂ (BitWordMatrixStage i) := by
  dsimp [bitWordStarMap]
  exact Nat.leRecOn_self (C := fun k =>
    BitWordMatrixStage i →⋆ₐ[ℂ] BitWordMatrixStage k)
    (StarAlgHom.id ℂ (BitWordMatrixStage i))

theorem bitWordStarMap_succ (T : BitWordStarData)
    {i j : ℕ} (hij : i ≤ j) :
    bitWordStarMap T (Nat.le.step hij) =
      (T j).comp (bitWordStarMap T hij) := by
  dsimp [bitWordStarMap]
  exact Nat.leRecOn_succ (C := fun k =>
    BitWordMatrixStage i →⋆ₐ[ℂ] BitWordMatrixStage k)
    hij (StarAlgHom.id ℂ (BitWordMatrixStage i))

theorem bitWordStarMap_comp (T : BitWordStarData)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (bitWordStarMap T hjk).comp (bitWordStarMap T hij) =
      bitWordStarMap T (le_trans hij hjk) := by
  induction hjk with
  | refl =>
      rw [bitWordStarMap_id T]
      simp
  | step hjm ih =>
      rw [bitWordStarMap_succ T hjm,
        bitWordStarMap_succ T (le_trans hij hjm),
        StarAlgHom.comp_assoc, ih]

theorem bitWordStarMap_trace_compatible
    (T : BitWordStarData)
    (hT : ∀ n A,
      bitWordMatrixTraceFunctional (n + 1) (T n A) =
        bitWordMatrixTraceFunctional n A)
    {i j : ℕ} (hij : i ≤ j) (A : BitWordMatrixStage i) :
    bitWordMatrixTraceFunctional j (bitWordStarMap T hij A) =
      bitWordMatrixTraceFunctional i A := by
  induction hij with
  | refl =>
      rw [bitWordStarMap_id T i]
      rfl
  | step hjm ih =>
      rw [bitWordStarMap_succ T hjm]
      change bitWordMatrixTraceFunctional _
          (T _ (bitWordStarMap T hjm A)) = _
      rw [hT, ih]

def bitWordDyadicStarData : BitWordStarData :=
  bitWordDyadicStarEmbedding

theorem bitWordDyadicStarMap_trace_compatible
    {i j : ℕ} (hij : i ≤ j) (A : BitWordMatrixStage i) :
    bitWordMatrixTraceFunctional j
        (bitWordStarMap bitWordDyadicStarData hij A) =
      bitWordMatrixTraceFunctional i A := by
  apply bitWordStarMap_trace_compatible bitWordDyadicStarData
    (fun n B => bitWordDyadicStarEmbedding_trace_compatible n B) hij A

end InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
