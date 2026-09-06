import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.StarAlgHom
import InfoGeometry.Canonical.ComplexMatrixStage
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge

/-!
# Genuine Matrix Stage Morphisms

This module establishes the full `StarAlgHom ℂ (Stage m) (Stage n)` morphism structure
on the finite matrix stages `Stage n := Matrix (BitWord n) (BitWord n) ℂ`.

Key Results:
1. `bondStarAlgHom n : Stage n →⋆ₐ[ℂ] Stage (n + 1)`:
   The elementary step embedding as a genuine C*-algebra homomorphism (preserving 1, *, +, ·, smul, algebraMap).
2. `bondFun_injective`, `bondStarAlgHom_injective`:
   Strict injectivity of the step embeddings.
3. Trace Doubling & Normalized Invariance:
   `trace (bondFun n M) = 2 * trace M` and `normalizedTrace (n + 1) (bondFun n M) = normalizedTrace n M`.
4. Transitive Morphism Family:
   `stageMorphism m n (h : m ≤ n) : Stage m →⋆ₐ[ℂ] Stage n`.
5. Functorial, Cocycle & Injectivity Coherences:
   - `stageMorphism_id : stageMorphism m m (le_refl m) = StarAlgHom.id ℂ (Stage m)`
   - `stageMorphism_step : stageMorphism m (n + 1) (Nat.le.step h) = (bondStarAlgHom n).comp (stageMorphism m n h)`
   - `stageMorphism_comp : (stageMorphism j k hjk).comp (stageMorphism i j hij) = stageMorphism i k (le_trans hij hjk)`
   - `stageMorphism_injective : Function.Injective (stageMorphism m n h)`
   - Normalized trace invariance: `normalizedTrace n (stageMorphism m n h M) = normalizedTrace m M`.

All proofs are complete in native Lean 4 with 0 sorrys and 0 custom axioms.
-/

namespace InfoGeometry.Canonical.GenuineMatrixStageMorphism

open ComplexMatrixStage
open UHFInductiveColimitBoundary
open Matrix
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge

noncomputable section

/-! ## 1. Normalized Trace on Matrix Stages -/

/-- Normalized trace functional at stage n: `2⁻ⁿ · Tr(M)`. -/
def normalizedTrace (n : ℕ) (M : Stage n) : ℂ :=
  (1 / (2 ^ n : ℂ)) * Matrix.trace M

@[simp] theorem normalizedTrace_apply (n : ℕ) (M : Stage n) :
    normalizedTrace n M = (1 / (2 ^ n : ℂ)) * Matrix.trace M := rfl

/-! ## 2. Star and SMul Preservation for the Step Morphism -/

theorem bondFun_smul (n : ℕ) (c : ℂ) (M : Stage n) :
    bondFun n (c • M) = c • bondFun n M := by
  ext v w
  dsimp [bondFun]
  split_ifs with h
  · rfl
  · simp

theorem bondFun_star (n : ℕ) (M : Stage n) :
    bondFun n (star M) = star (bondFun n M) := by
  ext v w
  dsimp [bondFun, Matrix.star_apply]
  by_cases h : v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩
  · simp [h]
  · have h_symm : w ⟨n, Nat.lt_succ_self n⟩ ≠ v ⟨n, Nat.lt_succ_self n⟩ := fun h_eq => h h_eq.symm
    simp [h, h_symm]

/-- The genuine star-algebra step homomorphism `Stage n →⋆ₐ[ℂ] Stage (n + 1)`. -/
def bondStarAlgHom (n : ℕ) : Stage n →⋆ₐ[ℂ] Stage (n + 1) where
  toFun := bondFun n
  map_one' := bondFun_one n
  map_mul' := bondFun_mul n
  map_zero' := by
    ext v w
    dsimp [bondFun]
    split_ifs <;> rfl
  map_add' := bondFun_add n
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one, bondFun_smul, bondFun_one]
  map_star' := bondFun_star n

@[simp] theorem bondStarAlgHom_apply (n : ℕ) (M : Stage n) :
    bondStarAlgHom n M = bondFun n M := rfl

/-- Injectivity of the elementary matrix step embedding `bondFun n`. -/
theorem bondFun_injective (n : ℕ) : Function.Injective (bondFun n) := by
  intro A B h
  ext u v
  have h_elem := congr_fun (congr_fun h (extendSucc n u false)) (extendSucc n v false)
  dsimp [bondFun] at h_elem
  have h_eq : (extendSucc n u false) ⟨n, Nat.lt_succ_self n⟩ = (extendSucc n v false) ⟨n, Nat.lt_succ_self n⟩ := by
    simp [extendSucc]
  simp [h_eq, prefixSucc_extendSucc] at h_elem
  exact h_elem

/-- Injectivity of the bundled step homomorphism `bondStarAlgHom n`. -/
theorem bondStarAlgHom_injective (n : ℕ) : Function.Injective (bondStarAlgHom n) :=
  bondFun_injective n

private theorem extendBitWord_eq_extendSucc (n : ℕ) (w : BitWord n) (b : Bool) :
    CantorKMSState.extendBitWord n w b = extendSucc n w b := by
  funext i
  by_cases hi : i.1 < n
  · simp [CantorKMSState.extendBitWord, CantorKMSState.bitWordEquiv, extendSucc, hi]
  · have hi' : i.1 = n := by omega
    simp [CantorKMSState.extendBitWord, CantorKMSState.bitWordEquiv, extendSucc, hi']

private theorem extendSucc_eq_iff (n : ℕ) (u : BitWord n) (b : Bool)
    (x : BitWord (n + 1)) :
    extendSucc n u b = x ↔
      u = prefixSucc n x ∧ x ⟨n, Nat.lt_succ_self n⟩ = b := by
  constructor
  · intro h
    subst x
    exact ⟨(prefixSucc_extendSucc n u b).symm, by simp [extendSucc]⟩
  · rintro ⟨hu, hb⟩
    subst u
    funext i
    by_cases hi : i.1 < n
    · simp [extendSucc, prefixSucc, hi]
    · have hi' : i.1 = n := by omega
      have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi'
      rw [hi_eq]
      simp [extendSucc, hb]

private theorem bondFun_single (n : ℕ) (u v : BitWord n) (c : ℂ) :
    bondFun n (Matrix.single u v c) =
      c • (Matrix.single (extendSucc n u false) (extendSucc n v false) 1 +
        Matrix.single (extendSucc n u true) (extendSucc n v true) 1) := by
  ext x y
  cases hx : x ⟨n, Nat.lt_succ_self n⟩ <;>
    cases hy : y ⟨n, Nat.lt_succ_self n⟩ <;>
      simp [bondFun, Matrix.single, extendSucc, prefixSucc,
        extendSucc_eq_iff, hx, hy]

theorem bondFun_eq_dyadicMatrixEmbedding
    (n : ℕ) (A : Matrix (BitWord n) (BitWord n) ℂ) :
    ComplexMatrixStage.bondFun n A = dyadicMatrixEmbedding n A := by
  classical
  let S : Matrix (BitWord n) (BitWord n) ℂ :=
    ∑ u : BitWord n, ∑ v : BitWord n, Matrix.single u v (A u v)
  have hA : S = A := by
    simpa [S] using (Matrix.matrix_eq_sum_single A).symm
  calc
    bondFun n A = bondFun n S := by rw [hA]
    _ = ∑ u : BitWord n, ∑ v : BitWord n,
        bondFun n (Matrix.single u v (A u v)) := by
      change bond n S = ∑ u : BitWord n, ∑ v : BitWord n,
        bond n (Matrix.single u v (A u v))
      simp only [S, map_sum]
    _ = dyadicMatrixEmbedding n A := by
      simp only [bondFun_single]
      simp [dyadicMatrixEmbedding, extendBitWord_eq_extendSucc]

/-! ## 3. Trace Doubling and Normalized Trace Invariance -/

/-- Under the step embedding, the unnormalized matrix trace doubles. -/
theorem bondFun_trace (n : ℕ) (M : Stage n) :
    Matrix.trace (bondFun n M) = 2 * Matrix.trace M := by
  dsimp [Matrix.trace]
  rw [bitword_sum_last_split]
  have h_pair (u : BitWord n) :
      bondFun n M (extendSucc n u true) (extendSucc n u true) +
      bondFun n M (extendSucc n u false) (extendSucc n u false) = 2 * M u u := by
    rw [bondFun_extendSucc, bondFun_extendSucc]
    simp [two_mul]
  simp_rw [h_pair]
  rw [← Finset.mul_sum]

/-- The normalized trace is invariant under the step embedding. -/
theorem normalizedTrace_bond (n : ℕ) (M : Stage n) :
    normalizedTrace (n + 1) (bondFun n M) = normalizedTrace n M := by
  rw [normalizedTrace_apply, normalizedTrace_apply]
  rw [bondFun_trace]
  have h2n : (2 ^ n : ℂ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero n (by norm_num)
  have hpow : (2 ^ (n + 1) : ℂ) = (2 ^ n : ℂ) * 2 := by
    ring
  rw [hpow]
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  field_simp

/-! ## 4. Transitive Morphisms Across Arbitrary Stage Jumps -/

/-- The transitive matrix stage morphism `Stage m →⋆ₐ[ℂ] Stage n` for `m ≤ n`. -/
def stageMorphism (m n : ℕ) (h : m ≤ n) : Stage m →⋆ₐ[ℂ] Stage n :=
  Nat.leRecOn h
    (fun {k} ih => (bondStarAlgHom k).comp ih)
    (StarAlgHom.id ℂ (Stage m))

@[simp] theorem stageMorphism_id (m : ℕ) :
    stageMorphism m m (le_refl m) = StarAlgHom.id ℂ (Stage m) := by
  dsimp [stageMorphism]
  exact Nat.leRecOn_self (C := fun k => Stage m →⋆ₐ[ℂ] Stage k)
    (StarAlgHom.id ℂ (Stage m))

theorem stageMorphism_step {m n : ℕ} (hmn : m ≤ n) :
    stageMorphism m (n + 1) (Nat.le.step hmn) = (bondStarAlgHom n).comp (stageMorphism m n hmn) := by
  dsimp [stageMorphism]
  exact Nat.leRecOn_succ (C := fun k => Stage m →⋆ₐ[ℂ] Stage k)
    hmn (StarAlgHom.id ℂ (Stage m))

theorem stageMorphism_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (stageMorphism j k hjk).comp (stageMorphism i j hij) = stageMorphism i k (le_trans hij hjk) := by
  induction hjk with
  | refl =>
      rw [stageMorphism_id]
      simp
  | step hjm ih =>
      rw [stageMorphism_step hjm, stageMorphism_step (le_trans hij hjm),
          StarAlgHom.comp_assoc, ih]

/-- Transitive stage morphisms are strictly injective. -/
theorem stageMorphism_injective (m n : ℕ) (h : m ≤ n) :
    Function.Injective (stageMorphism m n h) := by
  induction h with
  | refl =>
      rw [stageMorphism_id]
      exact Function.injective_id
  | step hmn ih =>
      rw [stageMorphism_step hmn]
      exact (bondStarAlgHom_injective _).comp ih

/-- Normalized trace is strictly invariant under arbitrary multi-stage jumps. -/
theorem normalizedTrace_stageMorphism {m n : ℕ} (h : m ≤ n) (M : Stage m) :
    normalizedTrace n (stageMorphism m n h M) = normalizedTrace m M := by
  induction h with
  | refl =>
      simp [stageMorphism_id]
  | step hjm ih =>
      rw [stageMorphism_step hjm]
      change normalizedTrace (_ + 1) (bondFun _ (stageMorphism m _ hjm M)) = normalizedTrace m M
      rw [normalizedTrace_bond, ih]

/-- Identity preservation under stage morphisms. -/
theorem stageMorphism_one {m n : ℕ} (h : m ≤ n) :
    stageMorphism m n h 1 = 1 :=
  map_one (stageMorphism m n h)

/-- Star preservation under stage morphisms. -/
theorem stageMorphism_star {m n : ℕ} (h : m ≤ n) (M : Stage m) :
    stageMorphism m n h (star M) = star (stageMorphism m n h M) :=
  map_star (stageMorphism m n h) M

/-- Multiplication preservation under stage morphisms. -/
theorem stageMorphism_mul {m n : ℕ} (h : m ≤ n) (A B : Stage m) :
    stageMorphism m n h (A * B) = stageMorphism m n h A * stageMorphism m n h B :=
  map_mul (stageMorphism m n h) A B

end

end InfoGeometry.Canonical.GenuineMatrixStageMorphism
