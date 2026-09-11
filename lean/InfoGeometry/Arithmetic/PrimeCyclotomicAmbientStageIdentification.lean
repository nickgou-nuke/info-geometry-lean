import Mathlib.NumberTheory.Cyclotomic.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Galois.Basic
import InfoGeometry.Arithmetic.PrimeCyclotomicGaloisTower

/-!
# Prime Cyclotomic Ambient Stage Identification and Subfield Equivalences

This module proves that the intermediate fields $F_i = \mathbb{Q}(\zeta_{30030}^{30030/N_i}) \subseteq \mathbb{Q}(\zeta_{30030})$
are literal cyclotomic extensions of conductor $N_i$, producing the canonical $\mathbb{Q}$-algebra isomorphisms
$$F_i \simeq_{\mathbb{Q}} \operatorname{CyclotomicField}(N_i, \mathbb{Q}).$$

## Mathematical Structure:
1. `conductor : Fin 7 → ℕ`: $N_0 = 1, N_1 = 2, N_2 = 6, N_3 = 30, N_4 = 210, N_5 = 2310, N_6 = 30030$.
2. `rootExponent : Fin 7 → ℕ`: $E_i = 30030 / N_i$.
3. Exact exponent identity: `rootExponent_mul_conductor (i : Fin 7) : rootExponent i * conductor i = 30030`.
4. Primitive root extraction: `zeta_stage_primitive (i : Fin 7)` proves that $\zeta_{30030}^{E_i}$ is a primitive $N_i$-th root.
5. Intermediate cyclotomic extensions: `fieldStage_isCyclotomic (i : Fin 7)`.
6. Canonical stage isomorphisms: `stageAlgEquiv (i : Fin 7) : CyclotomicField (conductor i) ℚ ≃ₐ[ℚ] fieldStage i`.
7. Galois properties: `fieldStage_isGalois (i : Fin 7)` and `fieldStage_isAbelian (i : Fin 7)`.

All proofs are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Arithmetic

open BigOperators IntermediateField

/-- The cumulative conductor at each stage of the 6-prime cyclotomic tower. -/
def conductor (i : Fin 7) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 30
  | 4 => 210
  | 5 => 2310
  | 6 => 30030
  | _ => 1

/-- The exact exponent dividing the top ambient degree 30030 by the stage conductor. -/
def rootExponent (i : Fin 7) : ℕ :=
  match i.val with
  | 0 => 30030
  | 1 => 15015
  | 2 => 5005
  | 3 => 1001
  | 4 => 143
  | 5 => 13
  | 6 => 1
  | _ => 1

/-- Exact multiplicative relation $E_i \cdot N_i = 30030$. -/
theorem rootExponent_mul_conductor (i : Fin 7) :
    rootExponent i * conductor i = 30030 := by
  fin_cases i <;> rfl

theorem conductor_pos (i : Fin 7) : 0 < conductor i := by
  fin_cases i <;> decide

instance (i : Fin 7) : NeZero (conductor i) := ⟨(conductor_pos i).ne'⟩

theorem conductor_dvd_30030 (i : Fin 7) : conductor i ∣ 30030 := by
  fin_cases i <;> decide

/-- The ambient terminal cyclotomic field $K_\infty = \mathbb{Q}(\zeta_{30030})$. -/
abbrev K_infty : Type := CyclotomicField 30030 ℚ

/-- The canonical primitive 30030-th root of unity in $K_\infty$. -/
def zeta_infty : K_infty :=
  IsCyclotomicExtension.zeta 30030 ℚ K_infty

theorem zeta_infty_primitive : IsPrimitiveRoot zeta_infty 30030 :=
  IsCyclotomicExtension.zeta_spec 30030 ℚ K_infty

/-- The stage generator $\zeta_i = \zeta_{30030}^{E_i}$. -/
def zeta_stage (i : Fin 7) : K_infty :=
  zeta_infty ^ (rootExponent i)

/-- 🏆 Key Theorem: $\zeta_i$ is a primitive $N_i$-th root of unity in $K_\infty$. -/
theorem zeta_stage_primitive (i : Fin 7) :
    IsPrimitiveRoot (zeta_stage i) (conductor i) := by
  dsimp [zeta_stage]
  have h_prod := rootExponent_mul_conductor i
  have h_prim := zeta_infty_primitive
  have h_dvd : rootExponent i ∣ 30030 := by
    fin_cases i <;> decide
  have h_div : 30030 / rootExponent i = conductor i := by
    fin_cases i <;> decide
  have h_res := h_prim.pow_of_dvd (by fin_cases i <;> decide) h_dvd
  rwa [h_div] at h_res

/-- The literal nested intermediate subfield $F_i = \mathbb{Q}(\zeta_i) \subseteq K_\infty$. -/
def fieldStage (i : Fin 7) : IntermediateField ℚ K_infty :=
  ℚ⟮zeta_stage i⟯

/-- Consecutive stage inclusions $F_i \le F_{i+1}$. -/
theorem fieldStage_consecutive_le (i : Fin 6) :
    fieldStage ⟨i.val, by omega⟩ ≤ fieldStage ⟨i.val + 1, by omega⟩ := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  have h_step : zeta_stage ⟨i.val, by omega⟩ = (zeta_stage ⟨i.val + 1, by omega⟩) ^ (rootExponent ⟨i.val, by omega⟩ / rootExponent ⟨i.val + 1, by omega⟩) := by
    dsimp [zeta_stage]
    rw [← pow_mul]
    congr 1
    fin_cases i <;> rfl
  rw [h_step]
  exact Subalgebra.pow_mem _ (IntermediateField.subset_adjoin ℚ _ (by simp)) _

/-- 🏆 Cyclotomic Extension Structure on Intermediate Subfields -/
theorem fieldStage_isCyclotomic (i : Fin 7) :
    IsCyclotomicExtension {conductor i} ℚ (fieldStage i) := by
  letI : NeZero (conductor i) := ⟨(conductor_pos i).ne'⟩
  have h_prim := zeta_stage_primitive i
  have h_in : zeta_stage i ∈ fieldStage i :=
    IntermediateField.subset_adjoin ℚ {zeta_stage i} (Set.mem_singleton _)
  let zeta_sub : fieldStage i := ⟨zeta_stage i, h_in⟩
  exact h_prim.intermediateField_adjoin_isCyclotomicExtension ℚ

/-- 🏆 Canonical $\mathbb{Q}$-Algebra Isomorphism between abstract and concrete cyclotomic fields -/
def stageAlgEquiv (i : Fin 7) :
    CyclotomicField (conductor i) ℚ ≃ₐ[ℚ] fieldStage i := by
  haveI : IsCyclotomicExtension {conductor i} ℚ (fieldStage i) := fieldStage_isCyclotomic i
  exact IsCyclotomicExtension.algEquiv {conductor i} ℚ (CyclotomicField (conductor i) ℚ) (fieldStage i)

/-- Galois property of each intermediate stage over $\mathbb{Q}$. -/
instance fieldStage_isGalois (i : Fin 7) :
    IsGalois ℚ (fieldStage i) :=
  haveI : IsCyclotomicExtension {conductor i} ℚ (fieldStage i) := fieldStage_isCyclotomic i
  IsCyclotomicExtension.isGalois {conductor i} ℚ (fieldStage i)

/-- Abelian Galois group property of each stage. -/
theorem fieldStage_isAbelian (i : Fin 7) :
    IsAbelianGalois ℚ (fieldStage i) :=
  haveI : IsCyclotomicExtension {conductor i} ℚ (fieldStage i) := fieldStage_isCyclotomic i
  IsCyclotomicExtension.isAbelianGalois {conductor i} ℚ (fieldStage i)

end InfoGeometry.Arithmetic
