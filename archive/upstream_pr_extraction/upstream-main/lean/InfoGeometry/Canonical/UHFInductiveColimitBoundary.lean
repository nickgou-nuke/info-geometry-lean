import Mathlib.Tactic
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# UHF Inductive Colimit Boundary

This module formalizes the diagonal-MASA/cylinder colimit structure of the
UHF algebra:
1. **Binary Words as Finite Prefixes:** `BitWord n = Fin n → Bool`.
2. **Successor Embedding:** `diagEmbedSucc n : DiagAlg n → DiagAlg (n + 1)`.
3. **Cylinder Functions on Cantor Space:** `cylinder n f : (ℕ → Bool) → ℂ`.
4. **Normalized Trace Functional:**
   $$\tau_n(f) = \frac{1}{2^n} \sum_{w \in \operatorname{BitWord}(n)} f(w)$$
5. **Colimit Trace Invariance:**
   $$\tau_{n+1}(\operatorname{diagEmbedSucc}_n(f)) = \tau_n(f)$$
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFInductiveColimitBoundary

open Finset

/-- Binary words of length `n`. -/
abbrev BitWord (n : ℕ) : Type :=
  Fin n → Bool

/-- Diagonal finite-dimensional algebra at stage `n`. -/
abbrev DiagAlg (n : ℕ) : Type :=
  BitWord n → ℂ

/-- Prefix a word of length `n + 1` down to length `n`. -/
def prefixSucc (n : ℕ) (w : BitWord (n + 1)) : BitWord n :=
  fun i => w ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩

/-- Diagonal successor embedding: duplicate over the newly added bit. -/
def diagEmbedSucc (n : ℕ) : DiagAlg n → DiagAlg (n + 1) :=
  fun f w => f (prefixSucc n w)

theorem diagEmbedSucc_apply (n : ℕ) (f : DiagAlg n) (w : BitWord (n + 1)) :
    diagEmbedSucc n f w = f (prefixSucc n w) := rfl

theorem diagEmbedSucc_add (n : ℕ) (f g : DiagAlg n) :
    diagEmbedSucc n (f + g) = diagEmbedSucc n f + diagEmbedSucc n g := by
  ext w
  rfl

theorem diagEmbedSucc_mul (n : ℕ) (f g : DiagAlg n) :
    diagEmbedSucc n (f * g) = diagEmbedSucc n f * diagEmbedSucc n g := by
  ext w
  rfl

theorem diagEmbedSucc_one (n : ℕ) :
    diagEmbedSucc n 1 = (1 : DiagAlg (n + 1)) := by
  ext w
  rfl

theorem diagEmbedSucc_zero (n : ℕ) :
    diagEmbedSucc n 0 = (0 : DiagAlg (n + 1)) := by
  ext w
  rfl

/-- The diagonal successor embedding as a linear map over `ℂ`. -/
def diagEmbedSuccLinear (n : ℕ) : DiagAlg n →ₗ[ℂ] DiagAlg (n + 1) :=
  { toFun := diagEmbedSucc n
    map_add' := diagEmbedSucc_add n
    map_smul' := by
      intro c f
      ext w
      rfl }

/-- Extend a word by one bit. -/
def extendSucc (n : ℕ) (w : BitWord n) (b : Bool) : BitWord (n + 1) :=
  fun i => if h : i.1 < n then w ⟨i.1, h⟩ else b

theorem prefixSucc_extendSucc (n : ℕ) (w : BitWord n) (b : Bool) :
    prefixSucc n (extendSucc n w b) = w := by
  ext i
  simp [prefixSucc, extendSucc, i.2]

/-- Prefix extension is injective in both its finite word and its new bit. -/
theorem extendSucc_injective {n : ℕ} :
    Function.Injective (fun p : BitWord n × Bool => extendSucc n p.1 p.2) := by
  rintro ⟨u, b⟩ ⟨v, c⟩ h
  apply Prod.ext
  · exact (prefixSucc_extendSucc n u b).symm.trans
      ((congrArg (prefixSucc n) h).trans (prefixSucc_extendSucc n v c))
  · have hl := congrFun h ⟨n, Nat.lt_succ_self n⟩
    simpa [extendSucc] using hl

/-- The diagonal successor embedding is injective. -/
theorem diagEmbedSucc_injective (n : ℕ) :
    Function.Injective (diagEmbedSucc n) := by
  intro f g hfg
  ext w
  have happ := congrFun hfg (extendSucc n w false)
  simpa [diagEmbedSucc_apply, prefixSucc_extendSucc] using happ

/-- Restrict a boundary point to its first `n` bits. -/
def boundaryPrefix (n : ℕ) (b : (ℕ → Bool)) : BitWord n :=
  fun i => b i.1

theorem boundaryPrefix_surjective (n : ℕ) :
    Function.Surjective (boundaryPrefix n) := by
  intro w
  let b : ℕ → Bool := fun i => if h : i < n then w ⟨i, h⟩ else false
  refine ⟨b, ?_⟩
  ext i
  simp [boundaryPrefix, b]

/-- Finite-cylinder realization of a stage-`n` diagonal observable. -/
def cylinder (n : ℕ) (f : DiagAlg n) : (ℕ → Bool) → ℂ :=
  fun b => f (boundaryPrefix n b)

theorem cylinder_apply (n : ℕ) (f : DiagAlg n) (b : (ℕ → Bool)) :
    cylinder n f b = f (boundaryPrefix n b) := rfl

theorem cylinder_injective (n : ℕ) :
    Function.Injective (cylinder n) := by
  intro f g hfg
  apply funext
  intro w
  obtain ⟨b, hb⟩ := boundaryPrefix_surjective n w
  have hpoint := congrFun hfg b
  simpa [cylinder, hb] using hpoint

theorem boundaryPrefix_succ_eq_prefixSucc (n : ℕ) (b : (ℕ → Bool)) :
    prefixSucc n (boundaryPrefix (n + 1) b) = boundaryPrefix n b := by
  ext i
  rfl

/-- A successor boundary prefix is the old prefix together with its next bit. -/
theorem boundaryPrefix_succ_eq_extendSucc (n : ℕ) (b : (ℕ → Bool)) :
    boundaryPrefix (n + 1) b = extendSucc n (boundaryPrefix n b) (b n) := by
  ext i
  by_cases hi : i.1 < n
  · simp [boundaryPrefix, extendSucc, hi]
  · have hi' : i.1 = n := by omega
    have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi'
    subst i
    simp [boundaryPrefix, extendSucc]

/-- Cylinder maps are compatible with the diagonal successor embeddings. -/
theorem cylinder_compatible_succ (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f := by
  ext b
  simp [cylinder, diagEmbedSucc, boundaryPrefix_succ_eq_prefixSucc]

theorem cylinder_add (n : ℕ) (f g : DiagAlg n) :
    cylinder n (f + g) = cylinder n f + cylinder n g := by
  ext b
  rfl

theorem cylinder_mul (n : ℕ) (f g : DiagAlg n) :
    cylinder n (f * g) = cylinder n f * cylinder n g := by
  ext b
  rfl

/-- The finite-stage cylinder realization as a linear map over `ℂ`. -/
def cylinderLinear (n : ℕ) : DiagAlg n →ₗ[ℂ] ((ℕ → Bool) → ℂ) :=
  { toFun := cylinder n
    map_add' := cylinder_add n
    map_smul' := by
      intro c f
      ext b
      rfl }

/-- Concrete compatibility of the finite diagonal tower with its boundary cone. -/
theorem cylinderLinear_compatible_succ (n : ℕ) :
    (cylinderLinear (n + 1)).comp (diagEmbedSuccLinear n) = cylinderLinear n := by
  apply LinearMap.ext
  intro f
  funext b
  exact congrFun (cylinder_compatible_succ n f) b

/-- Every finite diagonal observable has the same boundary realization at every
finite stage obtained by iterating the successor embedding. -/
theorem cylinderLinear_comp_iota_seq (n m : ℕ) :
    (cylinderLinear (n + m)).comp
        (_root_.iota_seq DiagAlg diagEmbedSuccLinear n m) =
      cylinderLinear n := by
  exact _root_.psi_comp_iota_seq
    DiagAlg diagEmbedSuccLinear ((ℕ → Bool) → ℂ) cylinderLinear
    cylinderLinear_compatible_succ n m

theorem cylinder_one (n : ℕ) :
    cylinder n 1 = (1 : (ℕ → Bool) → ℂ) := by
  ext b
  rfl

/-- Finite-cylinder functions: the concrete algebraic diagonal colimit carrier. -/
def CylinderColimit : Set ((ℕ → Bool) → ℂ) :=
  Set.range (fun p : Sigma DiagAlg => cylinder p.1 p.2)

theorem cylinder_mem_colimit (n : ℕ) (f : DiagAlg n) :
    cylinder n f ∈ CylinderColimit := by
  exact ⟨⟨n, f⟩, rfl⟩

theorem embedded_cylinder_mem_colimit (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) ∈ CylinderColimit := by
  exact cylinder_mem_colimit (n + 1) (diagEmbedSucc n f)

theorem embedded_cylinder_same_point (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f := by
  exact cylinder_compatible_succ n f

/-- Constant diagonal observable at a finite stage. -/
def constantStageObservable (n : ℕ) (z : ℂ) : DiagAlg n :=
  fun _ => z

theorem constantStageObservable_embed (n : ℕ) (z : ℂ) :
    diagEmbedSucc n (constantStageObservable n z) =
      constantStageObservable (n + 1) z := by
  ext w
  rfl

theorem constant_cylinder_compatible (n : ℕ) (z : ℂ) :
    cylinder (n + 1) (diagEmbedSucc n (constantStageObservable n z)) =
      cylinder n (constantStageObservable n z) := by
  exact cylinder_compatible_succ n (constantStageObservable n z)

/-! ## 2. Colimit Normalized Trace Functional -/

/-- Normalized trace functional on the stage-`n` diagonal algebra. -/
def stageTrace (n : ℕ) (f : DiagAlg n) : ℂ :=
  (1 / (2 ^ n : ℂ)) * ∑ w : BitWord n, f w

/-- Trace of the unit element is 1. -/
theorem stageTrace_one (n : ℕ) :
    stageTrace n 1 = 1 := by
  dsimp [stageTrace]
  have h_card : Fintype.card (BitWord n) = 2 ^ n := by
    dsimp [BitWord]
    simp
  have h_sum : ∑ w : BitWord n, (1 : ℂ) = (2 ^ n : ℂ) := by
    rw [sum_const, nsmul_eq_mul]
    simp [h_card]
  rw [h_sum]
  have h_two_pow_ne : (2 ^ n : ℂ) ≠ 0 := by
    exact pow_ne_zero n (by norm_num)
  exact one_div_mul_cancel h_two_pow_ne

/-- Additivity of the trace functional. -/
theorem stageTrace_add (n : ℕ) (f g : DiagAlg n) :
    stageTrace n (f + g) = stageTrace n f + stageTrace n g := by
  dsimp [stageTrace]
  rw [← mul_add]
  congr 1
  exact sum_add_distrib

/-- Scalar homogeneity of the trace functional. -/
theorem stageTrace_smul (n : ℕ) (c : ℂ) (f : DiagAlg n) :
    stageTrace n (c • f) = c * stageTrace n f := by
  dsimp [stageTrace]
  rw [← mul_sum]
  ring

/-- Extract the last bit of a word of length `n + 1`. -/
def lastBit (n : ℕ) (w : BitWord (n + 1)) : Bool :=
  w ⟨n, Nat.lt_succ_self n⟩

/-- Word decomposition bijection into prefix and last bit. -/
def bitWordSuccEquiv (n : ℕ) : BitWord (n + 1) ≃ (BitWord n × Bool) where
  toFun w := (prefixSucc n w, lastBit n w)
  invFun p := extendSucc n p.1 p.2
  left_inv w := by
    ext ⟨i, hi⟩
    dsimp [extendSucc, prefixSucc, lastBit]
    by_cases h : i < n
    · simp [h]
    · have hi_eq : i = n := by omega
      subst hi_eq
      simp
  right_inv := by
    rintro ⟨w, b⟩
    ext x
    · dsimp
      have h := prefixSucc_extendSucc n w b
      rw [h]
    · dsimp [lastBit, extendSucc]
      simp

/-- 🏆 THEOREM: The normalized trace is invariant under the diagonal successor embedding. -/
theorem stageTrace_compatible_succ (n : ℕ) (f : DiagAlg n) :
    stageTrace (n + 1) (diagEmbedSucc n f) = stageTrace n f := by
  dsimp [stageTrace]
  have h_sum_succ : (∑ w : BitWord (n + 1), diagEmbedSucc n f w) = 2 * (∑ w : BitWord n, f w) := by
    have h_equiv := (bitWordSuccEquiv n).symm.sum_comp (diagEmbedSucc n f)
    rw [← h_equiv]
    rw [Fintype.sum_prod_type]
    have h_bool : ∀ w : BitWord n, (∑ b : Bool, diagEmbedSucc n f ((bitWordSuccEquiv n).symm (w, b))) = 2 * f w := by
      intro w
      dsimp [diagEmbedSucc, bitWordSuccEquiv]
      have h_pref : ∀ b : Bool, prefixSucc n (extendSucc n w b) = w := fun b => prefixSucc_extendSucc n w b
      simp [h_pref]
    simp_rw [h_bool]
    rw [← mul_sum]
  rw [h_sum_succ]
  have h_pow : (2 ^ (n + 1) : ℂ) = 2 * (2 ^ n : ℂ) := by
    rw [pow_succ]
    ring
  rw [h_pow]
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  have h_two_pow_ne : (2 ^ n : ℂ) ≠ 0 := pow_ne_zero n (by norm_num)
  have h_prod_ne : (2 : ℂ) * (2 ^ n : ℂ) ≠ 0 := mul_ne_zero h_two_ne h_two_pow_ne
  field_simp [h_prod_ne, h_two_pow_ne]

end InfoGeometry.Canonical.UHFInductiveColimitBoundary
