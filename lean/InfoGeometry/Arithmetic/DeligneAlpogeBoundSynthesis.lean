/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore

/-!
# InfoGeometry.Arithmetic.DeligneAlpogeBoundSynthesis

Companion synthesis module extending `InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore`
to cover the remaining non-SGA-4 algebraic, fiber-pushforward, and Poincaré-duality
ingredients of `hexagon:2611.00789v1`:

1. **Section 1 (`stdBilinDot`, `stdBilinDot_right_nondegenerate`,
   `coordinate_dot_chain_transfer_bound`)**:
   Concrete right-nondegenerate bilinear form `∑ i, x i * y i` on `Fin d → E` over
   any commutative ring / field `E`, and the corresponding finite-coordinate path
   transfer estimate without an abstract nondegeneracy premise.
2. **Section 2 (`pathTailVec_eq_pinned_tuple_sum`, `pathCharSum_eq_sum_pathTailVec`)**:
   Definitional `Fin.cases` equivalence factoring the flat `r + 1`-variable path
   character sum into `ψ c * ∑ x₀, pathTailVec ψ h r t b x₀`.
3. **Section 3 (Section 7 Fiber-Pushed Hypersurface Remainder)**:
   - `addChar_zero_indicator`: multiplicative orthogonality indicator over `E`.
   - `sum_siteWeightProd_const`, `siteWeightProd_mul_psi_linear`,
     `sum_fiber_siteWeightProd`, `fiberSiteWeight`: fiber-pushforward absorption of
     single-site terms `g i (u i)` into unit-modulus phases `ψ (h * g i x)`.
   - `hypersurface_remainder_sqrt_bound`: bounds
     `‖|E| * N_hyp - M_tot^(r + 1)‖` by `(|E| - 1) * sqrt ((Bfib * W)^(2r + 2) * |A|^(r + 2))`.
4. **Section 4 (`poincare_duality_purity_eq`)**:
   Combines the upper Deligne bound `‖α‖ ≤ q ^ ((w + i) / 2)` with the Poincaré-dual
   bound `‖β‖ ≤ q ^ ((-w + (2d - i)) / 2)` under `‖α * β‖ = q ^ d` to deduce purity
   `‖α‖ = q ^ ((w + i) / 2)`.
-/

noncomputable section
open scoped BigOperators

namespace InfoGeometry.Arithmetic.DeligneAlpogeBoundSynthesis

open InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore

/-! ### Section 1: Concrete Non-Degenerate Bilinear Coupling (`stdBilinDot`) -/

/-- Standard coordinate bilinear form `∑ i, x i * y i` on `Fin d → E`. -/
def stdBilinDot (E : Type*) [CommRing E] (d : ℕ) :
    (Fin d → E) →ₗ[E] (Fin d → E) →ₗ[E] E where
  toFun x :=
    { toFun := fun y => ∑ i : Fin d, x i * y i
      map_add' := fun _ _ => by simp_rw [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  map_add' _ _ := by
    ext y; simp_rw [Pi.add_apply, add_mul, Finset.sum_add_distrib]; rfl
  map_smul' c x := LinearMap.ext fun y => by
    change (∑ i : Fin d, (c * x i) * y i) = c * ∑ i : Fin d, x i * y i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

theorem stdBilinDot_right_nondegenerate {E : Type*} [CommRing E] (d : ℕ)
    (y : Fin d → E) (hy : ∀ x : Fin d → E, stdBilinDot E d x y = 0) : y = 0 := by
  ext i
  simpa [stdBilinDot] using hy (fun j => if j = i then 1 else 0)

/-- The transfer estimate for the concrete coordinate pairing on a finite vector space.

This removes the abstract nondegeneracy input from the path estimate: each bond is the
standard dot product on `Fin d → E`, and its right radical is proved trivial above. -/
theorem coordinate_dot_chain_transfer_bound
    {E : Type*} [Field E] [Fintype E]
    (ψ : E → ℂ) (hψ0 : ψ 0 = 1)
    (hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hψ_ne : ∃ u : E, ψ u ≠ 1) {h : E} (hh : h ≠ 0) (c : E)
    (d r : ℕ) (t : Fin (r + 1) → (Fin d → E) → ℂ)
    {T : ℝ} (ht : ∀ i x, ‖t i x‖ ≤ T) :
    (∑ x : Fin d → E,
      ‖pathTailVec ψ h r t (fun _ => stdBilinDot E d) x‖ ^ 2 ≤
        T ^ (2 * r + 2) * (Fintype.card (Fin d → E) : ℝ) ^ (r + 1)) ∧
    ‖ψ c * ∑ x : Fin d → E,
      pathTailVec ψ h r t (fun _ => stdBilinDot E d) x‖ ^ 2 ≤
        T ^ (2 * r + 2) * (Fintype.card (Fin d → E) : ℝ) ^ (r + 2) := by
  classical
  exact chained_bilinear_transfer_l2_and_sum_bound ψ hψ0 hψ_add hψ_ne hh c r t
    (fun _ => stdBilinDot E d)
    (fun _ y hy => stdBilinDot_right_nondegenerate d y hy) ht

/-! ### Section 2: Tuple-to-MPO Factorization (`pathCharSum = ψ(c) ∑ pathTailVec`) -/

@[instance_reducible]
def finZeroArrowUnique (X : Type*) : Unique (Fin 0 → X) where
  default := Fin.elim0
  uniq _ := funext fun i => Fin.elim0 i

def finSuccArrowEquiv (X : Type*) (n : ℕ) :
    (X × (Fin n → X)) ≃ (Fin (n + 1) → X) where
  toFun p := Fin.cases p.1 p.2
  invFun v := (v 0, fun i => v i.succ)
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv _ := funext fun i => Fin.cases rfl (fun _ => rfl) i

def siteWeightProd {X : Type*} :
    (r : ℕ) → (Fin (r + 1) → X → ℂ) → (Fin (r + 1) → X) → ℂ
  | 0, t, u => t 0 (u 0)
  | m + 1, t, u => t 0 (u 0) * siteWeightProd m (fun i => t i.succ) (fun i => u i.succ)

def siteLinearSum {E X : Type*} [AddCommGroup E] :
    (r : ℕ) → (Fin (r + 1) → X → E) → (Fin (r + 1) → X) → E
  | 0, g, u => g 0 (u 0)
  | m + 1, g, u => g 0 (u 0) + siteLinearSum m (fun i => g i.succ) (fun i => u i.succ)

def chainCoupling {E A : Type*} [CommRing E] [AddCommGroup A] [Module E A] :
    (r : ℕ) → (Fin r → A →ₗ[E] A →ₗ[E] E) → (Fin (r + 1) → A) → E
  | 0, _, _ => 0
  | m + 1, b, u => b 0 (u 0) (u 1) + chainCoupling m (fun i => b i.succ) (fun i => u i.succ)

theorem pathTailVec_eq_pinned_tuple_sum {E A : Type*} [Field E]
    [AddCommGroup A] [Module E A] [Fintype A]
    (ψ : E → ℂ) (hψ0 : ψ 0 = 1) (hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (h : E) (r : ℕ) (t : Fin (r + 1) → A → ℂ) (b : Fin r → A →ₗ[E] A →ₗ[E] E) (x₀ : A) :
    pathTailVec ψ h r t b x₀ =
      ∑ tail : Fin r → A,
        siteWeightProd r t (Fin.cases x₀ tail) *
          ψ (h * chainCoupling r b (Fin.cases x₀ tail)) := by
  induction r generalizing x₀ with
  | zero =>
    let _ : Unique (Fin 0 → A) := finZeroArrowUnique A
    simp [pathTailVec, siteWeightProd, chainCoupling, Finset.univ_unique, hψ0]
  | succ m ih =>
    dsimp [pathTailVec]
    rw [← Fintype.sum_equiv (finSuccArrowEquiv A m) _ _ fun _ => rfl,
      Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ih (fun i => t i.succ) (fun i => b i.succ) y, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun rest _ => ?_
    dsimp [finSuccArrowEquiv, siteWeightProd, chainCoupling]
    have h1 : Fin.cases x₀ (fun i => Fin.cases y rest i) 1 = y := rfl
    rw [h1, mul_add, hψ_add]; ring

theorem pathCharSum_eq_sum_pathTailVec {E A : Type*} [Field E]
    [AddCommGroup A] [Module E A] [Fintype A]
    (ψ : E → ℂ) (hψ0 : ψ 0 = 1) (hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (h c : E) (r : ℕ) (t : Fin (r + 1) → A → ℂ) (b : Fin r → A →ₗ[E] A →ₗ[E] E) :
    (∑ u : Fin (r + 1) → A,
        siteWeightProd r t u * ψ (c + h * chainCoupling r b u)) =
      ψ c * ∑ x₀ : A, pathTailVec ψ h r t b x₀ := by
  rw [← Fintype.sum_equiv (finSuccArrowEquiv A r) _ _ fun _ => rfl,
    Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x₀ _ => ?_
  rw [pathTailVec_eq_pinned_tuple_sum ψ hψ0 hψ_add h r t b x₀, Finset.mul_sum]
  refine Finset.sum_congr rfl fun tail _ => ?_
  dsimp [finSuccArrowEquiv]
  rw [hψ_add]; ring

/-! ### Section 3: Section 7 Fiber-Pushed Hypersurface Remainder `q N - M^k = R` -/

theorem addChar_zero_indicator {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    (ψ : E → ℂ) (hψ0 : ψ 0 = 1) (hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hψ_ne : ∃ u : E, ψ u ≠ 1) (v : E) :
    (∑ h : E, ψ (h * v)) = if v = 0 then (Fintype.card E : ℂ) else 0 := by
  split_ifs with hv
  · subst hv; simp [hψ0]
  · obtain ⟨u₀, hu₀⟩ := hψ_ne
    have hshift : (∑ h : E, ψ (h * v)) = ψ u₀ * ∑ h : E, ψ (h * v) := by
      calc (∑ h : E, ψ (h * v))
          = ∑ h : E, ψ ((u₀ / v + h) * v) :=
              (Fintype.sum_equiv (Equiv.addLeft (u₀ / v)) _ _ fun _ => rfl).symm
        _ = ∑ h : E, ψ u₀ * ψ (h * v) := by
              refine Finset.sum_congr rfl fun h _ => ?_
              rw [add_mul, div_mul_cancel₀ u₀ hv, hψ_add]
        _ = ψ u₀ * ∑ h : E, ψ (h * v) := (Finset.mul_sum _ _ _).symm
    have hzero : (1 - ψ u₀) * ∑ h : E, ψ (h * v) = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hu₀.symm)

theorem sum_siteWeightProd_const {U : Type*} [Fintype U] (τ : U → ℂ) (r : ℕ) :
    (∑ u : Fin (r + 1) → U, siteWeightProd r (fun _ => τ) u) =
      (∑ x : U, τ x) ^ (r + 1) := by
  induction r with
  | zero =>
    let _ : Unique (Fin 0 → U) := finZeroArrowUnique U
    rw [← Fintype.sum_equiv (finSuccArrowEquiv U 0) _ _ fun _ => rfl,
      Fintype.sum_prod_type]
    simp [finSuccArrowEquiv, siteWeightProd, Finset.univ_unique]
  | succ m ih =>
    rw [← Fintype.sum_equiv (finSuccArrowEquiv U (m + 1)) _ _ fun _ => rfl,
      Fintype.sum_prod_type]
    dsimp [finSuccArrowEquiv, siteWeightProd]
    have hpull : (∑ x₀ : U, ∑ tail : Fin (m + 1) → U,
        τ x₀ * siteWeightProd m (fun _ => τ) tail) =
        (∑ x₀ : U, τ x₀) * ∑ tail : Fin (m + 1) → U, siteWeightProd m (fun _ => τ) tail := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x₀ _ => (Finset.mul_sum _ _ _).symm
    rw [hpull, ih]; ring

theorem siteWeightProd_mul_psi_linear {E U : Type*} [Field E]
    (ψ : E → ℂ) (hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (h : E) (τ : U → ℂ) (r : ℕ) (g : Fin (r + 1) → U → E) (u : Fin (r + 1) → U) :
    siteWeightProd r (fun _ => τ) u * ψ (h * siteLinearSum r g u) =
      siteWeightProd r (fun i x => τ x * ψ (h * g i x)) u := by
  induction r with
  | zero => rfl
  | succ m ih =>
    dsimp [siteWeightProd, siteLinearSum]
    rw [mul_add, hψ_add, ← ih (fun i => g i.succ) (fun i => u i.succ)]
    ring

theorem sum_fiber_siteWeightProd {U A : Type*} [Fintype U] [DecidableEq A]
    (π : U → A) (r : ℕ) (w : Fin (r + 1) → U → ℂ) (a : Fin (r + 1) → A) :
    (∑ u : Fin (r + 1) → U,
        if (fun i => π (u i)) = a then siteWeightProd r w u else 0) =
      siteWeightProd r (fun i b => ∑ x : U, if π x = b then w i x else 0) a := by
  induction r with
  | zero =>
    let _ : Unique (Fin 0 → U) := finZeroArrowUnique U
    rw [← Fintype.sum_equiv (finSuccArrowEquiv U 0) _ _ fun _ => rfl,
      Fintype.sum_prod_type]
    simp only [finSuccArrowEquiv, siteWeightProd, Finset.univ_unique, Finset.sum_singleton]
    refine Finset.sum_congr rfl fun x₀ _ => ?_
    have hiff : ((fun i : Fin 1 => π (Fin.cases x₀ default i)) = a) ↔ π x₀ = a 0 :=
      ⟨fun h => congrFun h 0, fun h => funext fun i => by simpa [Fin.eq_zero i] using h⟩
    simp [hiff]
  | succ m ih =>
    rw [← Fintype.sum_equiv (finSuccArrowEquiv U (m + 1)) _ _ fun _ => rfl,
      Fintype.sum_prod_type]
    dsimp [finSuccArrowEquiv, siteWeightProd]
    have hiff : ∀ (x₀ : U) (tail : Fin (m + 1) → U),
        ((fun i : Fin (m + 2) => π (Fin.cases x₀ tail i)) = a) ↔
          (π x₀ = a 0 ∧ (fun i : Fin (m + 1) => π (tail i)) = fun i => a i.succ) := by
      intro x₀ tail
      refine ⟨fun h => ⟨congrFun h 0, funext fun i => congrFun h i.succ⟩,
        fun ⟨h0, ht⟩ => funext fun i => Fin.cases h0 (congrFun ht) i⟩
    simp_rw [hiff, ite_and]
    have hpull : (∑ x₀ : U, ∑ tail : Fin (m + 1) → U,
        if π x₀ = a 0 then
          if (fun i => π (tail i)) = fun i => a i.succ then
            w 0 x₀ * siteWeightProd m (fun i => w i.succ) tail
          else 0
        else 0) =
        (∑ x₀ : U, if π x₀ = a 0 then w 0 x₀ else 0) *
          ∑ tail : Fin (m + 1) → U,
            if (fun i => π (tail i)) = fun i => a i.succ then
              siteWeightProd m (fun i => w i.succ) tail
            else 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x₀ _ => ?_
      split_ifs
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun tail _ => ?_
        split_ifs <;> ring
      · simp
    rw [hpull, ih (fun i => w i.succ) (fun i => a i.succ)]

/-- Fiber-pushed diagonal MPO site weight `t_{h, i}(a) = ∑_{π(u)=a} τ(u) ψ(h g_i(u))`. -/
def fiberSiteWeight {E U A : Type*} [Field E] [Fintype U] [DecidableEq A]
    (ψ : E → ℂ) (h : E) (π : U → A) (τ : U → ℂ)
    (r : ℕ) (g : Fin (r + 1) → U → E) (i : Fin (r + 1)) (a : A) : ℂ :=
  ∑ u : U, if π u = a then τ u * ψ (h * g i u) else 0

/-- Section 7 Complete `q N - M^k = R` Square-Root Bound: for any finite variety point-set
`U` projecting to `A` with fiber cardinality `≤ Bfib` and stalk trace `‖τ u‖ ≤ W`, the
chained hypersurface remainder `|E| * N_hyp - M_tot^(r + 1)` is bounded by
`(|E| - 1) * ((Bfib * W)^(r + 1) * |A|^((r + 2) / 2))`. -/
theorem hypersurface_remainder_sqrt_bound
    {E U A : Type*} [Field E] [Fintype E] [DecidableEq E]
    [Fintype U] [AddCommGroup A] [Module E A] [Fintype A] [DecidableEq A]
    (ψ : E → ℂ) (hψ0 : ψ 0 = 1) (hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hψ_ne : ∃ u : E, ψ u ≠ 1)
    (π : U → A) (τ : U → ℂ) (r : ℕ) (g : Fin (r + 1) → U → E)
    (b : Fin r → A →ₗ[E] A →ₗ[E] E)
    (hb : ∀ i : Fin r, ∀ y : A, (∀ x : A, b i x y = 0) → y = 0) (c : E)
    {Bfib W : ℝ} (hW : 0 ≤ W)
    (hfib : ∀ a : A, ((Finset.univ.filter fun u : U => π u = a).card : ℝ) ≤ Bfib)
    (hτ : ∀ u : U, ‖τ u‖ ≤ W) :
    let hypPoly := fun u : Fin (r + 1) → U =>
      c + siteLinearSum r g u + chainCoupling r b (fun i => π (u i))
    let Nhyp : ℂ := ∑ u : Fin (r + 1) → U,
      if hypPoly u = 0 then siteWeightProd r (fun _ => τ) u else 0
    let Mtot : ℂ := ∑ x : U, τ x
    ‖(Fintype.card E : ℂ) * Nhyp - Mtot ^ (r + 1)‖ ≤
      ((Fintype.card E - 1 : ℕ) : ℝ) *
        Real.sqrt ((Bfib * W) ^ (2 * r + 2) * (Fintype.card A : ℝ) ^ (r + 2)) := by
  intro hypPoly Nhyp Mtot
  have hident : (Fintype.card E : ℂ) * Nhyp - Mtot ^ (r + 1) =
      ∑ h ∈ (Finset.univ : Finset E).erase 0,
        ψ (h * c) * ∑ a₀ : A, pathTailVec ψ h r (fiberSiteWeight ψ h π τ r g) b a₀ := by
    have hN : (Fintype.card E : ℂ) * Nhyp =
        ∑ h : E, ∑ u : Fin (r + 1) → U,
          siteWeightProd r (fun _ => τ) u * ψ (h * hypPoly u) := by
      dsimp [Nhyp]
      rw [Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.mul_sum, addChar_zero_indicator ψ hψ0 hψ_add hψ_ne (hypPoly u)]
      split_ifs <;> ring
    rw [hN, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : E))]
    have h0 : (∑ u : Fin (r + 1) → U, siteWeightProd r (fun _ => τ) u * ψ (0 * hypPoly u)) =
        Mtot ^ (r + 1) := by
      simp only [zero_mul, hψ0, mul_one]; exact sum_siteWeightProd_const τ r
    rw [h0, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← pathCharSum_eq_sum_pathTailVec ψ hψ0 hψ_add h (h * c) r
      (fiberSiteWeight ψ h π τ r g) b]
    trans ∑ a : Fin (r + 1) → A, ∑ u : Fin (r + 1) → U,
      if (fun i => π (u i)) = a then
        siteWeightProd r (fun i x => τ x * ψ (h * g i x)) u *
          ψ (h * c + h * chainCoupling r b a)
      else 0
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hone : (∑ a : Fin (r + 1) → A,
          if (fun i => π (u i)) = a then
            siteWeightProd r (fun i x => τ x * ψ (h * g i x)) u *
              ψ (h * c + h * chainCoupling r b a)
          else 0) =
          siteWeightProd r (fun i x => τ x * ψ (h * g i x)) u *
            ψ (h * c + h * chainCoupling r b (fun i => π (u i))) := by simp
      rw [hone, ← siteWeightProd_mul_psi_linear ψ hψ_add h τ r g u]
      dsimp [hypPoly]
      have hlin : h * (c + siteLinearSum r g u + chainCoupling r b (fun i => π (u i))) =
          h * siteLinearSum r g u + (h * c + h * chainCoupling r b (fun i => π (u i))) := by
        ring
      rw [hlin, hψ_add]; ring
    · refine Finset.sum_congr rfl fun a _ => ?_
      have hpull : (∑ u : Fin (r + 1) → U,
          if (fun i => π (u i)) = a then
            siteWeightProd r (fun i x => τ x * ψ (h * g i x)) u *
              ψ (h * c + h * chainCoupling r b a)
          else 0) =
          (∑ u : Fin (r + 1) → U,
            if (fun i => π (u i)) = a then
              siteWeightProd r (fun i x => τ x * ψ (h * g i x)) u
            else 0) * ψ (h * c + h * chainCoupling r b a) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => by split_ifs <;> simp
      rw [hpull, sum_fiber_siteWeightProd π r _ a]; rfl
  rw [hident]
  let S_bound : ℝ :=
    Real.sqrt ((Bfib * W) ^ (2 * r + 2) * (Fintype.card A : ℝ) ^ (r + 2))
  have hterm : ∀ h ∈ (Finset.univ : Finset E).erase 0,
      ‖ψ (h * c) * ∑ a₀ : A, pathTailVec ψ h r (fiberSiteWeight ψ h π τ r g) b a₀‖ ≤
        S_bound := by
    intro h hh
    have hh0 : h ≠ 0 := Finset.ne_of_mem_erase hh
    have hfw : ∀ i a, ‖fiberSiteWeight ψ h π τ r g i a‖ ≤ Bfib * W := by
      intro i a
      dsimp [fiberSiteWeight]
      calc ‖∑ u : U, if π u = a then τ u * ψ (h * g i u) else 0‖
          ≤ ∑ u : U, ‖if π u = a then τ u * ψ (h * g i u) else 0‖ := norm_sum_le _ _
        _ ≤ ∑ u : U, if π u = a then W else 0 := Finset.sum_le_sum fun u _ => by
              split_ifs
              · rw [norm_mul, (addChar_norm_and_conj ψ hψ0 hψ_add _).1, mul_one]
                exact hτ u
              · simp
        _ = ((Finset.univ.filter fun u : U => π u = a).card : ℝ) * W := by
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ Bfib * W := mul_le_mul_of_nonneg_right (hfib a) hW
    have hsq := (chained_bilinear_transfer_l2_and_sum_bound ψ hψ0 hψ_add hψ_ne hh0
      (h * c) r (fiberSiteWeight ψ h π τ r g) b hb hfw).2
    exact Real.le_sqrt_of_sq_le hsq
  calc ‖∑ h ∈ (Finset.univ : Finset E).erase 0,
          ψ (h * c) * ∑ a₀ : A, pathTailVec ψ h r (fiberSiteWeight ψ h π τ r g) b a₀‖
      ≤ ∑ h ∈ (Finset.univ : Finset E).erase 0,
          ‖ψ (h * c) * ∑ a₀ : A, pathTailVec ψ h r (fiberSiteWeight ψ h π τ r g) b a₀‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _ ∈ (Finset.univ : Finset E).erase 0, S_bound :=
          Finset.sum_le_sum hterm
    _ = ((Fintype.card E - 1 : ℕ) : ℝ) * S_bound := by
          simp [Finset.card_erase_of_mem (Finset.mem_univ (0 : E)), nsmul_eq_mul]

/-! ### Section 4: Theorem 1(b) Poincaré-Duality Purity (`‖α‖ = q^((w + i) / 2)`) -/

/-- Theorem 1(b) Purity Deduction: combining the upper Deligne bound `‖α‖ ≤ q^((w + i)/2)`
with the dual sheaf bound `‖β‖ ≤ q^((-w + (2d - i))/2)` under Poincaré duality
`‖α * β‖ = q ^ d` forces exact Riemann Hypothesis purity `‖α‖ = q ^ ((w + i) / 2)`. -/
theorem poincare_duality_purity_eq {α β : ℂ} {q w i d : ℝ} (hq : 0 < q)
    (hpair : ‖α * β‖ = q ^ d)
    (hupper : ‖α‖ ≤ q ^ ((w + i) / 2))
    (hdual : ‖β‖ ≤ q ^ ((-w + (2 * d - i)) / 2)) :
    ‖α‖ = q ^ ((w + i) / 2) := by
  refine le_antisymm hupper ?_
  have hd_pos : 0 < q ^ (d - (w + i) / 2) := Real.rpow_pos_of_pos hq _
  have hexp : (-w + (2 * d - i)) / 2 = d - (w + i) / 2 := by ring
  rw [hexp] at hdual
  have hprod : q ^ d ≤ ‖α‖ * q ^ (d - (w + i) / 2) := by
    calc q ^ d = ‖α * β‖ := hpair.symm
      _ = ‖α‖ * ‖β‖ := norm_mul α β
      _ ≤ ‖α‖ * q ^ (d - (w + i) / 2) :=
          mul_le_mul_of_nonneg_left hdual (norm_nonneg α)
  have hsplit : q ^ d = q ^ ((w + i) / 2) * q ^ (d - (w + i) / 2) := by
    rw [← Real.rpow_add hq]; congr 1; ring
  rw [hsplit] at hprod
  exact le_of_mul_le_mul_right hprod hd_pos

end InfoGeometry.Arithmetic.DeligneAlpogeBoundSynthesis
