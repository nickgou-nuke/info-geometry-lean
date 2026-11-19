/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.ExteriorRegressive
import InfoGeometry.Projective.ExteriorBladeIncidence
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorPower.BilinForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Grassmann (1862) Editorial & Supplementary Notes: Regressive Duality, Normal Shadows, & Inertia

Formalizes core theorems and countermodels from Hermann Grassmann's *Extension Theory* (1862),
Engel–Grassmann Editorial Notes, and Seligman's Supplementary Notes
(`hmath019-endmatter.pdf`), reusing `ExteriorRegressive` and `ExteriorBladeIncidence` without
modifying frozen owners:

1. **Graded Supercommutativity (`No. 92`, Notes 20–24, pp. 335–336)**:
   `x ∈ ⋀[R]^p M, y ∈ ⋀[R]^q M → x * y = ((-1 : R) ^ (p * q)) • (y * x)`, plus centrality of
   every 2-form `Ω ∈ ⋀[R]^2 M` across the full `ExteriorAlgebra R M`.
2. **Homogeneous Hodge Square Involution (`ExteriorRegressive` open follow-up)**:
   `hodge b (hodge b x) = ((-1 : K) ^ (k * (n - k))) • x` for every `x ∈ ⋀[K]^k V`.
3. **Poincaré Contraction Duality & `GL(V)` Determinant Covariance (`Note 29`, `Seligman Ch. 3`)**:
   Basis-free `dualContractionAlgHom : ExteriorAlgebra K (Module.Dual K V) →ₐ[K] (End K (Λ V))ᵐᵒᵖ`,
   exact identification `poincareEval b (b.dualBasis.ExteriorAlgebra s) = hodge b (b.ExteriorAlgebra s)`,
   `regressive b x y = poincareEquiv b ((poincareEquiv b).symm x * (poincareEquiv b).symm y)`, and
   exact change-of-basis law `(b.det b') • regressive b' x y = regressive b x y` (`SL_n` invariance).
4. **Codimension-1 Decomposability vs. Dimension-4 Compound Bivector (`Note 19`, `Note 89`)**:
   Every `(n - 1)`-vector in an `n`-dimensional space (`n ≥ 2`) is decomposable via hyperplane
   `LinearMap.ker d`, whereas `e₀ ∧ e₁ + e₂ ∧ e₃` in 4D has `bladeSupport = ⊥` and is
   non-decomposable over every field.
5. **Grassmann No. 103, Note 31 Common-Factor Meet Law, & Explicit `n = 5` Counterexample**:
   Graded Leibniz contraction yields `hodge b (Z * ι (b i)) = contractLeft (b.dualBasis i) (hodge b Z)`,
   from which `regressive b (A * B) (A * C) = A * regressive b (A * B) C` holds for every
   decomposable blade `A` and arbitrary multivectors `B, C`, specializing to Grassmann No. 103
   `regressive b (A * B) (A * C) = volCoord b (A * B * C) • A` when `α + β + γ = n`; together with
   Engel's exact 5D counterexample (`Note 31, p. 342`) refuting `[AC · BC] = [C · ABC]`.
6. **Blade Inner Pairing, Universal Adjointness, Normal Shadow Reciprocity (`Note 68`), Open-Expression
   Polarization (`Note 105`), & Seligman's Inertia Critique of No. 391(c) (`p. 397`)**.
-/

noncomputable section

namespace InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow

open InfoGeometry.Projective.ExteriorRegressive
open InfoGeometry.Projective.ExteriorBladeIncidence
open scoped Matrix

/-! ## 1. Graded Supercommutativity (`No. 92`) & Homogeneous Hodge Square -/

section GradedAndHodgeSquare

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem units_neg_one_pow_smul (k : ℕ) (z : ExteriorAlgebra R M) :
    ((-1 : ℤˣ) ^ k) • z = ((-1 : R) ^ k) • z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_smul, Units.neg_smul, one_smul, smul_neg, ih, pow_succ', neg_one_mul,
      neg_smul]

/-- Multiplying on the left by `ι R m` commutes past `⋀[R]^q M` with sign `(-1)^q`. -/
theorem ι_mul_exteriorPower_comm (m : M) {q : ℕ} {y : ExteriorAlgebra R M}
    (hy : y ∈ ⋀[R]^q M) :
    ExteriorAlgebra.ι R m * y = ((-1 : R) ^ q) • (y * ExteriorAlgebra.ι R m) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R q] at hy
  induction hy using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨v, rfl⟩ := hu
    rw [ExteriorAlgebra.ι_mul_ιMulti_anticomm, units_neg_one_pow_smul]
  | zero => simp
  | add x y _ _ ihx ihy => rw [mul_add, add_mul, smul_add, ihx, ihy]
  | smul r x _ ih => rw [mul_smul_comm, smul_mul_assoc, ih, smul_comm]

/-- Homogeneous elements of exterior powers supercommute:
`x ∈ ⋀[R]^p M, y ∈ ⋀[R]^q M → x * y = (-1)^(p*q) • (y * x)`. -/
theorem exteriorPower_mul_comm {p q : ℕ} {x y : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^p M) (hy : y ∈ ⋀[R]^q M) :
    x * y = ((-1 : R) ^ (p * q)) • (y * x) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R p] at hx
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R q] at hy
  refine Submodule.span_induction₂
    (p := fun a b _ _ => a * b = ((-1 : R) ^ (p * q)) • (b * a))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
    rw [ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm, mul_comm q p, units_neg_one_pow_smul]
  · intro b _; simp
  · intro a _; simp
  · intro a₁ a₂ b _ _ _ ih₁ ih₂
    rw [add_mul, mul_add, smul_add, ih₁, ih₂]
  · intro a b₁ b₂ _ _ _ ih₁ ih₂
    rw [mul_add, add_mul, smul_add, ih₁, ih₂]
  · intro r a b _ _ ih
    rw [smul_mul_assoc, mul_smul_comm, ih, smul_comm]
  · intro r a b _ _ ih
    rw [mul_smul_comm, smul_mul_assoc, ih, smul_comm]

/-- Every homogeneous 2-form `Ω ∈ ⋀[R]^2 M` lies in the center of `ExteriorAlgebra R M`. -/
theorem exteriorPower_two_mul_comm {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^2 M)
    (z : ExteriorAlgebra R M) : x * z = z * x := by
  induction z using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[R]^i M) with
  | zero => simp
  | add a b ha hb => rw [mul_add, add_mul, ha, hb]
  | homogeneous z =>
    obtain ⟨i, hi⟩ : ∃ i, (z : ExteriorAlgebra R M) ∈ ⋀[R]^i M := ⟨_, z.2⟩
    have hcomm := exteriorPower_mul_comm hx hi
    have hpow : (-1 : R) ^ (2 * i) = 1 := by
      rw [pow_mul]
      norm_num
    simpa [hpow] using hcomm

/-- `ExteriorAlgebra.map f` preserves exterior power degrees. -/
theorem map_mem_exteriorPower {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) {k : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^k M) :
    ExteriorAlgebra.map f x ∈ ⋀[R]^k N := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R k] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨v, rfl⟩ := hu
    rw [ExteriorAlgebra.map_apply_ιMulti]
    exact ExteriorAlgebra.ιMulti_range R k ⟨f ∘ v, rfl⟩
  | zero => simp
  | add a b _ _ ih₁ ih₂ =>
    rw [map_add]
    exact Submodule.add_mem _ ih₁ ih₂
  | smul r a _ ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ r ih

end GradedAndHodgeSquare

section HodgeSquareField

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {n : ℕ} (b : Module.Basis (Fin n) K V)

theorem basis_mem_exteriorPower (s : Finset (Fin n)) :
    b.ExteriorAlgebra s ∈ ⋀[K]^s.card V := by
  let s' : Set.powersetCard (Fin n) s.card := Set.powersetCard.ofCard rfl
  have hmem : b.ExteriorAlgebra (s' : Finset (Fin n)) ∈ ⋀[K]^s.card V := by
    rw [ExteriorAlgebra.basis_eq_coe_basis]
    exact (b.exteriorPower s.card s').2
  simpa [s'] using hmem

/-- Exact complement orientation relation: `orientationUnit s * orientationUnit sᶜ = (-1)^(|s|*(n-|s|))`. -/
theorem orientationUnit_mul_compl (s : Finset (Fin n)) :
    (orientationUnit (K := K) s : K) * (orientationUnit (K := K) sᶜ : K) =
      (-1 : K) ^ (s.card * (n - s.card)) := by
  let b0 := Pi.basisFun K (Fin n)
  have hmem_s : b0.ExteriorAlgebra s ∈ ⋀[K]^s.card (Fin n → K) := basis_mem_exteriorPower b0 s
  have hcard_c : sᶜ.card = n - s.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hmem_sc : b0.ExteriorAlgebra sᶜ ∈ ⋀[K]^(n - s.card) (Fin n → K) := by
    rw [← hcard_c]
    exact basis_mem_exteriorPower b0 sᶜ
  have hcomm := exteriorPower_mul_comm hmem_s hmem_sc
  have h1 : b0.ExteriorAlgebra s * b0.ExteriorAlgebra sᶜ =
      (orientationUnit (K := K) s : K) • volume b0 := basis_mul_compl b0 s
  have h2 : b0.ExteriorAlgebra sᶜ * b0.ExteriorAlgebra s =
      (orientationUnit (K := K) sᶜ : K) • volume b0 := by
    simpa [compl_compl] using basis_mul_compl b0 sᶜ
  rw [h1, h2, smul_smul] at hcomm
  have hcoef : (orientationUnit (K := K) s : K) =
      (-1 : K) ^ (s.card * (n - s.card)) * (orientationUnit (K := K) sᶜ : K) :=
    smul_left_injective K (volume_ne_zero b0) hcomm
  calc
    (orientationUnit (K := K) s : K) * (orientationUnit (K := K) sᶜ : K)
        = ((-1 : K) ^ (s.card * (n - s.card)) * (orientationUnit (K := K) sᶜ : K)) *
            (orientationUnit (K := K) sᶜ : K) := by rw [hcoef]
    _ = (-1 : K) ^ (s.card * (n - s.card)) *
          ((orientationUnit (K := K) sᶜ : K) * (orientationUnit (K := K) sᶜ : K)) := by
      rw [mul_assoc]
    _ = (-1 : K) ^ (s.card * (n - s.card)) := by
      rw [orientationUnit_mul_self, mul_one]

/-- Basis formula for double Hodge star: `hodge b (hodge b e_s) = (-1)^(|s|*(n-|s|)) • e_s`. -/
@[simp] theorem hodge_hodge_basis (s : Finset (Fin n)) :
    hodge b (hodge b (b.ExteriorAlgebra s)) =
      ((-1 : K) ^ (s.card * (n - s.card))) • b.ExteriorAlgebra s := by
  rw [hodge_basis, map_smul, hodge_basis, compl_compl, smul_smul,
    orientationUnit_mul_compl (K := K) s]

/-- **Double Hodge Square Theorem** (closes the explicit open follow-up of `ExteriorRegressive`):
for every homogeneous `k`-vector `x ∈ ⋀[K]^k V`, `★(★x) = (-1)^(k(n-k)) x`. -/
theorem hodge_hodge_exteriorPower {k : ℕ} {x : ExteriorAlgebra K V} (hx : x ∈ ⋀[K]^k V) :
    hodge b (hodge b x) = ((-1 : K) ^ (k * (n - k))) • x := by
  let x' : ⋀[K]^k V := ⟨x, hx⟩
  have hsum : x = ∑ s : Set.powersetCard (Fin n) k,
      (b.exteriorPower k).repr x' s • b.ExteriorAlgebra s.val := by
    have hval := congrArg Subtype.val ((b.exteriorPower k).sum_repr x').symm
    change x = ((Submodule.subtype (⋀[K]^k V)) _) at hval
    rw [map_sum] at hval
    refine hval.trans (Finset.sum_congr rfl fun s _ => ?_)
    rw [map_smul, Submodule.coe_subtype, ← ExteriorAlgebra.basis_eq_coe_basis b s]
  rw [hsum]
  simp only [map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hcard : (s : Finset (Fin n)).card = k := s.2
  rw [hodge_hodge_basis b (s : Finset (Fin n)), hcard, smul_comm]

/-- Left inverse Hodge equals signed Hodge on homogeneous `k`-vectors. -/
theorem hodge_symm_exteriorPower {k : ℕ} {x : ExteriorAlgebra K V} (hx : x ∈ ⋀[K]^k V) :
    (hodge b).symm x = ((-1 : K) ^ (k * (n - k))) • hodge b x := by
  apply (hodge b).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, hodge_hodge_exteriorPower b hx, smul_smul,
    ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- Hodge preserves exterior degree complementarity: `x ∈ ⋀[K]^k V → hodge b x ∈ ⋀[K]^(n - k) V`. -/
theorem hodge_mem_exteriorPower {k : ℕ} {x : ExteriorAlgebra K V} (hx : x ∈ ⋀[K]^k V) :
    hodge b x ∈ ⋀[K]^(n - k) V := by
  let x' : ⋀[K]^k V := ⟨x, hx⟩
  have hsum : x = ∑ s : Set.powersetCard (Fin n) k,
      (b.exteriorPower k).repr x' s • b.ExteriorAlgebra s.val := by
    have hval := congrArg Subtype.val ((b.exteriorPower k).sum_repr x').symm
    change x = ((Submodule.subtype (⋀[K]^k V)) _) at hval
    rw [map_sum] at hval
    refine hval.trans (Finset.sum_congr rfl fun s _ => ?_)
    rw [map_smul, Submodule.coe_subtype, ← ExteriorAlgebra.basis_eq_coe_basis b s]
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [map_smul, hodge_basis]
  refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
  have hc : (s : Finset (Fin n))ᶜ.card = n - k := by
    rw [Finset.card_compl, Fintype.card_fin, s.2]
  rw [← hc]
  exact basis_mem_exteriorPower b (s : Finset (Fin n))ᶜ

/-- `(hodge b).symm` also maps `⋀[K]^k V` into `⋀[K]^(n - k) V`. -/
theorem hodge_symm_mem_exteriorPower {k : ℕ} {x : ExteriorAlgebra K V} (hx : x ∈ ⋀[K]^k V) :
    (hodge b).symm x ∈ ⋀[K]^(n - k) V := by
  rw [hodge_symm_exteriorPower b hx]
  exact Submodule.smul_mem _ _ (hodge_mem_exteriorPower b hx)

/-- In ambient dimension `n`, every exterior power of degree `k > n` vanishes identically. -/
theorem exteriorPower_eq_zero_of_gt (b : Module.Basis (Fin n) K V) {k : ℕ} (hk : n < k)
    {x : ExteriorAlgebra K V} (hx : x ∈ ⋀[K]^k V) : x = 0 := by
  have hempty : ∀ s : Set.powersetCard (Fin n) k, False := fun s =>
    Nat.not_lt_of_ge (by simpa [s.2] using s.1.card_le_univ) hk
  let x' : ⋀[K]^k V := ⟨x, hx⟩
  have hval := congrArg Subtype.val ((b.exteriorPower k).sum_repr x').symm
  change x = ((Submodule.subtype (⋀[K]^k V)) _) at hval
  rw [map_sum] at hval
  rw [hval]
  exact Finset.sum_eq_zero fun s _ => (hempty s).elim

end HodgeSquareField

/-! ## 2. Basis-Free Poincaré Contraction Duality & `GL(V)` Regressive Covariance -/

section PoincareContraction

/-- Basis-free contraction action of dual multivectors `Λ(V^*)` on `Λ(V)` via opposite multiplication:
`(dualContractionAlgHom (α * β)).unop z = (dualContractionAlgHom β).unop ((dualContractionAlgHom α).unop z)`. -/
def dualContractionAlgHom {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    ExteriorAlgebra R (Module.Dual R M) →ₐ[R] (Module.End R (ExteriorAlgebra R M))ᵐᵒᵖ :=
  ExteriorAlgebra.lift R
    ⟨{ toFun := fun d => MulOpposite.op (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d)
       map_add' := fun d₁ d₂ => by
         change MulOpposite.op _ = MulOpposite.op _ + MulOpposite.op _
         rw [map_add, MulOpposite.op_add]
       map_smul' := fun r d => by
         change MulOpposite.op _ = r • MulOpposite.op _
         rw [map_smul, MulOpposite.op_smul] },
     fun d => by
       apply MulOpposite.unop_injective
       change (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d) *
           (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d) = 0
       apply LinearMap.ext
       intro x
       exact CliffordAlgebra.contractLeft_contractLeft d x⟩

@[simp] theorem dualContractionAlgHom_ι {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (d : Module.Dual R M) :
    (dualContractionAlgHom (R := R) (M := M) (ExteriorAlgebra.ι R d)).unop =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d := by
  simp [dualContractionAlgHom]

theorem dualContractionAlgHom_mul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (α β : ExteriorAlgebra R (Module.Dual R M)) (z : ExteriorAlgebra R M) :
    (dualContractionAlgHom (α * β)).unop z =
      (dualContractionAlgHom β).unop ((dualContractionAlgHom α).unop z) := by
  rw [map_mul, MulOpposite.unop_mul]
  rfl

/-- Evaluation map `α ↦ α ⌋ volume b` sending dual multivectors to `Λ V`. -/
def poincareEval {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) :
    ExteriorAlgebra K (Module.Dual K V) →ₗ[K] ExteriorAlgebra K V where
  toFun α := (dualContractionAlgHom α).unop (volume b)
  map_add' α β := by simp [map_add]
  map_smul' c α := by simp [map_smul]

private theorem contractLeft_ιMulti_mul_eq_zero {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (d : Module.Dual R M) {k : ℕ} (v : Fin k → M) (hv : ∀ i, d (v i) = 0)
    (tail : ExteriorAlgebra R M)
    (htail : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d tail = 0) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d
        (ExteriorAlgebra.ιMulti R k v * tail) = 0 := by
  induction k with
  | zero => simpa using htail
  | succ k ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc, CliffordAlgebra.contractLeft_ι_mul,
      hv 0, zero_smul, zero_sub, ih (Matrix.vecTail v) (fun i => hv i.succ),
      mul_zero, neg_zero]

private theorem contractLeft_basis_of_notMem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x : Fin n) (t : Finset (Fin n)) (hx : x ∉ t) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis x)
        (b.ExteriorAlgebra t) = 0 := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl]
  let f := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := t) rfl)
  have heq : ExteriorAlgebra.ιMulti_family K t.card b (Set.powersetCard.ofCard (s := t) rfl) =
      ExteriorAlgebra.ιMulti K t.card (fun i => b (f i)) * 1 := by
    rw [mul_one]
    rfl
  rw [heq]
  have hv : ∀ i, b.dualBasis x (b (f i)) = 0 := fun i => by
    have hmem : f i ∈ t :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
        (Set.powersetCard.ofCard (s := t) rfl) (f i)).1 ⟨i, rfl⟩
    have hne : f i ≠ x := fun h => hx (h ▸ hmem)
    rw [b.dualBasis_apply_self, ite_eq_right hne]
  exact contractLeft_ιMulti_mul_eq_zero (b.dualBasis x) (fun i => b (f i)) hv 1
    (CliffordAlgebra.contractLeft_one (Q := (0 : QuadraticForm K V)) _)

private theorem dualContraction_peel_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) {k : ℕ} (f : Fin k → Fin n) (hf : Function.Injective f)
    (t : Finset (Fin n)) (ht : ∀ i, f i ∉ t) :
    (dualContractionAlgHom
        (ExteriorAlgebra.ιMulti K k (fun i => b.dualBasis (f i)))).unop
        (ExteriorAlgebra.ιMulti K k (fun i => b (f i)) * b.ExteriorAlgebra t) =
      b.ExteriorAlgebra t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      dualContractionAlgHom_mul, dualContractionAlgHom_ι, mul_assoc]
    have htail : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis (f 0))
        (ExteriorAlgebra.ιMulti K k (fun i => b (f i.succ)) * b.ExteriorAlgebra t) = 0 := by
      refine contractLeft_ιMulti_mul_eq_zero _ _ (fun i => ?_) _
        (contractLeft_basis_of_notMem b (f 0) t (ht 0))
      have hne : f i.succ ≠ f 0 := fun h => Fin.succ_ne_zero i (hf h)
      rw [b.dualBasis_apply_self, ite_eq_right hne]
    have htail' : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis (f 0))
        (ExteriorAlgebra.ιMulti K k (Matrix.vecTail (fun i => b (f i))) * b.ExteriorAlgebra t) = 0 :=
      htail
    rw [CliffordAlgebra.contractLeft_ι_mul, b.dualBasis_apply_self, ite_eq_left rfl, one_smul,
      htail', mul_zero, sub_zero]
    exact ih (Matrix.vecTail f) (fun i j hij => Fin.succ_inj.mp (hf hij)) (fun i => ht i.succ)

/-- **Fundamental Poincaré–Hodge Equivalence**: contracting the volume blade by
`b.dualBasis.ExteriorAlgebra s` equals `hodge b (b.ExteriorAlgebra s)` for every subset `s`. -/
theorem poincareEval_dualBasis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (s : Finset (Fin n)) :
    poincareEval b (b.dualBasis.ExteriorAlgebra s) = hodge b (b.ExteriorAlgebra s) := by
  have hvol : volume b =
      (orientationUnit (K := K) s : K) • (b.ExteriorAlgebra s * b.ExteriorAlgebra sᶜ) := by
    rw [basis_mul_compl b s, smul_smul, orientationUnit_mul_self, one_smul]
  dsimp [poincareEval]
  rw [hvol, map_smul, hodge_basis]
  congr 1
  rw [ExteriorAlgebra.basis_apply_ofCard b.dualBasis rfl, ExteriorAlgebra.basis_apply_ofCard b rfl]
  let f := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl)
  have hf : Function.Injective f := f.injective
  have ht : ∀ i, f i ∉ sᶜ := fun i => by
    have hmem : f i ∈ s :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
        (Set.powersetCard.ofCard (s := s) rfl) (f i)).1 ⟨i, rfl⟩
    simp [hmem]
  exact dualContraction_peel_basis b f hf sᶜ ht

/-- Linear equivalence transferring `Λ(V)` to `Λ(V^*)` along `b.toDualEquiv`. -/
def dualTransferEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) :
    ExteriorAlgebra K V ≃ₗ[K] ExteriorAlgebra K (Module.Dual K V) where
  toLinearMap := (ExteriorAlgebra.map b.toDualEquiv.toLinearMap).toLinearMap
  invFun := ExteriorAlgebra.map b.toDualEquiv.symm.toLinearMap
  left_inv x := by
    change ExteriorAlgebra.map b.toDualEquiv.symm.toLinearMap
        (ExteriorAlgebra.map b.toDualEquiv.toLinearMap x) = x
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    have hc : b.toDualEquiv.symm.toLinearMap.comp b.toDualEquiv.toLinearMap = LinearMap.id := by
      ext v; simp
    rw [hc, ExteriorAlgebra.map_id, AlgHom.id_apply]
  right_inv α := by
    change ExteriorAlgebra.map b.toDualEquiv.toLinearMap
        (ExteriorAlgebra.map b.toDualEquiv.symm.toLinearMap α) = α
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    have hc : b.toDualEquiv.toLinearMap.comp b.toDualEquiv.symm.toLinearMap = LinearMap.id := by
      ext d; simp
    rw [hc, ExteriorAlgebra.map_id, AlgHom.id_apply]

theorem dualTransferEquiv_mul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x y : ExteriorAlgebra K V) :
    dualTransferEquiv b (x * y) = dualTransferEquiv b x * dualTransferEquiv b y :=
  map_mul (ExteriorAlgebra.map b.toDualEquiv.toLinearMap) x y

/-- `poincareEval b` composed with `dualTransferEquiv b` equals `hodge b`. -/
theorem poincareEval_comp_dualTransferEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) :
    (poincareEval b).comp (dualTransferEquiv b).toLinearMap = (hodge b).toLinearMap := by
  apply b.ExteriorAlgebra.ext
  intro s
  have hmap : dualTransferEquiv b (b.ExteriorAlgebra s) = b.dualBasis.ExteriorAlgebra s := by
    change ExteriorAlgebra.map b.toDualEquiv.toLinearMap (b.ExteriorAlgebra s) = _
    rw [ExteriorAlgebra.basis_apply, ExteriorAlgebra.basis_apply, ExteriorAlgebra.map_apply_ιMulti]
    rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hmap]
  exact poincareEval_dualBasis b s

/-- Explicit linear equivalence `Λ(V^*) ≃ₗ[K] Λ(V)` realized purely by `volume b` contraction. -/
def poincareEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) :
    ExteriorAlgebra K (Module.Dual K V) ≃ₗ[K] ExteriorAlgebra K V :=
  (dualTransferEquiv b).symm.trans (hodge b)

@[simp] theorem poincareEquiv_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (α : ExteriorAlgebra K (Module.Dual K V)) :
    poincareEquiv b α = poincareEval b α := by
  have hcomp := LinearMap.congr_fun (poincareEval_comp_dualTransferEquiv b)
    ((dualTransferEquiv b).symm α)
  simpa [poincareEquiv] using hcomp.symm

@[simp] theorem poincareEquiv_symm_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x : ExteriorAlgebra K V) :
    (poincareEquiv b).symm x = dualTransferEquiv b ((hodge b).symm x) := rfl

/-- Bilinear wrapper for `regressive b`, enabling clean basis extensions. -/
def regressiveBilin {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) :
    ExteriorAlgebra K V →ₗ[K] ExteriorAlgebra K V →ₗ[K] ExteriorAlgebra K V where
  toFun x :=
    { toFun := fun y => regressive b x y
      map_add' := fun a c => regressive_add b x a c
      map_smul' := fun r a => regressive_smul b r x a }
  map_add' a c := by
    apply LinearMap.ext; intro y
    exact add_regressive b a c y
  map_smul' r a := by
    apply LinearMap.ext; intro y
    exact smul_regressive b r a y

@[simp] theorem regressiveBilin_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x y : ExteriorAlgebra K V) :
    regressiveBilin b x y = regressive b x y := rfl

/-- Conjugating exterior product by `(hodge b).symm` equals `regressive b` identically across all grades. -/
theorem hodge_hodge_symm_mul_eq_regressive {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x y : ExteriorAlgebra K V) :
    hodge b ((hodge b).symm x * (hodge b).symm y) = regressive b x y := by
  have heq : ∀ u v : Finset (Fin n),
      hodge b ((hodge b).symm (b.ExteriorAlgebra u) * (hodge b).symm (b.ExteriorAlgebra v)) =
        regressive b (b.ExteriorAlgebra u) (b.ExteriorAlgebra v) := by
    intro u v
    have hu := hodge_symm_exteriorPower b (basis_mem_exteriorPower b u)
    have hv := hodge_symm_exteriorPower b (basis_mem_exteriorPower b v)
    rw [hu, hv, smul_mul_assoc, mul_smul_comm, map_smul, map_smul, smul_smul]
    have hprod_deg : hodge b (b.ExteriorAlgebra u) * hodge b (b.ExteriorAlgebra v) ∈
        ⋀[K]^(n - u.card + (n - v.card)) V := by
      rw [ExteriorAlgebra.exteriorPower, pow_add]
      exact Submodule.mul_mem_mul (hodge_mem_exteriorPower b (basis_mem_exteriorPower b u))
        (hodge_mem_exteriorPower b (basis_mem_exteriorPower b v))
    have hs : (hodge b).symm (hodge b (b.ExteriorAlgebra u) * hodge b (b.ExteriorAlgebra v)) =
        ((-1 : K) ^ ((n - u.card + (n - v.card)) * (n - (n - u.card + (n - v.card))))) •
          hodge b (hodge b (b.ExteriorAlgebra u) * hodge b (b.ExteriorAlgebra v)) :=
      hodge_symm_exteriorPower b hprod_deg
    change _ = (hodge b).symm (hodge b (b.ExteriorAlgebra u) * hodge b (b.ExteriorAlgebra v))
    rw [hs]
    by_cases hgt : n < n - u.card + (n - v.card)
    · have hz := exteriorPower_eq_zero_of_gt b hgt hprod_deg
      rw [hz, map_zero, smul_zero, smul_zero]
    · have hle : n - u.card + (n - v.card) ≤ n := Nat.le_of_not_lt hgt
      have hu_le : u.card ≤ n := by simpa using u.card_le_univ
      have hv_le : v.card ≤ n := by simpa using v.card_le_univ
      congr 1
      have hnat : u.card * (n - u.card) + v.card * (n - v.card) =
          (n - u.card + (n - v.card)) * (n - (n - u.card + (n - v.card))) +
            2 * ((n - u.card) * (n - v.card)) := by
        zify [hu_le, hv_le, hle]
        ring
      have hsq : (-1 : K) ^ (2 * ((n - u.card) * (n - v.card))) = 1 := by
        rw [pow_mul]
        norm_num
      rw [← pow_add, hnat, pow_add, hsq, mul_one]
  have hx_eq : ∀ u : Finset (Fin n),
      hodge b ((hodge b).symm (b.ExteriorAlgebra u) * (hodge b).symm y) =
        regressive b (b.ExteriorAlgebra u) y := fun u => by
    let F : ExteriorAlgebra K V →ₗ[K] ExteriorAlgebra K V :=
      (hodge b).toLinearMap.comp
        ((LinearMap.mulLeft K ((hodge b).symm (b.ExteriorAlgebra u))).comp (hodge b).symm.toLinearMap)
    have hFG : F = regressiveBilin b (b.ExteriorAlgebra u) := by
      apply b.ExteriorAlgebra.ext
      intro v
      exact heq u v
    exact LinearMap.congr_fun hFG y
  let F' : ExteriorAlgebra K V →ₗ[K] ExteriorAlgebra K V :=
    (hodge b).toLinearMap.comp
      ((LinearMap.mulRight K ((hodge b).symm y)).comp (hodge b).symm.toLinearMap)
  let G' : ExteriorAlgebra K V →ₗ[K] ExteriorAlgebra K V :=
    { toFun := fun z => regressive b z y
      map_add' := fun a c => add_regressive b a c y
      map_smul' := fun r a => smul_regressive b r a y }
  have hFG' : F' = G' := by
    apply b.ExteriorAlgebra.ext
    intro u
    exact hx_eq u
  exact LinearMap.congr_fun hFG' x

/-- Basis-free expression of the regressive product via Poincaré contraction equivalence:
`regressive b x y = poincareEquiv b ((poincareEquiv b).symm x * (poincareEquiv b).symm y)`. -/
theorem regressive_eq_poincareEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x y : ExteriorAlgebra K V) :
    regressive b x y = poincareEquiv b ((poincareEquiv b).symm x * (poincareEquiv b).symm y) := by
  rw [poincareEquiv_symm_apply, poincareEquiv_symm_apply, ← dualTransferEquiv_mul]
  change regressive b x y = hodge b ((dualTransferEquiv b).symm (dualTransferEquiv b _))
  rw [LinearEquiv.symm_apply_apply]
  exact (hodge_hodge_symm_mul_eq_regressive b x y).symm

/-- Volume scaling under change of basis: `volume b' = (b.det b') • volume b`. -/
theorem volume_change_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b b' : Module.Basis (Fin n) K V) :
    volume b' = (b.det b') • volume b := by
  have hmem : volume b' ∈ ⋀[K]^n V := by
    change b'.ExteriorAlgebra Finset.univ ∈ _
    simpa [Finset.card_fin] using basis_mem_exteriorPower b' (Finset.univ : Finset (Fin n))
  let volSub' : ⋀[K]^n V := ⟨volume b', hmem⟩
  let sUniv : Set.powersetCard (Fin n) n :=
    Set.powersetCard.ofCard (Finset.card_fin n : (Finset.univ : Finset (Fin n)).card = n)
  have huniq : ∀ s : Set.powersetCard (Fin n) n, s = sUniv := fun s =>
    Subtype.ext (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp))
  have hsum : volSub' = ((b.exteriorPower n).repr volSub' sUniv) • (b.exteriorPower n sUniv) := by
    have hr := ((b.exteriorPower n).sum_repr volSub').symm
    refine hr.trans (Finset.sum_eq_single sUniv (fun s _ hne => absurd (huniq s) hne)
      (fun h => absurd (Finset.mem_univ sUniv) h))
  have hcoe := congrArg Subtype.val hsum
  change volume b' = ((b.exteriorPower n).coord sUniv volSub') • (b.exteriorPower n sUniv : ExteriorAlgebra K V) at hcoe
  rw [← ExteriorAlgebra.basis_eq_coe_basis b sUniv] at hcoe
  change volume b' = ((b.exteriorPower n).coord sUniv volSub') • volume b at hcoe
  rw [hcoe]
  congr 1
  rw [exteriorPower.basis_coord]
  let f := Set.powersetCard.ofFinEmbEquiv.symm sUniv
  have hf_bij : Function.Bijective f := (Finite.injective_iff_bijective).1 f.injective
  let e : Fin n ≃ Fin n := Equiv.ofBijective f hf_bij
  have hvol_ι : (volSub' : ExteriorAlgebra K V) = ExteriorAlgebra.ιMulti K n (fun i => b' (e i)) := by
    change volume b' = _
    dsimp [volume]
    rw [ExteriorAlgebra.basis_apply_ofCard b' (Finset.card_fin n)]
    rfl
  have hsub_eq : volSub' = exteriorPower.ιMulti K n (fun i => b' (e i)) :=
    Subtype.ext hvol_ι
  rw [hsub_eq, exteriorPower.ιMultiDual_apply_ιMulti]
  have hmat : Matrix.of (fun i j => b.coord (f j) (b' (e i))) =
      ((b.toMatrix b')ᵀ).submatrix e e := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply, e]
  rw [hmat, Matrix.det_submatrix_equiv_self e ((b.toMatrix b')ᵀ), Matrix.det_transpose,
    Module.Basis.det_apply]

theorem poincareEval_change_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b b' : Module.Basis (Fin n) K V) (α : ExteriorAlgebra K (Module.Dual K V)) :
    poincareEval b' α = (b.det b') • poincareEval b α := by
  dsimp [poincareEval]
  rw [volume_change_basis b b', LinearMap.map_smul]

/-- **`GL(V)` Determinant Covariance of Grassmann's Regressive Product**:
for any two bases `b, b'`, `(b.det b') • regressive b' x y = regressive b x y` across all grades. -/
theorem det_smul_regressive_change_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b b' : Module.Basis (Fin n) K V) (x y : ExteriorAlgebra K V) :
    (b.det b') • regressive b' x y = regressive b x y := by
  have hdet : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  have hsymm : ∀ z : ExteriorAlgebra K V,
      (poincareEquiv b').symm z = (b.det b')⁻¹ • (poincareEquiv b).symm z := fun z => by
    apply (poincareEquiv b').injective
    rw [LinearEquiv.apply_symm_apply, map_smul, poincareEquiv_apply, poincareEval_change_basis b b',
      ← poincareEquiv_apply b, LinearEquiv.apply_symm_apply, smul_smul, inv_mul_cancel₀ hdet,
      one_smul]
  rw [regressive_eq_poincareEquiv b', hsymm x, hsymm y, smul_mul_assoc, mul_smul_comm, map_smul,
    map_smul, poincareEquiv_apply, poincareEval_change_basis b b', ← poincareEquiv_apply b,
    ← regressive_eq_poincareEquiv b, smul_smul, smul_smul, smul_smul]
  have hscalar : b.det b' * (b.det b')⁻¹ * (b.det b')⁻¹ * b.det b' = 1 := by
    field_simp [hdet]
  rw [hscalar, one_smul]

/-- Specialization to `SL(V)`: unimodular basis changes preserve `regressive` identically. -/
theorem regressive_eq_of_det_eq_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b b' : Module.Basis (Fin n) K V) (hdet : b.det b' = 1) (x y : ExteriorAlgebra K V) :
    regressive b' x y = regressive b x y := by
  simpa [hdet] using det_smul_regressive_change_basis b b' x y

end PoincareContraction

/-! ## 3. Codimension-1 Decomposability (`Note 19`) vs. 4D Compound Bivector (`Note 89`) -/

section DecomposabilityVsCompound

/-- **Editorial Note 19 (`p. 335`)**: In ambient dimension `n ≥ 2`, every homogeneous `(n - 1)`-vector
is elementary (decomposable as `ιMulti K (n - 1) w`). -/
theorem codim_one_decomposable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) K V)
    {ω : ExteriorAlgebra K V} (hω : ω ∈ ⋀[K]^(n - 1) V) :
    ∃ w : Fin (n - 1) → V, ExteriorAlgebra.ιMulti K (n - 1) w = ω := by
  have hn_pos : 0 < n - 1 := Nat.sub_pos_of_lt hn
  by_cases hzero : ω = 0
  · subst hzero
    refine ⟨0, (ExteriorAlgebra.ιMulti K (n - 1)).map_coord_zero ⟨0, hn_pos⟩ rfl⟩
  · have hsymm_mem : (hodge b).symm ω ∈ ⋀[K]^1 V := by
      have hdeg := hodge_symm_mem_exteriorPower b hω
      rwa [show n - (n - 1) = 1 by omega] at hdeg
    have hdual_mem : (poincareEquiv b).symm ω ∈ ⋀[K]^1 (Module.Dual K V) := by
      rw [poincareEquiv_symm_apply]
      exact map_mem_exteriorPower _ hsymm_mem
    have hrange : (poincareEquiv b).symm ω ∈ LinearMap.range (ExteriorAlgebra.ι K) := by
      simpa [ExteriorAlgebra.exteriorPower, pow_one] using hdual_mem
    obtain ⟨d, hd_eq⟩ := hrange
    have hω_eval : ω = CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) d (volume b) := by
      have h1 := congrArg (poincareEquiv b) hd_eq
      rw [LinearEquiv.apply_symm_apply, poincareEquiv_apply] at h1
      simpa [poincareEval, dualContractionAlgHom_ι] using h1.symm
    have hd_ne : d ≠ 0 := by
      intro hd0
      apply hzero
      simpa [hd0] using hω_eval
    have hex : ∃ v₀ : V, d v₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hd_ne (LinearMap.ext fun v => h v)
    obtain ⟨v₀, hv₀⟩ := hex
    let x₀ : V := (d v₀)⁻¹ • v₀
    have hx₀ : d x₀ = 1 := by simp [x₀, inv_mul_cancel₀ hv₀]
    let m := n - 1
    have hm : m + 1 = n := by omega
    have hm_pos : 0 < m := by omega
    have : Module.Finite K V := Module.Finite.of_basis b
    have hfinV : Module.finrank K V = n := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    have hrange_top : LinearMap.range d = ⊤ :=
      Submodule.eq_top_iff'.2 fun r => ⟨r • x₀, by simp [hx₀]⟩
    have hker_rank : Module.finrank K (LinearMap.ker d) = m := by
      have hrt := LinearMap.finrank_range_add_finrank_ker d
      rw [hrange_top, finrank_top, Module.finrank_self, hfinV] at hrt
      omega
    let u : Module.Basis (Fin m) K (LinearMap.ker d) :=
      Module.finBasisOfFinrankEq K (LinearMap.ker d) hker_rank
    let fam : Fin (m + 1) → V := Fin.cons x₀ (fun j => (u j : V))
    have hli_tail : LinearIndependent K (fun j : Fin m => (u j : V)) :=
      u.linearIndependent.map' (LinearMap.ker d).subtype (Submodule.ker_subtype (LinearMap.ker d))
    have hx₀_notMem : x₀ ∉ Submodule.span K (Set.range fun j : Fin m => (u j : V)) := by
      intro hmem
      have hle : Submodule.span K (Set.range fun j : Fin m => (u j : V)) ≤ LinearMap.ker d := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact (u j).2
      have hx_ker := hle hmem
      rw [LinearMap.mem_ker, hx₀] at hx_ker
      exact one_ne_zero hx_ker
    have hli_fam : LinearIndependent K fam :=
      linearIndependent_finCons.2 ⟨hli_tail, hx₀_notMem⟩
    have hspan_fam : ⊤ ≤ Submodule.span K (Set.range fam) := by
      intro z _
      let kvec : LinearMap.ker d := ⟨z - d z • x₀, by simp [hx₀]⟩
      have hk_span : kvec ∈ Submodule.span K (Set.range u) := by
        rw [u.span_eq]
        trivial
      have hk_map : (kvec : V) ∈ Submodule.span K (Set.range fun j : Fin m => (u j : V)) := by
        have hm' := Submodule.mem_map_of_mem (f := (LinearMap.ker d).subtype) hk_span
        rwa [Submodule.map_span, ← Set.range_comp] at hm'
      have hsub_fam : Submodule.span K (Set.range fun j : Fin m => (u j : V)) ≤
          Submodule.span K (Set.range fam) := by
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        exact ⟨j.succ, rfl⟩
      have hx_mem : d z • x₀ ∈ Submodule.span K (Set.range fam) :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
      have hadd := Submodule.add_mem _ hx_mem (hsub_fam hk_map)
      simpa [kvec] using hadd
    let b₀ : Module.Basis (Fin (m + 1)) K V := Module.Basis.mk hli_fam hspan_fam
    let b' : Module.Basis (Fin n) K V := b₀.reindex (finCongr hm)
    let i₀ : Fin n := finCongr hm 0
    have hd_basis : d = b'.dualBasis i₀ := by
      apply b'.ext
      intro j
      obtain ⟨k, rfl⟩ := (finCongr hm).surjective j
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨q, rfl⟩
      · have hbi : b' i₀ = x₀ := by simp [b', b₀, i₀, fam]
        change d (b' i₀) = b'.dualBasis i₀ (b' i₀)
        rw [b'.dualBasis_apply_self, ite_eq_left rfl, hbi, hx₀]
      · have hne : finCongr hm q.succ ≠ i₀ := fun h =>
          Fin.succ_ne_zero q ((finCongr hm).injective h)
        have hbq : b' (finCongr hm q.succ) = (u q : V) := by simp [b', b₀, fam]
        rw [b'.dualBasis_apply_self, ite_eq_right hne, hbq]
        exact (u q).2
    have heval_b' : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) d (volume b') =
        (orientationUnit (K := K) {i₀} : K) • b'.ExteriorAlgebra ({i₀}ᶜ) := by
      have h1 : b'.dualBasis.ExteriorAlgebra ({i₀} : Finset (Fin n)) = ExteriorAlgebra.ι K d := by
        rw [ExteriorAlgebra.basis_apply_ofCard b'.dualBasis (Finset.card_singleton i₀), hd_basis]
        let g := Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.ofCard (Finset.card_singleton i₀))
        have hg0 : g 0 = i₀ := by
          have hmem : g 0 ∈ ({i₀} : Finset (Fin n)) :=
            (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ (g 0)).1 ⟨0, rfl⟩
          exact Finset.mem_singleton.mp hmem
        change ExteriorAlgebra.ιMulti K 1 (fun i => b'.dualBasis (g i)) = _
        rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, hg0]
      have hp := poincareEval_dualBasis b' ({i₀} : Finset (Fin n))
      rw [h1, hodge_basis] at hp
      simpa [poincareEval, dualContractionAlgHom_ι] using hp
    have hω_compl : ω = ((b'.det b) * (orientationUnit (K := K) {i₀} : K)) •
        b'.ExteriorAlgebra ({i₀}ᶜ) := by
      rw [hω_eval, volume_change_basis b' b, LinearMap.map_smul, heval_b', smul_smul]
    have hcard_compl : ({i₀}ᶜ : Finset (Fin n)).card = n - 1 := by
      rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hcard_compl)
    let w : Fin (n - 1) → V := fun j => b' (g j)
    have hcompl_eq : b'.ExteriorAlgebra ({i₀}ᶜ) = ExteriorAlgebra.ιMulti K (n - 1) w := by
      rw [ExteriorAlgebra.basis_apply_ofCard b' hcard_compl]
      rfl
    let c : K := (b'.det b) * (orientationUnit (K := K) {i₀} : K)
    let j₀ : Fin (n - 1) := ⟨0, hn_pos⟩
    refine ⟨Function.update w j₀ (c • w j₀), ?_⟩
    rw [(ExteriorAlgebra.ιMulti K (n - 1)).map_update_smul w j₀ c (w j₀),
      Function.update_eq_self, ← hcompl_eq]
    exact hω_compl.symm

/-- **Editorial Note 19 & Note 89 (`pp. 335, 363`)**: In 4D over ANY field `K`,
`ω = e₀ ∧ e₁ + e₂ ∧ e₃` has `bladeSupport = ⊥` and is NOT decomposable as any `ιMulti K 2 w`. -/
theorem compound_bivector_fin4_not_decomposable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis (Fin 4) K V) :
    let ω : ExteriorAlgebra K V :=
      ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1) +
        ExteriorAlgebra.ι K (b 2) * ExteriorAlgebra.ι K (b 3)
    bladeSupport ω = ⊥ ∧ ¬∃ w : Fin 2 → V, ExteriorAlgebra.ιMulti K 2 w = ω := by
  intro ω
  have hbasis_pair : ∀ (i j : Fin 4), i < j →
      ExteriorAlgebra.ι K (b i) * ExteriorAlgebra.ι K (b j) = b.ExteriorAlgebra {i, j} := by
    intro i j hij
    have hcard2 : ({i, j} : Finset (Fin 4)).card = 2 :=
      Finset.card_pair (ne_of_lt hij)
    rw [ExteriorAlgebra.basis_apply_ofCard b hcard2]
    let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hcard2)
    have hrange : ∀ t ∈ ({i, j} : Finset (Fin 4)), ∃ r : Fin 2, g r = t := fun t ht =>
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ t).mpr ht
    obtain ⟨r0, hr0⟩ := hrange i (by simp)
    obtain ⟨r1, hr1⟩ := hrange j (by simp)
    have hr01 : r0.val < r1.val := g.lt_iff_lt.mp (by simpa [hr0, hr1] using hij)
    have hr1_lt : r1.val < 2 := r1.isLt
    have hr0_eq : r0 = 0 := by ext; omega
    have hr1_eq : r1 = 1 := by ext; omega
    have hg_all : g 0 = i ∧ g 1 = j := ⟨hr0_eq ▸ hr0, hr1_eq ▸ hr1⟩
    change _ = ExteriorAlgebra.ιMulti K 2 (fun k => b (g k))
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    simp [Matrix.vecTail, hg_all.1, hg_all.2]
  have hbasis_triple : ∀ (i j k : Fin 4), i < j → j < k →
      ExteriorAlgebra.ι K (b i) * ExteriorAlgebra.ι K (b j) * ExteriorAlgebra.ι K (b k) =
        b.ExteriorAlgebra {i, j, k} := by
    intro i j k hij hjk
    have hik : i < k := hij.trans hjk
    have hcard3 : ({i, j, k} : Finset (Fin 4)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (ne_of_lt hjk)]
      simp [ne_of_lt hij, ne_of_lt hik]
    rw [ExteriorAlgebra.basis_apply_ofCard b hcard3]
    let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hcard3)
    have hrange : ∀ t ∈ ({i, j, k} : Finset (Fin 4)), ∃ r : Fin 3, g r = t := fun t ht =>
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ t).mpr ht
    obtain ⟨r0, hr0⟩ := hrange i (by simp)
    obtain ⟨r1, hr1⟩ := hrange j (by simp)
    obtain ⟨r2, hr2⟩ := hrange k (by simp)
    have hr01 : r0.val < r1.val := g.lt_iff_lt.mp (by simpa [hr0, hr1] using hij)
    have hr12 : r1.val < r2.val := g.lt_iff_lt.mp (by simpa [hr1, hr2] using hjk)
    have hr2_lt : r2.val < 3 := r2.isLt
    have hr0_eq : r0 = 0 := by ext; omega
    have hr1_eq : r1 = 1 := by ext; omega
    have hr2_eq : r2 = 2 := by ext; omega
    have hg_all : g 0 = i ∧ g 1 = j ∧ g 2 = k :=
      ⟨hr0_eq ▸ hr0, hr1_eq ▸ hr1, hr2_eq ▸ hr2⟩
    change _ = ExteriorAlgebra.ιMulti K 3 (fun r => b (g r))
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, ← mul_assoc]
    simp [Matrix.vecTail, hg_all.1, hg_all.2.1, hg_all.2.2]
  have h0w : ExteriorAlgebra.ι K (b 0) * ω = b.ExteriorAlgebra {0, 2, 3} := by
    dsimp [ω]
    rw [mul_add, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, zero_add, ← mul_assoc]
    exact hbasis_triple 0 2 3 (by decide) (by decide)
  have h1w : ExteriorAlgebra.ι K (b 1) * ω = b.ExteriorAlgebra {1, 2, 3} := by
    dsimp [ω]
    have h101 : ExteriorAlgebra.ι K (b 1) * (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) = 0 := by
      have hs : ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 0) =
          -(ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      rw [← mul_assoc, hs, neg_mul, mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero, neg_zero]
    rw [mul_add, h101, zero_add, ← mul_assoc]
    exact hbasis_triple 1 2 3 (by decide) (by decide)
  have h2w : ExteriorAlgebra.ι K (b 2) * ω = b.ExteriorAlgebra {0, 1, 2} := by
    dsimp [ω]
    have h201 : ExteriorAlgebra.ι K (b 2) * (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) =
        ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2) := by
      have hs20 : ExteriorAlgebra.ι K (b 2) * ExteriorAlgebra.ι K (b 0) =
          -(ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      have hs21 : ExteriorAlgebra.ι K (b 2) * ExteriorAlgebra.ι K (b 1) =
          -(ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      rw [← mul_assoc, hs20, neg_mul, mul_assoc, hs21, mul_neg, neg_neg, ← mul_assoc]
    rw [mul_add, h201, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, add_zero]
    exact hbasis_triple 0 1 2 (by decide) (by decide)
  have h3w : ExteriorAlgebra.ι K (b 3) * ω = b.ExteriorAlgebra {0, 1, 3} := by
    dsimp [ω]
    have h301 : ExteriorAlgebra.ι K (b 3) * (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) =
        ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 3) := by
      have hs30 : ExteriorAlgebra.ι K (b 3) * ExteriorAlgebra.ι K (b 0) =
          -(ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 3)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      have hs31 : ExteriorAlgebra.ι K (b 3) * ExteriorAlgebra.ι K (b 1) =
          -(ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 3)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      rw [← mul_assoc, hs30, neg_mul, mul_assoc, hs31, mul_neg, neg_neg, ← mul_assoc]
    have h323 : ExteriorAlgebra.ι K (b 3) * (ExteriorAlgebra.ι K (b 2) * ExteriorAlgebra.ι K (b 3)) = 0 := by
      have hs32 : ExteriorAlgebra.ι K (b 3) * ExteriorAlgebra.ι K (b 2) =
          -(ExteriorAlgebra.ι K (b 2) * ExteriorAlgebra.ι K (b 3)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      rw [← mul_assoc, hs32, neg_mul, mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero, neg_zero]
    rw [mul_add, h301, h323, add_zero]
    exact hbasis_triple 0 1 3 (by decide) (by decide)
  have hsupp : bladeSupport ω = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bladeSupport] at hx
    have hdecomp : ExteriorAlgebra.ι K x * ω =
        b.repr x 0 • b.ExteriorAlgebra {0, 2, 3} +
        b.repr x 1 • b.ExteriorAlgebra {1, 2, 3} +
        b.repr x 2 • b.ExteriorAlgebra {0, 1, 2} +
        b.repr x 3 • b.ExteriorAlgebra {0, 1, 3} := by
      have hxsum : x = b.repr x 0 • b 0 + b.repr x 1 • b 1 + b.repr x 2 • b 2 + b.repr x 3 • b 3 := by
        have h := (b.sum_repr x).symm
        rw [Fin.sum_univ_four] at h
        exact h.trans (by abel)
      conv_lhs => rw [hxsum]
      simp only [map_add, map_smul, add_mul, smul_mul_assoc, h0w, h1w, h2w, h3w]
    rw [hx] at hdecomp
    have hc0 : b.repr x 0 = 0 := by
      have h := congrArg (fun z => b.ExteriorAlgebra.coord ({0, 2, 3} : Finset (Fin 4)) z) hdecomp
      simpa [show ({1, 2, 3} : Finset (Fin 4)) ≠ {0, 2, 3} by decide,
        show ({0, 1, 2} : Finset (Fin 4)) ≠ {0, 2, 3} by decide,
        show ({0, 1, 3} : Finset (Fin 4)) ≠ {0, 2, 3} by decide] using h.symm
    have hc1 : b.repr x 1 = 0 := by
      have h := congrArg (fun z => b.ExteriorAlgebra.coord ({1, 2, 3} : Finset (Fin 4)) z) hdecomp
      simpa [show ({0, 2, 3} : Finset (Fin 4)) ≠ {1, 2, 3} by decide,
        show ({0, 1, 2} : Finset (Fin 4)) ≠ {1, 2, 3} by decide,
        show ({0, 1, 3} : Finset (Fin 4)) ≠ {1, 2, 3} by decide] using h.symm
    have hc2 : b.repr x 2 = 0 := by
      have h := congrArg (fun z => b.ExteriorAlgebra.coord ({0, 1, 2} : Finset (Fin 4)) z) hdecomp
      simpa [show ({0, 2, 3} : Finset (Fin 4)) ≠ {0, 1, 2} by decide,
        show ({1, 2, 3} : Finset (Fin 4)) ≠ {0, 1, 2} by decide,
        show ({0, 1, 3} : Finset (Fin 4)) ≠ {0, 1, 2} by decide] using h.symm
    have hc3 : b.repr x 3 = 0 := by
      have h := congrArg (fun z => b.ExteriorAlgebra.coord ({0, 1, 3} : Finset (Fin 4)) z) hdecomp
      simpa [show ({0, 2, 3} : Finset (Fin 4)) ≠ {0, 1, 3} by decide,
        show ({1, 2, 3} : Finset (Fin 4)) ≠ {0, 1, 3} by decide,
        show ({0, 1, 2} : Finset (Fin 4)) ≠ {0, 1, 3} by decide] using h.symm
    have hzero_x : x = 0 := b.repr.injective (by
      ext i
      fin_cases i <;> simp [hc0, hc1, hc2, hc3])
    simpa [Submodule.mem_bot] using hzero_x
  refine ⟨hsupp, ?_⟩
  rintro ⟨w, hw⟩
  have hω_bas : ω = b.ExteriorAlgebra {0, 1} + b.ExteriorAlgebra {2, 3} := by
    dsimp [ω]
    rw [hbasis_pair 0 1 (by decide), hbasis_pair 2 3 (by decide)]
  have hω_ne : ω ≠ 0 := by
    intro h0
    have hc := congrArg (fun z => b.ExteriorAlgebra.coord ({0, 1} : Finset (Fin 4)) z) (hω_bas.symm.trans h0)
    simp [show ({2, 3} : Finset (Fin 4)) ≠ {0, 1} by decide] at hc
  have hli : LinearIndependent K w := by
    by_contra hdep
    exact hω_ne (hw.symm.trans ((ιMulti_eq_zero_iff w).2 hdep))
  have hw0_ne : w 0 ≠ 0 := hli.ne_zero 0
  have hw0_mem : w 0 ∈ bladeSupport ω := by
    rw [← hw, bladeSupport_ιMulti w hli]
    exact Submodule.subset_span ⟨0, rfl⟩
  rw [hsupp, Submodule.mem_bot] at hw0_mem
  exact hw0_ne hw0_mem

end DecomposabilityVsCompound

/-! ## 4. Grassmann No. 103, Note 31 Common-Factor Meet Law, & 5D Countermodel -/

section RegressiveLawsAndCountermodel

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Volume coordinate linear functional `[·]` extracting the `volume b` coefficient. -/
def volCoord {n : ℕ} (b : Module.Basis (Fin n) K V) : ExteriorAlgebra K V →ₗ[K] K :=
  b.ExteriorAlgebra.coord Finset.univ

@[simp] theorem volCoord_volume {n : ℕ} (b : Module.Basis (Fin n) K V) :
    volCoord b (volume b) = 1 := by
  dsimp [volCoord, volume]
  simp

theorem eq_volCoord_smul_volume {n : ℕ} (b : Module.Basis (Fin n) K V)
    {x : ExteriorAlgebra K V} (hx : x ∈ ⋀[K]^n V) :
    x = volCoord b x • volume b := by
  let x' : ⋀[K]^n V := ⟨x, hx⟩
  let sUniv : Set.powersetCard (Fin n) n :=
    Set.powersetCard.ofCard (Finset.card_fin n : (Finset.univ : Finset (Fin n)).card = n)
  have huniq : ∀ s : Set.powersetCard (Fin n) n, s = sUniv := fun s =>
    Subtype.ext (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp))
  have hsum : x' = ((b.exteriorPower n).repr x' sUniv) • (b.exteriorPower n sUniv) := by
    refine ((b.exteriorPower n).sum_repr x').symm.trans ?_
    exact Finset.sum_eq_single sUniv (fun s _ hne => absurd (huniq s) hne)
      (fun h => absurd (Finset.mem_univ sUniv) h)
  have hcoe := congrArg Subtype.val hsum
  change x = _ • (b.exteriorPower n sUniv : ExteriorAlgebra K V) at hcoe
  rw [← ExteriorAlgebra.basis_eq_coe_basis b sUniv] at hcoe
  change x = _ • volume b at hcoe
  have hc : ((b.exteriorPower n).repr x' sUniv) = volCoord b x := by
    have hcoord := congrArg (volCoord b) hcoe
    simpa [volCoord_volume b, smul_eq_mul] using hcoord.symm
  rw [hc] at hcoe
  exact hcoe

private theorem contractLeft_ιMulti_mul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (d : Module.Dual R M) {m : ℕ} (v : Fin m → M) (z : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d (ExteriorAlgebra.ιMulti R m v * z) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d (ExteriorAlgebra.ιMulti R m v) * z +
        ((-1 : R) ^ m) • (ExteriorAlgebra.ιMulti R m v *
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d z) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    have h1 := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm R M)) d (v 0)
      (ExteriorAlgebra.ιMulti R m (Matrix.vecTail v) * z)
    have h2 := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm R M)) d (v 0)
      (ExteriorAlgebra.ιMulti R m (Matrix.vecTail v))
    have hι0 : CliffordAlgebra.ι (0 : QuadraticForm R M) (v 0) = ExteriorAlgebra.ι R (v 0) := rfl
    rw [hι0] at h1 h2
    rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc, h1, ih (Matrix.vecTail v) z, h2, sub_mul,
      smul_mul_assoc, mul_add, mul_smul_comm, pow_succ', neg_one_mul, neg_smul]
    simp only [mul_assoc, sub_eq_add_neg, neg_add]
    abel

/-- Graded Leibniz rule for left Clifford contraction on homogeneous `m`-vectors:
`contractLeft d (U * z) = contractLeft d U * z + (-1)^m • (U * contractLeft d z)`. -/
theorem contractLeft_mul_of_mem_exteriorPower {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (d : Module.Dual R M) {m : ℕ} {U : ExteriorAlgebra R M} (hU : U ∈ ⋀[R]^m M)
    (z : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d (U * z) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d U * z +
        ((-1 : R) ^ m) • (U * CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d z) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R m] at hU
  induction hU using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨v, rfl⟩ := h
    exact contractLeft_ιMulti_mul d v z
  | zero => simp
  | add x y _ _ ihx ihy =>
    simp only [add_mul, map_add, smul_add, ihx, ihy]
    abel
  | smul r x _ ih =>
    rw [smul_mul_assoc, LinearMap.map_smul, ih, LinearMap.map_smul, smul_mul_assoc, smul_add,
      smul_comm r ((-1 : R) ^ m), smul_mul_assoc]

/-- Right multiplication by basis vector `ι (b i)` corresponds under Hodge to left contraction by `b.dualBasis i`. -/
theorem hodge_mul_ι_basis {n : ℕ} (b : Module.Basis (Fin n) K V)
    (Z : ExteriorAlgebra K V) (i : Fin n) :
    hodge b (Z * ExteriorAlgebra.ι K (b i)) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis i) (hodge b Z) := by
  have h1 := LinearMap.congr_fun (poincareEval_comp_dualTransferEquiv b)
    (Z * ExteriorAlgebra.ι K (b i))
  have h2 := LinearMap.congr_fun (poincareEval_comp_dualTransferEquiv b) Z
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1 h2
  rw [dualTransferEquiv_mul] at h1
  have hi : dualTransferEquiv b (ExteriorAlgebra.ι K (b i)) = ExteriorAlgebra.ι K (b.dualBasis i) := by
    change ExteriorAlgebra.map b.toDualEquiv.toLinearMap (ExteriorAlgebra.ι K (b i)) = _
    rw [ExteriorAlgebra.map_apply_ι]
    rfl
  dsimp [poincareEval] at h1 h2
  rw [hi, dualContractionAlgHom_mul, dualContractionAlgHom_ι] at h1
  rw [← h1, ← h2]

/-- Single-basis-vector common-factor law:
`regressive b (ι (b i) * X) (ι (b i) * Y) = ι (b i) * regressive b (ι (b i) * X) Y`
for ALL (even inhomogeneous) `X, Y : ExteriorAlgebra K V`. -/
theorem regressive_ι_basis_mul_ι_basis {n : ℕ} (b : Module.Basis (Fin n) K V)
    (i : Fin n) (X Y : ExteriorAlgebra K V) :
    regressive b (ExteriorAlgebra.ι K (b i) * X) (ExteriorAlgebra.ι K (b i) * Y) =
      ExteriorAlgebra.ι K (b i) * regressive b (ExteriorAlgebra.ι K (b i) * X) Y := by
  have hhom : ∀ p q : ℕ, ∀ x y : ExteriorAlgebra K V, x ∈ ⋀[K]^p V → y ∈ ⋀[K]^q V →
      regressive b (ExteriorAlgebra.ι K (b i) * x) (ExteriorAlgebra.ι K (b i) * y) =
        ExteriorAlgebra.ι K (b i) * regressive b (ExteriorAlgebra.ι K (b i) * x) y := by
    intro p q x y hx hy
    have hix_mem : ExteriorAlgebra.ι K (b i) * x ∈ ⋀[K]^(p + 1) V := by
      rw [ExteriorAlgebra.exteriorPower, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ (b i)) hx
    by_cases hp1 : n < p + 1
    · rw [exteriorPower_eq_zero_of_gt b hp1 hix_mem, zero_regressive, zero_regressive, mul_zero]
    by_cases hq : n < q
    · rw [exteriorPower_eq_zero_of_gt b hq hy, mul_zero, regressive_zero, mul_zero]
    have hp1_le : p + 1 ≤ n := Nat.le_of_not_lt hp1
    have hq_le : q ≤ n := Nat.le_of_not_lt hq
    apply (hodge b).injective
    rw [hodge_regressive]
    set U := hodge b (ExteriorAlgebra.ι K (b i) * x)
    set V' := hodge b y
    have hU_mem : U ∈ ⋀[K]^(n - (p + 1)) V := hodge_mem_exteriorPower b hix_mem
    have hV_mem : V' ∈ ⋀[K]^(n - q) V := hodge_mem_exteriorPower b hy
    have hcU : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis i) U = 0 := by
      have hcomm_x : ExteriorAlgebra.ι K (b i) * x = ((-1 : K) ^ p) • (x * ExteriorAlgebra.ι K (b i)) :=
        ι_mul_exteriorPower_comm (b i) hx
      change CliffordAlgebra.contractLeft _ (hodge b (ExteriorAlgebra.ι K (b i) * x)) = 0
      rw [hcomm_x, map_smul, hodge_mul_ι_basis, LinearMap.map_smul,
        CliffordAlgebra.contractLeft_contractLeft, smul_zero]
    have hLHS : U * hodge b (ExteriorAlgebra.ι K (b i) * y) =
        ((-1 : K) ^ q) • (U * CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis i) V') := by
      rw [ι_mul_exteriorPower_comm (b i) hy, map_smul, hodge_mul_ι_basis b y i, mul_smul_comm]
    rw [hLHS]
    set R := regressive b (ExteriorAlgebra.ι K (b i) * x) y
    have hUV_mem : U * V' ∈ ⋀[K]^(n - (p + 1) + (n - q)) V := by
      rw [ExteriorAlgebra.exteriorPower, pow_add]
      exact Submodule.mul_mem_mul hU_mem hV_mem
    have hR_eq : hodge b R = U * V' := hodge_regressive b _ _
    by_cases hm : n < (n - (p + 1)) + (n - q)
    · have hUV0 : U * V' = 0 := exteriorPower_eq_zero_of_gt b hm hUV_mem
      have hR0 : R = 0 := (hodge b).injective (by rw [hR_eq, hUV0, map_zero])
      have hleib := contractLeft_mul_of_mem_exteriorPower (b.dualBasis i) hU_mem V'
      rw [hUV0, map_zero, hcU, zero_mul, zero_add] at hleib
      have hUc0 : U * CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis i) V' = 0 := by
        have hsmul := congrArg (fun t => ((-1 : K) ^ (n - (p + 1))) • t) hleib.symm
        simpa [smul_smul, ← mul_pow, neg_one_mul] using hsmul
      rw [hUc0, smul_zero, hR0, mul_zero, map_zero]
    · have hm_le : (n - (p + 1)) + (n - q) ≤ n := Nat.le_of_not_lt hm
      have hR_mem : R ∈ ⋀[K]^(n - ((n - (p + 1)) + (n - q))) V := by
        have hR_symm : R = (hodge b).symm (U * V') := by
          rw [← hR_eq, LinearEquiv.symm_apply_apply]
        rw [hR_symm]
        exact hodge_symm_mem_exteriorPower b hUV_mem
      have hcommR : ExteriorAlgebra.ι K (b i) * R =
          ((-1 : K) ^ (n - ((n - (p + 1)) + (n - q)))) • (R * ExteriorAlgebra.ι K (b i)) :=
        ι_mul_exteriorPower_comm (b i) hR_mem
      rw [hcommR, map_smul, hodge_mul_ι_basis b R i, hR_eq,
        contractLeft_mul_of_mem_exteriorPower (b.dualBasis i) hU_mem V', hcU, zero_mul, zero_add,
        smul_smul, ← pow_add]
      congr 1
      rw [show (n - (n - (p + 1) + (n - q))) + (n - (p + 1)) = q by omega]
  induction X using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[K]^i V) with
  | zero => simp
  | add x₁ x₂ ih₁ ih₂ => simp only [mul_add, add_regressive, ih₁, ih₂]
  | homogeneous x =>
    induction Y using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[K]^i V) with
    | zero => simp
    | add y₁ y₂ ih₁ ih₂ => simp only [mul_add, regressive_add, ih₁, ih₂]
    | homogeneous y =>
      exact hhom _ _ (x : ExteriorAlgebra K V) (y : ExteriorAlgebra K V) x.2 y.2

private theorem regressive_ιMulti_basis_common {n : ℕ} (b : Module.Basis (Fin n) K V)
    {α : ℕ} (f : Fin α → Fin n) (B C : ExteriorAlgebra K V) :
    regressive b (ExteriorAlgebra.ιMulti K α (fun i => b (f i)) * B)
        (ExteriorAlgebra.ιMulti K α (fun i => b (f i)) * C) =
      ExteriorAlgebra.ιMulti K α (fun i => b (f i)) *
        regressive b (ExteriorAlgebra.ιMulti K α (fun i => b (f i)) * B) C := by
  induction α generalizing B C with
  | zero => simp
  | succ α ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    set A' := ExteriorAlgebra.ιMulti K α (Matrix.vecTail (fun i => b (f i)))
    have hA'_eq : A' = ExteriorAlgebra.ιMulti K α (fun i => b (f i.succ)) := rfl
    have hA'_mem : A' ∈ ⋀[K]^α V := ExteriorAlgebra.ιMulti_range K α ⟨_, rfl⟩
    have hcommA' : ExteriorAlgebra.ι K (b (f 0)) * A' = ((-1 : K) ^ α) • (A' * ExteriorAlgebra.ι K (b (f 0))) :=
      ι_mul_exteriorPower_comm (b (f 0)) hA'_mem
    calc
      regressive b ((ExteriorAlgebra.ι K (b (f 0)) * A') * B) ((ExteriorAlgebra.ι K (b (f 0)) * A') * C)
          = regressive b (ExteriorAlgebra.ι K (b (f 0)) * (A' * B))
              (ExteriorAlgebra.ι K (b (f 0)) * (A' * C)) := by simp only [mul_assoc]
      _ = ExteriorAlgebra.ι K (b (f 0)) *
            regressive b (ExteriorAlgebra.ι K (b (f 0)) * (A' * B)) (A' * C) :=
          regressive_ι_basis_mul_ι_basis b (f 0) (A' * B) (A' * C)
      _ = ExteriorAlgebra.ι K (b (f 0)) *
            regressive b (A' * (((-1 : K) ^ α) • (ExteriorAlgebra.ι K (b (f 0)) * B))) (A' * C) := by
          rw [← mul_assoc (ExteriorAlgebra.ι K (b (f 0))) A' B, hcommA', smul_mul_assoc,
            mul_smul_comm, mul_assoc]
      _ = ((-1 : K) ^ α) • (ExteriorAlgebra.ι K (b (f 0)) *
            regressive b (A' * (ExteriorAlgebra.ι K (b (f 0)) * B)) (A' * C)) := by
          rw [mul_smul_comm, smul_regressive, mul_smul_comm]
      _ = ((-1 : K) ^ α) • (ExteriorAlgebra.ι K (b (f 0)) *
            (A' * regressive b (A' * (ExteriorAlgebra.ι K (b (f 0)) * B)) C)) := by
          rw [hA'_eq, ih (fun i => f i.succ) (ExteriorAlgebra.ι K (b (f 0)) * B) C]
      _ = (ExteriorAlgebra.ι K (b (f 0)) * A') *
            regressive b (((-1 : K) ^ α) • (A' * (ExteriorAlgebra.ι K (b (f 0)) * B))) C := by
          rw [smul_regressive, mul_smul_comm, mul_assoc]
      _ = (ExteriorAlgebra.ι K (b (f 0)) * A') *
            regressive b ((ExteriorAlgebra.ι K (b (f 0)) * A') * B) C := by
          congr 2
          rw [← mul_assoc A', ← smul_mul_assoc, ← hcommA']

/-- **Editorial Note 31 Valid Common-Factor Meet Law (`pp. 341–342`)**:
for any decomposable blade `A = ιMulti K α v` and ANY (even inhomogeneous) multivectors `B, C`,
`regressive b (A * B) (A * C) = A * regressive b (A * B) C`. -/
theorem note31_valid_left_common_factor {n : ℕ} (b : Module.Basis (Fin n) K V)
    {α : ℕ} (v : Fin α → V) (B C : ExteriorAlgebra K V) :
    regressive b (ExteriorAlgebra.ιMulti K α v * B) (ExteriorAlgebra.ιMulti K α v * C) =
      ExteriorAlgebra.ιMulti K α v * regressive b (ExteriorAlgebra.ιMulti K α v * B) C := by
  by_cases hli : LinearIndependent K v
  · have : Module.Finite K V := Module.Finite.of_basis b
    let sB := Module.Basis.sumExtend hli
    have : Finite (Fin α ⊕ Module.Basis.sumExtendIndex hli) :=
      Module.Finite.finite_basis sB
    have : Fintype (Fin α ⊕ Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
    have hcard : Fintype.card (Fin α ⊕ Module.Basis.sumExtendIndex hli) = n := by
      rw [← Module.finrank_eq_card_basis sB, Module.finrank_eq_card_basis b, Fintype.card_fin]
    let e := Fintype.equivFinOfCardEq hcard
    let b' : Module.Basis (Fin n) K V := sB.reindex e
    have hv_eq : ∀ i : Fin α, v i = b' (e (Sum.inl i)) := fun i => by
      dsimp [b']
      rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
      dsimp [sB, Module.Basis.sumExtend]
      rw [Module.Basis.reindex_apply, Module.Basis.extend_apply_self]
      let := Classical.decPred (· ∈ Set.range v)
      change v i = (((((Equiv.ofInjective v hli.injective).sumCongr
        (Equiv.refl (↑(hli.linearIndepOn_id.extend (Set.subset_univ _) \ Set.range v)))).trans
          (Equiv.Set.sumDiffSubset (hli.linearIndepOn_id.subset_extend _))) (Sum.inl i) :
            ↑(hli.linearIndepOn_id.extend (Set.subset_univ _))) : V)
      rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumDiffSubset_apply_inl]
      rfl
    let f : Fin α → Fin n := fun i => e (Sum.inl i)
    have hι : ExteriorAlgebra.ιMulti K α v = ExteriorAlgebra.ιMulti K α (fun i => b' (f i)) := by
      congr 1; funext i; exact hv_eq i
    have hb' := regressive_ιMulti_basis_common b' f B C
    have hc := congrArg (fun t => (b.det b') • t) hb'
    rw [det_smul_regressive_change_basis b b', ← mul_smul_comm,
      det_smul_regressive_change_basis b b'] at hc
    simpa only [← hι] using hc
  · have hz : ExteriorAlgebra.ιMulti K α v = 0 := (ιMulti_eq_zero_iff v).2 hli
    simp [hz]

/-- Complementary-degree regressive product reduces to top-volume scalar times identity `1`. -/
theorem regressive_compl_degree {n k m : ℕ} (b : Module.Basis (Fin n) K V) (hkm : k + m = n)
    {X Y : ExteriorAlgebra K V} (hX : X ∈ ⋀[K]^k V) (hY : Y ∈ ⋀[K]^m V) :
    regressive b X Y = volCoord b (X * Y) • (1 : ExteriorAlgebra K V) := by
  have hmem : ∀ s t : Finset (Fin n), s.card = k → t.card = m →
      regressive b (b.ExteriorAlgebra s) (b.ExteriorAlgebra t) =
        volCoord b (b.ExteriorAlgebra s * b.ExteriorAlgebra t) • (1 : ExteriorAlgebra K V) := by
    intro s t hs ht
    by_cases hdt : Disjoint sᶜ tᶜ
    · have hsub_compl : tᶜ ⊆ s := fun i hi => by
        by_contra his
        exact Finset.disjoint_left.mp hdt (Finset.mem_compl.mpr his) hi
      have hsub_scompl : sᶜ ⊆ t := fun i hi => by
        by_contra hit
        exact Finset.disjoint_left.mp hdt hi (Finset.mem_compl.mpr hit)
      have hst : t = sᶜ := (Finset.eq_of_subset_of_card_le hsub_scompl
        (by rw [Finset.card_compl, Fintype.card_fin, hs, ht]; omega)).symm
      subst hst
      rw [basis_mul_compl b s, LinearMap.map_smul, volCoord_volume, smul_eq_mul, mul_one]
      apply (hodge b).injective
      rw [hodge_regressive, hodge_basis, hodge_basis, smul_mul_assoc, mul_smul_comm,
        basis_mul_compl b sᶜ, map_smul, hodge_one, smul_smul (orientationUnit (K := K) sᶜ : K),
        orientationUnit_mul_self, one_smul]
    · have h0 : regressive b (b.ExteriorAlgebra s) (b.ExteriorAlgebra t) = 0 := by
        apply (hodge b).injective
        rw [hodge_regressive, hodge_basis, hodge_basis, smul_mul_assoc, mul_smul_comm]
        have hmul0 : b.ExteriorAlgebra sᶜ * b.ExteriorAlgebra tᶜ = 0 := by
          simpa only [Set.powersetCard.val_ofCard] using
            (ExteriorAlgebra.basis_mul_of_not_disjoint b
              (Set.powersetCard.ofCard (s := sᶜ) rfl)
              (Set.powersetCard.ofCard (s := tᶜ) rfl) hdt)
        simp [hmul0]
      have h0' : b.ExteriorAlgebra s * b.ExteriorAlgebra t = 0 := by
        have hnd : ¬Disjoint s t := by
          intro hdis
          apply hdt
          have hcardu := Finset.card_union_of_disjoint hdis
          rw [hs, ht, hkm] at hcardu
          have huniv : s ∪ t = Finset.univ :=
            Finset.eq_univ_of_card _ (by simpa using hcardu)
          rw [Finset.disjoint_left]
          intro i hi1 hi2
          have hi := Finset.mem_univ i
          rw [← huniv, Finset.mem_union] at hi
          exact hi.elim (fun h => Finset.mem_compl.mp hi1 h) (fun h => Finset.mem_compl.mp hi2 h)
        simpa only [Set.powersetCard.val_ofCard] using
          (ExteriorAlgebra.basis_mul_of_not_disjoint b
            (Set.powersetCard.ofCard (s := s) rfl)
            (Set.powersetCard.ofCard (s := t) rfl) hnd)
      simp [h0, h0']
  let rhsBilin : ExteriorAlgebra K V →ₗ[K] ExteriorAlgebra K V →ₗ[K] ExteriorAlgebra K V :=
    LinearMap.mk₂ K (fun u v => volCoord b (u * v) • (1 : ExteriorAlgebra K V))
      (fun u₁ u₂ v => by rw [add_mul, map_add, add_smul])
      (fun r u v => by rw [smul_mul_assoc, LinearMap.map_smul, smul_eq_mul, mul_smul])
      (fun u v₁ v₂ => by rw [mul_add, map_add, add_smul])
      (fun r u v => by rw [mul_smul_comm, LinearMap.map_smul, smul_eq_mul, mul_smul])
  let x' : ⋀[K]^k V := ⟨X, hX⟩
  let y' : ⋀[K]^m V := ⟨Y, hY⟩
  have hxsum : X = ∑ s : Set.powersetCard (Fin n) k,
      (b.exteriorPower k).repr x' s • b.ExteriorAlgebra s.val := by
    have hval := congrArg Subtype.val ((b.exteriorPower k).sum_repr x').symm
    change X = ((Submodule.subtype (⋀[K]^k V)) _) at hval
    rw [map_sum] at hval
    refine hval.trans (Finset.sum_congr rfl fun s _ => ?_)
    rw [map_smul, Submodule.coe_subtype, ← ExteriorAlgebra.basis_eq_coe_basis b s]
  have hysum : Y = ∑ t : Set.powersetCard (Fin n) m,
      (b.exteriorPower m).repr y' t • b.ExteriorAlgebra t.val := by
    have hval := congrArg Subtype.val ((b.exteriorPower m).sum_repr y').symm
    change Y = ((Submodule.subtype (⋀[K]^m V)) _) at hval
    rw [map_sum] at hval
    refine hval.trans (Finset.sum_congr rfl fun t _ => ?_)
    rw [map_smul, Submodule.coe_subtype, ← ExteriorAlgebra.basis_eq_coe_basis b t]
  change regressiveBilin b X Y = rhsBilin X Y
  rw [hxsum, map_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
  congr 1
  rw [hysum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, map_smul]
  congr 1
  exact hmem s.val t.val s.2 t.2

/-- **Grassmann No. 103 (`pp. 337–339`)**: For `α + β + γ = n`, decomposable blade `A = ιMulti K α v`,
and homogeneous `B ∈ ⋀^β V`, `C ∈ ⋀^γ V`,
`regressive b (A * B) (A * C) = volCoord b (A * B * C) • A`. -/
theorem grassmann_no103_blade {n α β γ : ℕ} (b : Module.Basis (Fin n) K V)
    (hdeg : α + β + γ = n) (v : Fin α → V)
    {B C : ExteriorAlgebra K V} (hB : B ∈ ⋀[K]^β V) (hC : C ∈ ⋀[K]^γ V) :
    regressive b (ExteriorAlgebra.ιMulti K α v * B) (ExteriorAlgebra.ιMulti K α v * C) =
      volCoord b (ExteriorAlgebra.ιMulti K α v * B * C) • ExteriorAlgebra.ιMulti K α v := by
  have hA_mem : ExteriorAlgebra.ιMulti K α v ∈ ⋀[K]^α V := ExteriorAlgebra.ιMulti_range K α ⟨v, rfl⟩
  have hAB_mem : ExteriorAlgebra.ιMulti K α v * B ∈ ⋀[K]^(α + β) V := by
    rw [ExteriorAlgebra.exteriorPower, pow_add]
    exact Submodule.mul_mem_mul hA_mem hB
  rw [note31_valid_left_common_factor b v B C,
    regressive_compl_degree b hdeg hAB_mem hC, Algebra.mul_smul_comm, mul_one, mul_assoc]

/-- **`[countermodel_found]` — Engel Editorial Note 31 Counterexample (`p. 342`)**:
In `K^5` over ANY field `K`, for `A = e₀ ∧ e₁`, `B = e₀ ∧ e₂`, `C = e₃ ∧ e₄`:
`A ∧ B = 0` so `C ∧ [AB · C] = 0` and `[C · [AB · C]] = 0`, whereas
`[(A ∧ C) · (B ∧ C)] ≠ 0` (hence `[(A ∧ C) · (B ∧ C)] ≠ C ∧ [AB · C]`). -/
theorem note31_counterexample_dim5 (K : Type*) [Field K] :
    let b := Pi.basisFun K (Fin 5)
    let A : ExteriorAlgebra K (Fin 5 → K) :=
      ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)
    let B : ExteriorAlgebra K (Fin 5 → K) :=
      ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)
    let C : ExteriorAlgebra K (Fin 5 → K) :=
      ExteriorAlgebra.ι K (b 3) * ExteriorAlgebra.ι K (b 4)
    A * B = 0 ∧
      C * regressive b (A * B) C = 0 ∧
      regressive b C (regressive b (A * B) C) = 0 ∧
      regressive b (A * C) (B * C) ≠ 0 ∧
      regressive b (A * C) (B * C) ≠ C * regressive b (A * B) C := by
  intro b A B C
  have hAB : A * B = 0 := by
    dsimp [A, B]
    have h10 : ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 0) =
        -(ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    calc
      (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) *
          (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2))
          = ExteriorAlgebra.ι K (b 0) * (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 0)) *
              ExteriorAlgebra.ι K (b 2) := by simp only [mul_assoc]
      _ = -((ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 0)) * ExteriorAlgebra.ι K (b 1) *
            ExteriorAlgebra.ι K (b 2)) := by
          rw [h10, mul_neg, neg_mul, ← mul_assoc (ExteriorAlgebra.ι K (b 0)) (ExteriorAlgebra.ι K (b 0))]
      _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero, zero_mul, zero_mul, neg_zero]
  have hC0 : C * regressive b (A * B) C = 0 := by rw [hAB, zero_regressive, mul_zero]
  have hC0' : regressive b C (regressive b (A * B) C) = 0 := by rw [hAB, zero_regressive, regressive_zero]
  have hbasis_4 : ∀ (i j k l : Fin 5), i < j → j < k → k < l →
      ExteriorAlgebra.ι K (b i) * ExteriorAlgebra.ι K (b j) *
          (ExteriorAlgebra.ι K (b k) * ExteriorAlgebra.ι K (b l)) =
        b.ExteriorAlgebra {i, j, k, l} := by
    intro i j k l hij hjk hkl
    have hik : i < k := hij.trans hjk
    have hil : i < l := hik.trans hkl
    have hjl : j < l := hjk.trans hkl
    have hcard4 : ({i, j, k, l} : Finset (Fin 5)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (ne_of_lt hkl)]
      · simp [ne_of_lt hjk, ne_of_lt hjl]
      · simp [ne_of_lt hij, ne_of_lt hik, ne_of_lt hil]
    rw [ExteriorAlgebra.basis_apply_ofCard b hcard4]
    let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hcard4)
    have hrange : ∀ t ∈ ({i, j, k, l} : Finset (Fin 5)), ∃ r : Fin 4, g r = t := fun t ht =>
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ t).mpr ht
    obtain ⟨r0, hr0⟩ := hrange i (by simp)
    obtain ⟨r1, hr1⟩ := hrange j (by simp)
    obtain ⟨r2, hr2⟩ := hrange k (by simp)
    obtain ⟨r3, hr3⟩ := hrange l (by simp)
    have hr01 : r0.val < r1.val := g.lt_iff_lt.mp (by simpa [hr0, hr1] using hij)
    have hr12 : r1.val < r2.val := g.lt_iff_lt.mp (by simpa [hr1, hr2] using hjk)
    have hr23 : r2.val < r3.val := g.lt_iff_lt.mp (by simpa [hr2, hr3] using hkl)
    have hr3_lt : r3.val < 4 := r3.isLt
    have hr0_eq : r0 = 0 := by ext; omega
    have hr1_eq : r1 = 1 := by ext; omega
    have hr2_eq : r2 = 2 := by ext; omega
    have hr3_eq : r3 = 3 := by ext; omega
    have hg_all : g 0 = i ∧ g 1 = j ∧ g 2 = k ∧ g 3 = l :=
      ⟨hr0_eq ▸ hr0, hr1_eq ▸ hr1, hr2_eq ▸ hr2, hr3_eq ▸ hr3⟩
    change _ = ExteriorAlgebra.ιMulti K 4 (fun r => b (g r))
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    simp [Matrix.vecTail, hg_all.1, hg_all.2.1, hg_all.2.2.1, hg_all.2.2.2, mul_assoc]
  have hAC_eq : A * C = b.ExteriorAlgebra {0, 1, 3, 4} :=
    hbasis_4 0 1 3 4 (by decide) (by decide) (by decide)
  have hBC_eq : B * C = b.ExteriorAlgebra {0, 2, 3, 4} :=
    hbasis_4 0 2 3 4 (by decide) (by decide) (by decide)
  have hcompl_AC : ({0, 1, 3, 4} : Finset (Fin 5))ᶜ = {2} := by decide
  have hcompl_BC : ({0, 2, 3, 4} : Finset (Fin 5))ᶜ = {1} := by decide
  have h1_eq : b.ExteriorAlgebra ({1} : Finset (Fin 5)) = ExteriorAlgebra.ι K (b 1) := by
    rw [ExteriorAlgebra.basis_apply]
    let g := Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (by decide : ({1} : Finset (Fin 5)).card = 1))
    have hg0 : g 0 = 1 := by
      have hm : g 0 ∈ ({1} : Finset (Fin 5)) :=
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ (g 0)).1 ⟨0, rfl⟩
      exact Finset.mem_singleton.mp hm
    change ExteriorAlgebra.ιMulti K 1 (fun r => b (g r)) = _
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, hg0]
  have h2_eq : b.ExteriorAlgebra ({2} : Finset (Fin 5)) = ExteriorAlgebra.ι K (b 2) := by
    rw [ExteriorAlgebra.basis_apply]
    let g := Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (by decide : ({2} : Finset (Fin 5)).card = 1))
    have hg0 : g 0 = 2 := by
      have hm : g 0 ∈ ({2} : Finset (Fin 5)) :=
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ (g 0)).1 ⟨0, rfl⟩
      exact Finset.mem_singleton.mp hm
    change ExteriorAlgebra.ιMulti K 1 (fun r => b (g r)) = _
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, hg0]
  have h12_eq : ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2) = b.ExteriorAlgebra {1, 2} := by
    have hcard2 : ({1, 2} : Finset (Fin 5)).card = 2 := by decide
    rw [ExteriorAlgebra.basis_apply_ofCard b hcard2]
    let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hcard2)
    have hrange : ∀ t ∈ ({1, 2} : Finset (Fin 5)), ∃ r : Fin 2, g r = t := fun t ht =>
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ t).mpr ht
    obtain ⟨r0, hr0⟩ := hrange 1 (by simp)
    obtain ⟨r1, hr1⟩ := hrange 2 (by simp)
    have hr01 : r0.val < r1.val :=
      g.lt_iff_lt.mp (by rw [hr0, hr1]; decide)
    have hr1_lt : r1.val < 2 := r1.isLt
    have hr0_eq : r0 = 0 := by ext; omega
    have hr1_eq : r1 = 1 := by ext; omega
    have hg0 : g 0 = 1 := hr0_eq ▸ hr0
    have hg1 : g 1 = 2 := hr1_eq ▸ hr1
    change _ = ExteriorAlgebra.ιMulti K 2 (fun r => b (g r))
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    simp [Matrix.vecTail, hg0, hg1]
  have hreg_ne : regressive b (A * C) (B * C) ≠ 0 := by
    intro hz
    have hhz := congrArg (hodge b) hz
    rw [map_zero, hodge_regressive, hAC_eq, hBC_eq, hodge_basis, hodge_basis,
      hcompl_AC, hcompl_BC, smul_mul_assoc, mul_smul_comm, h1_eq, h2_eq] at hhz
    have hs21 : ExteriorAlgebra.ι K (b 2) * ExteriorAlgebra.ι K (b 1) =
        -(b.ExteriorAlgebra {1, 2}) := by
      rw [← h12_eq]
      exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    rw [hs21, smul_neg, smul_neg] at hhz
    have hc : (orientationUnit (K := K) ({0, 1, 3, 4} : Finset (Fin 5)) : K) *
        (orientationUnit (K := K) ({0, 2, 3, 4} : Finset (Fin 5)) : K) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
    have hbas : b.ExteriorAlgebra ({1, 2} : Finset (Fin 5)) ≠ 0 :=
      b.ExteriorAlgebra.ne_zero {1, 2}
    rw [smul_smul, neg_eq_zero, smul_eq_zero] at hhz
    exact hhz.elim hc hbas
  refine ⟨hAB, hC0, hC0', hreg_ne, ?_⟩
  rw [hC0]
  exact hreg_ne

end RegressiveLawsAndCountermodel

/-! ## 5. Inner Product, Universal Adjointness, Normal Shadow Reciprocity (`Note 68`), & Open Expressions -/

section InnerAndNormalShadow

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Basis-orthonormal exterior inner pairing `[x | y] = volCoord b (x * hodge b y)`. -/
def extInner {n : ℕ} (b : Module.Basis (Fin n) K V) :
    LinearMap.BilinForm K (ExteriorAlgebra K V) :=
  LinearMap.mk₂ K (fun x y => volCoord b (x * hodge b y))
    (fun x₁ x₂ y => by simp only [add_mul, map_add])
    (fun r x y => by simp only [smul_mul_assoc, map_smul, smul_eq_mul])
    (fun x y₁ y₂ => by simp only [map_add, mul_add])
    (fun r x y => by simp only [map_smul, mul_smul_comm, smul_eq_mul])

@[simp] theorem extInner_apply {n : ℕ} (b : Module.Basis (Fin n) K V)
    (x y : ExteriorAlgebra K V) :
    extInner b x y = volCoord b (x * hodge b y) := rfl

@[simp] theorem extInner_smul_left {n : ℕ} (b : Module.Basis (Fin n) K V)
    (r : K) (x y : ExteriorAlgebra K V) :
    extInner b (r • x) y = r * extInner b x y :=
  LinearMap.map_smul₂ (extInner b) r x y

@[simp] theorem extInner_smul_right {n : ℕ} (b : Module.Basis (Fin n) K V)
    (r : K) (x y : ExteriorAlgebra K V) :
    extInner b x (r • y) = r * extInner b x y :=
  (extInner b x).map_smul r y

/-- Basis blades `b.ExteriorAlgebra s` form an orthonormal basis for `extInner b` across all degrees. -/
theorem extInner_basis {n : ℕ} (b : Module.Basis (Fin n) K V) (s t : Finset (Fin n)) :
    extInner b (b.ExteriorAlgebra s) (b.ExteriorAlgebra t) = if s = t then 1 else 0 := by
  dsimp [extInner]
  rw [hodge_basis, mul_smul_comm, LinearMap.map_smul, smul_eq_mul]
  by_cases hst : s = t
  · subst hst
    rw [ite_eq_left rfl, basis_mul_compl b s, LinearMap.map_smul, volCoord_volume b, smul_eq_mul,
      mul_one, orientationUnit_mul_self]
  · rw [ite_eq_right hst]
    suffices h0 : volCoord b (b.ExteriorAlgebra s * b.ExteriorAlgebra tᶜ) = 0 by simp [h0]
    by_cases hdt : Disjoint s tᶜ
    · have hsub : s ⊆ t := disjoint_compl_right_iff.mp hdt
      have hne_univ : s.disjUnion tᶜ hdt ≠ Finset.univ := by
        intro huniv
        have hsub' : t ⊆ s := by
          intro i hi
          have hmem : i ∈ s.disjUnion tᶜ hdt := huniv ▸ Finset.mem_univ i
          rw [Finset.mem_disjUnion] at hmem
          exact hmem.elim id fun hc => absurd hi (Finset.mem_compl.mp hc)
        exact hst (Finset.Subset.antisymm hsub hsub')
      let s' : Set.powersetCard (Fin n) s.card := Set.powersetCard.ofCard rfl
      let tc' : Set.powersetCard (Fin n) tᶜ.card := Set.powersetCard.ofCard rfl
      have hdt' : Disjoint (s' : Finset (Fin n)) (tc' : Finset (Fin n)) := by
        simpa [s', tc'] using hdt
      have hmul : b.ExteriorAlgebra s * b.ExteriorAlgebra tᶜ =
          (Set.powersetCard.permOfDisjoint hdt').sign •
            b.ExteriorAlgebra (s.disjUnion tᶜ hdt) := by
        simpa [s', tc'] using ExteriorAlgebra.basis_mul_of_disjoint b s' tc' hdt'
      rw [hmul, Units.smul_def, map_zsmul, volCoord, b.ExteriorAlgebra.coord_apply,
        b.ExteriorAlgebra.repr_self, Finsupp.single_eq_of_ne (Ne.symm hne_univ), zsmul_zero]
    · have hmul0 : b.ExteriorAlgebra s * b.ExteriorAlgebra tᶜ = 0 := by
        simpa only [Set.powersetCard.val_ofCard] using
          (ExteriorAlgebra.basis_mul_of_not_disjoint b
            (Set.powersetCard.ofCard (s := s) rfl)
            (Set.powersetCard.ofCard (s := tᶜ) rfl) hdt)
      rw [hmul0, map_zero]

/-- Explicit coordinate expansion of `extInner b`. -/
theorem extInner_eq_sum_repr {n : ℕ} (b : Module.Basis (Fin n) K V)
    (x y : ExteriorAlgebra K V) :
    extInner b x y = ∑ s : Finset (Fin n), b.ExteriorAlgebra.repr x s * b.ExteriorAlgebra.repr y s := by
  have hx : x = ∑ s : Finset (Fin n), b.ExteriorAlgebra.repr x s • b.ExteriorAlgebra s :=
    (b.ExteriorAlgebra.sum_repr x).symm
  have hy : y = ∑ t : Finset (Fin n), b.ExteriorAlgebra.repr y t • b.ExteriorAlgebra t :=
    (b.ExteriorAlgebra.sum_repr y).symm
  conv_lhs => rw [hx, hy]
  simp only [map_sum, LinearMap.sum_apply, extInner_smul_left, extInner_smul_right,
    extInner_basis, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single s
    (fun t _ hts => ite_eq_right hts)
    (fun h => absurd (Finset.mem_univ s) h),
    ite_eq_left rfl, mul_comm]

theorem extInner_symm {n : ℕ} (b : Module.Basis (Fin n) K V) (x y : ExteriorAlgebra K V) :
    extInner b x y = extInner b y x := by
  rw [extInner_eq_sum_repr, extInner_eq_sum_repr]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

theorem extInner_hodge_isometry {n : ℕ} (b : Module.Basis (Fin n) K V)
    (x y : ExteriorAlgebra K V) :
    extInner b (hodge b x) (hodge b y) = extInner b x y := by
  have hbas : ∀ s t : Finset (Fin n),
      extInner b (hodge b (b.ExteriorAlgebra s)) (hodge b (b.ExteriorAlgebra t)) =
        extInner b (b.ExteriorAlgebra s) (b.ExteriorAlgebra t) := fun s t => by
    rw [hodge_basis, hodge_basis, extInner_smul_left, extInner_smul_right,
      extInner_basis, extInner_basis]
    by_cases hst : s = t
    · subst hst; simp [orientationUnit_mul_self]
    · have hne : sᶜ ≠ tᶜ := fun h => hst (compl_inj_iff.mp h)
      simp [hst, hne]
  have hx : x = ∑ s : Finset (Fin n), b.ExteriorAlgebra.repr x s • b.ExteriorAlgebra s :=
    (b.ExteriorAlgebra.sum_repr x).symm
  have hy : y = ∑ t : Finset (Fin n), b.ExteriorAlgebra.repr y t • b.ExteriorAlgebra t :=
    (b.ExteriorAlgebra.sum_repr y).symm
  rw [hx, hy]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  exact hbas t s

/-- Universal adjointness (right): `⟨x * ★B, z⟩ = ⟨x, B · z⟩` for ALL `x, B, z` across all grades. -/
theorem extInner_mul_hodge_right {n : ℕ} (b : Module.Basis (Fin n) K V)
    (x B z : ExteriorAlgebra K V) :
    extInner b (x * hodge b B) z = extInner b x (regressive b B z) := by
  dsimp [extInner]
  rw [hodge_regressive, mul_assoc]

/-- Graded cyclic trace property of `volCoord`:
`volCoord b (u * hodge b (hodge b x)) = volCoord b (x * u)` for all `u, x`. -/
theorem volCoord_mul_hodge_hodge {n : ℕ} (b : Module.Basis (Fin n) K V)
    (u x : ExteriorAlgebra K V) :
    volCoord b (u * hodge b (hodge b x)) = volCoord b (x * u) := by
  have hbas : ∀ v s : Finset (Fin n),
      volCoord b (b.ExteriorAlgebra v * hodge b (hodge b (b.ExteriorAlgebra s))) =
        volCoord b (b.ExteriorAlgebra s * b.ExteriorAlgebra v) := fun v s => by
    rw [hodge_hodge_basis, mul_smul_comm, LinearMap.map_smul, smul_eq_mul]
    have hdeg_s : b.ExteriorAlgebra s ∈ ⋀[K]^s.card V := basis_mem_exteriorPower b s
    have hdeg_v : b.ExteriorAlgebra v ∈ ⋀[K]^v.card V := basis_mem_exteriorPower b v
    rw [exteriorPower_mul_comm hdeg_v hdeg_s, LinearMap.map_smul, smul_eq_mul, ← mul_assoc]
    by_cases hvs : v = sᶜ
    · subst hvs
      rw [basis_mul_compl b s, LinearMap.map_smul, volCoord_volume b, smul_eq_mul, mul_one,
        Finset.card_compl, Fintype.card_fin, mul_comm (n - s.card), ← pow_add, ← two_mul,
        pow_mul]
      have hsq : (-1 : K) ^ 2 = 1 := by norm_num
      rw [hsq, one_pow, one_mul]
    · have hv0 : volCoord b (b.ExteriorAlgebra s * b.ExteriorAlgebra v) = 0 := by
        by_cases hd : Disjoint s v
        · have hne_univ : s.disjUnion v hd ≠ Finset.univ := by
            intro huniv
            apply hvs
            ext i
            rw [Finset.mem_compl]
            refine ⟨fun hi => Finset.disjoint_right.mp hd hi, fun his => ?_⟩
            have hm : i ∈ s.disjUnion v hd := huniv ▸ Finset.mem_univ i
            exact (Finset.mem_disjUnion.mp hm).elim (fun h => absurd h his) id
          let s' : Set.powersetCard (Fin n) s.card := Set.powersetCard.ofCard rfl
          let v' : Set.powersetCard (Fin n) v.card := Set.powersetCard.ofCard rfl
          have hd' : Disjoint (s' : Finset (Fin n)) (v' : Finset (Fin n)) := by
            simpa [s', v'] using hd
          have hmul : b.ExteriorAlgebra s * b.ExteriorAlgebra v =
              (Set.powersetCard.permOfDisjoint hd').sign •
                b.ExteriorAlgebra (s.disjUnion v hd) := by
            simpa [s', v'] using ExteriorAlgebra.basis_mul_of_disjoint b s' v' hd'
          rw [hmul, Units.smul_def, map_zsmul, volCoord, b.ExteriorAlgebra.coord_apply,
            b.ExteriorAlgebra.repr_self, Finsupp.single_eq_of_ne (Ne.symm hne_univ), zsmul_zero]
        · have hmul0 : b.ExteriorAlgebra s * b.ExteriorAlgebra v = 0 := by
            simpa only [Set.powersetCard.val_ofCard] using
              (ExteriorAlgebra.basis_mul_of_not_disjoint b
                (Set.powersetCard.ofCard (s := s) rfl)
                (Set.powersetCard.ofCard (s := v) rfl) hd)
          rw [hmul0, map_zero]
      simp [hv0]
  have hu : u = ∑ v : Finset (Fin n), b.ExteriorAlgebra.repr u v • b.ExteriorAlgebra v :=
    (b.ExteriorAlgebra.sum_repr u).symm
  have hx : x = ∑ s : Finset (Fin n), b.ExteriorAlgebra.repr x s • b.ExteriorAlgebra s :=
    (b.ExteriorAlgebra.sum_repr x).symm
  conv_lhs => rw [hu, hx]
  conv_rhs => rw [hu, hx]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, map_smul, smul_mul_assoc,
    mul_smul_comm, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun v _ => ?_
  rw [hbas s v]
  ring

/-- Universal adjointness (left): `⟨[B · ★x], z⟩ = ⟨B, x * z⟩` for ALL `x, B, z` across all grades. -/
theorem extInner_regressive_hodge_left {n : ℕ} (b : Module.Basis (Fin n) K V)
    (x B z : ExteriorAlgebra K V) :
    extInner b (regressive b B (hodge b x)) z = extInner b B (x * z) := by
  rw [extInner_symm b _ z, ← extInner_mul_hodge_right b z B (hodge b x), extInner_apply,
    volCoord_mul_hodge_hodge, ← mul_assoc, ← extInner_apply, extInner_symm]

/-- Grassmann's normal shadow `A'` (unnormalized by `B²`): `regressive b B (A * hodge b B)`. -/
def normalShadowLeft {n : ℕ} (b : Module.Basis (Fin n) K V)
    (A B : ExteriorAlgebra K V) : ExteriorAlgebra K V :=
  regressive b B (A * hodge b B)

/-- Grassmann's normal shadow `B'` (unnormalized by `A²`): `A * regressive b B (hodge b A)`. -/
def normalShadowRight {n : ℕ} (b : Module.Basis (Fin n) K V)
    (A B : ExteriorAlgebra K V) : ExteriorAlgebra K V :=
  A * regressive b B (hodge b A)

/-- **Editorial Note 68 (`pp. 357–358`) — Blade Inner & Normal-Shadow Reciprocity**:
1. Unconditionally for ALL `A, B`: `⟨A, A'⟩ = ⟨A * ★B, A * ★B⟩` and `⟨B', B⟩ = ⟨B · ★A, B · ★A⟩`.
2. For arbitrary homogeneous `A ∈ ⋀^α V`, `B ∈ ⋀^β V` (including unequal orders `α ≠ β` and
   compound multivectors!): `⟨A * ★B, A * ★B⟩ = ⟨B · ★A, B · ★A⟩` and `⟨A, A'⟩ = ⟨B', B⟩`. -/
theorem note68_normal_shadow_reciprocity {n : ℕ} (b : Module.Basis (Fin n) K V)
    (A B : ExteriorAlgebra K V) :
    extInner b A (normalShadowLeft b A B) = extInner b (A * hodge b B) (A * hodge b B) := by
  exact (extInner_mul_hodge_right b A B (A * hodge b B)).symm

theorem note68_homogeneous_reciprocity {n α β : ℕ} (b : Module.Basis (Fin n) K V)
    {A B : ExteriorAlgebra K V} (hA : A ∈ ⋀[K]^α V) (hB : B ∈ ⋀[K]^β V) :
    extInner b (A * hodge b B) (A * hodge b B) =
      extInner b (regressive b B (hodge b A)) (regressive b B (hodge b A)) ∧
    extInner b A (normalShadowLeft b A B) =
      extInner b (normalShadowRight b A B) B := by
  have hB_c : hodge b B ∈ ⋀[K]^(n - β) V := hodge_mem_exteriorPower b hB
  have hh : hodge b (regressive b B (hodge b A)) =
      ((-1 : K) ^ (α * (n - α) + α * (n - β))) • (A * hodge b B) := by
    rw [hodge_regressive, hodge_hodge_exteriorPower b hA, mul_smul_comm,
      exteriorPower_mul_comm hB_c hA, smul_smul, ← pow_add, Nat.mul_comm (n - β) α, add_comm]
  have hnorm : extInner b (regressive b B (hodge b A)) (regressive b B (hodge b A)) =
      extInner b (A * hodge b B) (A * hodge b B) := by
    rw [← extInner_hodge_isometry b (regressive b B (hodge b A)), hh,
      extInner_smul_left, extInner_smul_right,
      ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  refine ⟨hnorm.symm, ?_⟩
  rw [note68_normal_shadow_reciprocity b A B, ← hnorm,
    extInner_regressive_hodge_left b A B (regressive b B (hodge b A)), extInner_symm]
  rfl

/-- **Editorial Note 105 (`pp. 371–372`)**: Free (symmetrized) open-expression pairing
`A_{ll} ab = (B a b + B b a) / 2`, coinciding with bound `B a b` for all `a, b` iff `B` is symmetric. -/
def freeOpenPair {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (x y : V) : K :=
  (2 : K)⁻¹ * (B x y + B y x)

theorem freeOpenPair_eq_self_iff_isSymm {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V) :
    (∀ x y, freeOpenPair B x y = B x y) ↔ LinearMap.IsSymm B := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  rw [LinearMap.isSymm_def]
  constructor
  · intro h x y
    have hx := h x y
    dsimp [freeOpenPair] at hx
    have hmul := congrArg ((2 : K) * ·) hx
    rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul] at hmul
    simp only [RingHom.id_apply]
    have hsub : (B x) y + (B y) x = (B x) y + (B x) y := by
      rw [hmul, two_mul]
    exact add_left_cancel hsub.symm
  · intro h x y
    dsimp [freeOpenPair]
    simp only [RingHom.id_apply] at h
    rw [h y x, ← two_mul, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]

end InnerAndNormalShadow

/-! ## 6. Seligman Critique of Grassmann No. 391(c) & Sylvester Inertia (`p. 397`) -/

section SeligmanInertiaCritique

/-- Canonical indefinite Minkowski bilinear form `B(x, y) = x₀ y₀ - x₁ y₁` on `ℝ²`. -/
def indefiniteForm2 : LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  Matrix.toBilin' !![(1 : ℝ), 0; 0, -1]

theorem indefiniteForm2_toQuadraticMap :
    indefiniteForm2.toQuadraticMap = QuadraticMap.weightedSumSquares ℝ (![1, -1] : Fin 2 → ℝ) := by
  ext x
  rw [QuadraticMap.weightedSumSquares_apply]
  simp [indefiniteForm2, Matrix.toBilin'_apply, Fin.sum_univ_two]

/-- `2 × 2` circular Givens rotation matrix by angle `θ`. -/
def rotationMatrix2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rotationMatrix2_orthog (θ : ℝ) :
    (rotationMatrix2 θ)ᵀ * rotationMatrix2 θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  · simpa [pow_two] using Real.cos_sq_add_sin_sq θ
  · ring
  · ring
  · simpa [pow_two, add_comm] using Real.cos_sq_add_sin_sq θ

/-- **Seligman Supplementary Note Critique of Grassmann No. 391(c) (`p. 397`)**:
1. For the nondegenerate indefinite form `Q₂(x) = x₀² - x₁²`, Sylvester inertia satisfies
   `sigPos Q₂ = 1 ∧ sigNeg Q₂ = 1` (using `QuadraticForm.sigPos_weightedSumSquares` / `sigNeg_weightedSumSquares`).
2. Every isometric equivalence `Q₂.IsometryEquiv Q'` preserves `(sigPos Q' = 1 ∧ sigNeg Q' = 1)`.
3. The circular rotation by `π / 4` sends `e₀` to the isotropic vector `(1/√2, 1/√2)` with `Q₂(v) = 0`,
   showing circular evolutions can create null diagonal vectors when definiteness is absent. -/
theorem seligman_note391_indefinite_critique :
    sigPos indefiniteForm2.toQuadraticMap = 1 ∧
      sigNeg indefiniteForm2.toQuadraticMap = 1 ∧
      (∀ {W : Type*} [AddCommGroup W] [Module ℝ W] {Q' : QuadraticForm ℝ W},
        indefiniteForm2.toQuadraticMap.Equivalent Q' →
          sigPos Q' = 1 ∧ sigNeg Q' = 1) ∧
      indefiniteForm2.toQuadraticMap ((rotationMatrix2 (Real.pi / 4)).mulVec ![1, 0]) = 0 := by
  have hsigPos : sigPos indefiniteForm2.toQuadraticMap = 1 := by
    have hsp : sigPos (QuadraticMap.weightedSumSquares ℝ (![1, -1] : Fin 2 → ℝ)) =
        {i : Fin 2 | (0 : ℝ) < (![1, -1] : Fin 2 → ℝ) i}.ncard :=
      QuadraticForm.sigPos_weightedSumSquares
    rw [indefiniteForm2_toQuadraticMap, hsp]
    have hset : ({i : Fin 2 | (0 : ℝ) < (![1, -1] : Fin 2 → ℝ) i} : Set (Fin 2)) = {0} := by
      ext i; fin_cases i <;> simp
    rw [hset, Set.ncard_singleton]
  have hsigNeg : sigNeg indefiniteForm2.toQuadraticMap = 1 := by
    have hsn : sigNeg (QuadraticMap.weightedSumSquares ℝ (![1, -1] : Fin 2 → ℝ)) =
        {i : Fin 2 | (![1, -1] : Fin 2 → ℝ) i < 0}.ncard :=
      QuadraticForm.sigNeg_weightedSumSquares
    rw [indefiniteForm2_toQuadraticMap, hsn]
    have hset : ({i : Fin 2 | (![1, -1] : Fin 2 → ℝ) i < 0} : Set (Fin 2)) = {1} := by
      ext i; fin_cases i <;> simp
    rw [hset, Set.ncard_singleton]
  refine ⟨hsigPos, hsigNeg, ?_, ?_⟩
  · intro W _ _ Q' heq
    exact ⟨heq.sigPos_eq.symm.trans hsigPos, heq.sigNeg_eq.symm.trans hsigNeg⟩
  · have hv : (rotationMatrix2 (Real.pi / 4)).mulVec ![1, 0] =
        ![Real.cos (Real.pi / 4), Real.sin (Real.pi / 4)] := by
      ext i
      fin_cases i <;>
        simp [rotationMatrix2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hcs : Real.cos (Real.pi / 4) = Real.sin (Real.pi / 4) := by
      rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
    rw [hv, indefiniteForm2_toQuadraticMap, QuadraticMap.weightedSumSquares_apply,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      smul_eq_mul, hcs]
    ring

end SeligmanInertiaCritique

end InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
