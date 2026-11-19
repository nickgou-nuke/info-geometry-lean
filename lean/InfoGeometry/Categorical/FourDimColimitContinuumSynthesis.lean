/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CategoryTheoryConeUniqueness
import InfoGeometry.Canonical.FilteredDirectLimitOperatorUniqueness
import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.Canonical.CantorProjectiveLimit
import InfoGeometry.Canonical.FilteredGNSHilbertColimit
import InfoGeometry.Canonical.CategoricalColimitContinuumBridge
import InfoGeometry.Categorical.ZornUHFColimit
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.OperatorAlgebra.CoarseGrainingComposition

/-!
# Constructive Unification of 4D Colimit--Continuum Lanes in `lean/`

Promotes the contravariant colimit $\leftrightarrow$ inverse-limit Hom duality and
bidirectional retraction--section tower cleanly into the compiled `lean/` library (without
`src/`-only dependencies or custom `structure` wrappers) and unifies the six 4D colimit-continuum
constructions in `InfoGeometry`:

1. **Concrete Projective Limits & `ℕᵒᵖ ⥤ Type u` Sections**:
   `ConcreteProjectiveLimit B π` as a pure compatible-thread subtype with universal cone lift
   `liftCone`, uniqueness `liftCone_unique`, and explicit bijection `equivOppositeSections` to
   Mathlib's `(inverseDiagram B π ...).sections`.
2. **Universal Colimit $\leftrightarrow$ Inverse-Limit Hom Duality**:
   Two-way equivalence `addCommGroupDirectLimitHomEquivProjectiveLimit` identifying
   `(AddCommGroup.DirectLimit Stage f →+ K) ≃ ConcreteProjectiveLimit (fun n => Stage n →+ K) ...`
   together with Cantor prefix truncation non-injectivity (`prefixSucc 1`).
3. **Bidirectional Retraction--Section Towers & Faithful Direct-Limit Embeddings**:
   Pure subtype `BidirectionalRetractionSectionTower A`, global injectivity of `ι m n h`,
   surjectivity of `π m n h`, idempotence of `coarseIdempotent T m n h`, and global injectivity
   of `directLimitOf bond n` into `DirectLimitSuperClosure bond`.
4. **Concrete 4D Dyadic Spacetime Refinement Tower (`SpacetimeLattice4D n` of `16^n` Sites)**:
   Constructs `SpacetimeLattice4D n := Fin (2^n) × Fin (2^n) × Fin (2^n) × Fin (2^n)`,
   proves `Fintype.card (SpacetimeLattice4D n) = 16^n`, builds the `BidirectionalRetractionSectionTower`
   on 4D fields `Field4D n := SpacetimeLattice4D n → ℝ`, proves every finite 4D lattice scale injects
   into `Field4DContinuum := AddCommGroup.DirectLimit Field4D ...`, and dualizes continuum
   functionals via `addCommGroupDirectLimitHomEquivProjectiveLimit`.
5. **Master Unification Across 4D Amplituhedron, Balaban Coarse-Graining (with T16 Noncommutative
   Matrix Witness), Zorn UHF Monoidal Colimit, and Completed GNS Hilbert Colimit**.
-/

noncomputable section

namespace InfoGeometry.Categorical.FourDimColimitContinuumSynthesis

open Matrix
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Matrix MonoidalCategory
open InfoGeometry.Canonical.CategoryTheoryConeUniqueness
open InfoGeometry.Canonical.FilteredDirectLimitOperator
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CategoricalColimitContinuum
open InfoGeometry.Topology.AmplituhedronColimit
open InfoGeometry.Categorical.ZornUHFColimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
open CStarStateColimit.Native.FilteredGNSHilbertColimit

universe u v

/-! ## 1. Pure-Subtype Concrete Projective Limits & Categorical Sections -/

/-- The concrete projective (inverse) limit carrier of an inverse system `(B n, π_{m,n})_{m ≤ n}`:
the subtype of compatible stage threads. -/
def ConcreteProjectiveLimit
    (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m) : Type u :=
  { thread : ∀ n : ℕ, B n // ∀ m n : ℕ, (h : m ≤ n) → π m n h (thread n) = thread m }

/-- Canonical contravariant `ℕᵒᵖ ⥤ Type u` diagram associated with an inverse system `(B, π)`. -/
def inverseSystemFunctor
    (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m)
    (h_id : ∀ (n : ℕ) (x : B n), π n n (le_refl n) x = x)
    (h_comp : ∀ {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (x : B n),
      π l m hlm (π m n hmn x) = π l n (le_trans hlm hmn) x) :
    ℕᵒᵖ ⥤ Type u where
  obj n := B n.unop
  map f := ↾(fun x => π _ _ (leOfHom f.unop) x)
  map_id n := by
    ext x
    exact h_id n.unop x
  map_comp f g := by
    ext x
    exact (h_comp (leOfHom g.unop) (leOfHom f.unop) x).symm

namespace ConcreteProjectiveLimit

variable {B : ℕ → Type u} {π : ∀ m n : ℕ, m ≤ n → B n → B m}

/-- Underlying compatible thread of `x : ConcreteProjectiveLimit B π`. -/
def thread (x : ConcreteProjectiveLimit B π) : ∀ n : ℕ, B n :=
  x.val

theorem compatible (x : ConcreteProjectiveLimit B π) (m n : ℕ) (h : m ≤ n) :
    π m n h (x.thread n) = x.thread m :=
  x.property m n h

@[ext]
theorem ext {x y : ConcreteProjectiveLimit B π} (h : x.thread = y.thread) : x = y :=
  Subtype.ext h

/-- Canonical projection onto stage `n`. -/
def proj (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m)
    (n : ℕ) (x : ConcreteProjectiveLimit B π) : B n :=
  x.thread n

theorem proj_compatible (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m)
    {m n : ℕ} (h : m ≤ n) (x : ConcreteProjectiveLimit B π) :
    π m n h (proj B π n x) = proj B π m x :=
  x.compatible m n h

/-- Universal cone lift into `ConcreteProjectiveLimit B π`. -/
def liftCone (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m)
    {W : Type v} (c : ∀ n : ℕ, W → B n)
    (hc : ∀ m n : ℕ, (h : m ≤ n) → ∀ w : W, π m n h (c n w) = c m w) :
    W → ConcreteProjectiveLimit B π :=
  fun w => ⟨fun n => c n w, fun m n h => hc m n h w⟩

/-- Uniqueness of the universal cone lift into `ConcreteProjectiveLimit B π`. -/
theorem liftCone_unique (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m)
    {W : Type v} (c : ∀ n : ℕ, W → B n)
    (hc : ∀ m n : ℕ, (h : m ≤ n) → ∀ w : W, π m n h (c n w) = c m w)
    (L : W → ConcreteProjectiveLimit B π)
    (hL : ∀ n : ℕ, ∀ w : W, proj B π n (L w) = c n w) :
    L = liftCone B π c hc := by
  funext w
  apply ConcreteProjectiveLimit.ext
  funext n
  exact hL n w

/-- Canonical bijection between `ConcreteProjectiveLimit B π` and Mathlib's functor sections. -/
def equivOppositeSections
    (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m)
    (h_id : ∀ (n : ℕ) (x : B n), π n n (le_refl n) x = x)
    (h_comp : ∀ {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (x : B n),
      π l m hlm (π m n hmn x) = π l n (le_trans hlm hmn) x) :
    ConcreteProjectiveLimit B π ≃
      (inverseSystemFunctor B π h_id h_comp).sections where
  toFun x :=
    ⟨fun n => x.val n.unop,
     fun {m n} f => by
       change π n.unop m.unop (leOfHom f.unop) (x.val m.unop) = x.val n.unop
       exact x.property n.unop m.unop (leOfHom f.unop)⟩
  invFun s :=
    ⟨fun n => s.val (Opposite.op n),
     fun m n h => by
       have hs := s.property (homOfLE h).op
       change π m n h (s.val (Opposite.op n)) = s.val (Opposite.op m) at hs
       exact hs⟩
  left_inv x := Subtype.ext rfl
  right_inv s := Subtype.ext rfl

end ConcreteProjectiveLimit

/-! ## 2. Universal Colimit--Inverse-Limit Hom Duality & Contravariant Asymmetry -/

/-- **Universal Colimit--to--Inverse-Limit Hom Duality**:
Additive homomorphisms `AddCommGroup.DirectLimit Stage f →+ K` out of Mathlib's filtered
direct limit are in canonical bijection `≃` with coherent projective threads in
`ConcreteProjectiveLimit (fun n => Stage n →+ K) (fun m n h φ => φ.comp (f m n h))`. -/
def addCommGroupDirectLimitHomEquivProjectiveLimit
    (Stage : ℕ → Type u) [∀ n, AddCommGroup (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)
    [DirectedSystem Stage (fun m n h => f m n h)]
    (K : Type u) [AddCommGroup K] :
    (AddCommGroup.DirectLimit Stage f →+ K) ≃
      ConcreteProjectiveLimit (fun n => Stage n →+ K)
        (fun m n h (φ : Stage n →+ K) => φ.comp (f m n h)) where
  toFun Ψ :=
    ⟨fun n => Ψ.comp (AddCommGroup.DirectLimit.of Stage f n),
     by
       intro m n h
       ext x
       simp only [AddMonoidHom.comp_apply, AddCommGroup.DirectLimit.of_f]⟩
  invFun φ :=
    AddCommGroup.DirectLimit.lift Stage f K φ.thread (by
      intro m n h x
      exact DFunLike.congr_fun (φ.compatible m n h) x)
  left_inv Ψ := by
    apply AddMonoidHom.ext
    intro z
    refine AddCommGroup.DirectLimit.induction_on z ?_
    intro n x
    simp only [AddCommGroup.DirectLimit.lift_of]
    rfl
  right_inv φ := by
    apply Subtype.ext
    funext n
    ext x
    dsimp [AddMonoidHom.comp]
    rw [AddCommGroup.DirectLimit.lift_of]
    rfl

/-- Contravariant separation witness on finite Cantor prefixes: `prefixSucc 1` is surjective
yet merges two distinct length-2 words (`bitWord 00` and `bitWord 01`). -/
theorem cantor_prefixSucc_surjective_not_injective :
    let w0 : BitWord 2 := fun _ => false
    let w1 : BitWord 2 := fun i => if i.1 = 0 then false else true
    w0 ≠ w1 ∧
      prefixSucc 1 w0 = prefixSucc 1 w1 ∧
      Function.Surjective (prefixSucc 1) := by
  intro w0 w1
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have h1 := congrFun heq ⟨1, by decide⟩
    simp [w0, w1] at h1
  · ext i
    fin_cases i
    rfl
  · intro w
    refine ⟨extendSucc 1 w false, ?_⟩
    exact prefixSucc_extendSucc 1 w false

/-! ## 3. Bidirectional Retraction--Section Tower & Faithful Noncommutative Colimit -/

/-- A bidirectional retraction--section tower over `(ℕ, ≤)` pairing upward fine-graining
embeddings `ι m n h : A m → A n` with downward coarse-graining projections
`π m n h : A n → A m` satisfying `π m n h (ι m n h x) = x`. -/
def BidirectionalRetractionSectionTower (A : ℕ → Type u) : Type u :=
  { p : (∀ m n : ℕ, m ≤ n → A m → A n) × (∀ m n : ℕ, m ≤ n → A n → A m) //
    (∀ m n : ℕ, (h : m ≤ n) → ∀ x : A m, p.2 m n h (p.1 m n h x) = x) ∧
    (∀ n : ℕ, ∀ x : A n, p.1 n n (le_refl n) x = x) ∧
    (∀ l m n : ℕ, (hlm : l ≤ m) → (hmn : m ≤ n) → ∀ x : A l,
      p.1 m n hmn (p.1 l m hlm x) = p.1 l n (le_trans hlm hmn) x) ∧
    (∀ n : ℕ, ∀ x : A n, p.2 n n (le_refl n) x = x) ∧
    (∀ l m n : ℕ, (hlm : l ≤ m) → (hmn : m ≤ n) → ∀ x : A n,
      p.2 l m hlm (p.2 m n hmn x) = p.2 l n (le_trans hlm hmn) x) }

namespace BidirectionalRetractionSectionTower

variable {A : ℕ → Type u}

def ι (T : BidirectionalRetractionSectionTower A) : ∀ m n : ℕ, m ≤ n → A m → A n :=
  T.val.1

def π (T : BidirectionalRetractionSectionTower A) : ∀ m n : ℕ, m ≤ n → A n → A m :=
  T.val.2

theorem retract (T : BidirectionalRetractionSectionTower A)
    (m n : ℕ) (h : m ≤ n) (x : A m) :
    T.π m n h (T.ι m n h x) = x :=
  T.property.1 m n h x

theorem ι_refl (T : BidirectionalRetractionSectionTower A) (n : ℕ) (x : A n) :
    T.ι n n (le_refl n) x = x :=
  T.property.2.1 n x

theorem ι_trans (T : BidirectionalRetractionSectionTower A)
    (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n) (x : A l) :
    T.ι m n hmn (T.ι l m hlm x) = T.ι l n (le_trans hlm hmn) x :=
  T.property.2.2.1 l m n hlm hmn x

theorem π_refl (T : BidirectionalRetractionSectionTower A) (n : ℕ) (x : A n) :
    T.π n n (le_refl n) x = x :=
  T.property.2.2.2.1 n x

theorem π_trans (T : BidirectionalRetractionSectionTower A)
    (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n) (x : A n) :
    T.π l m hlm (T.π m n hmn x) = T.π l n (le_trans hlm hmn) x :=
  T.property.2.2.2.2 l m n hlm hmn x

/-- Coarse-graining idempotent projector `P_{m,n} = ι_{m,n} ∘ π_{m,n}` on `A n`. -/
def coarseIdempotent (T : BidirectionalRetractionSectionTower A)
    (m n : ℕ) (h : m ≤ n) (y : A n) : A n :=
  T.ι m n h (T.π m n h y)

theorem ι_injective (T : BidirectionalRetractionSectionTower A)
    (m n : ℕ) (h : m ≤ n) : Function.Injective (T.ι m n h) := by
  intro x y hxy
  have h1 := congrArg (T.π m n h) hxy
  rw [T.retract m n h x, T.retract m n h y] at h1
  exact h1

theorem π_surjective (T : BidirectionalRetractionSectionTower A)
    (m n : ℕ) (h : m ≤ n) : Function.Surjective (T.π m n h) :=
  fun x => ⟨T.ι m n h x, T.retract m n h x⟩

theorem coarseIdempotent_idem (T : BidirectionalRetractionSectionTower A)
    (m n : ℕ) (h : m ≤ n) (y : A n) :
    T.coarseIdempotent m n h (T.coarseIdempotent m n h y) = T.coarseIdempotent m n h y := by
  unfold coarseIdempotent
  rw [T.retract]

theorem coarseIdempotent_fixes_embedded (T : BidirectionalRetractionSectionTower A)
    (m n : ℕ) (h : m ≤ n) (x : A m) :
    T.coarseIdempotent m n h (T.ι m n h x) = T.ι m n h x := by
  unfold coarseIdempotent
  rw [T.retract]

end BidirectionalRetractionSectionTower

/-- Any semiring tower with one-step left retractions embeds faithfully into Mathlib's
noncommutative `DirectLimitSuperClosure`. -/
theorem directLimitSuperClosure_faithful_of_retractions
    {Stage : ℕ → Type u} [∀ k, Semiring (Stage k)]
    (bond : ∀ k : ℕ, Stage k →+* Stage (k + 1))
    (ret : ∀ k : ℕ, Stage (k + 1) → Stage k)
    (hret : ∀ k : ℕ, ∀ s : Stage k, ret k (bond k s) = s)
    {m n : ℕ} (hmn : m ≤ n) (s_m : Stage m) :
    Function.Injective (directLimitOf bond n) ∧
      directLimitOf bond n (bondMap bond m n hmn s_m) = directLimitOf bond m s_m := by
  have hBondInj : ∀ k : ℕ, Function.Injective (bond k) := by
    intro k a b hab
    have h1 := congrArg (ret k) hab
    rw [hret k a, hret k b] at h1
    exact h1
  exact ⟨directLimitOf_injective bond hBondInj n, directLimitOf_bondMap bond m n hmn s_m⟩

/-! ## 4. Concrete 4D Dyadic Spacetime Refinement Tower (`16^n` Sites) -/

/-- Four-dimensional dyadic spacetime lattice at scale `n : ℕ`, with `(2^n)^4 = 16^n` sites. -/
abbrev SpacetimeLattice4D (n : ℕ) : Type :=
  Fin (2 ^ n) × Fin (2 ^ n) × Fin (2 ^ n) × Fin (2 ^ n)

/-- Cardinality scaling law for the 4D dyadic spacetime lattice: `|Λ_n| = 16 ^ n`. -/
theorem card_spacetimeLattice4D (n : ℕ) :
    Fintype.card (SpacetimeLattice4D n) = 16 ^ n := by
  simp only [SpacetimeLattice4D, Fintype.card_prod, Fintype.card_fin]
  repeat rw [← mul_pow]
  norm_num

/-- One-axis dyadic block coarsening `Fin (2 ^ n) → Fin (2 ^ m)` for `m ≤ n`. -/
def dyadicScaleDown {m n : ℕ} (h : m ≤ n) (i : Fin (2 ^ n)) : Fin (2 ^ m) :=
  ⟨i.1 / 2 ^ (n - m), by
    rw [Nat.div_lt_iff_lt_mul (pow_pos (by norm_num : 0 < 2) (n - m))]
    calc
      i.1 < 2 ^ n := i.2
      _ = 2 ^ (m + (n - m)) := by rw [Nat.add_sub_of_le h]
      _ = 2 ^ m * 2 ^ (n - m) := pow_add 2 m (n - m)⟩

/-- One-axis dyadic corner embedding `Fin (2 ^ m) → Fin (2 ^ n)` for `m ≤ n`. -/
def dyadicScaleUp {m n : ℕ} (h : m ≤ n) (j : Fin (2 ^ m)) : Fin (2 ^ n) :=
  ⟨j.1 * 2 ^ (n - m), by
    calc
      j.1 * 2 ^ (n - m) < 2 ^ m * 2 ^ (n - m) :=
        Nat.mul_lt_mul_of_pos_right j.2 (pow_pos (by norm_num : 0 < 2) (n - m))
      _ = 2 ^ (m + (n - m)) := (pow_add 2 m (n - m)).symm
      _ = 2 ^ n := by rw [Nat.add_sub_of_le h]⟩

theorem dyadicScaleDown_dyadicScaleUp {m n : ℕ} (h : m ≤ n) (j : Fin (2 ^ m)) :
    dyadicScaleDown h (dyadicScaleUp h j) = j := by
  ext
  simp [dyadicScaleDown, dyadicScaleUp,
    Nat.mul_div_cancel _ (pow_pos (by norm_num : 0 < 2) (n - m))]

theorem dyadicScaleDown_refl (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicScaleDown (le_refl n) i = i := by
  ext
  simp [dyadicScaleDown]

theorem dyadicScaleUp_refl (n : ℕ) (j : Fin (2 ^ n)) :
    dyadicScaleUp (le_refl n) j = j := by
  ext
  simp [dyadicScaleUp]

theorem dyadicScaleDown_trans {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (i : Fin (2 ^ n)) :
    dyadicScaleDown hlm (dyadicScaleDown hmn i) = dyadicScaleDown (le_trans hlm hmn) i := by
  ext
  simp only [dyadicScaleDown]
  rw [Nat.div_div_eq_div_mul, ← pow_add, show (n - m) + (m - l) = n - l by omega]

theorem dyadicScaleUp_trans {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (j : Fin (2 ^ l)) :
    dyadicScaleUp hmn (dyadicScaleUp hlm j) = dyadicScaleUp (le_trans hlm hmn) j := by
  ext
  simp only [dyadicScaleUp, mul_assoc, ← pow_add, show (m - l) + (n - m) = n - l by omega]

/-- 4D block-spin coordinate coarsening `Λ_n → Λ_m`. -/
def coord4Down {m n : ℕ} (h : m ≤ n) (x : SpacetimeLattice4D n) : SpacetimeLattice4D m :=
  (dyadicScaleDown h x.1, dyadicScaleDown h x.2.1, dyadicScaleDown h x.2.2.1, dyadicScaleDown h x.2.2.2)

/-- 4D dyadic corner section `Λ_m → Λ_n`. -/
def coord4Up {m n : ℕ} (h : m ≤ n) (y : SpacetimeLattice4D m) : SpacetimeLattice4D n :=
  (dyadicScaleUp h y.1, dyadicScaleUp h y.2.1, dyadicScaleUp h y.2.2.1, dyadicScaleUp h y.2.2.2)

theorem coord4Down_coord4Up {m n : ℕ} (h : m ≤ n) (y : SpacetimeLattice4D m) :
    coord4Down h (coord4Up h y) = y := by
  rcases y with ⟨t, x, y', z⟩
  simp [coord4Down, coord4Up, dyadicScaleDown_dyadicScaleUp]

/-- Real scalar field observable space on the 4D scale-`n` spacetime lattice (`dim = 16^n`). -/
abbrev Field4D (n : ℕ) : Type :=
  SpacetimeLattice4D n → ℝ

/-- Upward ℝ-linear block refinement embedding `Field4D m →ₗ[ℝ] Field4D n`. -/
def refineField4D {m n : ℕ} (h : m ≤ n) : Field4D m →ₗ[ℝ] Field4D n where
  toFun φ x := φ (coord4Down h x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Downward ℝ-linear lattice decimation `Field4D n →ₗ[ℝ] Field4D m`. -/
def coarseField4D {m n : ℕ} (h : m ≤ n) : Field4D n →ₗ[ℝ] Field4D m where
  toFun ψ y := ψ (coord4Up h y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coarseField4D_refineField4D {m n : ℕ} (h : m ≤ n) (φ : Field4D m) :
    coarseField4D h (refineField4D h φ) = φ := by
  ext y
  exact congrArg φ (coord4Down_coord4Up h y)

/-- Concrete 4D dyadic spacetime `BidirectionalRetractionSectionTower` on `Field4D`. -/
def spacetime4DRetractionSectionTower :
    BidirectionalRetractionSectionTower Field4D :=
  ⟨(fun _ _ h => refineField4D h, fun _ _ h => coarseField4D h),
   ⟨fun _ _ h φ => coarseField4D_refineField4D h φ,
    fun n φ => by
      ext x
      rcases x with ⟨t, x₁, x₂, x₃⟩
      simp [refineField4D, coord4Down, dyadicScaleDown_refl],
    fun l m n hlm hmn φ => by
      ext x
      rcases x with ⟨t, x₁, x₂, x₃⟩
      simp [refineField4D, coord4Down, dyadicScaleDown_trans],
    fun n ψ => by
      ext y
      rcases y with ⟨t, x₁, x₂, x₃⟩
      simp [coarseField4D, coord4Up, dyadicScaleUp_refl],
    fun l m n hlm hmn ψ => by
      ext y
      rcases y with ⟨t, x₁, x₂, x₃⟩
      simp [coarseField4D, coord4Up, dyadicScaleUp_trans]⟩⟩

/-- Additive directed system instance on the 4D dyadic field tower. -/
instance field4DDirectedSystem :
    DirectedSystem Field4D (fun _ _ h => (refineField4D h).toAddMonoidHom) where
  map_self n φ := by
    ext x
    rcases x with ⟨t, x₁, x₂, x₃⟩
    simp [refineField4D, coord4Down, dyadicScaleDown_refl]
  map_map l m n hlm hmn φ := by
    ext x
    rcases x with ⟨t, x₁, x₂, x₃⟩
    simp [refineField4D, coord4Down, dyadicScaleDown_trans]

/-- The algebraic continuum direct limit of 4D dyadic scalar fields over all refinement scales. -/
abbrev Field4DContinuum : Type :=
  AddCommGroup.DirectLimit Field4D (fun _ _ h => (refineField4D h).toAddMonoidHom)

/-- Every finite 4D lattice scale `Field4D n` embeds injectively into the 4D continuum direct
limit `Field4DContinuum`, and continuum functionals biject with coherent projective threads of
coarse-grained functionals across all 4D scales. -/
theorem field4DContinuum_faithful_and_dual_threads (n : ℕ) :
    Function.Injective
        (AddCommGroup.DirectLimit.of Field4D (fun _ _ h => (refineField4D h).toAddMonoidHom) n) ∧
      Nonempty
        ((Field4DContinuum →+ ℝ) ≃
          ConcreteProjectiveLimit (fun k => Field4D k →+ ℝ)
            (fun _ _ h (φ : Field4D _ →+ ℝ) =>
              φ.comp (refineField4D h).toAddMonoidHom)) := by
  have hinj : ∀ m k (h : m ≤ k),
      Function.Injective (refineField4D h).toAddMonoidHom := by
    intro m k h φ₁ φ₂ hφ
    have h₁ := congrArg (coarseField4D h) hφ
    simpa [coarseField4D_refineField4D h] using h₁
  have hOfInj :
      Function.Injective
        (AddCommGroup.DirectLimit.of Field4D
          (fun _ _ h => (refineField4D h).toAddMonoidHom) n) := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ0
    rcases AddCommGroup.DirectLimit.of.zero_exact
        (f := fun _ _ h => (refineField4D h).toAddMonoidHom) n φ hφ0 with ⟨k, hnk, hfk⟩
    exact hinj n k hnk (hfk.trans (map_zero _).symm)
  exact ⟨hOfInj,
    ⟨addCommGroupDirectLimitHomEquivProjectiveLimit
      Field4D (fun _ _ h => (refineField4D h).toAddMonoidHom) ℝ⟩⟩

/-! ## 5. Balaban Noncommutative Witness & Master 4D Colimit--Continuum Unification -/

/-- Explicit concrete fine precision matrix for two-stage Balaban coarse-graining. -/
def balabanFineA : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 1]

/-- Explicit concrete rectangular coarse-graining operator failing to commute with `balabanFineA`. -/
def balabanCoarseQ₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

/-- OpenGauss Trap T16 Noncommutativity Witness for `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem balabanFineA_mul_balabanCoarseQ₁_ne :
    balabanFineA * balabanCoarseQ₁ ≠ balabanCoarseQ₁ * balabanFineA := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  simp [balabanFineA, balabanCoarseQ₁, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Concrete noncommuting two-stage Balaban rectangular block coarse-graining realization
with positive definite precisions `A, R₁, R₂` and exact two-stage Schur inverse covariance
composition `twoStage_coarsePrecision_inv`. -/
theorem balaban_noncommuting_twoStage_witness :
    let A := balabanFineA
    let R₁ : Matrix (Fin 2) (Fin 2) ℝ := !![3, 1; 1, 2]
    let R₂ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]
    let Q₁ := balabanCoarseQ₁
    let Q₂ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]
    A.PosDef ∧ R₁.PosDef ∧ R₂.PosDef ∧
      A * Q₁ ≠ Q₁ * A ∧
      (coarsePrecision (coarsePrecision A R₁ Q₁) R₂ Q₂)⁻¹ =
        R₂⁻¹ + Q₂ * R₁⁻¹ * Q₂ᴴ + (Q₂ * Q₁) * A⁻¹ * (Q₂ * Q₁)ᴴ := by
  intro A R₁ R₂ Q₁ Q₂
  have hA : A.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [A, balabanFineA]
    · intro x hx
      have hsq : 0 ≤ x 0 ^ 2 ∧ 0 ≤ x 1 ^ 2 := ⟨sq_nonneg _, sq_nonneg _⟩
      have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra h
        push Not at h
        apply hx
        ext i
        fin_cases i <;> simp [h.1, h.2]
      simp [A, balabanFineA, dotProduct, mulVec, Fin.sum_univ_two]
      rcases hne with h0 | h1
      · have : 0 < x 0 ^ 2 := sq_pos_of_ne_zero h0
        linarith [hsq.2]
      · have : 0 < x 1 ^ 2 := sq_pos_of_ne_zero h1
        linarith [hsq.1]
  have hR₁ : R₁.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [R₁]
    · intro x hx
      have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra h
        push Not at h
        apply hx
        ext i
        fin_cases i <;> simp [h.1, h.2]
      have hform :
          star x ⬝ᵥ (R₁ *ᵥ x) =
            2 * x 0 ^ 2 + (x 0 + x 1) ^ 2 + x 1 ^ 2 := by
        simp [R₁, dotProduct, mulVec, Fin.sum_univ_two]
        ring
      rw [hform]
      have hsq : 0 ≤ (x 0 + x 1) ^ 2 := sq_nonneg _
      rcases hne with h0 | h1
      · have : 0 < x 0 ^ 2 := sq_pos_of_ne_zero h0
        have : 0 ≤ x 1 ^ 2 := sq_nonneg _
        linarith
      · have : 0 < x 1 ^ 2 := sq_pos_of_ne_zero h1
        have : 0 ≤ x 0 ^ 2 := sq_nonneg _
        linarith
  have hR₂ : R₂.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [R₂]
    · intro x hx
      have hsq : 0 ≤ x 0 ^ 2 ∧ 0 ≤ x 1 ^ 2 := ⟨sq_nonneg _, sq_nonneg _⟩
      have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra h
        push Not at h
        apply hx
        ext i
        fin_cases i <;> simp [h.1, h.2]
      simp [R₂, dotProduct, mulVec, Fin.sum_univ_two]
      rcases hne with h0 | h1
      · have : 0 < x 0 ^ 2 := sq_pos_of_ne_zero h0
        linarith [hsq.2]
      · have : 0 < x 1 ^ 2 := sq_pos_of_ne_zero h1
        linarith [hsq.1]
  exact ⟨hA, hR₁, hR₂, balabanFineA_mul_balabanCoarseQ₁_ne,
    twoStage_coarsePrecision_inv Q₁ Q₂ hA hR₁ hR₂⟩

/-- **Master 4D Colimit--Continuum Unification Theorem**:
Synthesizes across `lean/InfoGeometry/` in one theorem-bearing statement:
1. Universal `AddCommGroup.DirectLimit` $\leftrightarrow$ `ConcreteProjectiveLimit` Hom-duality;
2. 4D dyadic lattice scaling `|SpacetimeLattice4D n| = 16^n`, faithful embedding of `Field4D n`
   into `Field4DContinuum`, and coarse idempotence `coarseIdempotent`;
3. Contravariant Cantor prefix truncation asymmetry (`prefixSucc 1`);
4. 4D Amplituhedron boundary face retract (`truncateLastColumn ∘ amplituhedronInclusion = id`);
5. Zorn `(1,3)` UHF monoidal colimit naturality (`ZornUHFColimit.stageMul_naturality`);
6. Dense isometric union of noncommutative stage GNS Hilbert spaces inside `GNSHilbertColimit`. -/
theorem master_fourDim_colimit_continuum_unification
    (m n : ℕ) (hmn : m ≤ n) (y_n : Field4D n)
    (Ψ : Field4DContinuum →+ ℝ)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)] [∀ i, PartialOrder (Stage i)]
    [∀ i, StarOrderedRing (Stage i)]
    (sys : CStarStateColimit.Native.ContinuousStarInductiveSystem Stage)
    (ω : CStarStateColimit.Native.ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys) :
    let e := addCommGroupDirectLimitHomEquivProjectiveLimit
      Field4D (fun _ _ hab => (refineField4D hab).toAddMonoidHom) ℝ
    (e.symm (e Ψ) = Ψ) ∧
      Fintype.card (SpacetimeLattice4D n) = 16 ^ n ∧
      Function.Injective (spacetime4DRetractionSectionTower.ι m n hmn) ∧
      spacetime4DRetractionSectionTower.coarseIdempotent m n hmn
          (spacetime4DRetractionSectionTower.coarseIdempotent m n hmn y_n) =
        spacetime4DRetractionSectionTower.coarseIdempotent m n hmn y_n ∧
      Function.Surjective (prefixSucc 1) ∧
      (truncateLastColumn n).comp (amplituhedronInclusion n) = LinearMap.id ∧
      ((zornStageFunctor.map (homOfLE hmn) ⊗ₘ zornStageFunctor.map (homOfLE hmn)) ≫
          stageMul n =
        stageMul m ≫ zornStageFunctor.map (homOfLE hmn)) ∧
      Dense (⋃ i : I, Set.range (gnsStageToHilbertColimit Stage sys ω i)) := by
  intro e
  exact ⟨e.left_inv Ψ,
    card_spacetimeLattice4D n,
    spacetime4DRetractionSectionTower.ι_injective m n hmn,
    spacetime4DRetractionSectionTower.coarseIdempotent_idem m n hmn y_n,
    cantor_prefixSucc_surjective_not_injective.2.2,
    amplituhedron_boundary_retract n,
    stageMul_naturality (homOfLE hmn),
    dense_iUnion_range_gnsStageToHilbertColimit Stage sys ω⟩

end InfoGeometry.Categorical.FourDimColimitContinuumSynthesis
