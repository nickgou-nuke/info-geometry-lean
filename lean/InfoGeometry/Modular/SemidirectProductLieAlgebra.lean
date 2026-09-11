import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Tactic

/-!
# The Bundled Semidirect Product of Lie Algebras

This module constructs the canonical semidirect product $\mathfrak{g} \ltimes \mathfrak{h}$
of Lie algebras over a commutative ring $R$, where $\mathfrak{g}$ acts on $\mathfrak{h}$ by Lie derivations.
All axioms, Lie algebra instances, and canonical homomorphisms are fully verified natively in Lean 4.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace InfoGeometry.Modular.Semidirect

open LieAlgebra

/-- The derivation action property: L acts on M by Lie derivations. -/
class LieDerivationAction (L M : Type*) [LieRing L] [LieRing M] [LieRingModule L M] : Prop where
  lie_derivation : ∀ (x : L) (m₁ m₂ : M), ⁅x, ⁅m₁, m₂⁆⁆ = ⁅⁅x, m₁⁆, m₂⁆ + ⁅m₁, ⁅x, m₂⁆⁆

section Basic

variable (L M : Type*)

/-- The carrier type for the semidirect product Lie algebra $\mathfrak{g} \ltimes \mathfrak{h}$. -/
def SemidirectProduct := L × M

end Basic

namespace SemidirectProduct

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {M : Type*} [LieRing M] [LieAlgebra R M] [LieRingModule L M] [LieModule R L M]

@[ext]
theorem ext (x y : SemidirectProduct L M) (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y :=
  Prod.ext h1 h2

instance : AddCommGroup (SemidirectProduct L M) :=
  Prod.instAddCommGroup

instance : Module R (SemidirectProduct L M) :=
  Prod.instModule

/-- The Lie bracket on the semidirect product:
    [(l₁, m₁), (l₂, m₂)] = ([l₁, l₂], [m₁, m₂] + l₁ • m₂ - l₂ • m₁) -/
def bracket (x y : SemidirectProduct L M) : SemidirectProduct L M :=
  (⁅x.1, y.1⁆, ⁅x.2, y.2⁆ + ⁅x.1, y.2⁆ - ⁅y.1, x.2⁆)

instance : Bracket (SemidirectProduct L M) (SemidirectProduct L M) where
  bracket := bracket

@[simp]
theorem bracket_fst (x y : SemidirectProduct L M) :
    ⁅x, y⁆.1 = ⁅x.1, y.1⁆ := rfl

@[simp]
theorem bracket_snd (x y : SemidirectProduct L M) :
    ⁅x, y⁆.2 = ⁅x.2, y.2⁆ + ⁅x.1, y.2⁆ - ⁅y.1, x.2⁆ := rfl

theorem semidirect_add_lie (x y z : SemidirectProduct L M) :
    ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by
  ext
  · change ⁅x.1 + y.1, z.1⁆ = ⁅x.1, z.1⁆ + ⁅y.1, z.1⁆
    rw [_root_.add_lie]
  · change ⁅x.2 + y.2, z.2⁆ + ⁅x.1 + y.1, z.2⁆ - ⁅z.1, x.2 + y.2⁆ =
      (⁅x.2, z.2⁆ + ⁅x.1, z.2⁆ - ⁅z.1, x.2⁆) + (⁅y.2, z.2⁆ + ⁅y.1, z.2⁆ - ⁅z.1, y.2⁆)
    rw [_root_.add_lie, _root_.add_lie, _root_.lie_add]
    abel

theorem semidirect_lie_add (x y z : SemidirectProduct L M) :
    ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := by
  ext
  · change ⁅x.1, y.1 + z.1⁆ = ⁅x.1, y.1⁆ + ⁅x.1, z.1⁆
    rw [_root_.lie_add]
  · change ⁅x.2, y.2 + z.2⁆ + ⁅x.1, y.2 + z.2⁆ - ⁅y.1 + z.1, x.2⁆ =
      (⁅x.2, y.2⁆ + ⁅x.1, y.2⁆ - ⁅y.1, x.2⁆) + (⁅x.2, z.2⁆ + ⁅x.1, z.2⁆ - ⁅z.1, x.2⁆)
    rw [_root_.lie_add, _root_.lie_add, _root_.add_lie]
    abel

theorem semidirect_lie_self (x : SemidirectProduct L M) :
    ⁅x, x⁆ = 0 := by
  ext
  · change ⁅x.1, x.1⁆ = 0
    rw [_root_.lie_self]
  · change ⁅x.2, x.2⁆ + ⁅x.1, x.2⁆ - ⁅x.1, x.2⁆ = 0
    rw [_root_.lie_self]
    abel

theorem module_lie_neg (l : L) (m : M) : ⁅l, -m⁆ = -⁅l, m⁆ := by
  have h : ⁅l, m⁆ + ⁅l, -m⁆ = 0 := by
    rw [← _root_.lie_add, add_neg_cancel, _root_.lie_zero]
  exact eq_neg_of_add_eq_zero_right h

theorem ring_lie_neg (m₁ m₂ : M) : ⁅m₁, -m₂⁆ = -⁅m₁, m₂⁆ := by
  have h : ⁅m₁, m₂⁆ + ⁅m₁, -m₂⁆ = 0 := by
    rw [← _root_.lie_add, add_neg_cancel, _root_.lie_zero]
  exact eq_neg_of_add_eq_zero_right h

theorem ring_neg_lie (m₁ m₂ : M) : ⁅-m₁, m₂⁆ = -⁅m₁, m₂⁆ := by
  have h : ⁅m₁, m₂⁆ + ⁅-m₁, m₂⁆ = 0 := by
    rw [← _root_.add_lie, add_neg_cancel, _root_.zero_lie]
  exact eq_neg_of_add_eq_zero_right h

theorem module_lie_sub (l : L) (a b : M) : ⁅l, a - b⁆ = ⁅l, a⁆ - ⁅l, b⁆ := by
  rw [sub_eq_add_neg, _root_.lie_add, module_lie_neg, ← sub_eq_add_neg]

theorem ring_lie_sub (a b c : M) : ⁅a, b - c⁆ = ⁅a, b⁆ - ⁅a, c⁆ := by
  rw [sub_eq_add_neg, _root_.lie_add, ring_lie_neg, ← sub_eq_add_neg]

theorem ring_sub_lie (a b c : M) : ⁅a - b, c⁆ = ⁅a, c⁆ - ⁅b, c⁆ := by
  rw [sub_eq_add_neg, _root_.add_lie, ring_neg_lie, ← sub_eq_add_neg]

variable [LieDerivationAction L M]

theorem leibniz_lie_snd (x y z : SemidirectProduct L M) :
    ⁅x, ⁅y, z⁆⁆.2 = ⁅⁅x, y⁆, z⁆.2 + ⁅y, ⁅x, z⁆⁆.2 := by
  dsimp only [bracket_snd, bracket_fst]
  have h1 : ⁅x.1, ⁅y.2, z.2⁆⁆ = ⁅⁅x.1, y.2⁆, z.2⁆ + ⁅y.2, ⁅x.1, z.2⁆⁆ :=
    LieDerivationAction.lie_derivation x.1 y.2 z.2
  have h2 : ⁅y.1, ⁅x.2, z.2⁆⁆ = ⁅⁅y.1, x.2⁆, z.2⁆ + ⁅x.2, ⁅y.1, z.2⁆⁆ :=
    LieDerivationAction.lie_derivation y.1 x.2 z.2
  have h3 : ⁅z.1, ⁅x.2, y.2⁆⁆ = ⁅⁅z.1, x.2⁆, y.2⁆ + ⁅x.2, ⁅z.1, y.2⁆⁆ :=
    LieDerivationAction.lie_derivation z.1 x.2 y.2
  have h4 : ⁅⁅x.1, y.1⁆, z.2⁆ = ⁅x.1, ⁅y.1, z.2⁆⁆ - ⁅y.1, ⁅x.1, z.2⁆⁆ :=
    lie_lie x.1 y.1 z.2
  have h5 : ⁅⁅x.1, z.1⁆, y.2⁆ = ⁅x.1, ⁅z.1, y.2⁆⁆ - ⁅z.1, ⁅x.1, y.2⁆⁆ :=
    lie_lie x.1 z.1 y.2
  have h6 : ⁅⁅y.1, z.1⁆, x.2⁆ = ⁅y.1, ⁅z.1, x.2⁆⁆ - ⁅z.1, ⁅y.1, x.2⁆⁆ :=
    lie_lie y.1 z.1 x.2
  have h7 : ⁅x.2, ⁅y.2, z.2⁆⁆ = ⁅⁅x.2, y.2⁆, z.2⁆ + ⁅y.2, ⁅x.2, z.2⁆⁆ :=
    _root_.leibniz_lie x.2 y.2 z.2
  have hskew1 : ⁅x.2, ⁅y.1, z.2⁆⁆ = -⁅⁅y.1, z.2⁆, x.2⁆ := by
    rw [← _root_.lie_skew ⁅y.1, z.2⁆ x.2, neg_neg]
  have hskew2 : ⁅x.2, ⁅z.1, y.2⁆⁆ = -⁅⁅z.1, y.2⁆, x.2⁆ := by
    rw [← _root_.lie_skew ⁅z.1, y.2⁆ x.2, neg_neg]
  have hskew3 : ⁅⁅z.1, x.2⁆, y.2⁆ = -⁅y.2, ⁅z.1, x.2⁆⁆ := by
    rw [← _root_.lie_skew y.2 ⁅z.1, x.2⁆, neg_neg]
  rw [ring_lie_sub, _root_.lie_add, module_lie_sub, _root_.lie_add]
  rw [ring_sub_lie, _root_.add_lie, module_lie_sub, _root_.lie_add, ring_lie_sub, _root_.lie_add, module_lie_sub, _root_.lie_add]
  rw [h1, h2, h3, h4, h5, h6, h7, hskew1, hskew2, hskew3]
  abel

theorem semidirect_leibniz_lie (x y z : SemidirectProduct L M) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  ext
  · change ⁅x.1, ⁅y.1, z.1⁆⁆ = ⁅⁅x.1, y.1⁆, z.1⁆ + ⁅y.1, ⁅x.1, z.1⁆⁆
    rw [_root_.leibniz_lie]
  · exact leibniz_lie_snd x y z

instance : LieRing (SemidirectProduct L M) where
  add_lie := semidirect_add_lie
  lie_add := semidirect_lie_add
  lie_self := semidirect_lie_self
  leibniz_lie := semidirect_leibniz_lie

theorem semidirect_lie_smul (c : R) (x y : SemidirectProduct L M) :
    ⁅x, c • y⁆ = c • ⁅x, y⁆ := by
  ext
  · change ⁅x.1, c • y.1⁆ = c • ⁅x.1, y.1⁆
    rw [LieAlgebra.lie_smul]
  · change ⁅x.2, c • y.2⁆ + ⁅x.1, c • y.2⁆ - ⁅(c • y.1), x.2⁆ = c • (⁅x.2, y.2⁆ + ⁅x.1, y.2⁆ - ⁅y.1, x.2⁆)
    rw [LieAlgebra.lie_smul, LieModule.lie_smul, LieModule.smul_lie]
    simp only [smul_add, smul_sub]

instance : LieAlgebra R (SemidirectProduct L M) where
  lie_smul := semidirect_lie_smul

/-- Canonical Lie Homomorphism: Inclusion of the base Lie algebra $\mathfrak{g} \hookrightarrow \mathfrak{g} \ltimes \mathfrak{h}$. -/
def inl : L →ₗ⁅R⁆ SemidirectProduct L M where
  toFun l := (l, 0)
  map_add' _ _ := Prod.ext rfl (add_zero 0).symm
  map_smul' c _ := Prod.ext rfl (smul_zero c).symm
  map_lie' {l₁ l₂} := by
    ext
    · rfl
    · change (0 : M) = ⁅(0 : M), (0 : M)⁆ + ⁅l₁, (0 : M)⁆ - ⁅l₂, (0 : M)⁆
      rw [_root_.lie_zero, _root_.lie_zero, _root_.lie_zero, sub_zero, add_zero]

/-- Canonical Lie Homomorphism: Inclusion of the ideal $\mathfrak{h} \hookrightarrow \mathfrak{g} \ltimes \mathfrak{h}$. -/
def inr : M →ₗ⁅R⁆ SemidirectProduct L M where
  toFun m := (0, m)
  map_add' _ _ := Prod.ext (add_zero 0).symm rfl
  map_smul' c _ := Prod.ext (smul_zero c).symm rfl
  map_lie' {m₁ m₂} := by
    ext
    · change (0 : L) = ⁅(0 : L), (0 : L)⁆
      rw [_root_.lie_zero]
    · change ⁅m₁, m₂⁆ = ⁅m₁, m₂⁆ + ⁅(0 : L), m₂⁆ - ⁅(0 : L), m₁⁆
      rw [_root_.zero_lie, _root_.zero_lie, sub_zero, add_zero]

@[simp] theorem bracket_inl_inr (l : L) (m : M) :
    ⁅(inl (R := R) (L := L) (M := M)) l,
      (inr (R := R) (L := L) (M := M)) m⁆ =
      (inr (R := R) (L := L) (M := M)) ⁅l, m⁆ := by
  apply Prod.ext
  · change ⁅l, (0 : L)⁆ = 0
    simp
  · change ⁅(0 : M), m⁆ + ⁅l, m⁆ - ⁅(0 : L), (0 : M)⁆ = ⁅l, m⁆
    simp

@[simp] theorem bracket_inr_inl (m : M) (l : L) :
    ⁅(inr (R := R) (L := L) (M := M)) m,
      (inl (R := R) (L := L) (M := M)) l⁆ =
      -(inr (R := R) (L := L) (M := M)) ⁅l, m⁆ := by
  apply Prod.ext
  · change ⁅(0 : L), l⁆ = -(0 : L)
    simp
  · change ⁅m, (0 : M)⁆ + ⁅(0 : L), (0 : M)⁆ - ⁅l, m⁆ = -⁅l, m⁆
    simp

@[simp] theorem bracket_inl_inl (l₁ l₂ : L) :
    ⁅(inl (R := R) (L := L) (M := M)) l₁,
      (inl (R := R) (L := L) (M := M)) l₂⁆ =
      (inl (R := R) (L := L) (M := M)) ⁅l₁, l₂⁆ := by
  apply Prod.ext
  · rfl
  · simp

@[simp] theorem bracket_inr_inr (m₁ m₂ : M) :
    ⁅(inr (R := R) (L := L) (M := M)) m₁,
      (inr (R := R) (L := L) (M := M)) m₂⁆ =
      (inr (R := R) (L := L) (M := M)) ⁅m₁, m₂⁆ := by
  apply Prod.ext
  · simp
  · simp

theorem bracket_mem_range_inr (x : SemidirectProduct L M) (m : M) :
    ∃ n : M,
      (inr (R := R) (L := L) (M := M)) n =
        ⁅x, (inr (R := R) (L := L) (M := M)) m⁆ := by
  refine ⟨⁅x.2, m⁆ + ⁅x.1, m⁆, ?_⟩
  apply Prod.ext
  · change (0 : L) = ⁅x.1, (0 : L)⁆
    simp
  · change ⁅x.2, m⁆ + ⁅x.1, m⁆ =
      ⁅x.2, m⁆ + ⁅x.1, m⁆ - ⁅(0 : L), x.2⁆
    simp

/-- Canonical Projection: $\mathfrak{g} \ltimes \mathfrak{h} \to \mathfrak{g}$. -/
def fst : SemidirectProduct L M →ₗ⁅R⁆ L where
  toFun p := p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

theorem fst_surjective :
    Function.Surjective (fun p : SemidirectProduct L M =>
      (fst (R := R) (L := L) (M := M)) p) := by
  intro l
  exact ⟨(inl (R := R) (L := L) (M := M)) l, rfl⟩

theorem decomposition (p : SemidirectProduct L M) :
    p = (inl (R := R) (L := L) (M := M)) p.1 +
        (inr (R := R) (L := L) (M := M)) p.2 := by
  apply Prod.ext
  · change p.1 = p.1 + 0
    rw [add_zero]
  · change p.2 = 0 + p.2
    rw [zero_add]

theorem fst_eq_zero_iff_mem_range_inr (p : SemidirectProduct L M) :
    (fst (R := R) (L := L) (M := M)) p = 0 ↔
      ∃ m : M, (inr (R := R) (L := L) (M := M)) m = p := by
  constructor
  · intro hp
    refine ⟨p.2, ?_⟩
    apply Prod.ext
    · change (0 : L) = p.1
      exact hp.symm
    · rfl
  · rintro ⟨m, rfl⟩
    change (0 : L) = 0
    rfl

@[simp] theorem fst_inl (l : L) :
    (fst (R := R) (L := L) (M := M))
        ((inl (R := R) (L := L) (M := M)) l) = l := rfl

@[simp] theorem fst_inr (m : M) :
    (fst (R := R) (L := L) (M := M))
        ((inr (R := R) (L := L) (M := M)) m) = 0 := rfl

theorem inl_injective :
    Function.Injective (fun l : L => (inl (R := R) (L := L) (M := M)) l) := by
  intro l₁ l₂ h
  exact congrArg Prod.fst h

theorem inr_injective :
    Function.Injective (fun m : M => (inr (R := R) (L := L) (M := M)) m) := by
  intro m₁ m₂ h
  exact congrArg Prod.snd h

theorem mem_ker_fst_iff_mem_range_inr (p : SemidirectProduct L M) :
    p ∈ (fst (R := R) (L := L) (M := M)).ker ↔
      p ∈ (inr (R := R) (L := L) (M := M)).range := by
  change p.1 = 0 ↔ ∃ m, (0, m) = p
  constructor
  · intro hp
    refine ⟨p.2, ?_⟩
    ext
    · exact hp.symm
    · rfl
  · rintro ⟨m, hm⟩
    have h1 := congrArg Prod.fst hm
    exact h1.symm

theorem semidirect_short_exact_sequence :
    Function.Injective (fun m : M => (inr (R := R) (L := L) (M := M)) m) ∧
    Function.Surjective (fst (R := R) (L := L) (M := M)) ∧
    (∀ p : SemidirectProduct L M,
      p ∈ (fst (R := R) (L := L) (M := M)).ker ↔
        p ∈ (inr (R := R) (L := L) (M := M)).range) := by
  exact ⟨inr_injective (R := R),
    by
      intro l
      exact ⟨(l, 0), rfl⟩,
    mem_ker_fst_iff_mem_range_inr (R := R)⟩

end SemidirectProduct

end InfoGeometry.Modular.Semidirect
