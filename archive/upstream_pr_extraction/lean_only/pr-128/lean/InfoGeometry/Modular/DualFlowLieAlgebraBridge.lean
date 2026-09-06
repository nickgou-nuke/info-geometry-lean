import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Center
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Ideal
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.Derivation.AdjointAction
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Modular.LieAlgebra

/-!
=============================================================================
SECTION 1: Elementary Ring Derivations and Pointwise Commutator Closure
=============================================================================
-/

/-- An additive endomorphism D on a ring A satisfying the Leibniz rule. -/
structure RingDerivation (A : Type*) [Ring A] where
  toFun : A → A
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

namespace RingDerivation

variable {A : Type*} [Ring A]

instance : CoeFun (RingDerivation A) (fun _ => A → A) where
  coe D := D.toFun

variable (D : RingDerivation A)

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem leibniz (x y : A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 + D 0 = D 0 + 0 := by
    rw [← D.map_add, add_zero, add_zero]
  exact add_left_cancel h

@[simp]
theorem map_neg (x : A) :
    D (-x) = - D x := by
  have h : D x + D (-x) = 0 := by
    rw [← D.map_add, add_neg_cancel, D.map_zero]
  exact eq_neg_of_add_eq_zero_right h

@[simp]
theorem map_sub (x y : A) :
    D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, D.map_add, D.map_neg, ← sub_eq_add_neg]

@[simp]
theorem map_one : D 1 = 0 := by
  have h : D 1 + D 1 = D 1 + 0 := by
    calc D 1 + D 1
      _ = D 1 * 1 + 1 * D 1 := by rw [mul_one, one_mul]
      _ = D (1 * 1) := (D.leibniz 1 1).symm
      _ = D 1 := by rw [mul_one]
      _ = D 1 + 0 := by rw [add_zero]
  exact add_left_cancel h

/-- The Lie Bracket (Commutator) of two derivations: [D₁, D₂] = D₁ ∘ D₂ - D₂ ∘ D₁. -/
def bracket (D₁ D₂ : RingDerivation A) (x : A) : A :=
  D₁ (D₂ x) - D₂ (D₁ x)

/-- The Outer Lie Bracket [D₁, D₂] is an exact Derivation. -/
theorem bracket_leibniz (D₁ D₂ : RingDerivation A) (x y : A) :
    bracket D₁ D₂ (x * y) = (bracket D₁ D₂ x) * y + x * (bracket D₁ D₂ y) := by
  dsimp [bracket]
  rw [D₂.leibniz, D₁.map_add, D₁.leibniz, D₁.leibniz,
      D₁.leibniz, D₂.map_add, D₂.leibniz, D₂.leibniz]
  noncomm_ring

theorem bracket_skew (D₁ D₂ : RingDerivation A) (x : A) :
    bracket D₁ D₂ x = -bracket D₂ D₁ x := by
  dsimp [bracket]
  abel

@[simp]
theorem bracket_self (D : RingDerivation A) (x : A) :
    bracket D D x = 0 := by
  dsimp [bracket]
  abel


/-- The Lie bracket of derivations packaged as a bundled Derivation. -/
def derivationCommutator (D₁ D₂ : RingDerivation A) : RingDerivation A where
  toFun := bracket D₁ D₂
  map_add' x y := by
    dsimp [bracket]
    rw [D₂.map_add, D₁.map_add, D₁.map_add, D₂.map_add]
    abel
  leibniz' := bracket_leibniz D₁ D₂

@[simp]
theorem derivationCommutator_apply (D₁ D₂ : RingDerivation A) (x : A) :
    derivationCommutator D₁ D₂ x = bracket D₁ D₂ x := rfl

theorem bracket_jacobi (D₁ D₂ D₃ : RingDerivation A) (x : A) :
    bracket D₁ (derivationCommutator D₂ D₃) x +
        bracket D₂ (derivationCommutator D₃ D₁) x +
        bracket D₃ (derivationCommutator D₁ D₂) x = 0 := by
  dsimp [bracket, derivationCommutator]
  rw [D₁.map_sub, D₂.map_sub, D₃.map_sub]
  abel

end RingDerivation

variable {A : Type*} [Ring A]

/-- The Inner Modular Generator: ad_K(X) = [K, X] = K * X - X * K. -/
def adK (K : A) (X : A) : A :=
  K * X - X * K

@[simp] theorem adK_apply (K X : A) : adK K X = K * X - X * K := rfl

/-- The modular commutator packaged as a bundled Derivation on A. -/
def modularDerivation (K : A) : RingDerivation A where
  toFun := adK K
  map_add' x y := by
    dsimp [adK]
    simp only [mul_add, add_mul]
    abel
  leibniz' x y := by
    dsimp [adK]
    calc
      K * (x * y) - (x * y) * K
        = (K * x * y - x * K * y) + (x * K * y - x * y * K) := by
          simp only [mul_assoc]
          abel
      _ = (K * x - x * K) * y + x * (K * y - y * K) := by
          simp only [sub_mul, mul_sub, mul_assoc]

theorem adK_bracket (K₁ K₂ X : A) :
    adK K₁ (adK K₂ X) - adK K₂ (adK K₁ X) = adK (adK K₁ K₂) X := by
  dsimp [adK]
  noncomm_ring

theorem dual_flow_commutator (D : RingDerivation A) (K X : A) :
    D (adK K X) - adK K (D X) = adK (D K) X := by
  dsimp [adK]
  rw [D.map_sub, D.leibniz, D.leibniz]
  noncomm_ring

theorem bracket_modularDerivation (D : RingDerivation A) (K X : A) :
    RingDerivation.bracket D (modularDerivation K) X = adK (D K) X := by
  dsimp [RingDerivation.bracket, modularDerivation]
  exact dual_flow_commutator D K X

theorem bracket_modularDerivations (K₁ K₂ X : A) :
    RingDerivation.bracket (modularDerivation K₁) (modularDerivation K₂) X =
      adK (adK K₁ K₂) X := by
  dsimp [RingDerivation.bracket, modularDerivation]
  exact adK_bracket K₁ K₂ X

theorem adiabatic_decoupling (D : RingDerivation A) (K : A) (hK : D K = 0) (X : A) :
    D (adK K X) - adK K (D X) = 0 := by
  rw [dual_flow_commutator D K X, hK]
  dsimp [adK]
  simp

theorem central_modular_timelessness (K : A) (h_central : ∀ x, K * x = x * K) (X : A) :
    adK K X = 0 := by
  dsimp [adK]
  rw [h_central X, sub_self]

end InfoGeometry.Modular.LieAlgebra

/-!
=============================================================================
SECTION 2: The Full Native Mathlib Lie Algebra and Lie Ideal Structure
=============================================================================
-/

namespace InfoGeometry.Modular.FullLieAlgebra

variable (R : Type*) [CommRing R]
variable (A : Type*) [Ring A] [Algebra R A]

abbrev Der : Type _ := LieDerivation R A A

def Inn : LieIdeal R (Der R A) :=
  (LieDerivation.ad R A).idealRange

def Out : Type _ :=
  (Der R A) ⧸ (Inn R A)

instance : LieRing (Out R A) := by unfold Out; infer_instance
instance : LieAlgebra R (Out R A) := by unfold Out; infer_instance

theorem master_dual_flow_commutator (D : Der R A) (K : A) :
    ⁅D, LieDerivation.ad R A K⁆ = LieDerivation.ad R A (D K) :=
  LieDerivation.lie_der_ad_eq_ad_der D K

theorem inn_is_lie_ideal (D : Der R A) (I : Der R A) (hI : I ∈ Inn R A) :
    ⁅D, I⁆ ∈ Inn R A :=
  (Inn R A).lie_mem hI

theorem ker_ad_eq_center :
    (LieDerivation.ad R A).ker = LieAlgebra.center R A :=
  LieDerivation.ad_ker_eq_center R A

theorem ad_eq_zero_iff_mem_center (K : A) :
    LieDerivation.ad R A K = 0 ↔ K ∈ LieAlgebra.center R A := by
  rw [← LieHom.mem_ker, ker_ad_eq_center]

theorem adiabatic_decoupling (D : Der R A) (K : A) (hK : D K = 0) :
    ⁅D, LieDerivation.ad R A K⁆ = 0 := by
  rw [master_dual_flow_commutator, hK, map_zero]

theorem central_modular_timelessness (K : A) (hK : K ∈ LieAlgebra.center R A) :
    LieDerivation.ad R A K = 0 := by
  rw [← LieHom.mem_ker, ker_ad_eq_center]
  exact hK

def toOut : Der R A →ₗ⁅R⁆ Out R A where
  toLinearMap := (Inn R A).toSubmodule.mkQ
  map_lie' {x y} := by
    dsimp
    exact (LieSubmodule.Quotient.mk_bracket (R := R) (I := Inn R A) x y).symm

theorem ker_toOut :
    (toOut R A).ker = Inn R A := by
  ext x
  rw [LieHom.mem_ker]
  exact Submodule.Quotient.mk_eq_zero (Inn R A).toSubmodule

theorem surjective_toOut :
    Function.Surjective (toOut R A) :=
  Quot.mk_surjective

theorem toOut_eq_zero_iff_mem_Inn (D : Der R A) :
    toOut R A D = 0 ↔ D ∈ Inn R A := by
  rw [← LieHom.mem_ker, ker_toOut]

theorem derivation_short_exact_sequence :
    (toOut R A).ker = Inn R A ∧
    Function.Surjective (toOut R A) ∧
    ((LieDerivation.ad R A).ker = LieAlgebra.center R A) :=
  ⟨ker_toOut R A, surjective_toOut R A, ker_ad_eq_center R A⟩

/-!
=============================================================================
SECTION 3: Fully Instantiated Lie Algebra Product Object: Out(A) × Inn(A)
=============================================================================
-/

/-- The fully instantiated Lie Algebra Product Out(A) × Inn(A) with native LieRing and LieAlgebra instances. -/
def LieProduct (L M : Type*) := L × M

namespace LieProduct

variable {L M : Type*} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

instance : Bracket (L × M) (L × M) where
  bracket p q := (⁅p.1, q.1⁆, ⁅p.2, q.2⁆)

@[simp] lemma bracket_apply (p q : L × M) : ⁅p, q⁆ = (⁅p.1, q.1⁆, ⁅p.2, q.2⁆) := rfl

instance : LieRing (L × M) where
  add_lie p q r := by
    ext
    · exact add_lie p.1 q.1 r.1
    · exact add_lie p.2 q.2 r.2
  lie_add p q r := by
    ext
    · exact lie_add p.1 q.1 r.1
    · exact lie_add p.2 q.2 r.2
  lie_self p := by
    ext
    · exact lie_self p.1
    · exact lie_self p.2
  leibniz_lie p q r := by
    ext
    · exact leibniz_lie p.1 q.1 r.1
    · exact leibniz_lie p.2 q.2 r.2

instance : LieAlgebra R (L × M) where
  lie_smul r p q := by
    ext
    · exact LieAlgebra.lie_smul r p.1 q.1
    · exact LieAlgebra.lie_smul r p.2 q.2

/-- Canonical projection as a bundled Lie algebra homomorphism -/
def fstHom : (L × M) →ₗ⁅R⁆ L where
  toFun p := p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {_ _} := rfl

theorem fstHom_surjective : Function.Surjective (fstHom (R := R) (L := L) (M := M)) := by
  intro l
  exact ⟨(l, 0), rfl⟩

/-- Canonical inclusion as a bundled Lie algebra homomorphism -/
def inrHom : M →ₗ⁅R⁆ (L × M) where
  toFun m := (0, m)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  map_lie' {_ _} := by ext <;> simp

theorem inrHom_injective : Function.Injective (inrHom (R := R) (L := L) (M := M)) := by
  intro m₁ m₂ h
  injection h with _ h2

/-- Exactness: the kernel of fstHom is the range of inrHom -/
theorem mem_ker_fstHom_iff_mem_range_inrHom (p : L × M) :
    p ∈ (fstHom (R := R) (L := L) (M := M)).ker ↔ p ∈ (inrHom (R := R) (L := L) (M := M)).range := by
  rw [LieHom.mem_ker, LieHom.mem_range]
  constructor
  · intro hp
    dsimp [fstHom] at hp
    refine ⟨p.2, ?_⟩
    ext
    · exact hp.symm
    · rfl
  · rintro ⟨m, hm⟩
    have h1 := congr_arg Prod.fst hm
    exact h1.symm

end LieProduct

/-- MASTER THEOREM: The Full Lie Algebra Product Exact Sequence Architecture
    1. Der(A) has native LieAlgebra R instance.
    2. Inn(A) is a native LieIdeal R (Der(A)).
    3. Out(A) = Der(A) / Inn(A) is a native Lie quotient algebra.
    4. The short exact sequence 0 → Inn(A) → Der(A) → Out(A) → 0 is exact.
    5. The product Lie algebra Out(A) × Inn(A) carries exact injective and surjective Lie homomorphisms. -/
theorem full_lie_product_exact_sequence_architecture :
    (toOut R A).ker = Inn R A ∧
    Function.Surjective (toOut R A) ∧
    ((LieDerivation.ad R A).ker = LieAlgebra.center R A) ∧
    Function.Surjective (LieProduct.fstHom (R := R) (L := Out R A) (M := Inn R A)) ∧
    Function.Injective (LieProduct.inrHom (R := R) (L := Out R A) (M := Inn R A)) ∧
    (∀ p : Out R A × Inn R A,
      p ∈ (LieProduct.fstHom (R := R) (L := Out R A) (M := Inn R A)).ker ↔
      p ∈ (LieProduct.inrHom (R := R) (L := Out R A) (M := Inn R A)).range) :=
  ⟨ker_toOut R A, surjective_toOut R A, ker_ad_eq_center R A,
   LieProduct.fstHom_surjective (R := R),
   LieProduct.inrHom_injective (R := R),
   LieProduct.mem_ker_fstHom_iff_mem_range_inrHom (R := R)⟩

end InfoGeometry.Modular.FullLieAlgebra

end noncomputable section
