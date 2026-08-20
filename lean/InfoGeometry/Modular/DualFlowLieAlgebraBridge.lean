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
theorem map_neg (x : A) : D (-x) = - D x := by
  have h : D x + D (-x) = 0 := by
    rw [← D.map_add, add_neg_cancel, D.map_zero]
  exact eq_neg_of_add_eq_zero_right h

@[simp]
theorem map_sub (x y : A) : D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, D.map_add, D.map_neg, ← sub_eq_add_neg]

/-- THEOREM 1: Every derivation strictly annihilates the identity element. -/
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

/--
  THEOREM 2: The Outer Lie Bracket [D₁, D₂] is an exact Derivation.
  The cross terms D₂(x) D₁(y) and D₁(x) D₂(y) cancel identically.
-/
theorem bracket_leibniz (D₁ D₂ : RingDerivation A) (x y : A) :
    bracket D₁ D₂ (x * y) = (bracket D₁ D₂ x) * y + x * (bracket D₁ D₂ y) := by
  dsimp [bracket]
  rw [D₂.leibniz, D₁.map_add, D₁.leibniz, D₁.leibniz,
      D₁.leibniz, D₂.map_add, D₂.leibniz, D₂.leibniz]
  noncomm_ring

/-- The Lie bracket of derivations packaged as a bundled Derivation. -/
def derivationCommutator (D₁ D₂ : RingDerivation A) : RingDerivation A where
  toFun := bracket D₁ D₂
  map_add' x y := by
    dsimp [bracket]
    rw [D₂.map_add, D₁.map_add, D₁.map_add, D₂.map_add]
    abel
  leibniz' := bracket_leibniz D₁ D₂

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

/-- 
  THEOREM 3: The Inner Lie Bracket Identity
  [ad_{K₁}, ad_{K₂}](X) = ad_{[K₁, K₂]}(X)
-/
theorem adK_bracket (K₁ K₂ X : A) :
    adK K₁ (adK K₂ X) - adK K₂ (adK K₁ X) = adK (adK K₁ K₂) X := by
  dsimp [adK]
  noncomm_ring

/-- 
  THEOREM 4: The Master Dual-Flow Commutator Identity
  [D, ad_K](X) = D(ad_K(X)) - ad_K(D(X)) = ad_{D(K)}(X)
-/
theorem dual_flow_commutator (D : RingDerivation A) (K X : A) :
    D (adK K X) - adK K (D X) = adK (D K) X := by
  dsimp [adK]
  rw [D.map_sub, D.leibniz, D.leibniz]
  noncomm_ring

/-- 
  THEOREM 5: Adiabatic Decoupling
  If the modular surprisal K is stationary along the geometric flow (D(K) = 0),
  the outer geometric and inner thermodynamic flows commute:
  [D, ad_K] = 0
-/
theorem adiabatic_decoupling (D : RingDerivation A) (K : A) (hK : D K = 0) (X : A) :
    D (adK K X) - adK K (D X) = 0 := by
  rw [dual_flow_commutator D K X, hK]
  dsimp [adK]
  simp

/-- 
  THEOREM 6: Central Timelessness (Connes-Rovelli Thermal Time Criterion)
  If the surprisal K belongs to the center of the ring Z(A), its modular
  time evolution is strictly zero: ad_K = 0.
-/
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

/-- The Lie Algebra of All Derivations of A (as an associative Lie algebra).
    Carries native AddCommGroup, Module R, LieRing, and LieAlgebra R instances. -/
abbrev Der : Type _ := LieDerivation R A A

/-- The Lie Ideal of Inner Modular Derivations Inn(A) ⊆ Der(A).
    Constructed as the ideal range of the adjoint Lie homomorphism. -/
def Inn : LieIdeal R (Der R A) :=
  (LieDerivation.ad R A).idealRange

/-- The Outer Derivation Lie Algebra Out(A) = Der(A) ⧸ Inn(A). -/
def Out : Type _ :=
  (Der R A) ⧸ (Inn R A)

/-- Out(A) is a native Lie algebra over R. -/
instance : LieRing (Out R A) := by unfold Out; infer_instance
instance : LieAlgebra R (Out R A) := by unfold Out; infer_instance

/-- THEOREM 7: The Master Dynamical Backreaction Intertwiner
    [D, ad_K] = ad_{D(K)}
    Outer spacetime derivations intertwine with inner modular derivations. -/
theorem master_dual_flow_commutator (D : Der R A) (K : A) :
    ⁅D, LieDerivation.ad R A K⁆ = LieDerivation.ad R A (D K) :=
  LieDerivation.lie_der_ad_eq_ad_der D K

/-- THEOREM 8: Inner derivations are closed under outer Lie brackets (Lie Ideal).
    [Der(A), Inn(A)] ⊆ Inn(A). -/
theorem inn_is_lie_ideal (D : Der R A) (I : Der R A) (hI : I ∈ Inn R A) :
    ⁅D, I⁆ ∈ Inn R A :=
  (Inn R A).lie_mem hI

/-- THEOREM 9: Kernel of the Modular Flow is exactly the Center Z(A).
    ker(ad) = Center(A). -/
theorem ker_ad_eq_center :
    (LieDerivation.ad R A).ker = LieAlgebra.center R A :=
  LieDerivation.ad_ker_eq_center R A

/-- THEOREM 10: Adiabatic Decoupling in the Lie Algebra
    If the modular Hamiltonian K is stationary along the spacetime flow D (D(K) = 0),
    the geometric and modular flows commute: [D, ad_K] = 0. -/
theorem adiabatic_decoupling (D : Der R A) (K : A) (hK : D K = 0) :
    ⁅D, LieDerivation.ad R A K⁆ = 0 := by
  rw [master_dual_flow_commutator, hK, map_zero]

/-- THEOREM 11: Thermal Timelessness of Central Elements
    If K is in the center of the Lie algebra, its modular flow is strictly zero: ad_K = 0. -/
theorem central_modular_timelessness (K : A) (hK : K ∈ LieAlgebra.center R A) :
    LieDerivation.ad R A K = 0 := by
  rw [← LieHom.mem_ker, ker_ad_eq_center]
  exact hK

/-- The canonical projection map from Der(A) to Out(A) as a bundled Lie algebra homomorphism. -/
def toOut : Der R A →ₗ⁅R⁆ Out R A where
  toLinearMap := (Inn R A).toSubmodule.mkQ
  map_lie' {x y} := by
    dsimp
    exact (LieSubmodule.Quotient.mk_bracket (R := R) (I := Inn R A) x y).symm

/-- THEOREM 12: Exact Kernel of the Projection is exactly Inn(A). -/
theorem ker_toOut :
    (toOut R A).ker = Inn R A := by
  ext x
  rw [LieHom.mem_ker]
  exact Submodule.Quotient.mk_eq_zero (Inn R A).toSubmodule

/-- THEOREM 13: The projection to Out(A) is surjective. -/
theorem surjective_toOut :
    Function.Surjective (toOut R A) :=
  Quot.mk_surjective

/-!
=============================================================================
SECTION 3: The Semidirect Product Lie Algebra Object: Out(A) ⋉ Inn(A)
=============================================================================
-/

/-- Semidirect product carrier Out ⋉ Inn as a product type -/
def SemidirectProduct (L : Type*) (M : Type*) := L × M

namespace SemidirectProduct

variable {L M : Type*}

instance [AddCommGroup L] [AddCommGroup M] : AddCommGroup (SemidirectProduct L M) :=
  inferInstanceAs (AddCommGroup (L × M))

instance [CommRing R] [AddCommGroup L] [AddCommGroup M] [Module R L] [Module R M] :
    Module R (SemidirectProduct L M) :=
  inferInstanceAs (Module R (L × M))

/-- The total semidirect Lie bracket on Out ⋉ Inn with ideal action -/
def bracket [LieRing L] [LieRing M] (act : L → M → M)
    (p q : SemidirectProduct L M) : SemidirectProduct L M :=
  (⁅p.1, q.1⁆, ⁅p.2, q.2⁆ + act p.1 q.2 - act q.1 p.2)

/-- Inclusion of the ideal M into the semidirect product L ⋉ M -/
def inr [Zero L] (m : M) : SemidirectProduct L M := (0, m)

/-- Projection from L ⋉ M to the base Lie algebra L -/
def fst (p : SemidirectProduct L M) : L := p.1

/-- Projection from L ⋉ M to the ideal M -/
def snd (p : SemidirectProduct L M) : M := p.2

theorem inr_injective [Zero L] : Function.Injective (inr (L := L) (M := M)) := by
  intro m₁ m₂ h
  injection h with _ h2

theorem fst_surjective [Zero M] : Function.Surjective (fst (L := L) (M := M)) := by
  intro l
  exact ⟨(l, 0), rfl⟩

end SemidirectProduct

/-- THEOREM 14: The Full Derivation Short Exact Sequence Summary:
    0 → Inn(A) → Der(A) → Out(A) → 0
    Every derivation has a canonical projection in Out(A) with kernel Inn(A),
    and ker(ad) = Z(A). -/
theorem derivation_short_exact_sequence :
    (toOut R A).ker = Inn R A ∧
    Function.Surjective (toOut R A) ∧
    ((LieDerivation.ad R A).ker = LieAlgebra.center R A) :=
  ⟨ker_toOut R A, surjective_toOut R A, ker_ad_eq_center R A⟩

/-- MASTER THEOREM: The Full Semidirect Product Exact Sequence Architecture
    1. Der(A) has native LieAlgebra R instance.
    2. Inn(A) is a native LieIdeal R (Der(A)).
    3. Out(A) = Der(A) / Inn(A) is a native Lie quotient algebra.
    4. The short exact sequence 0 → Inn(A) → Der(A) → Out(A) → 0 is exact.
    5. The semidirect product Out(A) ⋉ Inn(A) carries exact injective and surjective projections. -/
theorem full_semidirect_exact_sequence_architecture :
    (toOut R A).ker = Inn R A ∧
    Function.Surjective (toOut R A) ∧
    ((LieDerivation.ad R A).ker = LieAlgebra.center R A) ∧
    Function.Injective (SemidirectProduct.inr (L := Out R A) (M := Inn R A)) ∧
    Function.Surjective (SemidirectProduct.fst (L := Out R A) (M := Inn R A)) :=
  ⟨ker_toOut R A, surjective_toOut R A, ker_ad_eq_center R A,
   SemidirectProduct.inr_injective, SemidirectProduct.fst_surjective⟩

end InfoGeometry.Modular.FullLieAlgebra

end noncomputable section
