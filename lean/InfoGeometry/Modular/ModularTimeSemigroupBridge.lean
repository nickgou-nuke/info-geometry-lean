import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Modular Time, Inner/Outer Derivations, and the Dynamical Semigroup

This module formalizes:
1. The Modular Hamiltonian Generator (Reversible Inner Derivation):
     ad_K(X) = [K, X] = K * X - X * K
2. The Total Open Dynamical Generator (Modular Flow + Dissipation):
     ℒ(X) = ad_K(X) + 𝒟(X)
3. The Master Semigroup Backreaction Theorem:
     [D, ℒ](X) = ad_{D(K)}(X) + [D, 𝒟](X)
4. Geometric Decoupling: If the dissipative channel is geometrically invariant ([D, 𝒟] = 0),
   the geometric shear pumps the semigroup strictly via the modular surprisal derivative:
     [D, ℒ](X) = ad_{D(K)}(X)

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Modular.TimeSemigroup

variable {A : Type*} [Ring A]

/-!
=============================================================================
PART 1: Bundled Derivations and the Modular Commutator
=============================================================================
-/

structure Derivation (A : Type*) [Ring A] where
  toFun : A → A
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

instance : CoeFun (Derivation A) (fun _ => A → A) where
  coe D := D.toFun

namespace Derivation

variable (D : Derivation A)

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem leibniz (x y : A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 = D 0 + D 0 := by
    calc D 0 = D (0 + 0) := by rw [add_zero]
    _ = D 0 + D 0 := D.map_add 0 0
  have h1 : D 0 - D 0 = (D 0 + D 0) - D 0 := congr_arg (fun x => x - D 0) h
  rw [sub_self, add_sub_cancel_right] at h1
  exact h1.symm

@[simp]
theorem map_neg (x : A) : D (-x) = - D x := by
  have h : D (x + -x) = D x + D (-x) := D.map_add x (-x)
  rw [add_neg_cancel, D.map_zero] at h
  have h_neg : - D x = - D x + (D x + D (-x)) := by rw [← h, add_zero]
  rw [← add_assoc, neg_add_cancel, zero_add] at h_neg
  exact h_neg.symm

@[simp]
theorem map_sub (x y : A) : D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, D.map_add, D.map_neg, ← sub_eq_add_neg]

end Derivation

/-- General Operator Commutator: [T₁, T₂](X) = T₁(T₂ X) - T₂(T₁ X). -/
def opComm (T₁ T₂ : A → A) (X : A) : A :=
  T₁ (T₂ X) - T₂ (T₁ X)

@[simp] theorem opComm_apply (T₁ T₂ : A → A) (X : A) :
    opComm T₁ T₂ X = T₁ (T₂ X) - T₂ (T₁ X) := rfl

/-- The Inner Modular Generator (Reversible Thermal Time): ad_K(X) = [K, X]. -/
def adK (K X : A) : A :=
  K * X - X * K

@[simp] theorem adK_apply (K X : A) : adK K X = K * X - X * K := rfl

/-- 
  THEOREM 1: The Modular Hamiltonian generates a genuine Leibniz Derivation:
  ad_K(X * Y) = (ad_K X) * Y + X * (ad_K Y)
  This guarantees that reversible modular time preserves algebraic products.
-/
theorem adK_is_derivation (K X Y : A) :
    adK K (X * Y) = (adK K X) * Y + X * (adK K Y) := by
  dsimp [adK]
  calc
    K * (X * Y) - (X * Y) * K
      = (K * X * Y - X * K * Y) + (X * K * Y - X * Y * K) := by
        simp only [mul_assoc]
        abel
    _ = (K * X - X * K) * Y + X * (K * Y - Y * K) := by
        simp only [sub_mul, mul_sub, mul_assoc]

/-!
=============================================================================
PART 2: The Total Dynamical Semigroup Generator (Modular + Dissipation)
=============================================================================
-/

/-- 
  The Total Dynamical Generator of Open System Evolution:
  ℒ(X) = ad_K(X) + 𝒟(X)
  where `ad_K` is the reversible modular Hamiltonian flow and `𝒟` is the dissipative channel.
-/
def totalDynamicalGenerator (K : A) (D_diss : A → A) (X : A) : A :=
  adK K X + D_diss X

/--
The total generator is itself inner when the dissipative channel is inner.

This is the canonical associative resolution of the ``rotational plus
irrotational'' split: the split remains available through
`totalDynamicalGenerator`, while the combined operator is exactly
`ad (K + B)`.  No analogue is asserted for a nonassociative commutator.
-/
theorem totalDynamicalGenerator_inner (K B X : A) :
    totalDynamicalGenerator K (adK B) X = adK (K + B) X := by
  dsimp [totalDynamicalGenerator, adK]
  simp only [add_mul, mul_add]
  abel

/-- 
  THEOREM 2 (Master Semigroup Backreaction Theorem):
  The commutator of an outer geometric derivation D with the total semigroup generator ℒ is:
    [D, ℒ](X) = ad_{D(K)}(X) + [D, 𝒟](X)
-/
theorem derivation_semigroup_commutator
    (D : Derivation A) (K : A) (D_diss : A → A) (X : A) :
    opComm D (totalDynamicalGenerator K D_diss) X =
      adK (D K) X + opComm D D_diss X := by
  dsimp [opComm, totalDynamicalGenerator, adK]
  rw [D.map_add, D.map_sub, D.leibniz, D.leibniz]
  abel

/-- 
  THEOREM 3 (Invariant Dissipation Pumping Theorem):
  If the dissipative channel is geometrically invariant under spacetime flow ([D, 𝒟] = 0),
  then outer geometric frame shear pumps the semigroup purely via the modular surprisal:
    [D, ℒ](X) = ad_{D(K)}(X)
-/
theorem derivation_semigroup_pumping_of_invariant_dissipation
    (D : Derivation A) (K : A) (D_diss : A → A) (X : A)
    (h_diss_inv : opComm D D_diss X = 0) :
    opComm D (totalDynamicalGenerator K D_diss) X = adK (D K) X := by
  rw [derivation_semigroup_commutator D K D_diss X]
  rw [h_diss_inv, add_zero]

/-- 
  THEOREM 4 (Equilibrium Decoupling):
  If both the modular state is stationary (D(K) = 0) and the dissipation is invariant,
  spacetime geometry and the dynamical semigroup strictly commute:
    [D, ℒ] = 0
-/
theorem semigroup_equilibrium_decoupling
    (D : Derivation A) (K : A) (D_diss : A → A) (X : A)
    (hK_stat : D K = 0)
    (h_diss_inv : opComm D D_diss X = 0) :
    opComm D (totalDynamicalGenerator K D_diss) X = 0 := by
  rw [derivation_semigroup_pumping_of_invariant_dissipation D K D_diss X h_diss_inv]
  dsimp [adK]
  rw [hK_stat, zero_mul, mul_zero, sub_zero]

end InfoGeometry.Modular.TimeSemigroup

end noncomputable section
