import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Modular.ExactSequence

variable {A : Type*} [Ring A]

/-!
=============================================================================
PART 1: Bundled Derivations and the Modular Map
=============================================================================
-/

/-- An additive derivation on the ring A. -/
@[ext]
structure Derivation (A : Type*) [Ring A] where
  toFun : A → A
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

namespace Derivation

instance : CoeFun (Derivation A) (fun _ => A → A) where
  coe D := D.toFun

instance : Zero (Derivation A) where
  zero :=
    { toFun := 0
      map_add' := by simp
      leibniz' := by simp }

instance : Add (Derivation A) where
  add D E :=
    { toFun := D.toFun + E.toFun
      map_add' := by
        intro x y
        simp only [Pi.add_apply, D.map_add', E.map_add']
        abel
      leibniz' := by
        intro x y
        simp only [Pi.add_apply, D.leibniz', E.leibniz']
        simp only [add_mul, mul_add]
        abel }

instance : Neg (Derivation A) where
  neg D :=
    { toFun := (-D.toFun)
      map_add' := by
        intro x y
        simp only [Pi.neg_apply, D.map_add', neg_add]
      leibniz' := by
        intro x y
        change -(D.toFun (x * y)) =
          (-D.toFun x) * y + x * (-D.toFun y)
        rw [D.leibniz']
        simp only [neg_add, neg_mul, mul_neg] }

instance : AddGroup (Derivation A) :=
  AddGroup.ofLeftAxioms
    (by
      intro D E F
      ext x
      change (D.toFun x + E.toFun x) + F.toFun x =
        D.toFun x + (E.toFun x + F.toFun x)
      abel)
    (by
      intro D
      ext x
      change 0 + D.toFun x = D.toFun x
      simp)
    (by
      intro D
      ext x
      change -D.toFun x + D.toFun x = 0
      simp)

instance : AddCommGroup (Derivation A) :=
  AddCommGroup.mk (by
    intro D E
    ext x
    change D.toFun x + E.toFun x = E.toFun x + D.toFun x
    abel)

variable (D : Derivation A)

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem leibniz (x y : A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 + D 0 = D 0 + 0 := by
    rw [add_zero, ← D.map_add, add_zero]
  exact add_left_cancel h

@[simp]
theorem map_neg (x : A) : D (-x) = - D x := by
  have h : D x + D (-x) = 0 := by
    rw [← D.map_add, add_neg_cancel, D.map_zero]
  exact eq_neg_of_add_eq_zero_right h

@[simp]
theorem map_sub (x y : A) : D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, D.map_add, D.map_neg, ← sub_eq_add_neg]

/-- The Lie Bracket of two derivations: [D₁, D₂] = D₁ ∘ D₂ - D₂ ∘ D₁. -/
def bracket (D₁ D₂ : Derivation A) (x : A) : A :=
  D₁ (D₂ x) - D₂ (D₁ x)

theorem bracket_leibniz (D₁ D₂ : Derivation A) (x y : A) :
    bracket D₁ D₂ (x * y) = (bracket D₁ D₂ x) * y + x * (bracket D₁ D₂ y) := by
  dsimp [bracket]
  rw [D₂.leibniz, D₁.map_add, D₁.leibniz, D₁.leibniz,
      D₁.leibniz, D₂.map_add, D₂.leibniz, D₂.leibniz]
  simp only [sub_mul, mul_sub]
  abel

/-- The commutator Lie bracket packaged as a bundled Derivation. -/
def derivationCommutator (D₁ D₂ : Derivation A) : Derivation A where
  toFun := bracket D₁ D₂
  map_add' x y := by
    dsimp [bracket]
    rw [D₂.map_add, D₁.map_add, D₁.map_add, D₂.map_add]
    abel
  leibniz' := bracket_leibniz D₁ D₂

end Derivation

/-!
=============================================================================
PART 2: The Kernel of the Modular Map: ker(ad) = Z(A)
=============================================================================
-/

/-- The Inner Modular Generator: ad_K(X) = [K, X] = K * X - X * K. -/
def adK (K : A) (X : A) : A :=
  K * X - X * K

@[simp] theorem adK_apply (K X : A) : adK K X = K * X - X * K := rfl

/-- Packaging ad_K as a bundled Derivation on A. -/
def modularDerivation (K : A) : Derivation A where
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

/-! Inner derivations are additive in their generating element. -/
theorem modularDerivation_add_apply (K L X : A) :
    modularDerivation (K + L) X =
      modularDerivation K X + modularDerivation L X := by
  dsimp [modularDerivation, adK]
  simp only [add_mul, mul_add]
  abel

/-- 
  THEOREM 1: The Exact Kernel of the Modular Map.
  ad_K is identically the zero derivation if and only if K is in the center Z(A):
    (∀ X, ad_K(X) = 0) ↔ (∀ X, K * X = X * K)
-/
theorem ker_adK_eq_center (K : A) :
    (∀ X : A, adK K X = 0) ↔ (∀ X : A, K * X = X * K) := by
  constructor
  · intro h X
    have hX := h X
    dsimp [adK] at hX
    have h_sub : K * X - X * K = 0 := hX
    exact eq_of_sub_eq_zero h_sub
  · intro h X
    dsimp [adK]
    rw [h X, sub_self]

/-!
=============================================================================
PART 3: The Lie Ideal Theorem: [Der(A), Inn(A)] ⊆ Inn(A)
=============================================================================
-/

/-- 
  THEOREM 2: Master Dual-Flow Commutator
  [D, ad_K](X) = ad_{D(K)}(X)
-/
theorem dual_flow_commutator (D : Derivation A) (K X : A) :
    D (adK K X) - adK K (D X) = adK (D K) X := by
  dsimp [adK]
  rw [D.map_sub, D.leibniz, D.leibniz]
  abel

/--
  THEOREM 3: Inn(A) is a Strict Lie Ideal of Der(A).
  For every outer derivation D ∈ Der(A) and every inner derivation ad_K ∈ Inn(A),
  their commutator [D, ad_K] is strictly an inner derivation, generated by D(K):
    [D, ad_K] = ad_{D(K)} ∈ Inn(A)
-/
theorem inn_is_lie_ideal (D : Derivation A) (K : A) :
    ∃ K' : A, Derivation.derivationCommutator D (modularDerivation K) = modularDerivation K' := by
  use D K
  ext X
  exact dual_flow_commutator D K X

/-- 
  THEOREM 4: The Jacobi Identity on the Inner Subalgebra
  [ad_{K₁}, ad_{K₂}] = ad_{[K₁, K₂]}
-/
theorem adK_bracket (K₁ K₂ X : A) :
    adK K₁ (adK K₂ X) - adK K₂ (adK K₁ X) = adK (adK K₁ K₂) X := by
  dsimp [adK]
  calc
    K₁ * (K₂ * X - X * K₂) - (K₂ * X - X * K₂) * K₁ -
      (K₂ * (K₁ * X - X * K₁) - (K₁ * X - X * K₁) * K₂)
      = (K₁ * K₂ - K₂ * K₁) * X - X * (K₁ * K₂ - K₂ * K₁) := by
        simp only [mul_sub, sub_mul, mul_assoc]
        abel
    _ = adK (adK K₁ K₂) X := by rfl

/-! The pointwise inner-bracket identity lifts to the bundled derivation
    commutator. -/
theorem commutator_modular_eq_modular_commutator (K₁ K₂ : A) :
    Derivation.derivationCommutator (modularDerivation K₁)
        (modularDerivation K₂) =
      modularDerivation (adK K₁ K₂) := by
  ext X
  exact adK_bracket K₁ K₂ X


/-!
=============================================================================
PART 4: Phenomenological Corollaries (The Dictionary of Reality)
=============================================================================
-/

/-- 
  THEOREM 5: Semidirect Lie Action Equality
  The derivation commutator [D, modularDerivation K] is strictly equal
  to modularDerivation (D K).
-/
theorem commutator_eq_modularDerivation (D : Derivation A) (K : A) :
    Derivation.derivationCommutator D (modularDerivation K) = modularDerivation (D K) := by
  ext X
  exact dual_flow_commutator D K X

/-!
## The additive inner quotient

The quotient below is deliberately additive.  It records the quotient by
inner derivations without claiming a splitting of the derivation extension.
The latter requires additional section data and is not a consequence of the
ideal theorem alone.
-/

noncomputable def modularDerivationAddHom : A →+ Derivation A where
  toFun := modularDerivation
  map_zero' := by
    ext X
    change (0 : A) * X - X * 0 = 0
    simp
  map_add' K L := by
    ext X
    change modularDerivation (K + L) X =
      modularDerivation K X + modularDerivation L X
    exact modularDerivation_add_apply K L X

def Inn : AddSubgroup (Derivation A) :=
  AddMonoidHom.range (modularDerivationAddHom (A := A))

abbrev Out := Derivation A ⧸ Inn (A := A)

noncomputable def quotientProjection : Derivation A →+ Out (A := A) :=
  QuotientAddGroup.mk' (Inn (A := A))

theorem quotientProjection_ker :
    (quotientProjection (A := A)).ker = Inn (A := A) := by
  exact QuotientAddGroup.ker_mk' (Inn (A := A))

/-- 
  THEOREM 6: Adiabatic Limit (The Stable Vacuum).
  When the spacetime derivation preserves the state generator D(K) = 0,
  the spacetime flow and modular thermal flow commute identically:
    [D, ad_K] = 0
-/
theorem adiabatic_commutator_zero (D : Derivation A) (K : A) (h_adiabatic : D K = 0) :
    Derivation.derivationCommutator D (modularDerivation K) = modularDerivation 0 := by
  rw [commutator_eq_modularDerivation, h_adiabatic]

/-- 
  THEOREM 7: Central Projection (The Classical Vacuum).
  When K is in the center Z(A), its modular derivation is zero,
  and therefore commutes with all spacetime derivations:
    K ∈ Z(A) ⟹ [D, ad_K] = 0
-/
theorem central_commutator_zero (D : Derivation A) (K : A) (h_center : ∀ X, K * X = X * K) :
    ∀ X, Derivation.bracket D (modularDerivation K) X = 0 := by
  intro X
  have h_ker : modularDerivation K = modularDerivation 0 := by
    ext Y
    dsimp [modularDerivation, adK]
    rw [h_center Y, sub_self, mul_zero, zero_mul, sub_self]
  rw [h_ker]
  dsimp [Derivation.bracket, modularDerivation, adK]
  simp only [mul_zero, zero_mul, sub_self, D.map_zero]

end InfoGeometry.Modular.ExactSequence
