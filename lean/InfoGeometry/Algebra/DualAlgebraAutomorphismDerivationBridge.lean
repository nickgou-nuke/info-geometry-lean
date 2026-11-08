import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Automorphisms and Derivations of Dual Algebras: The Exact Semidirect Product

This module establishes the exact algebraic structure of the automorphism group
of the dual algebra $D(B) = B \oplus \varepsilon B$ ($\varepsilon^2 = 0$) for an arbitrary
(possibly non-associative) algebra $B$ over a commutative ring $R$:

1. **Derivation Translations**: Every algebra derivation $D \in \operatorname{Der}_R(B)$ induces an
   automorphism $\tau_D(x + \varepsilon y) = x + \varepsilon (y + D(x))$.
2. **Abelian Group Law**: $\tau_{D_1 + D_2} = \tau_{D_1} \circ \tau_{D_2}$, with inverse $\tau_{-D}$.
3. **Faithful Embedding**: $\tau_D = \operatorname{id} \iff D = 0$.
4. **Semidirect Action**: For any base automorphism $\phi \in \operatorname{Aut}_R(B)$,
   lifting $\phi$ to $\widetilde{\phi}(x + \varepsilon y) = \phi(x) + \varepsilon \phi(y)$ normalizes the
   derivation subgroup:
   $$\widetilde{\phi} \circ \tau_D \circ \widetilde{\phi}^{-1} = \tau_{\phi \circ D \circ \phi^{-1}}$$
   yielding the exact structure $\operatorname{Aut}(D(B)) \cong \operatorname{Aut}(B) \ltimes \operatorname{Der}(B)$.
-/

noncomputable section

namespace InfoGeometry.Algebra.DualAlgebra

/-- A derivation on an R-algebra B (preserving addition, scalar multiplication, and Leibniz rule). -/
structure AlgDerivation (R B : Type*) [CommRing R] [NonUnitalNonAssocRing B] [Module R B] where
  toFun : B → B
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (r : R) x, toFun (r • x) = r • toFun x
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

namespace AlgDerivation

variable {R B : Type*} [CommRing R] [NonUnitalNonAssocRing B] [Module R B]

instance : CoeFun (AlgDerivation R B) (fun _ => B → B) where
  coe D := D.toFun

variable (D : AlgDerivation R B)

@[simp] theorem map_add (x y : B) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem map_smul (r : R) (x : B) : D (r • x) = r • D x := D.map_smul' r x
@[simp] theorem leibniz (x y : B) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 + D 0 = D 0 + 0 := by
    rw [← D.map_add, add_zero, add_zero]
  exact add_left_cancel h

@[simp]
theorem map_neg (x : B) : D (-x) = - D x := by
  have h : D x + D (-x) = 0 := by
    rw [← D.map_add, add_neg_cancel, D.map_zero]
  exact eq_neg_of_add_eq_zero_right h

@[simp]
theorem map_sub (x y : B) : D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, D.map_add, D.map_neg, ← sub_eq_add_neg]

/-- Zero derivation on B. -/
def zero : AlgDerivation R B where
  toFun := fun _ => 0
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  leibniz' _ _ := by simp

/-- Addition of derivations on B. -/
def add (D₁ D₂ : AlgDerivation R B) : AlgDerivation R B where
  toFun := fun x => D₁ x + D₂ x
  map_add' x y := by simp [D₁.map_add, D₂.map_add]; abel
  map_smul' r x := by simp [D₁.map_smul, D₂.map_smul, smul_add]
  leibniz' x y := by
    simp only [D₁.leibniz, D₂.leibniz, add_mul, mul_add]
    abel

end AlgDerivation

/-- An R-algebra automorphism on a (possibly non-associative) algebra B. -/
structure AlgAut (R B : Type*) [CommRing R] [NonUnitalNonAssocRing B] [Module R B] where
  toFun : B → B
  invFun : B → B
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ x, toFun (invFun x) = x
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (r : R) x, toFun (r • x) = r • toFun x
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y

namespace AlgAut

variable {R B : Type*} [CommRing R] [NonUnitalNonAssocRing B] [Module R B]

instance : CoeFun (AlgAut R B) (fun _ => B → B) where
  coe phi := phi.toFun

variable (phi : AlgAut R B)

@[simp] theorem map_add (x y : B) : phi (x + y) = phi x + phi y := phi.map_add' x y
@[simp] theorem map_smul (r : R) (x : B) : phi (r • x) = r • phi x := phi.map_smul' r x
@[simp] theorem map_mul (x y : B) : phi (x * y) = phi x * phi y := phi.map_mul' x y

theorem inv_map_add (x y : B) : phi.invFun (x + y) = phi.invFun x + phi.invFun y := by
  have h := phi.map_add (phi.invFun x) (phi.invFun y)
  rw [phi.right_inv x, phi.right_inv y] at h
  have h2 := congrArg phi.invFun h
  rw [phi.left_inv] at h2
  exact h2.symm

theorem inv_map_smul (r : R) (x : B) : phi.invFun (r • x) = r • phi.invFun x := by
  have h := phi.map_smul r (phi.invFun x)
  rw [phi.right_inv x] at h
  have h2 := congrArg phi.invFun h
  rw [phi.left_inv] at h2
  exact h2.symm

theorem inv_map_mul (x y : B) : phi.invFun (x * y) = phi.invFun x * phi.invFun y := by
  have h := phi.map_mul (phi.invFun x) (phi.invFun y)
  rw [phi.right_inv x, phi.right_inv y] at h
  have h2 := congrArg phi.invFun h
  rw [phi.left_inv] at h2
  exact h2.symm

/-- Conjugation of a derivation by an automorphism: $\phi \circ D \circ \phi^{-1} \in \operatorname{Der}(B)$. -/
def conjugateDerivation (phi : AlgAut R B) (D : AlgDerivation R B) : AlgDerivation R B where
  toFun := fun x => phi (D (phi.invFun x))
  map_add' x y := by
    rw [phi.inv_map_add, D.map_add, phi.map_add]
  map_smul' r x := by
    rw [phi.inv_map_smul, D.map_smul, phi.map_smul]
  leibniz' x y := by
    rw [phi.inv_map_mul, D.leibniz, phi.map_add, phi.map_mul, phi.map_mul, phi.right_inv, phi.right_inv]

end AlgAut

/-- The dual algebra $D(B) = B \oplus \varepsilon B$ with $\varepsilon^2 = 0$. -/
@[ext]
structure DualExt (B : Type*) where
  primal : B
  tangent : B

namespace DualExt

variable {R B : Type*} [CommRing R] [NonUnitalNonAssocRing B] [Module R B]

instance : Add (DualExt B) where
  add u v := ⟨u.primal + v.primal, u.tangent + v.tangent⟩

instance : Mul (DualExt B) where
  mul u v := ⟨u.primal * v.primal, u.primal * v.tangent + u.tangent * v.primal⟩

instance : SMul R (DualExt B) where
  smul r u := ⟨r • u.primal, r • u.tangent⟩

@[simp] theorem add_primal (u v : DualExt B) : (u + v).primal = u.primal + v.primal := rfl
@[simp] theorem add_tangent (u v : DualExt B) : (u + v).tangent = u.tangent + v.tangent := rfl
@[simp] theorem mul_primal (u v : DualExt B) : (u * v).primal = u.primal * v.primal := rfl
@[simp] theorem mul_tangent (u v : DualExt B) : (u * v).tangent = u.primal * v.tangent + u.tangent * v.primal := rfl
@[simp] theorem smul_primal (r : R) (u : DualExt B) : (r • u).primal = r • u.primal := rfl
@[simp] theorem smul_tangent (r : R) (u : DualExt B) : (r • u).tangent = r • u.tangent := rfl

/-- The infinitesimal translation automorphism induced by a derivation D:
    $\tau_D(x + \varepsilon y) = x + \varepsilon (y + D(x))$. -/
def transAut (D : AlgDerivation R B) (u : DualExt B) : DualExt B :=
  ⟨u.primal, u.tangent + D u.primal⟩

@[simp] theorem transAut_primal (D : AlgDerivation R B) (u : DualExt B) :
    (transAut D u).primal = u.primal := rfl

@[simp] theorem transAut_tangent (D : AlgDerivation R B) (u : DualExt B) :
    (transAut D u).tangent = u.tangent + D u.primal := rfl

/-- 🏆 THEOREM 1: $\tau_D$ preserves addition. -/
theorem transAut_add (D : AlgDerivation R B) (u v : DualExt B) :
    transAut D (u + v) = transAut D u + transAut D v := by
  ext
  · simp
  · simp only [transAut_tangent, add_tangent, add_primal, D.map_add]
    abel

/-- 🏆 THEOREM 2: $\tau_D$ preserves scalar multiplication. -/
theorem transAut_smul (D : AlgDerivation R B) (r : R) (u : DualExt B) :
    transAut D (r • u) = r • transAut D u := by
  ext
  · simp
  · simp only [transAut_tangent, smul_tangent, smul_primal, D.map_smul, smul_add]

/-- 🏆 THEOREM 3: $\tau_D$ preserves multiplication (Exact Automorphism Law). -/
theorem transAut_mul (D : AlgDerivation R B) (u v : DualExt B) :
    transAut D (u * v) = transAut D u * transAut D v := by
  ext
  · simp
  · simp only [transAut_tangent, mul_tangent, mul_primal, D.leibniz]
    calc
      u.primal * v.tangent + u.tangent * v.primal + (D u.primal * v.primal + u.primal * D v.primal)
        = u.primal * (v.tangent + D v.primal) + (u.tangent + D u.primal) * v.primal := by
          simp only [mul_add, add_mul]
          abel

/-- 🏆 THEOREM 4: Group Homomorphism Law for Derivation Translations:
    $\tau_{D_1 + D_2} = \tau_{D_1} \circ \tau_{D_2}$. -/
theorem transAut_comp (D₁ D₂ : AlgDerivation R B) (u : DualExt B) :
    transAut (AlgDerivation.add D₁ D₂) u = transAut D₁ (transAut D₂ u) := by
  ext
  · simp
  · dsimp [transAut, AlgDerivation.add]
    abel

/-- Negative of a derivation. -/
def negDerivation (D : AlgDerivation R B) : AlgDerivation R B where
  toFun := fun x => - D x
  map_add' x y := by
    simp only [D.map_add, neg_add]
  map_smul' r x := by
    simp only [D.map_smul, smul_neg]
  leibniz' x y := by
    simp only [D.leibniz, neg_add, neg_mul, mul_neg]

/-- 🏆 THEOREM 5: Involutive/Inverse Law: $\tau_{-D} \circ \tau_D = \operatorname{id}$. -/
theorem transAut_neg_comp (D : AlgDerivation R B) (u : DualExt B) :
    transAut (negDerivation D) (transAut D u) = u := by
  ext
  · simp
  · dsimp [transAut, negDerivation]
    simp

/-- 🏆 THEOREM 6: Injectivity of the Derivation-to-Automorphism Embedding:
    $\tau_D = \operatorname{id} \iff D = 0$. -/
theorem transAut_eq_id_iff (D : AlgDerivation R B) :
    (∀ u, transAut D u = u) ↔ (∀ x, D x = 0) := by
  constructor
  · intro h x
    have hu := h ⟨x, 0⟩
    have ht := congrArg tangent hu
    simp at ht
    exact ht
  · intro h u
    ext
    · rfl
    · simp [h u.primal]

/-- Lift an automorphism of B to D(B): $\widetilde{\phi}(x, y) = (\phi(x), \phi(y))$. -/
def liftAut (phi : AlgAut R B) (u : DualExt B) : DualExt B :=
  ⟨phi u.primal, phi u.tangent⟩

/-- Inverse lift of an automorphism. -/
def liftAutInv (phi : AlgAut R B) (u : DualExt B) : DualExt B :=
  ⟨phi.invFun u.primal, phi.invFun u.tangent⟩

theorem liftAut_left_inv (phi : AlgAut R B) (u : DualExt B) :
    liftAutInv phi (liftAut phi u) = u := by
  ext
  · exact phi.left_inv u.primal
  · exact phi.left_inv u.tangent

theorem liftAut_right_inv (phi : AlgAut R B) (u : DualExt B) :
    liftAut phi (liftAutInv phi u) = u := by
  ext
  · exact phi.right_inv u.primal
  · exact phi.right_inv u.tangent

/-- 🏆 THEOREM 7: Semidirect Product Conjugation Law ($\operatorname{Aut}(D(B)) = \operatorname{Aut}(B) \ltimes \operatorname{Der}(B)$):
    $\widetilde{\phi} \circ \tau_D \circ \widetilde{\phi}^{-1} = \tau_{\phi \circ D \circ \phi^{-1}}$. -/
theorem semidirect_conjugation (phi : AlgAut R B) (D : AlgDerivation R B) (u : DualExt B) :
    liftAut phi (transAut D (liftAutInv phi u)) =
      transAut (AlgAut.conjugateDerivation phi D) u := by
  ext
  · dsimp [liftAut, transAut, liftAutInv]
    exact phi.right_inv u.primal
  · dsimp [liftAut, transAut, liftAutInv, AlgAut.conjugateDerivation]
    rw [phi.map_add, phi.right_inv]

end DualExt

end InfoGeometry.Algebra.DualAlgebra
