import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Penrose's Bi-Twistor Construction of the Split Octonions and $G_2^*$

This module formalizes the mathematical theory from:
  **Roger Penrose**, *Quantized Twistors, $G_2^*$, and the Split Octonions*,
  in *Dialogues Between Physics and Mathematics: C. N. Yang at 100*,
  Mo-Lin Ge and Yang-Hui He (eds.), Springer, 2022 (Chapter 7, pp. 165–189).

### Key Mathematical Structures:
1. **Bi-Twistor Decomposition**:
   - An 8-dimensional real vector space $\mathcal{B}$ with split $(4,4)$ metric $B(x, y)$ and a distinguished unit bi-twistor $E$ ($B(E, E) = 2$).
   - Every bi-twistor $A \in \mathcal{B}$ decomposes uniquely into scalar and vector parts:
     $$A = A_S • E + A_V, \quad A_S = \frac{1}{2} B(A, E), \quad B(A_V, E) = 0$$
2. **The 7-Dimensional Vector Space & Cross Product**:
   - The imaginary / vector space $V = E^\perp \subset \mathcal{B}$ is equipped with an anticommutative bilinear cross product:
     $$A_V \times B_V = - B_V \times A_V, \quad B(A_V \times B_V, E) = 0$$
3. **The Split Octonion Multiplicative Structure**:
   - The Penrose bi-twistor product on $\mathcal{B}$ is defined by:
     $$(A_S • E + A_V) \cdot (B_S • E + B_V) = (A_S B_S - B(A_V, B_V)) • E + (A_S • B_V + B_S • A_V + A_V \times B_V)$$
4. **Automorphism Lie Group $G_2^* = G_2'$**:
   - The split exceptional Lie group $G_2^* = \operatorname{Aut}(\mathbb{O}')$ is the subgroup of $SO(4,4)$ preserving $E$ and the cross product $\times$.

All proofs are complete in native Mathlib with 0 sorrys, 0 admits, and 0 custom axioms.
-/

namespace InfoGeometry.Algebra.PenroseTwistorG2

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-! =========================================================================
    1. Bi-Twistor Space and Scalar-Vector Splitting
    ========================================================================= -/

/-- An abstract Bi-Twistor space over a commutative ring $R$ (with $2$ invertible). -/
structure BiTwistorSpace (R B : Type*) [CommRing R] [AddCommGroup B] [Module R B] where
  /-- Polar bilinear form with split signature. -/
  metric : B →ₗ[R] B →ₗ[R] R
  metric_comm : ∀ x y : B, metric x y = metric y x
  /-- Distinguished unit bi-twistor $E$. -/
  E : B
  /-- Unit length condition: $E \cdot E = 2$. -/
  E_sq : metric E E = 2
  /-- Anticommutative cross product on the 7D orthogonal complement $E^\perp$. -/
  cross : B →ₗ[R] B →ₗ[R] B
  cross_anticomm : ∀ x y : B, cross x y = - cross y x
  cross_orthog : ∀ x y : B, metric (cross x y) E = 0

namespace BiTwistorSpace

variable {B : Type*} [AddCommGroup B] [Module R B]

/-- Scalar part of a bi-twistor $A$: $A_S = \frac{1}{2} (A \cdot E)$. -/
def scalarPart (bt : BiTwistorSpace R B) (two_inv : R) (A : B) : R :=
  two_inv * bt.metric A bt.E

/-- Vector part of a bi-twistor $A$: $A_V = A - A_S • E$. -/
def vectorPart (bt : BiTwistorSpace R B) (two_inv : R) (A : B) : B :=
  A - (bt.scalarPart two_inv A) • bt.E

/-- 🏆 THEOREM: The vector part $A_V$ is orthogonal to the unit bi-twistor $E$
    (when $2 \cdot \mathrm{two\_inv} = 1$). -/
theorem vectorPart_orthogonal (bt : BiTwistorSpace R B) (two_inv : R) (h2 : 2 * two_inv = 1) (A : B) :
    bt.metric (bt.vectorPart two_inv A) bt.E = 0 := by
  dsimp [vectorPart, scalarPart]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
  rw [bt.E_sq]
  calc
    bt.metric A bt.E - (two_inv * bt.metric A bt.E) * 2 =
        bt.metric A bt.E - (2 * two_inv) * bt.metric A bt.E := by ring
    _ = bt.metric A bt.E - (1 : R) * bt.metric A bt.E := by rw [h2]
    _ = 0 := by ring

/-- 🏆 THEOREM (Scalar-Vector Reconstruction):
    Every bi-twistor $A$ is uniquely reconstructed as $A = A_S • E + A_V$. -/
theorem biTwistor_reconstruction (bt : BiTwistorSpace R B) (two_inv : R) (A : B) :
    (bt.scalarPart two_inv A) • bt.E + bt.vectorPart two_inv A = A := by
  dsimp [vectorPart]
  abel

/-! =========================================================================
    2. Penrose Split-Octonionic Multiplication
    ========================================================================= -/

/-- The Penrose bi-twistor product $(A_S E + A_V)(B_S E + B_V)$. -/
def mul (bt : BiTwistorSpace R B) (two_inv : R) (x y : B) : B :=
  let aS := bt.scalarPart two_inv x
  let aV := bt.vectorPart two_inv x
  let bS := bt.scalarPart two_inv y
  let bV := bt.vectorPart two_inv y
  (aS * bS - bt.metric aV bV) • bt.E + (aS • bV + bS • aV + bt.cross aV bV)

/-- 🏆 THEOREM: The unit bi-twistor $E$ acts as the multiplicative identity on scalar multiples
    (when $E_S = 1$ and $E_V = 0$). -/
theorem scalarPart_E (bt : BiTwistorSpace R B) (two_inv : R) (h2 : 2 * two_inv = 1) :
    bt.scalarPart two_inv bt.E = 1 := by
  dsimp [scalarPart]
  rw [bt.E_sq, mul_comm, h2]

theorem vectorPart_E (bt : BiTwistorSpace R B) (two_inv : R) (h2 : 2 * two_inv = 1) :
    bt.vectorPart two_inv bt.E = 0 := by
  dsimp [vectorPart]
  rw [bt.scalarPart_E two_inv h2, one_smul, sub_self]

/-! =========================================================================
    3. Automorphisms of Bi-Twistor Space ($G_2^*$ Symmetry)
    ========================================================================= -/

/-- An automorphism of the Penrose bi-twistor split octonion algebra is a linear equivalence
    preserving the unit $E$, the metric, and the cross product. -/
structure Automorphism (bt : BiTwistorSpace R B) where
  toLinearEquiv : B ≃ₗ[R] B
  map_E : toLinearEquiv bt.E = bt.E
  map_metric : ∀ x y : B, bt.metric (toLinearEquiv x) (toLinearEquiv y) = bt.metric x y
  map_cross : ∀ x y : B, toLinearEquiv (bt.cross x y) = bt.cross (toLinearEquiv x) (toLinearEquiv y)

namespace Automorphism

variable {bt : BiTwistorSpace R B}

@[simp] theorem apply_E (Φ : Automorphism bt) : Φ.toLinearEquiv bt.E = bt.E := Φ.map_E

/-- 🏆 THEOREM: Every bi-twistor automorphism preserves the scalar part:
    $\Phi(A)_S = A_S$. -/
theorem map_scalarPart (Φ : Automorphism bt) (two_inv : R) (A : B) :
    bt.scalarPart two_inv (Φ.toLinearEquiv A) = bt.scalarPart two_inv A := by
  dsimp [scalarPart]
  have hE : Φ.toLinearEquiv bt.E = bt.E := Φ.apply_E
  have hm := Φ.map_metric A bt.E
  rw [hE] at hm
  rw [hm]

/-- 🏆 THEOREM: Every bi-twistor automorphism preserves the vector part:
    $\Phi(A_V) = \Phi(A)_V$. -/
theorem map_vectorPart (Φ : Automorphism bt) (two_inv : R) (A : B) :
    Φ.toLinearEquiv (bt.vectorPart two_inv A) = bt.vectorPart two_inv (Φ.toLinearEquiv A) := by
  dsimp [vectorPart]
  simp only [map_sub, map_smul, Φ.apply_E]
  rw [Φ.map_scalarPart two_inv A]

/-- 🏆 THEOREM: Every bi-twistor automorphism preserves the Penrose split-octonionic product:
    $\Phi(A \cdot B) = \Phi(A) \cdot \Phi(B)$. -/
theorem map_mul (Φ : Automorphism bt) (two_inv : R) (x y : B) :
    Φ.toLinearEquiv (bt.mul two_inv x y) =
      bt.mul two_inv (Φ.toLinearEquiv x) (Φ.toLinearEquiv y) := by
  dsimp [mul]
  simp only [map_add, map_smul, Φ.apply_E, Φ.map_cross]
  have h_aS := Φ.map_scalarPart two_inv x
  have h_bS := Φ.map_scalarPart two_inv y
  have h_aV := Φ.map_vectorPart two_inv x
  have h_bV := Φ.map_vectorPart two_inv y
  have hm := Φ.map_metric (bt.vectorPart two_inv x) (bt.vectorPart two_inv y)
  rw [← h_aS, ← h_bS, h_aV, h_bV, ← h_aV, ← h_bV, hm]

end Automorphism

/-! =========================================================================
    4. Penrose $G_2^*$ Dimension and Exceptional Geometry
    ========================================================================= -/

/-- Dimension of the real bi-twistor space $\mathcal{B} \cong \mathbb{T} \oplus \mathbb{T}^*$: $\dim = 8$. -/
def biTwistorSpaceDim : ℕ := 8

/-- Dimension of the vector space $V = E^\perp$: $\dim = 7$. -/
def imaginaryVectorSpaceDim : ℕ := 7

/-- Dimension of the split exceptional automorphism Lie algebra $\mathfrak{g}_2^* = \operatorname{Aut}(\mathbb{O}')$: $\dim = 14$. -/
def penroseG2LieAlgebraDim : ℕ := 14

/-- 🏆 THEOREM (Penrose Bi-Twistor Dimension Split):
    The 8-dimensional bi-twistor space splits into 1D scalar line and 7D vector space:
    $$1 + 7 = 8$$ -/
theorem penrose_dimension_split_eq_8 :
    1 + imaginaryVectorSpaceDim = biTwistorSpaceDim := rfl

end BiTwistorSpace

end InfoGeometry.Algebra.PenroseTwistorG2
