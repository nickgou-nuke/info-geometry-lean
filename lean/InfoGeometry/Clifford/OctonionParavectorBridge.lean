import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

/-!
# Octonion paravectors and projected Clifford products

This module formalizes the theorem-safe core of the common statement that
(often after choosing a `G₂` cross product) octonions can be represented inside a
Clifford algebra.

The precise algebraic content is subtler than the slogan: an octonion algebra is
not an associative subalgebra of a Clifford algebra.  Instead, its underlying
carrier is a paravector space `ℝ × V`, and its nonassociative multiplication is
recovered from scalar/vector projection data, or equivalently from a symmetric
inner product and an alternating cross product.

This file proves the native finite algebraic layer:

* an abstract paravector/octonion product
  `(a,u)(b,v) = (ab - ⟪u,v⟫, a v + b u + u × v)`;
* `1` is a two-sided unit for that product;
* scalar and imaginary readouts, including `u² = -⟪u,u⟫` for pure imaginary
  paravectors;
* bilinearity of the product;
* a `ProjectedCliffordShadow` interface saying that an associative ambient
  algebra, in particular a mathlib `CliffordAlgebra Q`, realizes this product
  only after inclusion followed by projection.

What remains deliberately unclaimed here:

* no concrete `7`-dimensional Fano-plane/G₂ cross product is constructed;
* no full octonion associator or alternative-law theorem is proved;
* no assertion is made that octonions form an associative subalgebra of a
  Clifford algebra;
* no concrete projection formula from a chosen `Cl(V)` is identified.
-/

noncomputable section

namespace InfoGeometry.Clifford.OctonionParavectorBridge

/-- Algebraic data for the paravector presentation of an octonion-style product.

For the genuine real octonions one takes `V = ℝ⁷`, `inner` the Euclidean inner
product, and `cross` the `G₂` cross product.  This module keeps those structures
abstract so that downstream concrete Zorn/Fano/Clifford owners can instantiate
the interface without importing an unproved classification theorem. -/
structure OctonionParavectorData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  inner : LinearMap.BilinForm ℝ V
  cross : V →ₗ[ℝ] V →ₗ[ℝ] V
  inner_symm : ∀ u v, inner u v = inner v u
  cross_self : ∀ u, cross u u = 0
  cross_anticomm : ∀ u v, cross v u = - cross u v

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Paravectors `ℝ ⊕ V`, the carrier on which the octonion-style product lives. -/
abbrev Paravector (V : Type*) := ℝ × V

/-- Scalar paravector. -/
def scalar (r : ℝ) : Paravector V :=
  (r, 0)

/-- Pure-imaginary/vector paravector. -/
def imaginary (v : V) : Paravector V :=
  (0, v)

/-- The octonion-style paravector product determined by an inner product and a
cross product. -/
def paravectorMul (D : OctonionParavectorData V)
    (x y : Paravector V) : Paravector V :=
  (x.1 * y.1 - D.inner x.2 y.2,
    x.1 • y.2 + y.1 • x.2 + D.cross x.2 y.2)

/-- Scalar part of the paravector product. -/
theorem paravectorMul_fst (D : OctonionParavectorData V) (x y : Paravector V) :
    (paravectorMul D x y).1 = x.1 * y.1 - D.inner x.2 y.2 :=
  rfl

/-- Vector part of the paravector product. -/
theorem paravectorMul_snd (D : OctonionParavectorData V) (x y : Paravector V) :
    (paravectorMul D x y).2 = x.1 • y.2 + y.1 • x.2 + D.cross x.2 y.2 :=
  rfl

/-- `1` is a right unit for the paravector product. -/
theorem paravectorMul_one (D : OctonionParavectorData V) (x : Paravector V) :
    paravectorMul D x (scalar 1) = x := by
  cases x
  simp [paravectorMul, scalar]

/-- `1` is a left unit for the paravector product. -/
theorem one_paravectorMul (D : OctonionParavectorData V) (x : Paravector V) :
    paravectorMul D (scalar 1) x = x := by
  cases x
  simp [paravectorMul, scalar]

/-- Scalar paravectors multiply as real scalars. -/
theorem scalar_mul_scalar (D : OctonionParavectorData V) (a b : ℝ) :
    paravectorMul D (scalar (V := V) a) (scalar b) = scalar (a * b) := by
  ext <;> simp [paravectorMul, scalar]

/-- Left multiplication of a pure vector by a scalar paravector. -/
theorem scalar_mul_imaginary (D : OctonionParavectorData V) (a : ℝ) (u : V) :
    paravectorMul D (scalar a) (imaginary u) = imaginary (a • u) := by
  ext <;> simp [paravectorMul, scalar, imaginary]

/-- Right multiplication of a pure vector by a scalar paravector. -/
theorem imaginary_mul_scalar (D : OctonionParavectorData V) (a : ℝ) (u : V) :
    paravectorMul D (imaginary u) (scalar a) = imaginary (a • u) := by
  ext <;> simp [paravectorMul, scalar, imaginary]

/-- Product of two pure-imaginary paravectors. -/
theorem imaginary_mul_imaginary (D : OctonionParavectorData V) (u v : V) :
    paravectorMul D (imaginary u) (imaginary v) =
      (-(D.inner u v), D.cross u v) := by
  ext <;> simp [paravectorMul, imaginary]

/-- Swapping two pure-imaginary paravectors flips the cross-product part and
uses symmetry of the inner product. -/
theorem imaginary_mul_imaginary_swap (D : OctonionParavectorData V) (u v : V) :
    paravectorMul D (imaginary v) (imaginary u) =
      (-(D.inner u v), -D.cross u v) := by
  ext
  · simp [paravectorMul, imaginary, D.inner_symm v u]
  · simp [paravectorMul, imaginary]
    exact D.cross_anticomm u v

/-- A pure-imaginary paravector squares to the negative quadratic norm in the
scalar line. -/
theorem imaginary_sq (D : OctonionParavectorData V) (u : V) :
    paravectorMul D (imaginary u) (imaginary u) = scalar (-(D.inner u u)) := by
  ext <;> simp [paravectorMul, imaginary, scalar, D.cross_self]

/-- Left additivity of the paravector product. -/
theorem paravectorMul_add_left (D : OctonionParavectorData V)
    (x y z : Paravector V) :
    paravectorMul D (x + y) z = paravectorMul D x z + paravectorMul D y z := by
  ext
  · simp [paravectorMul]
    ring
  · simp [paravectorMul, add_smul, smul_add]
    abel

/-- Right additivity of the paravector product. -/
theorem paravectorMul_add_right (D : OctonionParavectorData V)
    (x y z : Paravector V) :
    paravectorMul D x (y + z) = paravectorMul D x y + paravectorMul D x z := by
  ext
  · simp [paravectorMul]
    ring
  · simp [paravectorMul, add_smul, smul_add]
    abel

/-- Left scalar compatibility of the paravector product. -/
theorem paravectorMul_smul_left (D : OctonionParavectorData V)
    (a : ℝ) (x y : Paravector V) :
    paravectorMul D (a • x) y = a • paravectorMul D x y := by
  ext
  · simp [paravectorMul]
    ring
  · simp [paravectorMul, smul_add, smul_smul]
    module

/-- Right scalar compatibility of the paravector product. -/
theorem paravectorMul_smul_right (D : OctonionParavectorData V)
    (a : ℝ) (x y : Paravector V) :
    paravectorMul D x (a • y) = a • paravectorMul D x y := by
  ext
  · simp [paravectorMul]
    ring
  · simp [paravectorMul, smul_add, smul_smul]
    module

/-- A projected associative-algebra shadow of the octonion paravector product.

`Cl` is intentionally only required to be an associative real algebra.  The
specialization to a mathlib Clifford algebra is `CliffordAlgebraParavectorShadow`
below.  The point is that the octonion-style product is recovered by

`include -> ambient multiplication -> project`,

not by making `Paravector V` an associative subalgebra. -/
structure ProjectedCliffordShadow (D : OctonionParavectorData V)
    (Cl : Type*) [Ring Cl] [Algebra ℝ Cl] where
  includeParavector : Paravector V →ₗ[ℝ] Cl
  projectParavector : Cl →ₗ[ℝ] Paravector V
  projected_mul : ∀ x y,
    projectParavector (includeParavector x * includeParavector y) = paravectorMul D x y

/-- Specialization of `ProjectedCliffordShadow` to a genuine mathlib Clifford
algebra. -/
abbrev CliffordAlgebraParavectorShadow (D : OctonionParavectorData V)
    (Q : QuadraticForm ℝ V) :=
  ProjectedCliffordShadow D (CliffordAlgebra Q)

variable {Cl : Type*} [Ring Cl] [Algebra ℝ Cl]

/-- The projected ambient product recovers the octonion-style paravector product. -/
theorem projectedCliffordProduct_eq_paravectorMul
    (D : OctonionParavectorData V) (S : ProjectedCliffordShadow D Cl)
    (x y : Paravector V) :
    S.projectParavector (S.includeParavector x * S.includeParavector y) =
      paravectorMul D x y :=
  S.projected_mul x y

/-- In a projected Clifford shadow, the square of an included pure-imaginary
paravector projects to the negative quadratic norm in the scalar line. -/
theorem projectedCliffordProduct_imaginary_sq
    (D : OctonionParavectorData V) (S : ProjectedCliffordShadow D Cl) (u : V) :
    S.projectParavector (S.includeParavector (imaginary u) *
        S.includeParavector (imaginary u)) =
      scalar (-(D.inner u u)) := by
  rw [S.projected_mul, imaginary_sq]

/-- Consolidated theorem-safe packet for the paravector/projected-Clifford
construction. -/
theorem octonion_paravector_bridge_synthesis
    (D : OctonionParavectorData V) (S : ProjectedCliffordShadow D Cl) :
    (∀ x : Paravector V, paravectorMul D (scalar 1) x = x) ∧
      (∀ x : Paravector V, paravectorMul D x (scalar 1) = x) ∧
      (∀ u : V, paravectorMul D (imaginary u) (imaginary u) =
        scalar (-(D.inner u u))) ∧
      (∀ x y : Paravector V,
        S.projectParavector (S.includeParavector x * S.includeParavector y) =
          paravectorMul D x y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact one_paravectorMul D
  · exact paravectorMul_one D
  · exact imaginary_sq D
  · exact S.projected_mul

end InfoGeometry.Clifford.OctonionParavectorBridge
