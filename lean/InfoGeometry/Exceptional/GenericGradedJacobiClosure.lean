import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Basic

/-!
# Generic finite graded Jacobi closure

This file isolates the purely algebraic closure mechanism used by the
Freudenthal 5-graded construction.  A bilinear alternating bracket on a module
becomes a Lie bracket once Leibniz/Jacobi is checked on a finite family of
linear homogeneous projections whose sum is the identity.

The global Jacobi law is not assumed as a field.  It is reconstructed from
finite homogeneous-cell certificates by trilinearity.
-/

noncomputable section

namespace InfoGeometry.Exceptional.GenericGradedJacobiClosure

variable {R V ι : Type*}
variable [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [Fintype ι] [DecidableEq ι]

/-- A finite linear decomposition of a module into homogeneous lanes. -/
structure DecompositionData where
  part : ι → V →ₗ[R] V
  sum_part : ∀ x : V, (∑ i : ι, part i x) = x

/-- A bilinear alternating bracket written natively as a curried linear map. -/
structure BracketData where
  bracket : V →ₗ[R] V →ₗ[R] V
  alternating : ∀ x : V, bracket x x = 0

variable (B : BracketData (R := R) (V := V))

/-- Leibniz defect.  Vanishing of this expression is exactly the Lie-ring
Leibniz/Jacobi law in Mathlib's orientation. -/
def leibnizDefect (x y z : V) : V :=
  B.bracket x (B.bracket y z) -
    B.bracket (B.bracket x y) z -
    B.bracket y (B.bracket x z)

@[simp] theorem leibnizDefect_add_left (x₁ x₂ y z : V) :
    leibnizDefect B (x₁ + x₂) y z =
      leibnizDefect B x₁ y z + leibnizDefect B x₂ y z := by
  simp [leibnizDefect, map_add]
  abel

@[simp] theorem leibnizDefect_add_middle (x y₁ y₂ z : V) :
    leibnizDefect B x (y₁ + y₂) z =
      leibnizDefect B x y₁ z + leibnizDefect B x y₂ z := by
  simp [leibnizDefect, map_add]
  abel

@[simp] theorem leibnizDefect_add_right (x y z₁ z₂ : V) :
    leibnizDefect B x y (z₁ + z₂) =
      leibnizDefect B x y z₁ + leibnizDefect B x y z₂ := by
  simp [leibnizDefect, map_add]
  abel

@[simp] theorem leibnizDefect_zero_left (y z : V) :
    leibnizDefect B 0 y z = 0 := by
  simp [leibnizDefect]

@[simp] theorem leibnizDefect_zero_middle (x z : V) :
    leibnizDefect B x 0 z = 0 := by
  simp [leibnizDefect]

@[simp] theorem leibnizDefect_zero_right (x y : V) :
    leibnizDefect B x y 0 = 0 := by
  simp [leibnizDefect]

private theorem leibnizDefect_sum_left
    (s : Finset ι) (f : ι → V) (y z : V) :
    leibnizDefect B (∑ i ∈ s, f i) y z =
      ∑ i ∈ s, leibnizDefect B (f i) y z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, leibnizDefect_add_left]

private theorem leibnizDefect_sum_middle
    (s : Finset ι) (x : V) (f : ι → V) (z : V) :
    leibnizDefect B x (∑ i ∈ s, f i) z =
      ∑ i ∈ s, leibnizDefect B x (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, leibnizDefect_add_middle]

private theorem leibnizDefect_sum_right
    (s : Finset ι) (x y : V) (f : ι → V) :
    leibnizDefect B x y (∑ i ∈ s, f i) =
      ∑ i ∈ s, leibnizDefect B x y (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, leibnizDefect_add_right]

/-- Local homogeneous-cell certificate.  This is strictly weaker than a global
Jacobi assumption: it only asks for the finite family of projected triples. -/
structure HomogeneousJacobiCertificate
    (D : DecompositionData (R := R) (V := V) (ι := ι)) : Prop where
  cell : ∀ i j k : ι, ∀ x y z : V,
    leibnizDefect B (D.part i x) (D.part j y) (D.part k z) = 0

/-- The generic closure theorem: homogeneous-cell Jacobi plus a finite linear
decomposition implies the full global Leibniz/Jacobi identity. -/
theorem global_leibniz_of_homogeneous
    (D : DecompositionData (R := R) (V := V) (ι := ι))
    (C : HomogeneousJacobiCertificate B D)
    (x y z : V) :
    B.bracket x (B.bracket y z) =
      B.bracket (B.bracket x y) z + B.bracket y (B.bracket x z) := by
  classical
  have hdefect : leibnizDefect B x y z = 0 := by
    rw [← D.sum_part x, ← D.sum_part y, ← D.sum_part z]
    rw [leibnizDefect_sum_left B Finset.univ]
    apply Finset.sum_eq_zero
    intro i hi
    rw [leibnizDefect_sum_middle B Finset.univ]
    apply Finset.sum_eq_zero
    intro j hj
    rw [leibnizDefect_sum_right B Finset.univ]
    apply Finset.sum_eq_zero
    intro k hk
    exact C.cell i j k x y z
  dsimp [leibnizDefect] at hdefect
  exact sub_sub_eq_zero.mp hdefect

/-- Native Lie-ring promotion from the finite homogeneous certificate. -/
def lieRingOfHomogeneous
    (D : DecompositionData (R := R) (V := V) (ι := ι))
    (C : HomogeneousJacobiCertificate B D) : LieRing V where
  bracket := fun x y => B.bracket x y
  add_lie := by
    intro x y z
    exact (B.bracket.map_add x y z)
  lie_add := by
    intro x y z
    exact ((B.bracket x).map_add y z)
  lie_self := B.alternating
  leibniz_lie := by
    intro x y z
    exact global_leibniz_of_homogeneous B D C x y z

/-- Native scalar compatibility: bilinearity already supplies the Lie-algebra
scalar law. -/
def lieAlgebraOfHomogeneous
    (D : DecompositionData (R := R) (V := V) (ι := ι))
    (C : HomogeneousJacobiCertificate B D) :
    @LieAlgebra R V _ _ _ _ (lieRingOfHomogeneous B D C) where
  lie_smul := by
    intro r x y
    exact (B.bracket x).map_smul r y

end InfoGeometry.Exceptional.GenericGradedJacobiClosure
