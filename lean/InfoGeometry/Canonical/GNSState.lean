import Mathlib.Tactic
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.Canonical.GNSState

open scoped BigOperators

open InfoGeometry.Canonical.CantorCuntzBasis

/-!
# Finite-Cylinder GNS State

This file replaces the abstract generated `CuntzAlgebra` socket with the
finite-cylinder substrate needed before a real GNS completion can be built.

The carrier is the finitely supported real vector space on finite binary
cylinder words.  The pre-inner product is the uniform KMS/Born cylinder
quadratic form

`⟪x,y⟫ = Σ_w x_w y_w 2^(-|w|)`.

This is not the completed GNS Hilbert space and it is not claimed to be
isomorphic to `ℓ²(BinaryWord, ℝ²)`.  Those analytic completion and
identification theorems remain explicit closure debt.

#### BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully
checked by the kernel.]

* `gnsPreInner_zero_left`
* `gnsPreInner_zero_right`
* `gnsCylinderWeight_nonneg`
* `gnsCylinderWeight_cons`
* `gnsPreInner_symm`
* `gnsPreInner_self_nonneg`
* `gnsPreInner_basis_self`
* `gnsPreInner_basis_ne`
* `gnsPreInner_basis_cons_self`
* `gnsPreInner_basis_false_true`
* `gnsPreInner_basis_true_false`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported
verified premises.]

* None.

#### BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields,
witnesses, certificates, or renamed placeholders.]

* Construct the GNS null quotient for `gnsPreInner`.
* Complete that quotient as a Hilbert space.
* Prove the explicit unitary identification with the concrete Hilbert/Cantor
  boundary carrier.
* Transport the Cuntz branch operators and phase-axis commutation through that
  completed representation.
-/

/-- Finite real cylinder vectors on binary words. -/
@[rep_depth operator]
abbrev CylinderVector : Type :=
  BinaryWord →₀ ℝ

/-- Basis vector for a finite binary cylinder word. -/
@[rep_depth operator]
def cylinderBasis (w : BinaryWord) : CylinderVector :=
  Finsupp.single w 1

/-- Uniform binary GNS/KMS cylinder weight: `2^-|w|`. -/
@[rep_depth operator]
def gnsCylinderWeight (w : BinaryWord) : ℝ :=
  ((1 / 2 : ℝ) ^ w.length)

@[rep_depth operator]
theorem gnsCylinderWeight_nonneg (w : BinaryWord) :
    0 ≤ gnsCylinderWeight w := by
  unfold gnsCylinderWeight
  exact pow_nonneg (by norm_num) w.length

/-- Prefixing either binary branch halves the finite-cylinder weight. -/
@[rep_depth operator]
theorem gnsCylinderWeight_cons (b : Bool) (w : BinaryWord) :
    gnsCylinderWeight (b :: w) = (1 / 2 : ℝ) * gnsCylinderWeight w := by
  simp [gnsCylinderWeight, pow_succ, mul_comm]

/--
Uniform KMS/Born pre-inner product on finite cylinder vectors.

The support union is used only to make the finite sum manifest for both inputs.
-/
@[rep_depth operator]
def gnsPreInner (x y : CylinderVector) : ℝ :=
  Finset.sum (x.support ∪ y.support) (fun w => x w * y w * gnsCylinderWeight w)

@[simp, rep_depth operator]
theorem gnsPreInner_zero_left (x : CylinderVector) :
    gnsPreInner 0 x = 0 := by
  simp [gnsPreInner]

@[simp, rep_depth operator]
theorem gnsPreInner_zero_right (x : CylinderVector) :
    gnsPreInner x 0 = 0 := by
  simp [gnsPreInner]

/-- The finite-cylinder GNS pre-inner product is symmetric over `ℝ`. -/
@[rep_depth operator]
theorem gnsPreInner_symm (x y : CylinderVector) :
    gnsPreInner x y = gnsPreInner y x := by
  unfold gnsPreInner
  rw [Finset.union_comm]
  refine Finset.sum_congr rfl ?_
  intro w _
  ring

/-- The finite-cylinder GNS quadratic form is nonnegative. -/
@[rep_depth operator]
theorem gnsPreInner_self_nonneg (x : CylinderVector) :
    0 ≤ gnsPreInner x x := by
  unfold gnsPreInner
  refine Finset.sum_nonneg ?_
  intro w _
  exact mul_nonneg (mul_self_nonneg (x w)) (gnsCylinderWeight_nonneg w)

/-- A basis cylinder has squared norm equal to its KMS cylinder weight. -/
@[simp, rep_depth operator]
theorem gnsPreInner_basis_self (w : BinaryWord) :
    gnsPreInner (cylinderBasis w) (cylinderBasis w) = gnsCylinderWeight w := by
  unfold gnsPreInner cylinderBasis
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hvw
    simp [Finsupp.single_eq_of_ne hvw]
  · intro hw
    simp at hw

/-- Distinct basis cylinders are orthogonal. -/
@[rep_depth operator]
theorem gnsPreInner_basis_ne {u v : BinaryWord} (h : u ≠ v) :
    gnsPreInner (cylinderBasis u) (cylinderBasis v) = 0 := by
  unfold gnsPreInner cylinderBasis
  refine Finset.sum_eq_zero ?_
  intro w _
  by_cases hwu : w = u
  · subst w
    simp [Finsupp.single_eq_of_ne h]
  · simp [Finsupp.single_eq_of_ne hwu]

/-- Prefixing the same branch halves the squared basis-cylinder norm. -/
@[rep_depth operator]
theorem gnsPreInner_basis_cons_self (b : Bool) (w : BinaryWord) :
    gnsPreInner (cylinderBasis (b :: w)) (cylinderBasis (b :: w)) =
      (1 / 2 : ℝ) * gnsPreInner (cylinderBasis w) (cylinderBasis w) := by
  simp [gnsCylinderWeight_cons]

/-- Opposite cylinder branches are orthogonal in the finite GNS pre-inner product. -/
@[rep_depth operator]
theorem gnsPreInner_basis_false_true (u v : BinaryWord) :
    gnsPreInner (cylinderBasis (false :: u)) (cylinderBasis (true :: v)) = 0 := by
  exact gnsPreInner_basis_ne (by intro h; cases h)

/-- Opposite cylinder branches are orthogonal in the finite GNS pre-inner product. -/
@[rep_depth operator]
theorem gnsPreInner_basis_true_false (u v : BinaryWord) :
    gnsPreInner (cylinderBasis (true :: u)) (cylinderBasis (false :: v)) = 0 := by
  exact gnsPreInner_basis_ne (by intro h; cases h)

end InfoGeometry.Canonical.GNSState
