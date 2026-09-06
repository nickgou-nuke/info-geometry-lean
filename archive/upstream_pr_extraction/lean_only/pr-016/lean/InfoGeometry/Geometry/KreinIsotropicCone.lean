/-
InfoGeometry/Geometry/KreinIsotropicCone.lean

Krein isotropic cones.

The isotropic cone is geometric carrier data.  Algebraic nilpotents and
zero-divisors are related to it only through representation theorems.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.Geometry.KreinIsotropicCone

/--
A quadratic Krein readout on a real carrier.

The homogeneity law is what makes the null locus projective.
-/
structure KreinQuadraticDatum
    (H : Type*) [AddCommGroup H] [Module ℝ H] where
  /-- Quadratic readout, morally `inner v (J v)`. -/
  q : H → ℝ

  /-- The zero vector is null. -/
  q_zero : q 0 = 0

  /-- Quadratic homogeneity. -/
  q_smul :
    ∀ (a : ℝ) (v : H), q (a • v) = a ^ 2 * q v

/--
The isotropic/null cone.
-/
def IsotropicCone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) : Set H :=
  {v : H | Q.q v = 0}

/--
The strict isotropic cone excludes the zero vector.
-/
def StrictIsotropicCone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) : Set H :=
  {v : H | v ≠ 0 ∧ Q.q v = 0}

/--
The positive cone/component where hyperbolic geometry usually lives.
-/
def PositiveKreinCone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) : Set H :=
  {v : H | 0 < Q.q v}

/--
The negative cone/component.
-/
def NegativeKreinCone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) : Set H :=
  {v : H | Q.q v < 0}

namespace KreinQuadraticDatum

variable {H : Type*} [AddCommGroup H] [Module ℝ H]
variable (Q : KreinQuadraticDatum H)

@[simp]
theorem mem_isotropicCone_iff
    (v : H) :
    v ∈ IsotropicCone Q ↔ Q.q v = 0 :=
  Iff.rfl

@[simp]
theorem mem_strictIsotropicCone_iff
    (v : H) :
    v ∈ StrictIsotropicCone Q ↔ v ≠ 0 ∧ Q.q v = 0 :=
  Iff.rfl

@[simp]
theorem mem_positiveKreinCone_iff
    (v : H) :
    v ∈ PositiveKreinCone Q ↔ 0 < Q.q v :=
  Iff.rfl

@[simp]
theorem mem_negativeKreinCone_iff
    (v : H) :
    v ∈ NegativeKreinCone Q ↔ Q.q v < 0 :=
  Iff.rfl

end KreinQuadraticDatum

@[simp]
theorem zero_mem_isotropicCone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) :
    (0 : H) ∈ IsotropicCone Q := by
  exact Q.q_zero

namespace KreinQuadraticDatum

variable {H : Type*} [AddCommGroup H] [Module ℝ H]
variable (Q : KreinQuadraticDatum H)

/-- The zero vector lies in the isotropic cone. -/
theorem zero_mem_isotropicCone :
    (0 : H) ∈ IsotropicCone Q :=
  InfoGeometry.Geometry.KreinIsotropicCone.zero_mem_isotropicCone Q

/--
The isotropic cone is stable under scalar multiplication.
-/
theorem smul_mem_isotropicCone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H)
    {v : H}
    (hv : v ∈ IsotropicCone Q)
    (a : ℝ) :
    a • v ∈ IsotropicCone Q := by
  dsimp [IsotropicCone] at hv ⊢
  rw [Q.q_smul, hv, mul_zero]

/-- The positive cone is stable under nonzero real scaling. -/
theorem smul_mem_positiveKreinCone
    {a : ℝ}
    (ha : a ≠ 0)
    {v : H}
    (hv : v ∈ PositiveKreinCone Q) :
    a • v ∈ PositiveKreinCone Q := by
  dsimp [PositiveKreinCone] at hv ⊢
  rw [Q.q_smul]
  exact mul_pos (sq_pos_of_ne_zero ha) hv

/-- The negative cone is stable under nonzero real scaling. -/
theorem smul_mem_negativeKreinCone
    {a : ℝ}
    (ha : a ≠ 0)
    {v : H}
    (hv : v ∈ NegativeKreinCone Q) :
    a • v ∈ NegativeKreinCone Q := by
  dsimp [NegativeKreinCone] at hv ⊢
  rw [Q.q_smul]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ha) hv

/-- The positive cone is disjoint from the isotropic cone. -/
theorem positive_not_isotropic
    {v : H}
    (hv : v ∈ PositiveKreinCone Q) :
    v ∉ IsotropicCone Q := by
  intro h0
  have hp : 0 < Q.q v := hv
  have hz : Q.q v = 0 := h0
  linarith

/-- The negative cone is disjoint from the isotropic cone. -/
theorem negative_not_isotropic
    {v : H}
    (hv : v ∈ NegativeKreinCone Q) :
    v ∉ IsotropicCone Q := by
  intro h0
  have hn : Q.q v < 0 := hv
  have hz : Q.q v = 0 := h0
  linarith

end KreinQuadraticDatum

/--
Projective ray equivalence.
-/
def SameProjectiveRay
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (v w : H) : Prop :=
  ∃ lam : ℝ, lam ≠ 0 ∧ w = lam • v

/--
A represented algebraic defect geometry.

The algebraic defect locus is not definitionally the isotropic cone.  The
representation supplies a carrier readout, and the bridge theorem says defects
land in the geometric null cone.
-/
structure DefectMapsToIsotropic
    (Split H : Type*)
    [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) where
  /-- Defect locus inside the split source. -/
  defectLocus : Set Split

  /-- Carrier readout of a split element. -/
  carrierReadout : Split → H

  /-- Algebraic defects map to isotropic vectors. -/
  defect_is_isotropic :
    ∀ a : Split,
      a ∈ defectLocus →
        carrierReadout a ∈ IsotropicCone Q

namespace DefectMapsToIsotropic

variable {Split H : Type*}
variable [AddCommGroup H] [Module ℝ H]
variable {Q : KreinQuadraticDatum H}
variable (W : DefectMapsToIsotropic Split H Q)

/-- A defect-locus element has null Krein quadratic readout. -/
theorem defect_q_zero
    {a : Split}
    (ha : a ∈ W.defectLocus) :
    Q.q (W.carrierReadout a) = 0 :=
  W.defect_is_isotropic a ha

/-- A defect-locus element maps into the isotropic cone. -/
theorem defect_mem_isotropic
    {a : Split}
    (ha : a ∈ W.defectLocus) :
    W.carrierReadout a ∈ IsotropicCone Q :=
  W.defect_is_isotropic a ha

end DefectMapsToIsotropic

/-! ## Owner target -/

/--
Owner target for connecting represented algebraic defects to carrier-null
geometry.
-/
def DefectToIsotropicOwnerTarget
    (Split H : Type*) [AddCommGroup H] [Module ℝ H]
    (Q : KreinQuadraticDatum H) : Prop :=
  Nonempty (DefectMapsToIsotropic Split H Q)

end InfoGeometry.Geometry.KreinIsotropicCone
