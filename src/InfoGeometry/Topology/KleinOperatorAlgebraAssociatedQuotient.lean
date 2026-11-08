/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinGlideCovering
import InfoGeometry.Canonical.KleinSixStateBundle
import Mathlib.Topology.Constructions

/-!
# The honest six-state operator-algebra quotient over the Klein base

Although the state representation is naturally projective, conjugation is
insensitive to central scalar signs.  This file constructs the literal orbit
quotient of the matrix algebra by the simultaneous base glide and inner
automorphism `A ↦ Θ A Θ`.

Local vector-bundle packaging is deliberately separated into the covering
atlas / `VectorBundleCore` owner.  Here the quotient and all fibrewise algebra
laws are genuine and require no projective lift.
-/

noncomputable section
namespace KleinOperatorAlgebraAssociatedQuotient

open KleinBrillouinBase KleinBottleOrbitQuotient
open InfoGeometry.Canonical.KleinSixStateBundle

abbrev Operator := Mat23C

/-- Conjugation by the sheet-colour reflection.  Since `Θ²=1`, the same
formula is its inverse. -/
def operatorGlide (A : Operator) : Operator := theta * A * theta

theorem operatorGlide_involutive (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Function.Involutive operatorGlide := by
  intro A
  calc
    operatorGlide (operatorGlide A) =
        (theta * theta) * A * (theta * theta) := by
          simp only [operatorGlide]
          noncomm_ring
    _ = A := by
      simp only [← pow_two, theta_sq, one_mul, mul_one]

@[simp] theorem operatorGlide_zero : operatorGlide 0 = 0 := by
  simp [operatorGlide]

theorem operatorGlide_add (A B : Operator) :
    operatorGlide (A + B) = operatorGlide A + operatorGlide B := by
  simp [operatorGlide, Matrix.mul_add, Matrix.add_mul]

theorem operatorGlide_smul (c : ℂ) (A : Operator) :
    operatorGlide (c • A) = c • operatorGlide A := by
  simp [operatorGlide]

theorem operatorGlide_one (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    operatorGlide 1 = 1 := by
  simpa only [operatorGlide, mul_one, ← pow_two] using theta_sq

theorem operatorGlide_mul (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (A B : Operator) :
    operatorGlide (A * B) = operatorGlide A * operatorGlide B := by
  calc
    operatorGlide (A * B) = theta * A * B * theta := by
      simp [operatorGlide, Matrix.mul_assoc]
    _ = theta * A * (theta * theta) * B * theta := by
      rw [← pow_two, theta_sq]
      simp [Matrix.mul_assoc]
    _ = operatorGlide A * operatorGlide B := by
      simp [operatorGlide, Matrix.mul_assoc]

/-- A central scalar sign is invisible to the conjugation action. -/
theorem neg_conjugator_same (A : Operator) :
    (-theta) * A * (-theta) = operatorGlide A := by
  simp [operatorGlide]

/-- Simultaneous glide on the base and the full operator algebra. -/
def totalOperatorGlide (p : BrillouinTorus × Operator) :
    BrillouinTorus × Operator :=
  (torusGlide p.1, operatorGlide p.2)

theorem totalOperatorGlide_involutive (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Function.Involutive totalOperatorGlide := by
  rintro ⟨k, A⟩
  apply Prod.ext
  · exact torusGlide_involutive k
  · exact operatorGlide_involutive omega homega A

/-- Orbit relation of the simultaneous involution. -/
def totalOperatorGlideSetoid (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Setoid (BrillouinTorus × Operator) where
  r x y := y = x ∨ y = totalOperatorGlide x
  iseqv := by
    constructor
    · intro x; exact Or.inl rfl
    · intro x y h
      rcases h with rfl | h
      · exact Or.inl rfl
      · right
        rw [h, totalOperatorGlide_involutive omega homega]
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      · rcases hyz with rfl | hyz
        · exact Or.inr hxy
        · left
          rw [hyz, hxy, totalOperatorGlide_involutive omega homega]

abbrev AssociatedOperatorAlgebra (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :=
  Quotient (totalOperatorGlideSetoid omega homega)

def totalQuotientMap (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    BrillouinTorus × Operator → AssociatedOperatorAlgebra omega homega :=
  @Quotient.mk' _ (totalOperatorGlideSetoid omega homega)

private def representativeBase (p : BrillouinTorus × Operator) :
    KleinBrillouinQuotient := quotientMap p.1

private theorem representativeBase_respects (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (x y : BrillouinTorus × Operator)
    (h : (totalOperatorGlideSetoid omega homega).r x y) :
    representativeBase x = representativeBase y := by
  rcases h with rfl | h
  · rfl
  · rw [h]
    exact (quotientMap_glide x.1).symm

def bundleProjection (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    AssociatedOperatorAlgebra omega homega → KleinBrillouinQuotient :=
  Quotient.lift representativeBase (representativeBase_respects omega homega)

@[simp] theorem bundleProjection_mk (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (p : BrillouinTorus × Operator) :
    bundleProjection omega homega (totalQuotientMap omega homega p) =
      quotientMap p.1 := rfl

theorem bundleProjection_continuous (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Continuous (bundleProjection omega homega) := by
  apply continuous_quot_lift
  exact quotientMap_continuous.comp continuous_fst

theorem bundleProjection_surjective (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Function.Surjective (bundleProjection omega homega) := by
  intro q
  obtain ⟨k, rfl⟩ := quotientMap_surjective q
  exact ⟨totalQuotientMap omega homega (k, 0), rfl⟩

/-- Kernel-checked packet: the quotient is a genuine orbit quotient over the
Klein base and its fibre gluing map is a complex algebra automorphism. -/
theorem operator_algebra_quotient_packet (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Function.Surjective (bundleProjection omega homega) ∧
    Continuous (bundleProjection omega homega) ∧
    Function.Involutive operatorGlide ∧
    (∀ A B : Operator,
      operatorGlide (A * B) = operatorGlide A * operatorGlide B) :=
  ⟨bundleProjection_surjective omega homega,
   bundleProjection_continuous omega homega,
   operatorGlide_involutive omega homega,
   operatorGlide_mul omega homega⟩

/-! ## Möbius conjugation descends through the Klein operator gluing -/

/-- The operator Möbius action on a single fibre, written without an
operator-valued division: `A ↦ u A u⁻¹`. The inverse is supplied explicitly
so the definition retains the ordered noncommutative product. -/
def operatorMobiusConjugation (u uInv A : Operator) : Operator :=
  u * A * uInv

/-- A conjugation descends across the Klein seam when its two group factors
are fixed by the seam involution. This is the equivariance condition needed
by the orbit quotient, proved using the existing operator-glide algebra law. -/
theorem operatorMobiusConjugation_glide_equivariant
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (u uInv A : Operator)
    (hu : operatorGlide u = u) (huInv : operatorGlide uInv = uInv) :
    operatorMobiusConjugation u uInv (operatorGlide A) =
      operatorGlide (operatorMobiusConjugation u uInv A) := by
  change u * operatorGlide A * uInv = operatorGlide (u * A * uInv)
  calc
    u * operatorGlide A * uInv =
        operatorGlide u * operatorGlide A * operatorGlide uInv := by
          rw [hu, huInv]
    _ = operatorGlide (u * A * uInv) := by
          rw [operatorGlide_mul omega homega (u * A) uInv,
            operatorGlide_mul omega homega u A]

/-- Simultaneous base glide and operator Möbius conjugation commute. -/
def totalOperatorMobiusConjugation (u uInv : Operator)
    (p : BrillouinTorus × Operator) : BrillouinTorus × Operator :=
  (p.1, operatorMobiusConjugation u uInv p.2)

theorem totalOperatorMobiusConjugation_commutes_glide
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (u uInv : Operator)
    (hu : operatorGlide u = u) (huInv : operatorGlide uInv = uInv)
    (p : BrillouinTorus × Operator) :
    totalOperatorMobiusConjugation u uInv (totalOperatorGlide p) =
      totalOperatorGlide (totalOperatorMobiusConjugation u uInv p) := by
  apply Prod.ext
  · rfl
  · exact operatorMobiusConjugation_glide_equivariant omega homega
      u uInv p.2 hu huInv

/-- The fibrewise operator Möbius conjugation induces a well-defined map on
the already-constructed Klein orbit quotient. The only extra condition is
that the chosen conjugator and inverse are fixed by the gluing involution. -/
noncomputable def operatorMobiusConjugationOnQuotient
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (u uInv : Operator)
    (hu : operatorGlide u = u) (huInv : operatorGlide uInv = uInv) :
    AssociatedOperatorAlgebra omega homega → AssociatedOperatorAlgebra omega homega :=
  Quotient.lift
    (fun p => totalQuotientMap omega homega
      (totalOperatorMobiusConjugation u uInv p))
    (by
      intro p q hpq
      apply Quotient.sound
      rcases hpq with h | h
      · rw [h]
      · rw [h, totalOperatorMobiusConjugation_commutes_glide
          omega homega u uInv hu huInv]
        exact Or.inr rfl)

@[simp] theorem operatorMobiusConjugationOnQuotient_mk
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (u uInv : Operator)
    (hu : operatorGlide u = u) (huInv : operatorGlide uInv = uInv)
    (p : BrillouinTorus × Operator) :
    operatorMobiusConjugationOnQuotient omega homega u uInv hu huInv
        (totalQuotientMap omega homega p) =
      totalQuotientMap omega homega
        (totalOperatorMobiusConjugation u uInv p) := rfl

theorem continuous_totalOperatorMobiusConjugation (u uInv : Operator) :
    Continuous (totalOperatorMobiusConjugation u uInv) := by
  apply Continuous.prodMk
  · exact continuous_fst
  · exact (continuous_const.mul continuous_snd).mul continuous_const

/-- The descended Möbius map is continuous in the quotient topology. -/
theorem operatorMobiusConjugationOnQuotient_continuous
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (u uInv : Operator)
    (hu : operatorGlide u = u) (huInv : operatorGlide uInv = uInv) :
    Continuous (operatorMobiusConjugationOnQuotient
      omega homega u uInv hu huInv) := by
  apply continuous_quot_lift
  exact continuous_quotient_mk'.comp
    (continuous_totalOperatorMobiusConjugation u uInv)

end KleinOperatorAlgebraAssociatedQuotient
end noncomputable section
