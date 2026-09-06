import InfoGeometry.Canonical.MultiplicativeToAdditiveBridge

/-!
# InfoGeometry.Canonical.VolumeDeformationPrinciple

Canonical physical naming for the already-owned multiplicative-to-additive
descent pattern

`noncommutative multiplicative source -> commutative multiplicative volume
character -> additive deformation potential`.

This file introduces no new primitive structures. It re-exports the exact and
defective bridge owners under volume-deformation language.
-/

namespace InfoGeometry.Canonical.VolumeDeformationPrinciple

open InfoGeometry.Canonical

abbrev ExactVolumeBridge
    (M S A : Type*)
    [Monoid M] [CommMonoid S] [AddCommMonoid A] :=
  ExactMultiplicativeToAdditiveBridge M S A

abbrev DefectiveVolumeBridge
    (M S A : Type*)
    [Monoid M] [CommMonoid S] [AddCommMonoid A] :=
  DefectiveMultiplicativeToAdditiveBridge M S A

namespace ExactVolumeBridge

variable {M S A : Type*}
variable [Monoid M] [CommMonoid S] [AddCommMonoid A]

/-- The descended additive volume / entropic potential. -/
def potential (B : ExactVolumeBridge M S A) : M → A :=
  B.additiveInvariant

/-- Exact multiplicative descent gives additive volume deformation upstairs. -/
theorem potential_mul (B : ExactVolumeBridge M S A) (x y : M) :
    B.potential (x * y) = B.potential x + B.potential y :=
  B.additiveInvariant_mul x y

end ExactVolumeBridge

namespace DefectiveVolumeBridge

variable {M S A : Type*}
variable [Monoid M] [CommMonoid S] [AddCommMonoid A]

/-- The descended additive potential with anomaly bookkeeping. -/
def potential (B : DefectiveVolumeBridge M S A) : M → A :=
  B.additiveInvariant

/-- Linearized defect term of non-exact multiplicative descent. -/
def anomaly (B : DefectiveVolumeBridge M S A) : M → M → A :=
  B.additiveDefect

/-- Defective descent becomes additive up to the anomaly term. -/
theorem potential_mul
    (B : DefectiveVolumeBridge M S A) (x y : M) :
    B.potential (x * y)
      = B.anomaly x y + (B.potential x + B.potential y) :=
  B.additiveInvariant_mul x y

end DefectiveVolumeBridge


section CommutatorPotential

variable {G S A : Type*}
variable [Group G] [CommGroup S] [AddCommGroup A]

/-- Multiplicative commutator in a group. -/
def mulCommutator (x y : G) : G :=
  x * y * x⁻¹ * y⁻¹

namespace ExactVolumeBridge

private theorem linearize_one_eq_zero
    (B : ExactVolumeBridge G S A) :
    B.toAdditiveLinearization.linearize (1 : S) = 0 := by
  let a := B.toAdditiveLinearization.linearize (1 : S)
  have h : a + a = a := by
    simpa [a] using (B.toAdditiveLinearization.map_mul (1 : S) (1 : S)).symm
  apply add_left_cancel (a := a)
  simpa [a] using h

-- theorem-class: lower bridge identification
/-- The descended commutative character kills multiplicative commutators. -/
theorem character_mulCommutator_eq_one
    (B : ExactVolumeBridge G S A) (x y : G) :
    B.toExactAbelianizingBridge.character (mulCommutator x y) = 1 := by
  simp [mulCommutator, mul_assoc]

-- theorem-class: transport lemma
/-- The additive volume potential of a multiplicative commutator is zero. -/
theorem potential_mulCommutator_eq_zero
    (B : ExactVolumeBridge G S A) (x y : G) :
    B.potential (mulCommutator x y) = 0 := by
  unfold potential ExactMultiplicativeToAdditiveBridge.additiveInvariant
  rw [character_mulCommutator_eq_one (B := B) (x := x) (y := y)]
  exact linearize_one_eq_zero (B := B)

end ExactVolumeBridge

end CommutatorPotential

end InfoGeometry.Canonical.VolumeDeformationPrinciple
