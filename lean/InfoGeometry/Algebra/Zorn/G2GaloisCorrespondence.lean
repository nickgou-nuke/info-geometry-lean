import InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators

/-!
# The Galois Connection for the native split-octonion carrier

This module formalizes the elementary Galois connection between subgroups of
the native automorphism carrier `SplitOctF2Aut` and invariant subsets of the
split-octonion carrier `SplitOctF2`.

In particular:
- Any subgroup `H ≤ SplitOctF2Aut` defines a Galois fixed set `galoisFixedSet H`.
- Any subset `S ⊆ SplitOctF2` defines a Galois stabilizer `galoisStabilizer S`.
- The pair `(galoisFixedSet, galoisStabilizer)` forms an antitone Galois connection.
- The native flag stabilizer fixes the base point `basis8 4`; no subgroup
  equality or parabolic identification is asserted here.
-/

namespace InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

/-- The Galois fixed set in `Oₛ(𝔽₂)` of a subgroup `H ≤ SplitOctF2Aut`. -/
def galoisFixedSet (H : Subgroup SplitOctF2Aut) : Set SplitOctF2 :=
  { X : SplitOctF2 | ∀ g : SplitOctF2Aut, g ∈ H → g.1 X = X }

/-- The Galois stabilizer subgroup in `SplitOctF2Aut` of a set `S ⊆ Oₛ(𝔽₂)`. -/
def galoisStabilizer (S : Set SplitOctF2) : Subgroup SplitOctF2Aut where
  carrier := { g : SplitOctF2Aut | ∀ X ∈ S, g.1 X = X }
  one_mem' := by
    intro X _
    rfl
  mul_mem' := by
    intro g h hg hh X hX
    rw [automorphism_mul_apply]
    rw [hg X hX]
    exact hh X hX
  inv_mem' := by
    intro g hg X hX
    have hgX := hg X hX
    have hid : (g * g⁻¹).1 X = X := by
      rw [mul_inv_cancel]
      rfl
    rw [automorphism_mul_apply] at hid
    rw [hgX] at hid
    exact hid

theorem mem_galoisFixedSet_iff (H : Subgroup SplitOctF2Aut) (X : SplitOctF2) :
    X ∈ galoisFixedSet H ↔ ∀ g : SplitOctF2Aut, g ∈ H → g.1 X = X :=
  Iff.rfl

theorem mem_galoisStabilizer_iff (S : Set SplitOctF2) (g : SplitOctF2Aut) :
    g ∈ galoisStabilizer S ↔ ∀ X ∈ S, g.1 X = X :=
  Iff.rfl

/-- The fundamental Galois connection between subgroups of `G₂(𝔽₂)` and subsets of `Oₛ(𝔽₂)`. -/
theorem galois_connection (H : Subgroup SplitOctF2Aut) (S : Set SplitOctF2) :
    H ≤ galoisStabilizer S ↔ S ⊆ galoisFixedSet H := by
  constructor
  · intro hLE X hX g hg
    exact hLE hg X hX
  · intro hSub g hg X hX
    exact hSub hX g hg

/-- Antitone property for the fixed set map. -/
theorem galoisFixedSet_antitone {H₁ H₂ : Subgroup SplitOctF2Aut} (h : H₁ ≤ H₂) :
    galoisFixedSet H₂ ⊆ galoisFixedSet H₁ := by
  intro X hX g hg
  exact hX g (h hg)

/-- Antitone property for the stabilizer subgroup map. -/
theorem galoisStabilizer_antitone {S₁ S₂ : Set SplitOctF2} (h : S₁ ⊆ S₂) :
    galoisStabilizer S₂ ≤ galoisStabilizer S₁ := by
  intro g hg X hX
  exact hg X (h hX)

theorem galoisFixedSet_mono {H₁ H₂ : Subgroup SplitOctF2Aut} (h : H₁ ≤ H₂) :
    galoisFixedSet H₂ ⊆ galoisFixedSet H₁ :=
  galoisFixedSet_antitone h

theorem galoisStabilizer_mono {S₁ S₂ : Set SplitOctF2} (h : S₁ ⊆ S₂) :
    galoisStabilizer S₂ ≤ galoisStabilizer S₁ :=
  galoisStabilizer_antitone h

/-- Subgroup inclusion into the double Galois dual. -/
theorem subgroup_le_galois_closure (H : Subgroup SplitOctF2Aut) :
    H ≤ galoisStabilizer (galoisFixedSet H) := by
  rw [galois_connection]

/-- Subset inclusion into the double Galois dual. -/
theorem subset_le_galois_closure (S : Set SplitOctF2) :
    S ⊆ galoisFixedSet (galoisStabilizer S) := by
  intro X hX g hg
  exact hg X hX

/-! The two Galois maps induce genuine closure operators on their respective
    powersets.  The inclusions above are the extensive half; the following
    equalities record idempotence without adding any finite-cardinality or
    representation-theoretic assumptions. -/

theorem galoisFixedSet_galoisStabilizer_fixedSet (H : Subgroup SplitOctF2Aut) :
    galoisFixedSet (galoisStabilizer (galoisFixedSet H)) =
      galoisFixedSet H := by
  apply Set.Subset.antisymm
  · intro X hX g hg
    exact hX g (subgroup_le_galois_closure H hg)
  · exact subset_le_galois_closure (galoisFixedSet H)

theorem galoisStabilizer_galoisFixedSet_stabilizer (S : Set SplitOctF2) :
    galoisStabilizer (galoisFixedSet (galoisStabilizer S)) =
      galoisStabilizer S := by
  apply le_antisymm
  · intro g hg X hX
    exact hg X (subset_le_galois_closure S hX)
  · exact subgroup_le_galois_closure (galoisStabilizer S)

/-- The scalar 0 is in the Galois fixed set of every subgroup. -/
theorem zero_mem_galoisFixedSet (H : Subgroup SplitOctF2Aut) :
    zero ∈ galoisFixedSet H := by
  intro g _
  exact automorphism_map_zero g

theorem add_mem_galoisFixedSet {H : Subgroup SplitOctF2Aut}
    {X Y : SplitOctF2}
    (hX : X ∈ galoisFixedSet H) (hY : Y ∈ galoisFixedSet H) :
    add X Y ∈ galoisFixedSet H := by
  intro g hg
  change g.1 (add X Y) = add X Y
  rw [automorphism_map_add, hX g hg, hY g hg]

theorem mul_mem_galoisFixedSet {H : Subgroup SplitOctF2Aut}
    {X Y : SplitOctF2}
    (hX : X ∈ galoisFixedSet H) (hY : Y ∈ galoisFixedSet H) :
    mul X Y ∈ galoisFixedSet H := by
  intro g hg
  change g.1 (mul X Y) = mul X Y
  rw [g.2.2.2, hX g hg, hY g hg]

/-- The unit 1 (ePlus + eMinus) is in the Galois fixed set of every subgroup. -/
theorem one_mem_galoisFixedSet (H : Subgroup SplitOctF2Aut) :
    one ∈ galoisFixedSet H := by
  intro g _
  exact g.2.1

/-- The base isotropic point `basis8 4` is a Galois invariant of the native flag stabilizer `B`. -/
theorem basis8_four_mem_galoisFixedSet_nativeFlagStabilizer :
    basis8 4 ∈ galoisFixedSet nativeFlagStabilizer := by
  intro g hg
  exact nativeFlagStabilizer_basis8_four hg

/-- The native flag stabilizer `B` is contained in the Galois stabilizer of `basis8 4`. -/
theorem nativeFlagStabilizer_le_galoisStabilizer_basis8_four :
    nativeFlagStabilizer ≤ galoisStabilizer {basis8 4} := by
  rw [galois_connection]
  intro X hX
  rcases hX with rfl
  exact basis8_four_mem_galoisFixedSet_nativeFlagStabilizer

/-- The unipotent radical `U` is contained in the Galois stabilizer of `basis8 4`. -/
theorem unipotentSubgroup_le_galoisStabilizer_basis8_four :
    unipotentSubgroup ≤ galoisStabilizer {basis8 4} := by
  exact le_trans unipotentSubgroup_le_nativeFlagStabilizer
    nativeFlagStabilizer_le_galoisStabilizer_basis8_four

/-- The base isotropic point `basis8 4` is a Galois invariant of `unipotentSubgroup`. -/
theorem basis8_four_mem_galoisFixedSet_unipotentSubgroup :
    basis8 4 ∈ galoisFixedSet unipotentSubgroup := by
  intro u hu
  exact nativeFlagStabilizer_basis8_four (unipotentSubgroup_le_nativeFlagStabilizer hu)

/-- Every element of the unipotent radical has trivial fullPeel residual (Galois identity). -/
theorem unipotent_fullPeel_galois_trivial
    {u : SplitOctF2Aut} (hu : u ∈ unipotentSubgroup) :
    fullPeel u = 1 :=
  fullPeel_unipotent_eq_one hu

end InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence
