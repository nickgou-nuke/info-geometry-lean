import InfoGeometry.Algebra.Zorn.G2PCPositiveRootPacket
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Labels for the verified positive-root PC packet

This file separates two carriers which must not be identified:

* `positiveRootPacket` is the older Steinberg packet of concrete root
  automorphisms;
* `pcPositiveRootPacket` is the six-element packet built from the verified
  PC generators.

The equivalence below is only an equivalence of the six abstract labels with
the six PC coordinates.  It does not assert equality between those two
concrete packets.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootPCAlignment

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2PCPositiveRootPacket
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

private def rootPCIndex : G2PositiveRoot → Fin 6
  | .alpha => 0
  | .beta => 1
  | .alpha_add_beta => 2
  | .two_alpha_beta => 3
  | .three_alpha_beta => 4
  | .three_alpha_two_beta => 5

private theorem rootPCIndex_injective : Function.Injective rootPCIndex := by
  intro a b h
  cases a <;> cases b <;> simp [rootPCIndex] at h ⊢

private theorem rootPCIndex_surjective : Function.Surjective rootPCIndex := by
  intro i
  fin_cases i
  · exact ⟨.alpha, rfl⟩
  · exact ⟨.beta, rfl⟩
  · exact ⟨.alpha_add_beta, rfl⟩
  · exact ⟨.two_alpha_beta, rfl⟩
  · exact ⟨.three_alpha_beta, rfl⟩
  · exact ⟨.three_alpha_two_beta, rfl⟩

/-- The coordinate equivalence for the verified PC positive-root labels. -/
noncomputable def rootPCAlignment : G2PositiveRoot ≃ Fin 6 :=
  Equiv.ofBijective rootPCIndex ⟨rootPCIndex_injective, rootPCIndex_surjective⟩

@[simp] theorem rootPCAlignment_apply (α : G2PositiveRoot) :
    rootPCAlignment α = rootPCIndex α := rfl

@[simp] theorem pcPositiveRootPacket_eq_aligned_generator
    (α : G2PositiveRoot) :
    pcPositiveRootPacket α =
      pcGenerator (rootPCAlignment α) := by
  rfl

/-- Transport of the six binary PC coordinates to the abstract positive-root
labels.  This is a coordinate equivalence, not an identification of the
older Steinberg automorphism packet with the PC generators. -/
noncomputable def rootPCCoordinateEquiv :
    (G2PositiveRoot → ZMod 2) ≃ (Fin 6 → ZMod 2) :=
  Equiv.arrowCongr rootPCAlignment (Equiv.refl (ZMod 2))

@[simp] theorem rootPCCoordinateEquiv_apply
    (x : G2PositiveRoot → ZMod 2) (i : Fin 6) :
    rootPCCoordinateEquiv x i = x (rootPCAlignment.symm i) := by
  rfl

theorem rootPCCoordinate_card :
    Fintype.card (G2PositiveRoot → ZMod 2) = 64 := by
  rw [Fintype.card_congr rootPCCoordinateEquiv]
  simp

theorem pcPositiveRootPacket_range_eq_aligned_generator_range :
    Set.range pcPositiveRootPacket =
      Set.range (fun α : G2PositiveRoot => pcGenerator (rootPCAlignment α)) := by
  ext g
  constructor
  · rintro ⟨α, rfl⟩
    exact ⟨α, (pcPositiveRootPacket_eq_aligned_generator α).symm⟩
  · rintro ⟨α, rfl⟩
    exact ⟨α, pcPositiveRootPacket_eq_aligned_generator α⟩

end InfoGeometry.Algebra.Zorn.G2RootPCAlignment
