/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.KleinAction

/-!
# The tetraktys sandwich channels realize the conditional Klein action

When the horizon operator is the identity, the four tetraktys sandwich
channels reduce to the identity and the three nontrivial automorphisms in the
Peirce Klein action. This identifies the character channels with actual
superoperators on the ambient noncommutative ring, without claiming that the
off-shell homogenized projectors are automorphisms.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P) (A C : B)

/-- On the unit-horizon locus, the four tetraktys sandwich maps are exactly
the identity, the `Φ` conjugation, its product with Peirce parity, and parity.
Thus the character channels are the four maps of the existing Klein action.
-/
theorem tetraktys_sandwich_channels_are_peirce_klein_action
    (hV : genV P A C = 1) (X : B) :
    grpId P A C X = X ∧
    grpPhi P A C X = phiUnitSquareEquiv hP A C hV X ∧
    grpJ P A C X = phiUnitSquareEquiv hP A C hV (parityConjRingEquiv hP X) ∧
    grpSig P A C X = parityConjRingEquiv hP X := by
  have hPhiSq : genPhi P A C * genPhi P A C = 1 := by
    calc
      genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
      _ = 1 := hV
  have hSigV : genSig P A C = invS P * genV P A C :=
    (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.2.2.2.2.2.2.1
  have hSig : genSig P A C = invS P := by
    rw [hSigV, hV]
    simp
  have hJ : genJ P A C = -(genPhi P A C * invS P) := by
    peirce_nf hP
  have hPhiS : genPhi P A C * invS P = -genJ P A C := by
    peirce_nf hP
  have hSPhi : invS P * genPhi P A C = genJ P A C := by
    peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [grpId, hV]
  · change genV P A C * (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * X * genPhi P A C
    rw [hV]
    simp
  · change -(genV P A C * (genJ P A C * X * genJ P A C)) =
      genPhi P A C * (invS P * X * invS P) * genPhi P A C
    rw [hV, one_mul]
    calc
      -(genJ P A C * X * genJ P A C) =
          (genPhi P A C * invS P) * X * (invS P * genPhi P A C) := by
            rw [hPhiS, hSPhi]
            noncomm_ring
      _ = genPhi P A C * (invS P * X * invS P) * genPhi P A C := by
            noncomm_ring
  · change genSig P A C * X * genSig P A C = invS P * X * invS P
    rw [hSig]

end InfoGeometry.OperatorAlgebra.PeirceSpine
