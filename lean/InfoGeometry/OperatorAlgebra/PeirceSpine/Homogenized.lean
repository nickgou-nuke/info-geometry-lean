/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Peirce spine A₁₃, A₁₅: `V`-homogenized Klein–Hadamard projectors

The raw projectors of A₅/A₁₁ mix eigenvalues `V` and `V²`. Multiplying the
`ad_Φ²`, `ad_J²` channels by `V` makes all four channels have eigenvalue
`8 V²` on their own generator and `0` on the other three (A₁₃). The
projectors are mutually orthogonal to second order (A₁₅). No inverse of `V` is used.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def hProjV (P A C X : B) : B :=
  (8 : ℤ) • ((genV P A C * genV P A C) * X) +
    (genV P A C * derivSqPhi P A C X + genV P A C * derivSqJ P A C X + derivSqSig P A C X)
def hProjPhi (P A C X : B) : B :=
  genV P A C * derivSqPhi P A C X - genV P A C * derivSqJ P A C X - derivSqSig P A C X
def hProjJ (P A C X : B) : B :=
  genV P A C * derivSqJ P A C X - genV P A C * derivSqPhi P A C X - derivSqSig P A C X
def hProjSig (P A C X : B) : B :=
  derivSqSig P A C X - genV P A C * derivSqPhi P A C X - genV P A C * derivSqJ P A C X

/-! ### Degeneracy obstruction to interpreting the channels as automorphisms -/

/-- With both Peirce corners zero, each homogenized channel is the zero map.
Thus these operators, in general, are linear channels rather than elements of
a group of automorphisms. -/
theorem homogenized_channels_zero_at_zero_corners (P X : B) :
    hProjV P (0 : B) (0 : B) X = 0 ∧ hProjPhi P (0 : B) (0 : B) X = 0 ∧
      hProjJ P (0 : B) (0 : B) X = 0 ∧ hProjSig P (0 : B) (0 : B) X = 0 := by
  simp [hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig,
    genPhi, genJ, genV, genSig, anticomm, comm, conePlus, coneMinus]

/-- Any nonzero input witnesses failure of injectivity at the zero-corner
specialization. In particular, these homogenized channels cannot uniformly
be Galois automorphisms of the ambient ring. -/
theorem hProjV_not_injective_at_zero_corners (P X : B) (hX : X ≠ 0) :
    ¬ Function.Injective (hProjV P (0 : B) (0 : B)) := by
  intro hinj
  have hEq : hProjV P (0 : B) (0 : B) X = hProjV P (0 : B) (0 : B) 0 := by
    rw [(homogenized_channels_zero_at_zero_corners P X).1,
      (homogenized_channels_zero_at_zero_corners P 0).1]
  exact hX (hinj hEq)

/-- On every nontrivial ring, the zero-corner specialization is an explicit
counterexample to the claim that `hProjV` is an ambient ring automorphism. -/
theorem hProjV_not_injective_at_zero_corners_of_nontrivial [Nontrivial B] (P : B) :
    ¬ Function.Injective (hProjV P (0 : B) (0 : B)) :=
  hProjV_not_injective_at_zero_corners P 1 one_ne_zero

variable {P : B} (hP : P * P = P)
include hP

/-! ### A₁₃ -/

theorem archetype_A13_homogenized_projectors (A C X : B) :
    hProjV P A C X + hProjPhi P A C X + hProjJ P A C X + hProjSig P A C X =
      (8 : ℤ) • ((genV P A C * genV P A C) * X) ∧
    hProjV P A C (genV P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genV P A C) ∧
    hProjV P A C (genPhi P A C) = 0 ∧
    hProjV P A C (genJ P A C) = 0 ∧
    hProjV P A C (genSig P A C) = 0 ∧
    hProjPhi P A C (genPhi P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    hProjPhi P A C (genV P A C) = 0 ∧
    hProjPhi P A C (genJ P A C) = 0 ∧
    hProjPhi P A C (genSig P A C) = 0 ∧
    hProjJ P A C (genJ P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) ∧
    hProjJ P A C (genV P A C) = 0 ∧
    hProjJ P A C (genPhi P A C) = 0 ∧
    hProjJ P A C (genSig P A C) = 0 ∧
    hProjSig P A C (genSig P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) ∧
    hProjSig P A C (genV P A C) = 0 ∧
    hProjSig P A C (genPhi P A C) = 0 ∧
    hProjSig P A C (genJ P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig]);
      peirce_nf hP)

/-! ### A₁₅ -/

/-- The mass `V` commutes with `Φ`, `J`, `Σ` (right-associated rewriting forms). -/
theorem mass_commute_generators (A C z : B) :
    genPhi P A C * (genV P A C * z) = genV P A C * (genPhi P A C * z) ∧
    genJ P A C * (genV P A C * z) = genV P A C * (genJ P A C * z) ∧
    genSig P A C * (genV P A C * z) = genV P A C * (genSig P A C * z) ∧
    genPhi P A C * genV P A C = genV P A C * genPhi P A C ∧
    genJ P A C * genV P A C = genV P A C * genJ P A C ∧
    genSig P A C * genV P A C = genV P A C * genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

omit hP in
/-- The homogenized projectors are additive. -/
theorem hProj_add (A C X Y : B) :
    hProjV P A C (X + Y) = hProjV P A C X + hProjV P A C Y ∧
    hProjPhi P A C (X + Y) = hProjPhi P A C X + hProjPhi P A C Y ∧
    hProjJ P A C (X + Y) = hProjJ P A C X + hProjJ P A C Y ∧
    hProjSig P A C (X + Y) = hProjSig P A C X + hProjSig P A C Y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig, comm];
      noncomm_ring)

omit hP in
/-- The homogenized projectors are `ℤ`-linear. -/
theorem hProj_zsmul (A C Y : B) (n : ℤ) :
    hProjV P A C (n • Y) = n • hProjV P A C Y ∧
    hProjPhi P A C (n • Y) = n • hProjPhi P A C Y ∧
    hProjJ P A C (n • Y) = n • hProjJ P A C Y ∧
    hProjSig P A C (n • Y) = n • hProjSig P A C Y :=
  ⟨map_zsmul (AddMonoidHom.mk' (hProjV P A C) fun X Y => (hProj_add A C X Y).1) n Y,
    map_zsmul (AddMonoidHom.mk' (hProjPhi P A C) fun X Y => (hProj_add A C X Y).2.1) n Y,
    map_zsmul (AddMonoidHom.mk' (hProjJ P A C) fun X Y => (hProj_add A C X Y).2.2.1) n Y,
    map_zsmul (AddMonoidHom.mk' (hProjSig P A C) fun X Y => (hProj_add A C X Y).2.2.2) n Y⟩

/-- The homogenized projectors commute with left multiplication by `V`. -/
theorem hProj_mass_mul (A C Y : B) :
    hProjV P A C (genV P A C * Y) = genV P A C * hProjV P A C Y ∧
    hProjPhi P A C (genV P A C * Y) = genV P A C * hProjPhi P A C Y ∧
    hProjJ P A C (genV P A C * Y) = genV P A C * hProjJ P A C Y ∧
    hProjSig P A C (genV P A C * Y) = genV P A C * hProjSig P A C Y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig, comm,
      mul_sub, sub_mul, mul_add, neg_sub, mul_smul_comm, mul_assoc,
      (mass_commute_generators hP A C _).1, (mass_commute_generators hP A C _).2.1,
      (mass_commute_generators hP A C _).2.2.1]

theorem archetype_A15_second_order_orthogonality (A C : B) :
    hProjV P A C (hProjV P A C (genV P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjV P A C (genV P A C)) ∧
    hProjPhi P A C (hProjPhi P A C (genPhi P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjPhi P A C (genPhi P A C)) ∧
    hProjJ P A C (hProjJ P A C (genJ P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjJ P A C (genJ P A C)) ∧
    hProjSig P A C (hProjSig P A C (genSig P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjSig P A C (genSig P A C)) ∧
    hProjPhi P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjJ P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjSig P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjV P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjJ P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjSig P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjV P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjPhi P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjSig P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjV P A C (hProjSig P A C (genSig P A C)) = 0 ∧
    hProjPhi P A C (hProjSig P A C (genSig P A C)) = 0 ∧
    hProjJ P A C (hProjSig P A C (genSig P A C)) = 0 := by
  obtain ⟨_, hV1, hV2, hV3, hV4, hF1, hF2, hF3, hF4, hJ1, hJ2, hJ3, hJ4, hS1, hS2, hS3, hS4⟩ :=
    archetype_A13_homogenized_projectors hP A C (0 : B)
  have m := hProj_mass_mul hP A C
  have z := fun Y : B => hProj_zsmul (P := P) A C Y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hV1, hF1, hJ1, hS1, mul_assoc, (z _ _).1, (z _ _).2.1, (z _ _).2.2.1, (z _ _).2.2.2,
      (m _).1, (m _).2.1, (m _).2.2.1, (m _).2.2.2,
      hV2, hV3, hV4, hF2, hF3, hF4, hJ2, hJ3, hJ4, hS2, hS3, hS4, mul_zero, smul_zero]

end InfoGeometry.OperatorAlgebra.PeirceSpine
