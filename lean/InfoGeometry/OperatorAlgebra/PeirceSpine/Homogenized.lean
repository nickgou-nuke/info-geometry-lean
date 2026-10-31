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
second-order identities in A₁₅ are evaluated on those named generators, not
asserted as identities of endomorphisms on every input. These are additive
channels; the name `projector` does not assert ambient idempotence or
invertibility. No inverse of `V` is used.
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

/-! ### A₁₇: group-sandwich character channels

These are additive polynomial maps on the ring. The names record their
formulas; they do not assert that the maps are group actions or automorphisms.
-/

def grpId (P A C X : B) : B := (genV P A C * genV P A C) * X
def grpPhi (P A C X : B) : B := genV P A C * (genPhi P A C * X * genPhi P A C)
def grpJ (P A C X : B) : B := -(genV P A C * (genJ P A C * X * genJ P A C))
def grpSig (P A C X : B) : B := genSig P A C * X * genSig P A C

def fourierV (P A C X : B) : B :=
  (2 : ℤ) • (grpId P A C X + grpPhi P A C X + grpJ P A C X + grpSig P A C X)
def fourierPhi (P A C X : B) : B :=
  (2 : ℤ) • (grpId P A C X + grpPhi P A C X - grpJ P A C X - grpSig P A C X)
def fourierJ (P A C X : B) : B :=
  (2 : ℤ) • (grpId P A C X - grpPhi P A C X + grpJ P A C X - grpSig P A C X)
def fourierSig (P A C X : B) : B :=
  (2 : ℤ) • (grpId P A C X - grpPhi P A C X - grpJ P A C X + grpSig P A C X)

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

/-! The four sandwich channels act on the tetraktys generators with the
character table below. The Fourier combinations agree with the homogenized
channels on their matching generators, with common operator-valued scale
`8 V²` already established by A₁₃.
-/

theorem archetype_A17_group_sandwich_character_table (A C : B) :
    grpPhi P A C (genV P A C) = grpId P A C (genV P A C) ∧
    grpPhi P A C (genPhi P A C) = grpId P A C (genPhi P A C) ∧
    grpPhi P A C (genJ P A C) = -grpId P A C (genJ P A C) ∧
    grpPhi P A C (genSig P A C) = -grpId P A C (genSig P A C) ∧
    grpJ P A C (genV P A C) = grpId P A C (genV P A C) ∧
    grpJ P A C (genPhi P A C) = -grpId P A C (genPhi P A C) ∧
    grpJ P A C (genJ P A C) = grpId P A C (genJ P A C) ∧
    grpJ P A C (genSig P A C) = -grpId P A C (genSig P A C) ∧
    grpSig P A C (genV P A C) = grpId P A C (genV P A C) ∧
    grpSig P A C (genPhi P A C) = -grpId P A C (genPhi P A C) ∧
    grpSig P A C (genJ P A C) = -grpId P A C (genJ P A C) ∧
    grpSig P A C (genSig P A C) = grpId P A C (genSig P A C) ∧
    hProjV P A C (genV P A C) = fourierV P A C (genV P A C) ∧
    hProjPhi P A C (genPhi P A C) = fourierPhi P A C (genPhi P A C) ∧
    hProjJ P A C (genJ P A C) = fourierJ P A C (genJ P A C) ∧
    hProjSig P A C (genSig P A C) = fourierSig P A C (genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [grpId, grpPhi, grpJ, grpSig, fourierV, fourierPhi, fourierJ, fourierSig,
      hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig]; peirce_nf hP)

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

/-! ### A₂₀: equivariance of the homogenized channels under Peirce sandwiches -/

/-- A two-sided multiplication expansion of the `V`-homogenized channel. -/
theorem hProjV_expansion (A C X : B) :
    hProjV P A C X =
      (5 : ℤ) • ((genV P A C * genV P A C) * X) -
        (2 : ℤ) • (genV P A C * X * genV P A C) -
        X * (genV P A C * genV P A C) +
        (2 : ℤ) • (genV P A C * genPhi P A C * X * genPhi P A C) -
        (2 : ℤ) • (genV P A C * genJ P A C * X * genJ P A C) +
        (2 : ℤ) • (genSig P A C * X * genSig P A C) := by
  simp only [hProjV, derivSqPhi, derivSqJ, derivSqSig, comm]
  peirce_nf hP

theorem hProjPhi_sandwichJ (A C X : B) :
    hProjPhi P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjPhi P A C X * (-genJ P A C) := by
  simp only [hProjPhi, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

theorem hProjJ_sandwichJ (A C X : B) :
    hProjJ P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjJ P A C X * (-genJ P A C) := by
  simp only [hProjJ, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

theorem hProjSig_sandwichJ (A C X : B) :
    hProjSig P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjSig P A C X * (-genJ P A C) := by
  simp only [hProjSig, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

theorem hProjPhi_sandwichPhi (A C X : B) :
    hProjPhi P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjPhi P A C X * genPhi P A C := by
  simp only [hProjPhi, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

theorem hProjJ_sandwichPhi (A C X : B) :
    hProjJ P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjJ P A C X * genPhi P A C := by
  simp only [hProjJ, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

theorem hProjSig_sandwichPhi (A C X : B) :
    hProjSig P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjSig P A C X * genPhi P A C := by
  simp only [hProjSig, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

omit hP in
theorem hProjV_decomp (A C Y : B) :
    hProjV P A C Y =
      (8 : ℤ) • ((genV P A C * genV P A C) * Y) -
        (hProjPhi P A C Y + hProjJ P A C Y + hProjSig P A C Y) := by
  simp only [hProjV, hProjPhi, hProjJ, hProjSig]
  abel

theorem grpId_sandwichJ (A C X : B) :
    (genV P A C * genV P A C) * (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * ((genV P A C * genV P A C) * X) * (-genJ P A C) := by
  peirce_nf hP

theorem grpId_sandwichPhi (A C X : B) :
    (genV P A C * genV P A C) * (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * ((genV P A C * genV P A C) * X) * genPhi P A C := by
  peirce_nf hP

omit hP in
theorem zsmul_mul_left_right (n : ℤ) (U V : B) :
    (n • U) * V = n • (U * V) ∧
    U * (n • V) = n • (U * V) :=
  ⟨map_zsmul (AddMonoidHom.mk' (fun u => u * V) (fun x y => add_mul x y V)) n U,
   map_zsmul (AddMonoidHom.mk' (fun v => U * v) (fun x y => mul_add U x y)) n V⟩

/-- The `V`-homogenized channel intertwines with the sandwich by `J`. -/
theorem hProjV_sandwichJ (A C X : B) :
    hProjV P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjV P A C X * (-genJ P A C) := by
  rw [hProjV_decomp, hProjV_decomp, grpId_sandwichJ hP,
    hProjPhi_sandwichJ hP, hProjJ_sandwichJ hP, hProjSig_sandwichJ hP]
  simp only [mul_sub, sub_mul, mul_add, add_mul,
    (zsmul_mul_left_right _ _ _).1, (zsmul_mul_left_right _ _ _).2]

/-- The `V`-homogenized channel intertwines with the sandwich by `Φ`. -/
theorem hProjV_sandwichPhi (A C X : B) :
    hProjV P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjV P A C X * genPhi P A C := by
  rw [hProjV_decomp, hProjV_decomp, grpId_sandwichPhi hP,
    hProjPhi_sandwichPhi hP, hProjJ_sandwichPhi hP, hProjSig_sandwichPhi hP]
  simp only [mul_sub, sub_mul, mul_add, add_mul,
    (zsmul_mul_left_right _ _ _).1, (zsmul_mul_left_right _ _ _).2]

/-- Theorem A20 combines the two families of explicit sandwich intertwiners.
These are polynomial maps, not asserted to be automorphisms or group actions. -/
theorem archetype_A20_weyl_clifford_covariance_of_homogenized_projectors (A C X : B) :
    hProjV P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjV P A C X * (-genJ P A C) ∧
    hProjPhi P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjPhi P A C X * (-genJ P A C) ∧
    hProjJ P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjJ P A C X * (-genJ P A C) ∧
    hProjSig P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjSig P A C X * (-genJ P A C) ∧
    hProjV P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjV P A C X * genPhi P A C ∧
    hProjPhi P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjPhi P A C X * genPhi P A C ∧
    hProjJ P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjJ P A C X * genPhi P A C ∧
    hProjSig P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjSig P A C X * genPhi P A C := by
  exact ⟨hProjV_sandwichJ hP A C X, hProjPhi_sandwichJ hP A C X,
    hProjJ_sandwichJ hP A C X, hProjSig_sandwichJ hP A C X,
    hProjV_sandwichPhi hP A C X, hProjPhi_sandwichPhi hP A C X,
    hProjJ_sandwichPhi hP A C X, hProjSig_sandwichPhi hP A C X⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
