/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.Lie.Loop
import Mathlib.Tactic
import InfoGeometry.External.Virasoro.CentralExtension
import InfoGeometry.External.Virasoro.LieCohomologySmallDegree

/-!
# Affine Kac-Moody algebra

This file defines the untwisted affine Kac-Moody algebra as a central extension of the
loop algebra `loopAlgebra 𝕜 ℤ 𝓰`.

## Main definitions

* `VirasoroProject.affineKacMoodyCocycle`: The 2-cocycle defining the central extension,
  transported from Mathlib's `LieAlgebra.LoopAlgebra.twoCocycleOfBilinear`.
* `VirasoroProject.AffineKacMoody`: The affine Kac-Moody algebra.
* `VirasoroProject.affineCurrentGen_bracket`: The generator-level Kac-Moody bracket obtained by
  evaluating the loop-algebra residue cocycle on monomials.
-/

namespace VirasoroProject

open LieAlgebra
open LieAlgebra.LoopAlgebra

universe u
variable (𝕜 : Type u) [CommRing 𝕜] [IsAddTorsionFree 𝕜]
variable (𝓰 : Type u) [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
variable (Φ : LinearMap.BilinForm 𝕜 𝓰)
variable (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)

/-- Mathlib's `Cohomology.twoCochain` corresponds to `LieTwoCocycle.toBilin` + `self'`. -/
noncomputable def affineKacMoodyCocycle : LieTwoCocycle 𝕜 (loopAlgebra 𝕜 ℤ 𝓰) 𝕜 where
  toBilin := residuePairing 𝕜 ℤ 𝓰 Φ
  self' := by
    let c := twoCochainOfBilinear 𝕜 ℤ 𝓰 Φ hΦs
    intro X
    have h : c X X = 0 := LieModule.Cohomology.twoCochain_alt c X
    have h_def :
        c X X =
          (TrivialLieModule.equiv 𝕜 (loopAlgebra 𝕜 ℤ 𝓰) 𝕜).symm (residuePairing 𝕜 ℤ 𝓰 Φ X X) :=
      rfl
    rw [h_def] at h
    have h2 := congrArg (TrivialLieModule.equiv 𝕜 (loopAlgebra 𝕜 ℤ 𝓰) 𝕜) h
    simpa using h2
  leibniz' := by
    let c := twoCocycleOfBilinear 𝕜 ℤ 𝓰 Φ hΦ hΦs
    intro X Y Z
    have h_cocycle := (LieModule.Cohomology.mem_twoCocycle_iff_of_trivial (a := c.val)).mp c.property
    have h_eq := h_cocycle X Y Z
    have h_def (U V) :
        c.val U V =
          (TrivialLieModule.equiv 𝕜 (loopAlgebra 𝕜 ℤ 𝓰) 𝕜).symm (residuePairing 𝕜 ℤ 𝓰 Φ U V) :=
      rfl
    simp only [h_def] at h_eq
    have h2 := congrArg (TrivialLieModule.equiv 𝕜 (loopAlgebra 𝕜 ℤ 𝓰) 𝕜) h_eq
    simpa using h2

/-- The untwisted affine Kac-Moody algebra. -/
abbrev AffineKacMoody :=
  LieTwoCocycle.CentralExtension (affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs)

/-- The loop-algebra monomial `t^n ⊗ x`. -/
noncomputable def affineLoopMode (n : ℤ) (x : 𝓰) : loopAlgebra 𝕜 ℤ 𝓰 :=
  AddMonoidAlgebra.single n (1 : 𝕜) ⊗ₜ[𝕜] x

omit [IsAddTorsionFree 𝕜] in
/-- Loop monomials bracket by adding exponents and taking the bracket in `𝓰`. -/
theorem affineLoopMode_bracket (m n : ℤ) (x y : 𝓰) :
    ⁅affineLoopMode (𝕜 := 𝕜) (𝓰 := 𝓰) m x,
        affineLoopMode (𝕜 := 𝕜) (𝓰 := 𝓰) n y⁆ =
      affineLoopMode (𝕜 := 𝕜) (𝓰 := 𝓰) (m + n) (⁅x, y⁆ : 𝓰) := by
  change ⁅AddMonoidAlgebra.single m (1 : 𝕜) ⊗ₜ[𝕜] x,
      AddMonoidAlgebra.single n (1 : 𝕜) ⊗ₜ[𝕜] y⁆ =
    AddMonoidAlgebra.single (m + n) (1 : 𝕜) ⊗ₜ[𝕜] (⁅x, y⁆ : 𝓰)
  rw [LieAlgebra.ExtendScalars.bracket_tmul]
  rw [AddMonoidAlgebra.single_mul_single]
  simp only [mul_one]

omit [IsAddTorsionFree 𝕜] in
/--
The residue cocycle on two loop monomials.  With the exponent convention in mathlib's
`residuePairing`, the central coefficient is the exponent of the second monomial.
-/
theorem residuePairing_affineLoopMode (m n : ℤ) (x y : 𝓰) :
    residuePairing 𝕜 ℤ 𝓰 Φ
      (affineLoopMode (𝕜 := 𝕜) (𝓰 := 𝓰) m x)
      (affineLoopMode (𝕜 := 𝕜) (𝓰 := 𝓰) n y) =
    if m + n = 0 then (n : 𝕜) * Φ x y else 0 := by
  rw [residuePairing_apply_apply]
  simp only [affineLoopMode, toFinsupp_single_tmul]
  rw [Finsupp.sum_single_index]
  · by_cases hmn : -n = m
    · have hsum : m + n = 0 := by omega
      rw [if_pos hsum]
      simp [hmn]
    · have hsum : ¬ m + n = 0 := by omega
      rw [if_neg hsum]
      simp [Finsupp.single_eq_of_ne hmn]
  · simp

/-- The affine Kac-Moody 2-cocycle evaluated on two loop monomials. -/
theorem affineKacMoodyCocycle_affineLoopMode (m n : ℤ) (x y : 𝓰) :
    affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs
      (affineLoopMode (𝕜 := 𝕜) (𝓰 := 𝓰) m x)
      (affineLoopMode (𝕜 := 𝕜) (𝓰 := 𝓰) n y) =
    if m + n = 0 then (n : 𝕜) * Φ x y else 0 := by
  change residuePairing 𝕜 ℤ 𝓰 Φ
      (affineLoopMode (𝕜 := 𝕜) (𝓰 := 𝓰) m x)
      (affineLoopMode (𝕜 := 𝕜) (𝓰 := 𝓰) n y) =
    if m + n = 0 then (n : 𝕜) * Φ x y else 0
  exact residuePairing_affineLoopMode (𝕜 := 𝕜) (𝓰 := 𝓰) Φ m n x y

/--
Affine current generator.  The current index `n` is represented by loop exponent `-n`,
so that the residue cocycle has the standard central coefficient `m` in
`[J_m, J_n]` when `m + n = 0`.
-/
noncomputable def affineCurrentGen (n : ℤ) (x : 𝓰) :
    AffineKacMoody 𝕜 𝓰 Φ hΦ hΦs :=
  ⟨affineLoopMode (𝕜 := 𝕜) (𝓰 := 𝓰) (-n) x, 0⟩

/--
Affine current mode is well-defined as a linear map in the Lie-algebra input.

This is the concrete `km_current_def_well_defined` step:
for each mode `n`, `x ↦ J⁽ˣ⁾ₙ` is linear.
-/
theorem km_current_def_well_defined (n : ℤ) :
    ∃ Jn : 𝓰 →ₗ[𝕜] AffineKacMoody 𝕜 𝓰 Φ hΦ hΦs,
      ∀ x : 𝓰,
        Jn x = affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n x := by
  refine ⟨
    { toFun := fun x => affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n x
      map_add' := ?_
      map_smul' := ?_ },
    ?_⟩
  · intro x y
    ext <;> simp [affineCurrentGen, affineLoopMode, TensorProduct.tmul_add]
  · intro a x
    ext <;> simp [affineCurrentGen, affineLoopMode, TensorProduct.tmul_smul]
  · intro x
    rfl

/-- The central generator of the affine Kac-Moody central extension. -/
noncomputable def affineCentralGen : AffineKacMoody 𝕜 𝓰 Φ hΦ hΦs :=
  ⟨0, 1⟩

/--
Generator-level affine Kac-Moody bracket.

This is the nonabelian current-algebra readback from the mathlib-backed loop-algebra
central extension.  It does not assume a fermionic current theorem; it evaluates the
existing residue 2-cocycle on loop monomials.
-/
theorem affineCurrentGen_bracket (m n : ℤ) (x y : 𝓰) :
    ⁅affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x,
        affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y⁆ =
      affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs (m + n) (⁅x, y⁆ : 𝓰)
        + (if m + n = 0
            then ((m : 𝕜) * Φ x y) • affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs
            else 0) := by
  ext
  · have hidx : -m + -n = -(m + n) := by omega
    simp [affineCurrentGen, affineCentralGen, affineLoopMode_bracket, hidx]
    by_cases h : m + n = 0 <;> simp [h]
  · by_cases h : m + n = 0
    · have hmn : -n = m := by omega
      simp [affineCurrentGen, affineCentralGen, affineKacMoodyCocycle_affineLoopMode, h, hmn]
    · have hloop : ¬ -m + -n = 0 := by omega
      simp [affineCurrentGen, affineKacMoodyCocycle_affineLoopMode, h, hloop]

/--
Kac--Moody bracket expansion for current generators:
structure bracket part plus central cocycle part.

This is the `km_bracket_expand` closure item.
-/
theorem km_bracket_expand (m n : ℤ) (x y : 𝓰) :
    ⁅affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x,
      affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y⁆ =
      affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs (m + n) (⁅x, y⁆ : 𝓰)
        + (if m + n = 0
            then ((m : 𝕜) * Φ x y) • affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs
            else 0) := by
  simpa using affineCurrentGen_bracket (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m n x y

/--
Bilinearity of the affine Kac--Moody cocycle.

This is the `km_cocycle_bilinear` closure item.
-/
theorem km_cocycle_bilinear
    (X Y Z : loopAlgebra 𝕜 ℤ 𝓰) (a : 𝕜) :
    affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs (X + Y) Z
      =
      affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Z
        + affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs Y Z
    ∧
    affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs (a • X) Z
      =
      a * affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Z
    ∧
    affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X (Y + Z)
      =
      affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Y
        + affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Z
    ∧
    affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X (a • Y)
      =
      a * affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Y := by
  constructor
  · simpa using (affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs).map_add_left X Y Z
  constructor
  · simpa using (affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs).map_smul_left a X Z
  constructor
  · simpa using (affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs).map_add_right X Y Z
  · simpa using (affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs).map_smul_right a X Y

/--
Skew-symmetry of the affine Kac--Moody cocycle.

This is the `km_cocycle_skew` closure item.
-/
theorem km_cocycle_skew
    (X Y : loopAlgebra 𝕜 ℤ 𝓰) :
    affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X Y
      =
      - affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs Y X := by
  have hskew := (affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs).skew X Y
  simpa using hskew.symm

/--
Leibniz/2-cocycle identity for the affine Kac--Moody cocycle.

This is the `km_cocycle_2cocycle_identity` closure item.
-/
theorem km_cocycle_2cocycle_identity
    (X Y Z : loopAlgebra 𝕜 ℤ 𝓰) :
    affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs X ⁅Y, Z⁆
      =
      affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs ⁅X, Y⁆ Z
        + affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs Y ⁅X, Z⁆ := by
  simpa using
    (LieTwoCocycle.leibniz
      (γ := affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs)
      (X := X) (Y := Y) (Z := Z))

/--
Jacobi identity for affine current generators.

This is the `km_jacobi_from_structure_and_cocycle` closure item, read at the
generator level in the affine central extension.
-/
theorem km_jacobi_from_structure_and_cocycle
    (m n p : ℤ) (x y z : 𝓰) :
    ⁅affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x,
        ⁅affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y,
          affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs p z⁆⁆
      +
      ⁅affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y,
        ⁅affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs p z,
          affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x⁆⁆
      +
      ⁅affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs p z,
        ⁅affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x,
          affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y⁆⁆
      = 0 := by
  simpa [add_assoc] using
    (lie_jacobi
      (affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x)
      (affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y)
      (affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs p z))

/--
Full affine Kac--Moody generator commutator.

This is the `km_comm_full` closure item.
-/
theorem km_comm_full
    (m n : ℤ) (x y : 𝓰) :
    ⁅affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x,
      affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y⁆ =
      affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs (m + n) (⁅x, y⁆ : 𝓰)
        + (if m + n = 0
            then ((m : 𝕜) * Φ x y) • affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs
            else 0) := by
  simpa using km_bracket_expand (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m n x y

end VirasoroProject
