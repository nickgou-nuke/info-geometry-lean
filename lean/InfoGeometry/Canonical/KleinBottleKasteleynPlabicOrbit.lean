/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Canonical.KleinBottleBipartiteKasteleynBridge
import InfoGeometry.Canonical.KleinBottleFiniteCoverKasteleynBridge
import InfoGeometry.Canonical.KleinBottleTwistedCommutantBridge
import InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge
import InfoGeometry.Canonical.Cl11BipartiteDiracBridge
import InfoGeometry.Canonical.CPTGradingCompass
import InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra
import InfoGeometry.Canonical.CantorPlabicTwistorBridge
import InfoGeometry.Topology.WallpaperSymmetry

/-!
# Klein-Bottle Kasteleyn, Twisted Commutant, Finite Cover, and Plabic Orbit Bridge

## i. Overview
This module unifies the clean repository owners for the division-free Kasteleyn–Dirac
bipartite algebra on `ℤ × ℤ` and the `2 : 1` finite torus cover `Fin 2 × Fin (2 * N)`,
restricted `KleinInvolution` twisted commutants on seam-invariant hopping subrings,
the `SignedPerm (2 * N)` glide-orbit sector swap, lattice face-orientation reversal with
`CantorPlabicTwistorBridge.mutateF_rev`, and an explicit `N = 1` non-vacuity master witness.

## ii. Key results
- `M2-K1` (`kastDirac_sq_and_anticomm_bipartiteB`): `D² = H_x² + H_y²`, `{D, B} = 0`,
  `{U_G, B} = 0`, finite-cover `finKastDirac` square identity, and `Cl11BipartiteDiracBridge` /
  `CPTGradingCompass` instantiation.
- `M2-K2` (`bareGlide_mem_twistedCommutant_and_wallpaper`): `seamTwistRingAut`, seam-invariant
  hopping subrings `kastHopSubring` and `finKastHopSubring`, `IsTwistedCommutant` on
  `Subring.subtype` with `seamTwistSubringInvolution` / `finSeamSubringInvolution`,
  `Algebra.KleinBottleTwistedCommutantBridge.twistedCommutant` membership, and `Wallpaper.G` /
  `Wallpaper.T_x` intertwining.
- `M2-K3` (`dressedGlide_swaps_untwisted_mobius_sectors`): bipartite grading `B` swaps the `+1`
  untwisted and `-1` Möbius eigenspaces of `dressedGlideUG` and `finDressedGlideUG`.
- `M2-K4` (`finiteTorusCover_glide_orbit_signFlip`): partition of `Fin 2 × Fin (2 * N)` into
  disjoint 2-element `coverGlide` orbits identified with `Sector (2 * N)` and swapped by the
  central involution `kleinCoverCentralSignedPerm N : SignedPerm (2 * N)`.
- `M2-K5` (`kleinBottle_lattice_face_reversal_and_plabic_twist`): unit-square Kasteleyn `-1`
  boundary reversal under `integralGlide` and `τ_y` gauge, paired with `reverseSquareFace`
  intertwining `mutateF` and `mutateF_rev`.
- `M2-K6` (`kleinBottle_bipartite_kasteleyn_master_witness_N1`): non-vacuity master witness
  over `FiniteCoverState ℤ 1`.

## Scope boundary

The operator identities are on function modules over `ℤ × ℤ` and on the stated finite
double cover. This file does not construct the topological Klein-bottle quotient or a
spinor bundle on it. The plabic result is reversal-equivariance of the chosen square-face
coordinate operation; it does not identify Kasteleyn holonomy with a cluster coordinate.
The theorem `kasteleyn_holonomy_cluster_chart_roundtrip_fails` records why the direct
identification fails for the `-1` face holonomy.

## iii. Table of contents
- Section 1 (`M2-K1`): Kasteleyn–Dirac squares, chirality anticommutation, and `Cl11`/`CPT` link.
- Section 2 (`M2-K2`): Seam-twist `RingAut`, invariant hopping subrings, and `Wallpaper` glide.
- Section 3 (`M2-K3`): Dressed-glide sector swapping under bipartite grading `B`.
- Section 4 (`M2-K4`): Finite torus cover glide-orbit bijection with `SignedPerm (2 * N)`.
- Section 5 (`M2-K5`): Lattice unit-square face reversal and plabic `mutateF_rev` twist.
- Section 6 (`M2-K6`): `N = 1` non-vacuity master witness.

## iv. References
- `InfoGeometry.Canonical.KleinBottleBipartiteKasteleynBridge`
- `InfoGeometry.Canonical.KleinBottleFiniteCoverKasteleynBridge`
- `InfoGeometry.Canonical.KleinBottleTwistedCommutantBridge`
- `InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge`
- `InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra`
- `InfoGeometry.Canonical.CantorPlabicTwistorBridge`
- `InfoGeometry.Topology.WallpaperSymmetry`
-/

namespace InfoGeometry.Canonical.KleinBottleKasteleynPlabicOrbit

open scoped Matrix Kronecker
open InfoGeometry.Canonical.KleinBottleBipartiteKasteleynBridge
open InfoGeometry.Canonical.KleinBottleFiniteCoverKasteleynBridge
open InfoGeometry.Canonical.KleinBottleTwistedCommutant
open InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra
open InfoGeometry.PlabicCluster
open InfoGeometry.Canonical.CantorPlabicTwistorBridge

/-! ## Section 1: Kasteleyn–Dirac squares and chirality (`M2-K1`) -/

section KasteleynDirac

/-- On `ℤ × ℤ`, `kastDirac R ^ 2 = kastHx R ^ 2 + kastHy R ^ 2`. -/
lemma kastDirac_sq (R : Type*) [CommRing R] :
    kastDirac R * kastDirac R = kastHx R * kastHx R + kastHy R * kastHy R := by
  unfold kastDirac
  rw [add_mul, mul_add, mul_add]
  have h :
      kastHx R * kastHx R + kastHx R * kastHy R +
          (kastHy R * kastHx R + kastHy R * kastHy R) =
        kastHx R * kastHx R + kastHy R * kastHy R +
          (kastHx R * kastHy R + kastHy R * kastHx R) := by
    abel
  rw [h, kastHx_anticomm_kastHy, add_zero]

/-- On `Fin 2 × Fin (2 * N)`, `finKastDirac R N ^ 2 = finKastHx R N ^ 2 + finKastHy R N ^ 2`. -/
lemma finKastDirac_sq (R : Type*) [CommRing R] (N : ℕ) [NeZero N] :
    finKastDirac R N * finKastDirac R N =
      finKastHx R N * finKastHx R N + finKastHy R N * finKastHy R N := by
  unfold finKastDirac
  rw [add_mul, mul_add, mul_add]
  have h :
      finKastHx R N * finKastHx R N + finKastHx R N * finKastHy R N +
          (finKastHy R N * finKastHx R N + finKastHy R N * finKastHy R N) =
        finKastHx R N * finKastHx R N + finKastHy R N * finKastHy R N +
          (finKastHx R N * finKastHy R N + finKastHy R N * finKastHx R N) := by
    abel
  rw [h, finKastHx_anticomm_finKastHy, add_zero]

/-- On `ℤ × ℤ`, `kastDirac R` anticommutes with the bipartite grading `bipartiteB R`. -/
lemma kastDirac_anticomm_bipartiteB (R : Type*) [CommRing R] :
    kastDirac R * bipartiteB R + bipartiteB R * kastDirac R = 0 := by
  ext ψ ⟨m, n⟩
  simp only [kastDirac, LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
    Pi.add_apply, Pi.zero_apply, kastHx, kastHy, bipartiteB,
    LinearMap.coe_mk, AddHom.coe_mk]
  have h1 : m + 1 + n = m + n + 1 := by omega
  have h2 : m - 1 + n = m + n - 1 := by omega
  have h3 : m + (n + 1) = m + n + 1 := by omega
  have h4 : m + (n - 1) = m + n - 1 := by omega
  rw [h1, h2, h3, h4]
  simp only [paritySign_add_one, paritySign_sub_one]
  ring

/-- On `ℤ × ℤ`, the bare glide `bareGlideUG R` anticommutes with `bipartiteB R`. -/
lemma bareGlideUG_anticomm_bipartiteB (R : Type*) [CommRing R] :
    bareGlideUG R * bipartiteB R + bipartiteB R * bareGlideUG R = 0 := by
  ext ψ ⟨m, n⟩
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
    Pi.add_apply, Pi.zero_apply, bareGlideUG, bipartiteB,
    LinearMap.coe_mk, AddHom.coe_mk, paritySign_glide_bipartite]
  ring

/-- Master `M2-K1` bundle: division-free `D² = H_x² + H_y²` and `{D, B} = 0` on `ℤ × ℤ` and
`Fin 2 × Fin (2 * N)`, `{U_G, B} = 0`, and instantiation of `Cl11BipartiteDiracBridge` and
`CPTGradingCompass`. -/
lemma kastDirac_sq_and_anticomm_bipartiteB
    (R : Type*) [CommRing R] (N : ℕ) [NeZero N]
    (DL : Cl11BipartiteDiracBridge.StageOne) :
    kastDirac R * kastDirac R = kastHx R * kastHx R + kastHy R * kastHy R ∧
      finKastDirac R N * finKastDirac R N =
        finKastHx R N * finKastHx R N + finKastHy R N * finKastHy R N ∧
      kastDirac R * bipartiteB R + bipartiteB R * kastDirac R = 0 ∧
      finKastDirac R N * finBipartiteB R N + finBipartiteB R N * finKastDirac R N = 0 ∧
      bareGlideUG R * bipartiteB R + bipartiteB R * bareGlideUG R = 0 ∧
      Cl11BipartiteDiracBridge.compositeDirac DL Cl11BipartiteDiracBridge.kreinBeta
          (Cl11BipartiteDiracBridge.offDiagonalDirac 1 1) *
        Cl11BipartiteDiracBridge.compositeDirac DL Cl11BipartiteDiracBridge.kreinBeta
          (Cl11BipartiteDiracBridge.offDiagonalDirac 1 1) =
        (DL * DL) ⊗ₖ (1 : Cl11BipartiteDiracBridge.Atom) +
        (1 : Cl11BipartiteDiracBridge.StageOne) ⊗ₖ
          (Cl11BipartiteDiracBridge.offDiagonalDirac 1 1 *
            Cl11BipartiteDiracBridge.offDiagonalDirac 1 1) ∧
      Cl11BipartiteDiracBridge.kreinBeta * Cl11BipartiteDiracBridge.offDiagonalDirac 1 1 +
        Cl11BipartiteDiracBridge.offDiagonalDirac 1 1 * Cl11BipartiteDiracBridge.kreinBeta = 0 ∧
      CPTGradingCompass.cptBivector * CPTGradingCompass.cptBivector = 1 ∧
      finBipartiteB R N * finBipartiteB R N = 1 := by
  refine ⟨kastDirac_sq R, finKastDirac_sq R N, kastDirac_anticomm_bipartiteB R,
    finKastDirac_anticomm_finBipartiteB, bareGlideUG_anticomm_bipartiteB R,
    Cl11BipartiteDiracBridge.compositeDirac_chiral_decoupled DL 1 1,
    Cl11BipartiteDiracBridge.offDiagonalDirac_anticomm_kreinBeta 1 1,
    CPTGradingCompass.cptBivector_sq, finBipartiteB_sq⟩

end KasteleynDirac

/-! ## Section 2: Seam-twist subrings, twisted commutant, and Wallpaper glide (`M2-K2`) -/

section TwistedCommutantAndWallpaper

/-- `rowParityTau R` squares to `1` on `LatticeState R`. -/
lemma rowParityTau_sq (R : Type*) [CommRing R] :
    rowParityTau R * rowParityTau R = 1 := by
  ext ψ ⟨m, n⟩
  simp only [Module.End.mul_apply, Module.End.one_apply, rowParityTau,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [← mul_assoc, paritySign_sq, one_mul]

/-- Order-2 ring automorphism `α(A) = τ_y A τ_y` on `Module.End R (LatticeState R)`. -/
def seamTwistRingAut (R : Type*) [CommRing R] :
    RingAut (Module.End R (LatticeState R)) where
  toFun := seamTwistAlpha R
  invFun := seamTwistAlpha R
  left_inv A := by
    change rowParityTau R * (rowParityTau R * A * rowParityTau R) * rowParityTau R = A
    calc
      rowParityTau R * (rowParityTau R * A * rowParityTau R) * rowParityTau R
          = (rowParityTau R * rowParityTau R) * A * (rowParityTau R * rowParityTau R) := by
            simp [mul_assoc]
      _ = A := by rw [rowParityTau_sq]; simp
  right_inv A := by
    change rowParityTau R * (rowParityTau R * A * rowParityTau R) * rowParityTau R = A
    calc
      rowParityTau R * (rowParityTau R * A * rowParityTau R) * rowParityTau R
          = (rowParityTau R * rowParityTau R) * A * (rowParityTau R * rowParityTau R) := by
            simp [mul_assoc]
      _ = A := by rw [rowParityTau_sq]; simp
  map_mul' A B := by
    change rowParityTau R * (A * B) * rowParityTau R =
      (rowParityTau R * A * rowParityTau R) * (rowParityTau R * B * rowParityTau R)
    calc
      rowParityTau R * (A * B) * rowParityTau R
          = rowParityTau R * A * (1 * B) * rowParityTau R := by simp [mul_assoc]
      _ = rowParityTau R * A * (rowParityTau R * rowParityTau R * B) * rowParityTau R := by
            rw [rowParityTau_sq]
      _ = (rowParityTau R * A * rowParityTau R) * (rowParityTau R * B * rowParityTau R) := by
            simp [mul_assoc]
  map_add' A B := by
    change rowParityTau R * (A + B) * rowParityTau R =
      rowParityTau R * A * rowParityTau R + rowParityTau R * B * rowParityTau R
    simp [mul_add, add_mul]

/-- `seamTwistRingAut R` fixes `kastHx R`. -/
lemma seamTwistRingAut_kastHx (R : Type*) [CommRing R] :
    seamTwistRingAut R (kastHx R) = kastHx R := by
  ext ψ ⟨m, n⟩
  change (rowParityTau R * kastHx R * rowParityTau R) ψ (m, n) = kastHx R ψ (m, n)
  simp only [Module.End.mul_apply, rowParityTau, kastHx, LinearMap.coe_mk, AddHom.coe_mk]
  have hsq : paritySign R n ^ 2 = 1 := by rw [sq, paritySign_sq]
  ring_nf
  simp only [hsq, one_mul]

/-- `seamTwistRingAut R` negates `kastHy R`. -/
lemma seamTwistRingAut_kastHy (R : Type*) [CommRing R] :
    seamTwistRingAut R (kastHy R) = -kastHy R := by
  ext ψ ⟨m, n⟩
  change (rowParityTau R * kastHy R * rowParityTau R) ψ (m, n) = (-kastHy R) ψ (m, n)
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Pi.neg_apply,
    rowParityTau, kastHy, LinearMap.coe_mk, AddHom.coe_mk,
    paritySign_add_one, paritySign_sub_one]
  have hsq : paritySign R n ^ 2 = 1 := by rw [sq, paritySign_sq]
  ring_nf
  simp only [hsq, one_mul]

/-- `bareGlideUG R` twisted-commutes with `kastHx R`. -/
lemma bareGlideUG_twistedCommutes_kastHx (R : Type*) [CommRing R] :
    bareGlideUG R * kastHx R = seamTwistRingAut R (kastHx R) * bareGlideUG R := by
  rw [seamTwistRingAut_kastHx]
  ext ψ ⟨m, n⟩
  simp only [Module.End.mul_apply, bareGlideUG, kastHx, LinearMap.coe_mk, AddHom.coe_mk]
  have h1 : (m + 1 - 1, -n) = (m, -n) := Prod.ext (by omega) rfl
  have h2 : (m - 1 + 1, -n) = (m, -n) := Prod.ext (by omega) rfl
  rw [h1, h2]

/-- `bareGlideUG R` twisted-commutes with `kastHy R`. -/
lemma bareGlideUG_twistedCommutes_kastHy (R : Type*) [CommRing R] :
    bareGlideUG R * kastHy R = seamTwistRingAut R (kastHy R) * bareGlideUG R := by
  rw [seamTwistRingAut_kastHy]
  ext ψ ⟨m, n⟩
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Pi.neg_apply,
    bareGlideUG, kastHy, LinearMap.coe_mk, AddHom.coe_mk]
  have h3 : (m + 1, -(n + 1)) = (m + 1, -n - 1) := Prod.ext rfl (by omega)
  have h4 : (m + 1, -(n - 1)) = (m + 1, -n + 1) := Prod.ext rfl (by omega)
  rw [h3, h4, paritySign_add_one]
  ring

/-- `finSeamConjAut R N` fixes `finKastHx R N`. -/
lemma finSeamConjAut_finKastHx (R : Type*) [CommRing R] (N : ℕ) [NeZero N] :
    finSeamConjAut R N (finKastHx R N) = finKastHx R N := by
  apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
  change (finRowParityTau R N * finKastHx R N * finRowParityTau R N) ψ (m, n) =
    finKastHx R N ψ (m, n)
  simp only [Module.End.mul_apply, finRowParityTau, finKastHx, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← mul_assoc, finEvenSign_sq, one_mul]

/-- `finSeamConjAut R N` negates `finKastHy R N`. -/
lemma finSeamConjAut_finKastHy (R : Type*) [CommRing R] (N : ℕ) [NeZero N] :
    finSeamConjAut R N (finKastHy R N) = -finKastHy R N := by
  apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
  change (finRowParityTau R N * finKastHy R N * finRowParityTau R N) ψ (m, n) =
    (-finKastHy R N) ψ (m, n)
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Pi.neg_apply,
    finRowParityTau, finKastHy, LinearMap.coe_mk, AddHom.coe_mk,
    finEvenSign_add_one, finEvenSign_sub_one]
  have hsq : finEvenSign R n ^ 2 = 1 := by rw [sq, finEvenSign_sq]
  ring_nf
  simp only [hsq, one_mul]

/-- `finBareGlideUG R N` twisted-commutes with `finKastHx R N`. -/
lemma finBareGlideUG_twistedCommutes_finKastHx (R : Type*) [CommRing R] (N : ℕ) [NeZero N] :
    finBareGlideUG R N * finKastHx R N =
      finSeamConjAut R N (finKastHx R N) * finBareGlideUG R N := by
  rw [finSeamConjAut_finKastHx]
  apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
  simp only [Module.End.mul_apply, finBareGlideUG, finKastHx, coverGlide,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- `finBareGlideUG R N` twisted-commutes with `finKastHy R N`. -/
lemma finBareGlideUG_twistedCommutes_finKastHy (R : Type*) [CommRing R] (N : ℕ) [NeZero N] :
    finBareGlideUG R N * finKastHy R N =
      finSeamConjAut R N (finKastHy R N) * finBareGlideUG R N := by
  rw [finSeamConjAut_finKastHy]
  apply LinearMap.ext; intro ψ; funext ⟨m, n⟩
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Pi.neg_apply,
    finBareGlideUG, finKastHy, coverGlide, LinearMap.coe_mk, AddHom.coe_mk]
  have hn1 : -(n + 1) = -n - 1 := by abel
  have hn2 : -(n - 1) = -n + 1 := by abel
  rw [hn1, hn2, fin2Sign_add_one]
  ring

/-- Seam-invariant Kasteleyn hopping subring generated by `kastHx R` and `kastHy R`. -/
def kastHopSubring (R : Type*) [CommRing R] : Subring (Module.End R (LatticeState R)) :=
  Subring.closure {kastHx R, kastHy R}

/-- `seamTwistRingAut R` preserves `kastHopSubring R`. -/
lemma seamTwistRingAut_mem_kastHopSubring {R : Type*} [CommRing R]
    {A : Module.End R (LatticeState R)} (hA : A ∈ kastHopSubring R) :
    seamTwistRingAut R A ∈ kastHopSubring R := by
  induction hA using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [seamTwistRingAut_kastHx]
      exact Subring.subset_closure (by simp)
    · rw [seamTwistRingAut_kastHy]
      exact neg_mem (Subring.subset_closure (by simp))
  | one =>
    rw [map_one]
    exact one_mem _
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [map_neg]
    exact neg_mem hx
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

/-- Restricted order-2 `KleinInvolution` on `kastHopSubring R`. -/
def seamTwistSubringInvolution (R : Type*) [CommRing R] :
    KleinInvolution ↥(kastHopSubring R) where
  toRingAut :=
    { toFun := fun a => ⟨seamTwistRingAut R a.1, seamTwistRingAut_mem_kastHopSubring a.2⟩
      invFun := fun a => ⟨seamTwistRingAut R a.1, seamTwistRingAut_mem_kastHopSubring a.2⟩
      left_inv := fun a => by
        apply Subtype.ext
        exact (seamTwistRingAut R).symm_apply_apply a.1
      right_inv := fun a => by
        apply Subtype.ext
        exact (seamTwistRingAut R).apply_symm_apply a.1
      map_mul' := fun a b => by
        apply Subtype.ext
        exact map_mul (seamTwistRingAut R) a.1 b.1
      map_add' := fun a b => by
        apply Subtype.ext
        exact map_add (seamTwistRingAut R) a.1 b.1 }
  involutive := fun a => by
    apply Subtype.ext
    exact (seamTwistRingAut R).symm_apply_apply a.1

/-- Seam-invariant finite-cover hopping subring generated by `finKastHx R N` and `finKastHy R N`. -/
def finKastHopSubring (R : Type*) [CommRing R] (N : ℕ) [NeZero N] :
    Subring (Module.End R (FiniteCoverState R N)) :=
  Subring.closure {finKastHx R N, finKastHy R N}

/-- `finSeamConjAut R N` preserves `finKastHopSubring R N`. -/
lemma finSeamConjAut_mem_finKastHopSubring {R : Type*} [CommRing R] {N : ℕ} [NeZero N]
    {A : Module.End R (FiniteCoverState R N)} (hA : A ∈ finKastHopSubring R N) :
    finSeamConjAut R N A ∈ finKastHopSubring R N := by
  induction hA using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [finSeamConjAut_finKastHx]
      exact Subring.subset_closure (by simp)
    · rw [finSeamConjAut_finKastHy]
      exact neg_mem (Subring.subset_closure (by simp))
  | one =>
    rw [map_one]
    exact one_mem _
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [map_neg]
    exact neg_mem hx
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

/-- Restricted order-2 `KleinInvolution` on `finKastHopSubring R N`. -/
def finSeamSubringInvolution (R : Type*) [CommRing R] (N : ℕ) [NeZero N] :
    KleinInvolution ↥(finKastHopSubring R N) where
  toRingAut :=
    { toFun := fun a => ⟨finSeamConjAut R N a.1, finSeamConjAut_mem_finKastHopSubring a.2⟩
      invFun := fun a => ⟨finSeamConjAut R N a.1, finSeamConjAut_mem_finKastHopSubring a.2⟩
      left_inv := fun a => by
        apply Subtype.ext
        exact (finSeamConjAut R N).symm_apply_apply a.1
      right_inv := fun a => by
        apply Subtype.ext
        exact (finSeamConjAut R N).apply_symm_apply a.1
      map_mul' := fun a b => by
        apply Subtype.ext
        exact map_mul (finSeamConjAut R N) a.1 b.1
      map_add' := fun a b => by
        apply Subtype.ext
        exact map_add (finSeamConjAut R N) a.1 b.1 }
  involutive := fun a => by
    apply Subtype.ext
    exact (finSeamConjAut R N).symm_apply_apply a.1

/-- `bareGlideUG R` squares to the period-2 horizontal translation `transX2 R`. -/
lemma bareGlideUG_sq (R : Type*) [CommRing R] :
    bareGlideUG R * bareGlideUG R = transX2 R := by
  ext ψ ⟨m, n⟩
  simp only [Module.End.mul_apply, bareGlideUG, transX2, LinearMap.coe_mk, AddHom.coe_mk]
  have h : (m + 1 + 1, - -n) = (m + 2, n) := Prod.ext (by omega) (by omega)
  rw [h]

/-- Scaled embedding of `ℤ × ℤ` into `InfoGeometry.Topology.Wallpaper.Lattice2D = ℝ × ℝ`
aligning unit `x`-steps with half-period glide steps `(1 / 2 : ℝ)`. -/
noncomputable def toLat (p : ℤ × ℤ) : InfoGeometry.Topology.Wallpaper.Lattice2D :=
  ((p.1 : ℝ) / 2, (p.2 : ℝ))

/-- `toLat` intertwines `(m + 1, -n)` with `Wallpaper.G` and `(m + 2, n)` with `Wallpaper.T_x`. -/
lemma toLat_intertwines_wallpaper (p : ℤ × ℤ) :
    toLat (p.1 + 1, -p.2) = InfoGeometry.Topology.Wallpaper.G (toLat p) ∧
      toLat (p.1 + 2, p.2) = InfoGeometry.Topology.Wallpaper.T_x (toLat p) ∧
      InfoGeometry.Topology.Wallpaper.G (InfoGeometry.Topology.Wallpaper.G (toLat p)) =
        InfoGeometry.Topology.Wallpaper.T_x (toLat p) := by
  refine ⟨?_, ?_, InfoGeometry.Topology.Wallpaper.glide_squared_eq_x_translation (toLat p)⟩
  · exact Prod.ext
      (by simp [toLat, InfoGeometry.Topology.Wallpaper.G]; ring)
      (by simp [toLat, InfoGeometry.Topology.Wallpaper.G])
  · exact Prod.ext
      (by simp [toLat, InfoGeometry.Topology.Wallpaper.T_x]; ring)
      (by simp [toLat, InfoGeometry.Topology.Wallpaper.T_x])

/-- Master `M2-K2` theorem: `bareGlideUG R` and `finBareGlideUG R N` satisfy `IsTwistedCommutant`
on the `seamTwistRingAut`-invariant hopping subrings (`Subring.subtype`), belong to
`Algebra.KleinBottleTwistedCommutantBridge.twistedCommutant`, square to `transX2` / `1`, and
intertwine with `Wallpaper.G` and `Wallpaper.T_x`. -/
lemma bareGlide_mem_twistedCommutant_and_wallpaper
    (R : Type*) [CommRing R] (N : ℕ) [NeZero N] (p : ℤ × ℤ) :
    IsTwistedCommutant (kastHopSubring R).subtype
        (seamTwistSubringInvolution R).toRingAut (bareGlideUG R) ∧
      IsTwistedCommutant (finKastHopSubring R N).subtype
        (finSeamSubringInvolution R N).toRingAut (finBareGlideUG R N) ∧
      bareGlideUG R ∈ InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.twistedCommutant
        {kastHx R, kastHy R, kastDirac R} (seamTwistRingAut R) ∧
      finBareGlideUG R N ∈ InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.twistedCommutant
        {finKastHx R N, finKastHy R N, finKastDirac R N} (finSeamConjAut R N) ∧
      bareGlideUG R * bareGlideUG R = transX2 R ∧
      toLat (p.1 + 1, -p.2) = InfoGeometry.Topology.Wallpaper.G (toLat p) ∧
      toLat (p.1 + 2, p.2) = InfoGeometry.Topology.Wallpaper.T_x (toLat p) := by
  have htw_inf : ∀ A ∈ kastHopSubring R,
      bareGlideUG R * A = seamTwistRingAut R A * bareGlideUG R := by
    intro A hA
    induction hA using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact bareGlideUG_twistedCommutes_kastHx R
      · exact bareGlideUG_twistedCommutes_kastHy R
    | one => simp
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add, hx, hy, map_add, add_mul]
    | neg x _ hx =>
      have hmul_neg : ∀ A B : Module.End R (LatticeState R), A * (-B) = -(A * B) := by
        intro A B; ext ψ q; simp
      have hneg_mul : ∀ A B : Module.End R (LatticeState R), (-A) * B = -(A * B) := by
        intro A B; ext ψ q; simp
      rw [hmul_neg, hx, map_neg, hneg_mul]
    | mul x y _ _ hx hy =>
      rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc, map_mul]
  have htw_fin : ∀ A ∈ finKastHopSubring R N,
      finBareGlideUG R N * A = finSeamConjAut R N A * finBareGlideUG R N := by
    intro A hA
    induction hA using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact finBareGlideUG_twistedCommutes_finKastHx R N
      · exact finBareGlideUG_twistedCommutes_finKastHy R N
    | one => simp
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add, hx, hy, map_add, add_mul]
    | neg x _ hx =>
      have hmul_neg : ∀ A B : Module.End R (FiniteCoverState R N), A * (-B) = -(A * B) := by
        intro A B; ext ψ q; simp
      have hneg_mul : ∀ A B : Module.End R (FiniteCoverState R N), (-A) * B = -(A * B) := by
        intro A B; ext ψ q; simp
      rw [hmul_neg, hx, map_neg, hneg_mul]
    | mul x y _ _ hx hy =>
      rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc, map_mul]
  obtain ⟨hG, hTx, _⟩ := toLat_intertwines_wallpaper p
  refine ⟨?_, ?_, ?_, ?_, bareGlideUG_sq R, hG, hTx⟩
  · intro a
    exact htw_inf a.1 a.2
  · intro a
    exact htw_fin a.1 a.2
  · intro a ha
    rcases ha with rfl | rfl | rfl
    · exact bareGlideUG_twistedCommutes_kastHx R
    · exact bareGlideUG_twistedCommutes_kastHy R
    · exact bareGlide_twistedCommutes_kastDirac
  · intro a ha
    rcases ha with rfl | rfl | rfl
    · exact finBareGlideUG_twistedCommutes_finKastHx R N
    · exact finBareGlideUG_twistedCommutes_finKastHy R N
    · exact finBareGlide_twistedCommutes_finKastDirac

end TwistedCommutantAndWallpaper

/-! ## Section 3: Dressed-glide sector swapping (`M2-K3`) -/

section DressedGlideSectorSwap

/-- Bipartite grading `B` swaps the untwisted (`+1`) and Möbius (`-1`) eigenspaces of
`dressedGlideUG` on `LatticeState R` and of `finDressedGlideUG` on `FiniteCoverState R N`. -/
lemma dressedGlide_swaps_untwisted_mobius_sectors
    (R : Type*) [CommRing R] (N : ℕ) [NeZero N]
    (ψ : LatticeState R) (φ : FiniteCoverState R N) :
    (dressedGlideUG R ψ = ψ → dressedGlideUG R (bipartiteB R ψ) = -(bipartiteB R ψ)) ∧
      (dressedGlideUG R ψ = -ψ → dressedGlideUG R (bipartiteB R ψ) = bipartiteB R ψ) ∧
      (finDressedGlideUG R N φ = φ →
        finDressedGlideUG R N (finBipartiteB R N φ) = -(finBipartiteB R N φ)) ∧
      (finDressedGlideUG R N φ = -φ →
        finDressedGlideUG R N (finBipartiteB R N φ) = finBipartiteB R N φ) := by
  have hanti_inf :
      dressedGlideUG R (bipartiteB R ψ) + bipartiteB R (dressedGlideUG R ψ) = 0 := by
    have h := congrArg (fun T : Module.End R (LatticeState R) => T ψ)
      (dressedGlide_sq_comm_dirac_anticomm_grading (R := R)).2.2
    simpa [LinearMap.add_apply, Module.End.mul_apply] using h
  have hanti_fin :
      finDressedGlideUG R N (finBipartiteB R N φ) +
        finBipartiteB R N (finDressedGlideUG R N φ) = 0 := by
    have h := congrArg (fun T : Module.End R (FiniteCoverState R N) => T φ)
      (finDressedGlide_involution_comm_dirac_anticomm_grading (R := R) (N := N)).2.2
    simpa [LinearMap.add_apply, Module.End.mul_apply] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hψ
    have h := eq_neg_of_add_eq_zero_left hanti_inf
    rwa [hψ] at h
  · intro hψ
    have h := eq_neg_of_add_eq_zero_left hanti_inf
    rwa [hψ, map_neg, neg_neg] at h
  · intro hφ
    have h := eq_neg_of_add_eq_zero_left hanti_fin
    rwa [hφ] at h
  · intro hφ
    have h := eq_neg_of_add_eq_zero_left hanti_fin
    rwa [hφ, map_neg, neg_neg] at h

end DressedGlideSectorSwap

/-! ## Section 4: Finite torus cover glide-orbit identification with `SignedPerm` (`M2-K4`) -/

section GlideOrbitSignedPerm

/-- Canonical `coverGlide` orbit representative `(0, n)` in `FiniteCoverVertex N`. -/
def orbitRep {N : ℕ} (n : Fin (2 * N)) : FiniteCoverVertex N :=
  (0, n)

/-- Two-bit encoding `(f (orbitRep n), f (coverGlide N (orbitRep n)))` on the `n`-th
`coverGlide` orbit. -/
def orbitPairBitEncode {N : ℕ} [NeZero N] (f : FiniteCoverVertex N → Bool)
    (n : Fin (2 * N)) : Bool × Bool :=
  (f (orbitRep n), f (coverGlide N (orbitRep n)))

/-- `Sector (2 * N)` image of a Boolean vertex field `f : FiniteCoverVertex N → Bool`. -/
def orbitPairSector {N : ℕ} [NeZero N] (f : FiniteCoverVertex N → Bool) : Sector (2 * N) :=
  fun n => kreinSectorBitEquiv.symm (orbitPairBitEncode f n)

/-- Central element of `SignedPerm (2 * N)` flipping every orbit bit simultaneously. -/
def kleinCoverCentralSignedPerm (N : ℕ) : SignedPerm (2 * N) :=
  SemidirectProduct.inl (fun _ => Multiplicative.ofAdd (1 : ZMod 2))

/-- `Fin 2 × Fin (2 * N)` decomposes into `2 * N` disjoint 2-element `coverGlide` orbits, and
pulling back a Boolean field along `coverGlide N` acts on `orbitPairSector f` as the central
involutive element `kleinCoverCentralSignedPerm N : SignedPerm (2 * N)`. -/
lemma finiteTorusCover_glide_orbit_signFlip (N : ℕ) [NeZero N]
    (f : FiniteCoverVertex N → Bool) :
    (∀ p : FiniteCoverVertex N,
        (p.1 = 0 ∧ p = orbitRep p.2) ∨ (p.1 = 1 ∧ p = coverGlide N (orbitRep (-p.2)))) ∧
      (∀ n₁ n₂ : Fin (2 * N), orbitRep n₁ ≠ coverGlide N (orbitRep n₂)) ∧
      orbitPairSector (fun p => f (coverGlide N p)) =
        kleinCoverCentralSignedPerm N • orbitPairSector f ∧
      (∀ g : SignedPerm (2 * N),
        kleinCoverCentralSignedPerm N * g = g * kleinCoverCentralSignedPerm N) ∧
      kleinCoverCentralSignedPerm N * kleinCoverCentralSignedPerm N = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rcases p with ⟨m, n⟩
    fin_cases m
    · exact Or.inl ⟨rfl, rfl⟩
    · refine Or.inr ⟨rfl, ?_⟩
      ext <;> simp [orbitRep, coverGlide]
  · intro n₁ n₂ h
    have h0 := congrArg Prod.fst h
    simp [orbitRep, coverGlide] at h0
  · funext n
    apply kreinSectorBitEquiv.injective
    have hsmul :
        (kleinCoverCentralSignedPerm N • orbitPairSector f) n =
          applyFlipBit (Multiplicative.ofAdd (1 : ZMod 2)) (orbitPairSector f n) := by
      change signFlipSector (kleinCoverCentralSignedPerm N).left
          ((kleinCoverCentralSignedPerm N).right • orbitPairSector f) n = _
      simp [kleinCoverCentralSignedPerm, signFlipSector]
    rw [hsmul, kreinSectorBitEquiv_applyFlipBit]
    have h1 : Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2)) = (1 : ZMod 2) := rfl
    rw [ite_eq_left_iff.mpr (fun hne => (hne h1).elim)]
    simp only [orbitPairSector, Equiv.apply_symm_apply, orbitPairBitEncode,
      coverGlide_involutive, Prod.swap]
  · intro g
    apply SemidirectProduct.ext
    · funext i
      simp only [kleinCoverCentralSignedPerm, SemidirectProduct.mul_left,
        SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, MulAut.one_apply,
        Pi.mul_apply]
      exact mul_comm (Multiplicative.ofAdd (1 : ZMod 2)) (g.left i)
    · simp [kleinCoverCentralSignedPerm]
  · apply SemidirectProduct.ext
    · funext i
      simp only [SemidirectProduct.mul_left, kleinCoverCentralSignedPerm,
        SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, MulAut.one_apply,
        Pi.mul_apply, SemidirectProduct.one_left, Pi.one_apply]
      rw [← ofAdd_add]
      have h2 : (1 + 1 : ZMod 2) = 0 := by decide
      rw [h2, ofAdd_zero]
    · simp [kleinCoverCentralSignedPerm]

end GlideOrbitSignedPerm

/-! ## Section 5: Lattice face reversal and plabic square twist (`M2-K5`) -/

section LatticeFaceAndPlabicTwist

/-- Orientation-reversing integral Klein-bottle glide `(m, n) ↦ (m + 1, -n)` on `ℤ × ℤ`. -/
def integralGlide (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 + 1, -p.2)

/-- Product of the four Kasteleyn edge weights around the unit square `[u, u+1] × [v, v+1]`. -/
def unitSquareCycleProduct (R : Type*) [CommRing R] (u : ℤ) : R :=
  (1 : R) * paritySign R (u + 1) * (1 : R) * paritySign R u

/-- Reversing the boundary orientation of a plabic square face swaps the four boundary
edge-weight coordinates `(y1, y2, y3, y4) ↦ (y4, y3, y2, y1)`. -/
def reverseSquareFace {F : Type*} (w : SquareFaceWeights F) : SquareFaceWeights F :=
  ⟨w.yf, w.y4, w.y3, w.y2, w.y1⟩

/-- Candidate direct identification of the signed Kasteleyn holonomy with the
central plabic face coordinate, retaining unit neighboring coordinates. -/
def kasteleynClusterChartSeed (u : ℤ) : SquareFaceWeights ℝ :=
  ⟨unitSquareCycleProduct ℝ u, 1, 1, 1, 1⟩

/-- Every unit square on `ℤ × ℤ` has Kasteleyn cycle product `-1`; `integralGlide` maps the
counterclockwise boundary of `(u, v)` to the reversed boundary of `(u + 1, -v - 1)` while
preserving `-1` under the `τ_y` (`paritySign R n`) gauge, and `reverseSquareFace` intertwines
`mutateF` with `mutateF_rev` compatibly with `cantor_square_mutation_involutive`. -/
lemma kleinBottle_lattice_face_reversal_and_plabic_twist
    (R : Type*) [CommRing R] (u v m n : ℤ)
    {F : Type*} [DivisionRing F] (w : SquareFaceWeights F)
    (M : InfoGeometry.Projective.MatrixPluckerPositiveBridge.Matrix2x4)
    (s : SquareFaceWeights ℝ)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4)) :
    unitSquareCycleProduct R u = -1 ∧
      (integralGlide (u, v) = (u + 1, -v) ∧
        integralGlide (u + 1, v) = (u + 2, -v) ∧
        integralGlide (u + 1, v + 1) = (u + 2, -v - 1) ∧
        integralGlide (u, v + 1) = (u + 1, -v - 1)) ∧
      paritySign R n * (1 : R) * paritySign R n = 1 ∧
      paritySign R n * paritySign R m * paritySign R (n + 1) = paritySign R (m + 1) ∧
      unitSquareCycleProduct R (u + 1) = -1 ∧
      reverseSquareFace (reverseSquareFace w) = w ∧
      reverseSquareFace (mutateF w) = mutateF_rev (reverseSquareFace w) ∧
      mutateF (reverseSquareFace (mutateF (cantorSquareSeed M s))) =
        reverseSquareFace (cantorSquareSeed M s) := by
  have hcyc : ∀ k : ℤ, unitSquareCycleProduct R k = -1 := by
    intro k
    unfold unitSquareCycleProduct
    rw [paritySign_add_one]
    have hmul : (1 : R) * -paritySign R k * (1 : R) * paritySign R k =
        -(paritySign R k * paritySign R k) := by ring
    rw [hmul, paritySign_sq]
  refine ⟨hcyc u, ⟨rfl, ?_, ?_, ?_⟩, ?_, ?_, hcyc (u + 1), rfl, rfl, ?_⟩
  · exact Prod.ext (by dsimp [integralGlide]; omega) rfl
  · exact Prod.ext (by dsimp [integralGlide]; omega) (by dsimp [integralGlide]; omega)
  · exact Prod.ext rfl (by dsimp [integralGlide]; omega)
  · rw [mul_one, paritySign_sq]
  · rw [paritySign_add_one n, paritySign_add_one m]
    have hcalc : paritySign R n * paritySign R m * -paritySign R n =
        -(paritySign R m * (paritySign R n * paritySign R n)) := by ring
    rw [hcalc, paritySign_sq, mul_one]
  · have hrev : mutateF (reverseSquareFace (mutateF (cantorSquareSeed M s))) =
        reverseSquareFace (mutateF_rev (mutateF (cantorSquareSeed M s))) := rfl
    rw [hrev, cantor_square_mutation_involutive M s hM]

/-- The direct chart identification `y_f = Kasteleyn face holonomy` is singular:
the holonomy is `-1`, so `1 + y_f = 0`, and forward then reversed plabic
mutation does not recover even this unit-neighbor seed. -/
lemma kasteleyn_holonomy_cluster_chart_roundtrip_fails (u : ℤ) :
    (1 + (kasteleynClusterChartSeed u).yf = 0) ∧
      (mutateF_rev (mutateF (kasteleynClusterChartSeed u))).y1 = 0 ∧
      mutateF_rev (mutateF (kasteleynClusterChartSeed u)) ≠
        kasteleynClusterChartSeed u := by
  have hcycle : unitSquareCycleProduct ℝ u = -1 := by
    unfold unitSquareCycleProduct
    rw [paritySign_add_one]
    have hmul : (1 : ℝ) * -paritySign ℝ u * (1 : ℝ) * paritySign ℝ u =
        -(paritySign ℝ u * paritySign ℝ u) := by ring
    rw [hmul, paritySign_sq]
  constructor
  · simp [kasteleynClusterChartSeed, hcycle]
  constructor
  · simp [kasteleynClusterChartSeed, mutateF, mutateF_rev, hcycle]
  · intro h
    have h1 := congrArg (fun w : SquareFaceWeights ℝ => w.y1) h
    norm_num [kasteleynClusterChartSeed, mutateF, mutateF_rev, hcycle] at h1

end LatticeFaceAndPlabicTwist

/-! ## Section 6: `N = 1` non-vacuity master witness (`M2-K6`) -/

section MasterWitnessN1

/-- Point-mass witness state `δ_{(0,0)}` on `FiniteCoverVertex 1 = Fin 2 × Fin 2`. -/
def deltaZeroZero : FiniteCoverState ℤ 1 :=
  fun p => if p = (0, 0) then 1 else 0

/-- Complete `N = 1` non-vacuity master witness over `FiniteCoverState ℤ 1` proving that
`finKastDirac`, `finDressedGlideUG`, `[finKastDirac, finBipartiteB]`, and
`[finBareGlideUG, finKastDirac]` are all nontrivial alongside the `M2-K1..M2-K5` algebraic laws. -/
lemma kleinBottle_bipartite_kasteleyn_master_witness_N1 :
    finKastDirac ℤ 1 ≠ 0 ∧
      finDressedGlideUG ℤ 1 ≠ 1 ∧
      finKastDirac ℤ 1 * finBipartiteB ℤ 1 ≠ finBipartiteB ℤ 1 * finKastDirac ℤ 1 ∧
      finBareGlideUG ℤ 1 * finKastDirac ℤ 1 ≠ finKastDirac ℤ 1 * finBareGlideUG ℤ 1 ∧
      finKastDirac ℤ 1 * finKastDirac ℤ 1 =
        finKastHx ℤ 1 * finKastHx ℤ 1 + finKastHy ℤ 1 * finKastHy ℤ 1 ∧
      IsTwistedCommutant (finKastHopSubring ℤ 1).subtype
        (finSeamSubringInvolution ℤ 1).toRingAut (finBareGlideUG ℤ 1) ∧
      finDressedGlideUG ℤ 1 * finDressedGlideUG ℤ 1 = 1 ∧
      (∀ p : FiniteCoverVertex 1, coverGlide 1 p ≠ p) ∧
      kleinCoverCentralSignedPerm 1 * kleinCoverCentralSignedPerm 1 = 1 ∧
      unitSquareCycleProduct ℤ 0 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, finKastDirac_sq ℤ 1, ?_,
    (finDressedGlide_involution_comm_dirac_anticomm_grading (R := ℤ) (N := 1)).1,
    coverGlide_fixedPointFree 1, ?_, ?_⟩
  · intro h
    have hval := congrArg (fun T : Module.End ℤ (FiniteCoverState ℤ 1) => T deltaZeroZero (1, 0)) h
    simp only [finKastDirac, finKastHx, finKastHy, fin2Sign, deltaZeroZero,
      LinearMap.add_apply, LinearMap.zero_apply, Pi.add_apply, Pi.zero_apply,
      LinearMap.coe_mk, AddHom.coe_mk] at hval
    revert hval
    decide
  · intro h
    have hval := congrArg (fun T : Module.End ℤ (FiniteCoverState ℤ 1) => T deltaZeroZero (1, 0)) h
    simp only [finDressedGlideUG, finRowParityTau, finBareGlideUG, coverGlide,
      finEvenSign, deltaZeroZero, Module.End.mul_apply, Module.End.one_apply,
      LinearMap.coe_mk, AddHom.coe_mk] at hval
    revert hval
    decide
  · intro h
    have hval := congrArg (fun T : Module.End ℤ (FiniteCoverState ℤ 1) => T deltaZeroZero (1, 0)) h
    simp only [finKastDirac, finKastHx, finKastHy, finBipartiteB,
      fin2Sign, finEvenSign, deltaZeroZero, Module.End.mul_apply,
      LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk] at hval
    revert hval
    decide
  · intro h
    have hval := congrArg (fun T : Module.End ℤ (FiniteCoverState ℤ 1) => T deltaZeroZero (1, 1)) h
    simp only [finBareGlideUG, finKastDirac, finKastHx, finKastHy, coverGlide,
      fin2Sign, deltaZeroZero, Module.End.mul_apply, LinearMap.add_apply,
      Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk] at hval
    revert hval
    decide
  · exact (bareGlide_mem_twistedCommutant_and_wallpaper ℤ 1 (0, 0)).2.1
  · exact (finiteTorusCover_glide_orbit_signFlip 1 (fun _ => false)).2.2.2.2
  · unfold unitSquareCycleProduct
    norm_num [paritySign]

end MasterWitnessN1

end InfoGeometry.Canonical.KleinBottleKasteleynPlabicOrbit
