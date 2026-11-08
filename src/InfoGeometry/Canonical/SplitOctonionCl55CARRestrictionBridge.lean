/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge
import InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal

/-!
# First-three-mode CAR action on the `Cl(5,5)` vacuum ideal

The three-mode exterior/Zorn Fock carrier embeds into the five-mode exterior
spinor by extending its basis coordinates by zero. This file proves that the
first three `Cl(5,5)` creation and annihilation generators preserve that image
and restrict to the three-mode wedge and contraction operators. In particular,
this is an operator intertwiner on a concrete subspace, not an identification
of the nonassociative Zorn product with Clifford multiplication.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionCl55CARRestrictionBridge

open InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

/-- Extend a three-mode vector by zero in the two spectator coordinates. -/
def colorVectorToFive : V3 →ₗ[ℝ]
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5 where
  toFun v := embedV5 v
  map_add' v w := by
    funext j
    by_cases h : j.val < 3 <;> simp [embedV5, h, add_comm]
  map_smul' c v := by
    funext j
    by_cases h : j.val < 3 <;> simp [embedV5, h]

/-- Project a five-mode vector to its first three coordinates. -/
def fiveVectorToColor : InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5 →ₗ[ℝ] V3 where
  toFun w := fun i => w (Fin.castAdd 2 i)
  map_add' w z := by ext i; rfl
  map_smul' c w := by ext i; rfl

theorem fiveVectorToColor_colorVectorToFive :
    fiveVectorToColor.comp colorVectorToFive = LinearMap.id := by
  apply LinearMap.ext
  intro v
  ext i
  simp [fiveVectorToColor, colorVectorToFive, embedV5]

/-- The first three exterior modes included in the five-mode spinor. -/
noncomputable def includeColorExterior : Exterior3 →ₐ[ℝ]
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.Spinor :=
  ExteriorAlgebra.map colorVectorToFive

theorem includeColorExterior_injective : Function.Injective includeColorExterior := by
  apply ExteriorAlgebra.map_injective
  exact ⟨fiveVectorToColor, fiveVectorToColor_colorVectorToFive⟩

theorem colorVectorToFive_basis (i : Fin 3) :
    colorVectorToFive (basisVector3 i) = basisVector (Fin.castAdd 2 i) := by
  calc
    colorVectorToFive (basisVector3 i) =
        fun j => if j = Fin.castAdd 2 i then 1 else 0 := by
      simpa [colorVectorToFive] using embedV5_basisVector3 i
    _ = basisVector (Fin.castAdd 2 i) := by
      funext j
      simp [basisVector, Pi.single_apply]

/-- Creation on the embedded three-mode states is the first-three-mode
five-dimensional wedge action. -/
theorem includeColorExterior_wedgeVector (v : V3) (ψ : Exterior3) :
    includeColorExterior (exteriorWedge3 v ψ) =
      wedge (colorVectorToFive v) (includeColorExterior ψ) := by
  change includeColorExterior (ExteriorAlgebra.ι ℝ v * ψ) = _
  rw [map_mul]
  simp [includeColorExterior, wedge]

theorem includeColorExterior_wedge (i : Fin 3) (ψ : Exterior3) :
    includeColorExterior (exteriorWedge3 (basisVector3 i) ψ) =
      wedge (basisVector (Fin.castAdd 2 i)) (includeColorExterior ψ) := by
  rw [includeColorExterior_wedgeVector, colorVectorToFive_basis]

/-- The pulled-back fifth-space coordinate covector agrees with the original
three-space coordinate covector on the embedded modes. -/
theorem fiveDual_colorBasis (i j : Fin 3) :
    dualBasisVector (Fin.castAdd 2 i) (colorVectorToFive (basisVector3 j)) =
      (LinearMap.proj i : V3 →ₗ[ℝ] ℝ) (basisVector3 j) := by
  rw [colorVectorToFive_basis]
  have hcast : Fin.castAdd 2 i = Fin.castAdd 2 j ↔ i = j := by
    constructor
    · intro h
      exact (Fin.castAdd_injective 3 2) h
    · intro h
      simpa [h]
  simp [dualBasisVector, basisVector3, basisVector, LinearMap.proj_apply,
    Pi.single_apply, hcast]

/-- Contraction commutes with the exterior inclusion for each of the first
three coordinate modes. -/
theorem includeColorExterior_contract (i : Fin 3) (ψ : Exterior3) :
    includeColorExterior (exteriorContract3 (LinearMap.proj i) ψ) =
      contract (dualBasisVector (Fin.castAdd 2 i)) (includeColorExterior ψ) := by
  refine CliffordAlgebra.left_induction (Q := (0 : QuadraticForm ℝ V3)) ?_ ?_ ?_ ψ
  · intro r
    have hsource :
        exteriorContract3 (LinearMap.proj i) (algebraMap ℝ Exterior3 r) = 0 := by
      simp [exteriorContract3]
    rw [hsource, map_zero]
    change 0 = contract (dualBasisVector (Fin.castAdd 2 i))
      (includeColorExterior (algebraMap ℝ Exterior3 r))
    rw [AlgHom.map_algebraMap]
    simpa [contract] using
      (CliffordAlgebra.contractLeft_algebraMap
        (0 : QuadraticForm ℝ V5) (dualBasisVector (Fin.castAdd 2 i)) r)
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro x v hx
    change includeColorExterior
        (exteriorContract3 (LinearMap.proj i) (exteriorWedge3 v x)) =
      contract (dualBasisVector (Fin.castAdd 2 i))
        (includeColorExterior (exteriorWedge3 v x))
    rw [exteriorContract3_wedge3_apply, map_sub, map_smul]
    simp only [includeColorExterior_wedgeVector, hx, contract_wedge]
    rw [show dualBasisVector (Fin.castAdd 2 i) (colorVectorToFive v) = v i by
      simp [dualBasisVector, colorVectorToFive, embedV5]]
    simp [LinearMap.proj_apply]

/-- The two complementary exterior coordinates are removed by the color
projection after wedge multiplication. -/
theorem projectColorExterior_complement_wedge
    (i : Fin 2) (ψ : Exterior3) :
    ExteriorAlgebra.map fiveVectorToColor
      (wedge (basisVector (Fin.natAdd 3 i)) (includeColorExterior ψ)) = 0 := by
  change ExteriorAlgebra.map fiveVectorToColor
    (ExteriorAlgebra.ι ℝ (basisVector (Fin.natAdd 3 i)) * includeColorExterior ψ) = 0
  rw [map_mul, ExteriorAlgebra.map_apply_ι]
  have hmode : fiveVectorToColor (basisVector (Fin.natAdd 3 i)) = 0 := by
    funext j
    have hne : Fin.castAdd 2 j ≠ Fin.natAdd 3 i := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    simp [fiveVectorToColor, basisVector, Pi.single_apply, hne]
  rw [hmode]
  simp

/-- Contraction by either complementary coordinate annihilates every state
in the embedded three-mode exterior subspace. -/
theorem includeColorExterior_complement_contract
    (i : Fin 2) (ψ : Exterior3) :
    contract (dualBasisVector (Fin.natAdd 3 i)) (includeColorExterior ψ) = 0 := by
  refine CliffordAlgebra.left_induction (Q := (0 : QuadraticForm ℝ V3)) ?_ ?_ ?_ ψ
  · intro r
    rw [AlgHom.map_algebraMap]
    simpa [contract] using
      (CliffordAlgebra.contractLeft_algebraMap
        (0 : QuadraticForm ℝ V5) (dualBasisVector (Fin.natAdd 3 i)) r)
  · intro x y hx hy
    simp [hx, hy]
  · intro x v hx
    change contract (dualBasisVector (Fin.natAdd 3 i))
      (includeColorExterior (exteriorWedge3 v x)) = 0
    rw [includeColorExterior_wedgeVector, contract_wedge]
    have hmode : dualBasisVector (Fin.natAdd 3 i) (colorVectorToFive v) = 0 := by
      simp [dualBasisVector, colorVectorToFive, embedV5, Fin.natAdd]
    rw [hmode, hx]
    simp

/-- The first-three-mode states inside the actual Cl(5,5) vacuum ideal. -/
def colorStateInCl55Ideal (ψ : Exterior3) : MinimalLeftIdeal :=
  cl55VacuumIdealSpinorEquiv.symm (includeColorExterior ψ)

/-- The positive-null Cl(5,5) generator acts on the embedded states as the
three-mode exterior creation operator. -/
theorem cl55_annihilation55_restricts_to_color_creation
    (i : Fin 3) (ψ : Exterior3) :
    cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (annihilation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ)) =
      includeColorExterior (exteriorWedge3 (basisVector3 i) ψ) := by
  rw [vacuumIdeal_annihilation55_action, colorStateInCl55Ideal,
    cl55VacuumIdealSpinorEquiv.apply_symm_apply, ← includeColorExterior_wedge]

/-- The negative-null Cl(5,5) generator acts on the embedded states as the
three-mode exterior contraction operator. -/
theorem cl55_creation55_restricts_to_color_annihilation
    (i : Fin 3) (ψ : Exterior3) :
    cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (creation55 (Fin.castAdd 2 i)) (colorStateInCl55Ideal ψ)) =
      includeColorExterior (exteriorContract3 (LinearMap.proj i) ψ) := by
  rw [vacuumIdeal_creation55_action, colorStateInCl55Ideal,
    cl55VacuumIdealSpinorEquiv.apply_symm_apply, ← includeColorExterior_contract]

/-- The complementary positive-null Cl(5,5) mode has zero action after
projection to the three-color exterior carrier. -/
theorem cl55_complement_annihilation_projects_to_zero
    (i : Fin 2) (ψ : Exterior3) :
    ExteriorAlgebra.map fiveVectorToColor
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (annihilation55 (Fin.natAdd 3 i)) (colorStateInCl55Ideal ψ))) = 0 := by
  rw [vacuumIdeal_annihilation55_action, colorStateInCl55Ideal,
    cl55VacuumIdealSpinorEquiv.apply_symm_apply,
    projectColorExterior_complement_wedge]

/-- The complementary negative-null Cl(5,5) mode has zero action after
projection to the three-color exterior carrier. -/
theorem cl55_complement_creation_projects_to_zero
    (i : Fin 2) (ψ : Exterior3) :
    ExteriorAlgebra.map fiveVectorToColor
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (creation55 (Fin.natAdd 3 i)) (colorStateInCl55Ideal ψ))) = 0 := by
  rw [vacuumIdeal_creation55_action, colorStateInCl55Ideal,
    cl55VacuumIdealSpinorEquiv.apply_symm_apply,
    includeColorExterior_complement_contract]
  simp

end InfoGeometry.Canonical.SplitOctonionCl55CARRestrictionBridge

end
