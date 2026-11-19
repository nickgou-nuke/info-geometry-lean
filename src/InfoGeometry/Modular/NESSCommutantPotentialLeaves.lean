/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.CommutantInvariantGKSLFlow
import InfoGeometry.Thermodynamics.FiniteEntropyLeaves
import InfoGeometry.Thermodynamics.SouriauFoliation

/-!
# Potential leaves of conserved GKSL commutant readouts

For a family of observables in the joint commutant of a Schrödinger
GKSL generator, the real trace readouts form a conserved profile. The inverse
image of any real-valued potential on that profile is therefore an invariant
level set for the full matrix flow. Every limit of the flow remains on the same
level set. No coadjoint-orbit or symplectic structure is asserted here; this
is the precise finite-matrix conserved-leaf statement available from the
commutant data.
-/

noncomputable section

namespace InfoGeometry.Modular.NESSCommutantPotentialLeaves

open InfoGeometry.Modular.CommutantInvariantGKSLFlow
open InfoGeometry.Modular.SchrodingerGKSLFlowBridge
open InfoGeometry.Thermodynamics.SouriauFoliation
open Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- A scalar potential evaluated on the joint commutant-charge profile. -/
def potentialReadout {ι : Type*}
    (Q : ι → Mat) (potential : (ι → ℝ) → ℝ) (X : Mat) : ℝ :=
  potential (commutantReadoutProfile Q X)

/-- The level leaf of a potential of conserved commutant charges. This is an
actual subset of the full complex matrix algebra. -/
def potentialLeaf {ι : Type*}
    (Q : ι → Mat) (potential : (ι → ℝ) → ℝ) (c : ℝ) : Set Mat :=
  InfoGeometry.Thermodynamics.FiniteEntropyLeaves.entropyLeaf
    (potentialReadout Q potential) c

/-- Membership in a commutant-potential leaf is exactly equality of the
potential readout with its prescribed level. -/
theorem mem_potentialLeaf_iff {ι : Type*}
    (Q : ι → Mat) (potential : (ι → ℝ) → ℝ) (c : ℝ) (X : Mat) :
    X ∈ potentialLeaf Q potential c ↔ potentialReadout Q potential X = c := by
  exact InfoGeometry.Thermodynamics.FiniteEntropyLeaves.mem_entropyLeaf_iff

/-- The full Schrödinger GKSL orbit preserves every potential of a finite
joint-commutant readout profile. In particular, this applies to nonlinear
charge potentials, not only to individual linear readouts. -/
theorem gkslFlow_preserves_potentialReadout
    {ι κ : Type*} [Fintype κ]
    (H X : Mat) (V : κ → Mat) (Q : ι → Mat)
    (hQH : ∀ i, Q i * H = H * Q i)
    (hQV : ∀ i j, Q i * V j = V j * Q i)
    (hQstarV : ∀ i j, Q i * star (V j) = star (V j) * Q i)
    (potential : (ι → ℝ) → ℝ) (t : ℝ) :
    potentialReadout Q potential (gkslFlow H V t X) =
      potentialReadout Q potential X := by
  unfold potentialReadout
  rw [gkslFlow_maps_jointCommutantReadoutLeaf H X V Q hQH hQV hQstarV t]

/-- A GKSL orbit stays on the potential leaf selected by its initial matrix. -/
theorem gkslFlow_maps_potentialLeaf
    {ι κ : Type*} [Fintype κ]
    (H X : Mat) (V : κ → Mat) (Q : ι → Mat)
    (hQH : ∀ i, Q i * H = H * Q i)
    (hQV : ∀ i j, Q i * V j = V j * Q i)
    (hQstarV : ∀ i j, Q i * star (V j) = star (V j) * Q i)
    (potential : (ι → ℝ) → ℝ) (t : ℝ) :
    gkslFlow H V t X ∈ potentialLeaf Q potential
      (potentialReadout Q potential X) := by
  rw [mem_potentialLeaf_iff]
  exact gkslFlow_preserves_potentialReadout H X V Q hQH hQV hQstarV potential t

/-- Any norm limit of a GKSL orbit lies on its initial commutant-potential
leaf. The limit's existence is an explicit hypothesis; no ergodicity claim is
needed. -/
theorem tendsto_limit_mem_potentialLeaf
    {ι κ : Type*} [Fintype κ]
    (H X rhoLimit : Mat) (V : κ → Mat) (Q : ι → Mat)
    (hQH : ∀ i, Q i * H = H * Q i)
    (hQV : ∀ i j, Q i * V j = V j * Q i)
    (hQstarV : ∀ i j, Q i * star (V j) = star (V j) * Q i)
    (potential : (ι → ℝ) → ℝ)
    (hlim : Tendsto (fun t : ℝ => gkslFlow H V t X) atTop (𝓝 rhoLimit)) :
    rhoLimit ∈ potentialLeaf Q potential
      (potentialReadout Q potential X) := by
  rw [mem_potentialLeaf_iff]
  unfold potentialReadout
  rw [tendsto_limit_mem_jointCommutantReadoutLeaf H X rhoLimit V Q
    hQH hQV hQstarV hlim]

/-- The commutant profile induces a finite-matrix Souriau leaf whose entropy
and Weyl-scale readouts are two chosen potentials of the conserved charges.
This is a concrete instance of the repository's leaf interface; it does not
identify the leaf with a coadjoint orbit or assert a symplectic form. -/
def souriauLeafOfCommutantPotentials {ι : Type*}
    (Q : ι → Mat)
    (entropyPotential weylPotential : (ι → ℝ) → ℝ) (X : Mat) :
    SymplecticLeaf Mat where
  carrier := {Y | potentialReadout Q entropyPotential Y =
      potentialReadout Q entropyPotential X ∧
    potentialReadout Q weylPotential Y =
      potentialReadout Q weylPotential X}
  entropyReadout := potentialReadout Q entropyPotential
  weylScaleReadout := potentialReadout Q weylPotential
  leafEntropy := potentialReadout Q entropyPotential X
  leafWeylScale := potentialReadout Q weylPotential X
  entropy_constant := by
    intro Y hY
    exact hY.1
  weylScale_constant := by
    intro Y hY
    exact hY.2

/-- Every GKSL trajectory with the stated joint commutant constraints stays
on the induced Souriau entropy/Weyl leaf. -/
theorem gkslFlow_maps_souriauLeafOfCommutantPotentials
    {ι κ : Type*} [Fintype κ]
    (H X : Mat) (V : κ → Mat) (Q : ι → Mat)
    (hQH : ∀ i, Q i * H = H * Q i)
    (hQV : ∀ i j, Q i * V j = V j * Q i)
    (hQstarV : ∀ i j, Q i * star (V j) = star (V j) * Q i)
    (entropyPotential weylPotential : (ι → ℝ) → ℝ) (t : ℝ) :
    gkslFlow H V t X ∈
      (souriauLeafOfCommutantPotentials Q entropyPotential weylPotential X).carrier := by
  change potentialReadout Q entropyPotential (gkslFlow H V t X) =
      potentialReadout Q entropyPotential X ∧
    potentialReadout Q weylPotential (gkslFlow H V t X) =
      potentialReadout Q weylPotential X
  exact ⟨
    gkslFlow_preserves_potentialReadout H X V Q hQH hQV hQstarV
      entropyPotential t,
    gkslFlow_preserves_potentialReadout H X V Q hQH hQV hQstarV
      weylPotential t⟩

/-- Every existing norm limit of the orbit remains on the induced Souriau
entropy/Weyl leaf. -/
theorem tendsto_limit_mem_souriauLeafOfCommutantPotentials
    {ι κ : Type*} [Fintype κ]
    (H X rhoLimit : Mat) (V : κ → Mat) (Q : ι → Mat)
    (hQH : ∀ i, Q i * H = H * Q i)
    (hQV : ∀ i j, Q i * V j = V j * Q i)
    (hQstarV : ∀ i j, Q i * star (V j) = star (V j) * Q i)
    (entropyPotential weylPotential : (ι → ℝ) → ℝ)
    (hlim : Tendsto (fun t : ℝ => gkslFlow H V t X) atTop (𝓝 rhoLimit)) :
    rhoLimit ∈
      (souriauLeafOfCommutantPotentials Q entropyPotential weylPotential X).carrier := by
  change potentialReadout Q entropyPotential rhoLimit =
      potentialReadout Q entropyPotential X ∧
    potentialReadout Q weylPotential rhoLimit =
      potentialReadout Q weylPotential X
  exact ⟨
    tendsto_limit_mem_potentialLeaf H X rhoLimit V Q hQH hQV hQstarV
      entropyPotential hlim,
    tendsto_limit_mem_potentialLeaf H X rhoLimit V Q hQH hQV hQstarV
      weylPotential hlim⟩

end InfoGeometry.Modular.NESSCommutantPotentialLeaves
