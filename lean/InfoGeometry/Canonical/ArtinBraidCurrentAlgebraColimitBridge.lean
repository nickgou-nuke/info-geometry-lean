/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
import InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
import InfoGeometry.Canonical.ArtinBraidFilteredColimit
import InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation
import InfoGeometry.Canonical.Cl11CommonFockCarrier
import InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence
import InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit
import InfoGeometry.Canonical.AffineKacMoodyColimitIsomorphism

/-!
# Canonical Artin Braid, Fermionic Fock, Heisenberg, and Affine Kac--Moody Colimit Corridor

This module connects the algebraic $B_\infty$ Artin braid representation on the
$\mathrm{Cl}(1,1)$ fermionic Fock colimit carrier, the completed Heisenberg
current representation on charged Fock space, and the categorical `ModuleCat`
colimits of the Heisenberg and affine Kac--Moody algebras.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge`:
    `heisenbergColimitMode`, `heisenbergFiniteModeColimitEquiv_mode`,
    `heisenbergColimitMode_lie_eq`, `chargedFock_vira_mode_shift`.
  * `InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation` &
    `InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence`:
    `bInfinityTensorRepresentation`, `sigmaInfinity`, `clLimitFockOpAlgEquiv`.
  * `InfoGeometry.Canonical.AffineKacMoodyColimitIsomorphism`:
    `affineCurrentColimitMode`, `affineCentralColimitMode`,
    `affineCurrentColimitMode_lie_eq`.
- BUCKET 2 (Deconfabulation):
  * Eliminated 6 pass-through wrapper theorems and 2 `injected-hypothesis-surface`
    section variable assumptions.
  * Wired the affine current colimit section directly to the intrinsic
    `ModuleCat` colimit commutator `affineCurrentColimitMode_lie_eq`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `completedCurrent_mode_chargedFock_readout`, `completedCurrent_mode_virasoro_shift`:
    charged-Fock current readout and Sugawara Virasoro shift.
  * `bInfinityOperatorRepresentation`, `bInfinityOperator_artin`,
    `bInfinityOperator_commute`, `bInfinityFermionicFockOperatorMulHom`,
    `bInfinityFermionicFockOperatorMulHom_artin`,
    `bInfinityFermionicFockOperatorMulHom_commute`:
    $B_\infty$ braid group Yang--Baxter and far-commutativity relations on the
    fermionic Fock operator colimit.
  * `heisenberg_colimit_current_readout`, `affine_current_colimit_readout`,
    `affine_current_colimit_kacMoody_bracket`,
    `affine_current_intrinsic_colimit_kacMoody_bracket`:
    Heisenberg and affine Kac--Moody categorical colimit current readouts and
    commutation relations.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArtinBraidCurrentAlgebraColimitBridge

open InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
open InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.ArtinBraidFilteredColimit
open InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation
open InfoGeometry.Canonical.Cl11CommonFockCarrier
open InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence
open InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit
open VirasoroProject

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Evaluating `representedCompletedCurrentMode` at the point-mode
`completedCurrentPoint m` yields the charged-Fock Heisenberg generator `J m`. -/
theorem completedCurrent_mode_chargedFock_readout
    (α : 𝕜) (m : ℤ) :
    representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m := by
  rw [representedCompletedCurrentMode_point (𝕜 := 𝕜) α m]

/-- The Sugawara Virasoro generator $L_r$ shifts the represented completed
current mode `completedCurrentPoint m` to `-m • representedCompletedCurrentMode α (completedCurrentPoint (r + m))`. -/
theorem completedCurrent_mode_virasoro_shift
    (α : 𝕜) (r m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 r)).commutator
      (representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint m)) =
      -m • representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint (r + m)) := by
  have h := virasoro_lgen_acts_on_completedCurrent (𝕜 := 𝕜) α r m
  exact h

/-- Representation of the infinite Artin braid group $B_\infty$ in the unit
group of the common $\mathrm{Cl}(1,1)$ Fock colimit operator algebra. -/
def bInfinityOperatorRepresentation :
    BInfinity →* (Cl11CommonFockCarrier.Operator)ˣ :=
  (Units.map Cl11CommonFockCarrier.limitRepresentation).comp
    bInfinityTensorRepresentation

/-- The infinite braid generator is represented by the canonical left-regular
Majorana unit on the algebraic tensor-tower colimit. -/
@[simp] theorem bInfinityOperatorRepresentation_sigma (i : ℕ) :
    bInfinityOperatorRepresentation (sigmaInfinity i) =
      Units.map Cl11CommonFockCarrier.limitRepresentation
        (majoranaBraidUnit i) := by
  change Units.map Cl11CommonFockCarrier.limitRepresentation.toMonoidHom
      (bInfinityTensorRepresentation (sigmaInfinity i)) = _
  rw [bInfinityTensorRepresentation_sigma]
  rfl

/-- The operator-valued braid representation acts on the common colimit by
left multiplication with the corresponding Jordan--Wigner unit. -/
theorem bInfinityOperatorRepresentation_apply
    (b : BInfinity) (x : Cl11CommonFockCarrier.Carrier) :
    ((↑(bInfinityOperatorRepresentation b) :
        Cl11CommonFockCarrier.Operator) x) =
      (bInfinityTensorRepresentation b : Cl11CommonFockCarrier.Carrier) * x := by
  change Cl11CommonFockCarrier.limitRepresentation
      (bInfinityTensorRepresentation b) x = _
  simp [Cl11CommonFockCarrier.limitRepresentation_apply]

/-- Artin braid relation $\sigma_i \sigma_{i+1} \sigma_i = \sigma_{i+1} \sigma_i \sigma_{i+1}$
for `bInfinityOperatorRepresentation`. -/
theorem bInfinityOperator_artin (i : ℕ) :
    bInfinityOperatorRepresentation (sigmaInfinity i) *
        bInfinityOperatorRepresentation (sigmaInfinity (i + 1)) *
        bInfinityOperatorRepresentation (sigmaInfinity i) =
      bInfinityOperatorRepresentation (sigmaInfinity (i + 1)) *
        bInfinityOperatorRepresentation (sigmaInfinity i) *
        bInfinityOperatorRepresentation (sigmaInfinity (i + 1)) := by
  have h := congrArg bInfinityOperatorRepresentation (sigmaInfinity_artin i)
  simpa only [map_mul] using h

/-- Far-commutativity $\sigma_i \sigma_j = \sigma_j \sigma_i$ for $i + 1 < j$
under `bInfinityOperatorRepresentation`. -/
theorem bInfinityOperator_commute {i j : ℕ} (hij : i + 1 < j) :
    bInfinityOperatorRepresentation (sigmaInfinity i) *
        bInfinityOperatorRepresentation (sigmaInfinity j) =
      bInfinityOperatorRepresentation (sigmaInfinity j) *
        bInfinityOperatorRepresentation (sigmaInfinity i) := by
  have h := congrArg bInfinityOperatorRepresentation (sigmaInfinity_commute hij)
  simpa only [map_mul] using h

/-! ### Transport to the fermionic Fock-operator limit -/

/-- Image of a braid element $b \in B_\infty$ in the fermionic Fock-operator
colimit `RealCantorOpInf` under `clLimitFockOpAlgEquiv`. -/
def bInfinityFermionicFockOperatorValue (b : BInfinity) :
    InfoGeometry.Canonical.JordanWignerCantorRepresentation.RealCantorOpInf :=
  clLimitFockOpAlgEquiv (bInfinityTensorRepresentation b : Limit)

/-- Multiplicativity of `bInfinityFermionicFockOperatorValue`. -/
theorem bInfinityFermionicFockOperatorValue_mul (b c : BInfinity) :
    bInfinityFermionicFockOperatorValue (b * c) =
      bInfinityFermionicFockOperatorValue b *
        bInfinityFermionicFockOperatorValue c := by
  unfold bInfinityFermionicFockOperatorValue
  rw [map_mul]
  change clLimitFockOpAlgEquiv
      ((bInfinityTensorRepresentation b : Limit) *
        (bInfinityTensorRepresentation c : Limit)) = _
  rw [map_mul]

/-- Multiplicative homomorphism `BInfinity →ₙ* RealCantorOpInf` into the
fermionic Fock-operator direct limit. -/
def bInfinityFermionicFockOperatorMulHom :
    BInfinity →ₙ*
      InfoGeometry.Canonical.JordanWignerCantorRepresentation.RealCantorOpInf where
  toFun := bInfinityFermionicFockOperatorValue
  map_mul' := bInfinityFermionicFockOperatorValue_mul

/-- Applying `clLimitFockOpAlgEquiv.symm` to `bInfinityFermionicFockOperatorValue b`
recovers `(bInfinityTensorRepresentation b : Limit)`. -/
theorem bInfinityFermionicFockOperatorValue_roundtrip (b : BInfinity) :
    clLimitFockOpAlgEquiv.symm
        (bInfinityFermionicFockOperatorValue b) =
      (bInfinityTensorRepresentation b : Limit) := by
  unfold bInfinityFermionicFockOperatorValue
  exact clLimitFockOpAlgEquiv.symm_apply_apply
    (bInfinityTensorRepresentation b : Limit)

/-- Roundtrip identity for `bInfinityFermionicFockOperatorMulHom`. -/
theorem bInfinityFermionicFockOperatorMulHom_roundtrip (b : BInfinity) :
    clLimitFockOpAlgEquiv.symm
        (bInfinityFermionicFockOperatorMulHom b) =
      (bInfinityTensorRepresentation b : Limit) := by
  change clLimitFockOpAlgEquiv.symm
      (bInfinityFermionicFockOperatorValue b) = _
  exact bInfinityFermionicFockOperatorValue_roundtrip b

/-- Generator readout of `bInfinityFermionicFockOperatorValue` at `sigmaInfinity i`
in terms of the adjacent Majorana modes $1 + \gamma_i \gamma_{i+1}$. -/
@[simp] theorem bInfinityFermionicFockOperatorValue_sigma (i : ℕ) :
    bInfinityFermionicFockOperatorValue (sigmaInfinity i) =
      clLimitFockOpAlgEquiv (1 + majoranaMode i * majoranaMode (i + 1)) := by
  unfold bInfinityFermionicFockOperatorValue
  rw [bInfinityTensorRepresentation_sigma]
  rfl

/-- Artin braid relation for `bInfinityFermionicFockOperatorValue`. -/
theorem bInfinityFermionicFockOperatorValue_artin (i : ℕ) :
    bInfinityFermionicFockOperatorValue (sigmaInfinity i) *
        bInfinityFermionicFockOperatorValue (sigmaInfinity (i + 1)) *
        bInfinityFermionicFockOperatorValue (sigmaInfinity i) =
      bInfinityFermionicFockOperatorValue (sigmaInfinity (i + 1)) *
        bInfinityFermionicFockOperatorValue (sigmaInfinity i) *
        bInfinityFermionicFockOperatorValue (sigmaInfinity (i + 1)) := by
  have h := congrArg bInfinityTensorRepresentation (sigmaInfinity_artin i)
  have h' := congrArg (fun x : Limitˣ => (x : Limit)) h
  have h'' := congrArg (fun x : Limit => clLimitFockOpAlgEquiv x) h'
  simpa [bInfinityFermionicFockOperatorValue, map_mul] using h''

/-- Far-commutativity for `bInfinityFermionicFockOperatorValue`. -/
theorem bInfinityFermionicFockOperatorValue_commute {i j : ℕ} (hij : i + 1 < j) :
    bInfinityFermionicFockOperatorValue (sigmaInfinity i) *
        bInfinityFermionicFockOperatorValue (sigmaInfinity j) =
      bInfinityFermionicFockOperatorValue (sigmaInfinity j) *
        bInfinityFermionicFockOperatorValue (sigmaInfinity i) := by
  have h := congrArg bInfinityTensorRepresentation (sigmaInfinity_commute hij)
  have h' := congrArg (fun x : Limitˣ => (x : Limit)) h
  have h'' := congrArg (fun x : Limit => clLimitFockOpAlgEquiv x) h'
  simpa [bInfinityFermionicFockOperatorValue, map_mul] using h''

/-- Generator readout for `bInfinityFermionicFockOperatorMulHom` at `sigmaInfinity i`. -/
@[simp] theorem bInfinityFermionicFockOperatorMulHom_sigma (i : ℕ) :
    bInfinityFermionicFockOperatorMulHom (sigmaInfinity i) =
      clLimitFockOpAlgEquiv (1 + majoranaMode i * majoranaMode (i + 1)) := by
  change bInfinityFermionicFockOperatorValue (sigmaInfinity i) = _
  exact bInfinityFermionicFockOperatorValue_sigma i

/-- Artin braid relation for `bInfinityFermionicFockOperatorMulHom`. -/
theorem bInfinityFermionicFockOperatorMulHom_artin (i : ℕ) :
    bInfinityFermionicFockOperatorMulHom (sigmaInfinity i) *
        bInfinityFermionicFockOperatorMulHom (sigmaInfinity (i + 1)) *
        bInfinityFermionicFockOperatorMulHom (sigmaInfinity i) =
      bInfinityFermionicFockOperatorMulHom (sigmaInfinity (i + 1)) *
        bInfinityFermionicFockOperatorMulHom (sigmaInfinity i) *
        bInfinityFermionicFockOperatorMulHom (sigmaInfinity (i + 1)) := by
  change bInfinityFermionicFockOperatorValue (sigmaInfinity i) *
      bInfinityFermionicFockOperatorValue (sigmaInfinity (i + 1)) *
      bInfinityFermionicFockOperatorValue (sigmaInfinity i) =
    bInfinityFermionicFockOperatorValue (sigmaInfinity (i + 1)) *
      bInfinityFermionicFockOperatorValue (sigmaInfinity i) *
      bInfinityFermionicFockOperatorValue (sigmaInfinity (i + 1))
  exact bInfinityFermionicFockOperatorValue_artin (i := i)

/-- Far-commutativity for `bInfinityFermionicFockOperatorMulHom`. -/
theorem bInfinityFermionicFockOperatorMulHom_commute {i j : ℕ} (hij : i + 1 < j) :
    bInfinityFermionicFockOperatorMulHom (sigmaInfinity i) *
        bInfinityFermionicFockOperatorMulHom (sigmaInfinity j) =
      bInfinityFermionicFockOperatorMulHom (sigmaInfinity j) *
        bInfinityFermionicFockOperatorMulHom (sigmaInfinity i) := by
  change bInfinityFermionicFockOperatorValue (sigmaInfinity i) *
      bInfinityFermionicFockOperatorValue (sigmaInfinity j) =
    bInfinityFermionicFockOperatorValue (sigmaInfinity j) *
      bInfinityFermionicFockOperatorValue (sigmaInfinity i)
  exact bInfinityFermionicFockOperatorValue_commute (i := i) (j := j) hij

/-- The categorical Heisenberg colimit mode `heisenbergColimitMode m` maps to
`HeisenbergAlgebra.jgen 𝕜 m` under `heisenbergFiniteModeColimitEquiv`. -/
theorem heisenberg_colimit_current_readout (m : ℤ) :
    heisenbergFiniteModeColimitEquiv
        (heisenbergColimitMode (𝕜 := 𝕜) m) =
      HeisenbergAlgebra.jgen 𝕜 m := by
  rw [heisenbergFiniteModeColimitEquiv_mode (𝕜 := 𝕜) m]

/-- The represented completed current mode at `completedCurrentPoint m` agrees
with the charged-Fock Heisenberg mode `(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m`. -/
theorem completedCurrent_to_same_heisenberg_current
    (α : 𝕜) (m : ℤ) :
    representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m := by
  rw [representedCompletedCurrentMode_eq_chargedFockJ (𝕜 := 𝕜) α m]

section Affine
universe u
variable {𝕜a : Type u} [CommRing 𝕜a] [IsAddTorsionFree 𝕜a]
variable {𝓰 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜a 𝓰]

/-- Comparison readout of the categorical affine Kac--Moody current mode
`affineCurrentColimitMode Φ hΦ hΦs n x`. -/
theorem affine_current_colimit_readout
    (Φ : LinearMap.BilinForm 𝕜a 𝓰) (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)
    (n : ℤ) (x : 𝓰) :
    (affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCurrentColimitMode Φ hΦ hΦs n x) =
      VirasoroProject.affineCurrentGen (𝕜 := 𝕜a) (𝓰 := 𝓰) Φ hΦ hΦs n x := by
  rw [affineFiniteModeColimitMap_current Φ hΦ hΦs n x]

/-- Comparison-image Kac--Moody commutator for two categorical colimit current modes. -/
theorem affine_current_colimit_kacMoody_bracket
    (Φ : LinearMap.BilinForm 𝕜a 𝓰) (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)
    (m n : ℤ) (x y : 𝓰) :
    ⁅(affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCurrentColimitMode Φ hΦ hΦs m x),
      (affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCurrentColimitMode Φ hΦ hΦs n y)⁆ =
      VirasoroProject.affineCurrentGen (𝕜 := 𝕜a) (𝓰 := 𝓰) Φ hΦ hΦs
        (m + n) (⁅x, y⁆ : 𝓰) +
        if m + n = 0 then
          (↑m * (Φ x) y) •
            VirasoroProject.affineCentralGen (𝕜 := 𝕜a) (𝓰 := 𝓰) Φ hΦ hΦs
        else 0 := by
  rw [affineCurrentColimit_bracket_readout Φ hΦ hΦs m n x y]

/-- Intrinsic Kac--Moody commutator inside the `ModuleCat 𝕜a` colimit
`affineFiniteModeColimit Φ hΦ hΦs`. -/
theorem affine_current_intrinsic_colimit_kacMoody_bracket
    (Φ : LinearMap.BilinForm 𝕜a 𝓰) (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)
    (m n : ℤ) (x y : 𝓰) :
    ⁅affineCurrentColimitMode Φ hΦ hΦs m x,
      affineCurrentColimitMode Φ hΦ hΦs n y⁆ =
      affineCurrentColimitMode Φ hΦ hΦs (m + n) (⁅x, y⁆ : 𝓰) +
        if m + n = 0 then
          ((m : 𝕜a) * Φ x y) • affineCentralColimitMode Φ hΦ hΦs
        else 0 := by
  rw [affineCurrentColimitMode_bracket Φ hΦ hΦs m n x y]

end Affine

end InfoGeometry.Canonical.ArtinBraidCurrentAlgebraColimitBridge

end noncomputable section
