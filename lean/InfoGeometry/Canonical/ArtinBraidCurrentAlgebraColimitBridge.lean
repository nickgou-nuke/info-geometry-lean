import InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation
import InfoGeometry.Canonical.Cl11CommonFockCarrier
import InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
import InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
import InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
import InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit

/-!
# Braid, tensor, current, Sugawara and Virasoro colimit corridor

This file records the exact common architecture now present in the repository.
There are two genuinely different filtered systems:

1. finite Artin braid groups, whose `GrpCat` colimit is `B∞` and which act by
   Jordan--Wigner Majorana units on the `Cl(1,1)` tensor direct limit;
2. finite current-mode modules, whose `ModuleCat` colimits feed Heisenberg and
   affine Kac--Moody current algebras.

On the Heisenberg lane, the existing constructive current bridge supplies the
normal-ordered fermionic source and the existing Sugawara representation turns
currents into Virasoro modes.  On the affine lane, the new finite-mode colimit
maps canonical current representatives into the native loop-algebra central
extension.

The file intentionally does *not* identify the `Cl(1,1)` algebraic direct-limit
carrier with the external charged Fock carrier or with a general affine
Kac--Moody module.  Such an identification would require an additional
representation/bosonization equivalence and is not a consequence of the
colimit universal properties alone.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArtinBraidCurrentAlgebraColimitBridge

open InfoGeometry.Canonical.ArtinBraidFilteredColimit
open InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation
open InfoGeometry.Canonical.Cl11CommonFockCarrier
open InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
open InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
open InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
open InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit
open VirasoroProject

/-! ## B∞ as genuine operators on the common tensor-colimit carrier -/

/-- The unit representation of `B∞` is transported through the faithful
left-regular representation of the algebraic tensor colimit.  Hence every
stable braid is a genuine invertible linear operator on the common carrier. -/
def bInfinityOperatorRepresentation :
    BInfinity →* (Cl11CommonFockCarrier.Operator)ˣ :=
  (Units.map Cl11CommonFockCarrier.limitRepresentation).comp
    bInfinityTensorRepresentation

/-- A stable Artin generator acts by left multiplication with the concrete
Jordan--Wigner Majorana gate `1 + γᵢγᵢ₊₁`. -/
theorem bInfinityOperatorRepresentation_sigma (i : ℕ) :
    ((bInfinityOperatorRepresentation (sigmaInfinity i) :
        (Cl11CommonFockCarrier.Operator)ˣ) :
      Cl11CommonFockCarrier.Operator) =
      LinearMap.mulLeft ℝ
        (1 + majoranaMode i * majoranaMode (i + 1)) := by
  change Cl11CommonFockCarrier.limitRepresentation
      ((bInfinityTensorRepresentation (sigmaInfinity i) :
        InfoGeometry.Clifford.Cl11TensorTowerLimit.Limitˣ) :
        InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) = _
  rw [bInfinityTensorRepresentation_sigma_val]
  rfl

/-- The operator-valued infinite braid generators retain the adjacent Artin
relation. -/
theorem bInfinityOperator_artin (i : ℕ) :
    bInfinityOperatorRepresentation (sigmaInfinity i) *
        bInfinityOperatorRepresentation (sigmaInfinity (i + 1)) *
        bInfinityOperatorRepresentation (sigmaInfinity i) =
      bInfinityOperatorRepresentation (sigmaInfinity (i + 1)) *
        bInfinityOperatorRepresentation (sigmaInfinity i) *
        bInfinityOperatorRepresentation (sigmaInfinity (i + 1)) := by
  exact congrArg bInfinityOperatorRepresentation (sigmaInfinity_artin i)

/-- Distant operator-valued infinite braid generators commute. -/
theorem bInfinityOperator_commute {i j : ℕ} (hij : i + 1 < j) :
    bInfinityOperatorRepresentation (sigmaInfinity i) *
        bInfinityOperatorRepresentation (sigmaInfinity j) =
      bInfinityOperatorRepresentation (sigmaInfinity j) *
        bInfinityOperatorRepresentation (sigmaInfinity i) := by
  exact congrArg bInfinityOperatorRepresentation (sigmaInfinity_commute hij)

/-! ## Heisenberg colimit -> represented current -> Sugawara -> Virasoro -/

section HeisenbergSugawara

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The canonical finite-mode Heisenberg colimit representative is sent to the
native current generator. -/
theorem heisenberg_colimit_current_readout (m : ℤ) :
    heisenbergFiniteModeColimitEquiv
        (heisenbergColimitMode (𝕜 := 𝕜) m) =
      HeisenbergAlgebra.jgen 𝕜 m := by
  exact heisenbergFiniteModeColimitEquiv_mode (𝕜 := 𝕜) m

/-- The same categorical current mode is represented on charged Fock by the
existing current representation. -/
theorem heisenberg_colimit_chargedFock_readout (α : 𝕜) (m : ℤ) :
    colimitCurrentMode (𝕜 := 𝕜) α m =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m := by
  exact colimitCurrentMode_eq_chargedFock (𝕜 := 𝕜) α m

/-- Sugawara acts on the represented colimit current by the exact mode shift. -/
theorem sugawara_on_heisenberg_colimit
    (α : 𝕜) (n m : ℤ) :
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode n).commutator
        ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J m) =
      (-m : 𝕜) • (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J (n + m) := by
  exact sugawara_colimit_mode_shift (𝕜 := 𝕜) α n m

/-- The actual Virasoro generator obtained from the Sugawara representation
acts on the same current colimit by the same shift. -/
theorem virasoro_on_heisenberg_colimit
    (α : 𝕜) (n m : ℤ) :
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 n)).commutator
        ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J m) =
      (-m : 𝕜) • (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J (n + m) := by
  exact virasoro_lgen_colimit_mode_shift (𝕜 := 𝕜) α n m

/-- The constructive completed-current source lands on exactly the same
charged-Fock current `J_m`; this is the fermion/current side of the corridor. -/
theorem completedCurrent_to_same_heisenberg_current
    (α : 𝕜) (m : ℤ) :
    representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m := by
  exact representedCompletedCurrentMode_eq_chargedFockJ (𝕜 := 𝕜) α m

end HeisenbergSugawara

/-! ## Affine Kac--Moody finite-mode categorical lane -/

section AffineKacMoody

universe u
variable {𝕜 : Type u} [Field 𝕜] [CharZero 𝕜]
variable {𝓰 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
variable (Φ : LinearMap.BilinForm 𝕜 𝓰)
variable (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)

/-- An affine current generator is represented at a finite mode cutoff and the
categorical comparison map recovers it exactly. -/
theorem affine_current_colimit_readout (n : ℤ) (x : 𝓰) :
    (affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCurrentColimitMode Φ hΦ hΦs n x) =
      affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n x := by
  exact affineFiniteModeColimitMap_current Φ hΦ hΦs n x

/-- The bracket readout of two categorical affine-current representatives is
exactly the Kac--Moody loop bracket plus residue central cocycle. -/
theorem affine_current_colimit_kacMoody_bracket
    (m n : ℤ) (x y : 𝓰) :
    ⁅(affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCurrentColimitMode Φ hΦ hΦs m x),
      (affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCurrentColimitMode Φ hΦ hΦs n y)⁆ =
      affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs
          (m + n) (⁅x, y⁆ : 𝓰)
        + (if m + n = 0
            then ((m : 𝕜) * Φ x y) •
              affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs
            else 0) := by
  exact affineCurrentColimit_bracket_readout Φ hΦ hΦs m n x y

end AffineKacMoody

/-!
The resulting formal architecture is therefore:

`finite Artin B_n -> GrpCat colim B∞ -> Units(Cl11∞) -> End(Cl11∞)`

and independently, from the fermionic/current source,

`finite current stages -> ModuleCat colim Heis -> J_m -> Sugawara -> Vir`,

with the nonabelian current analogue

`finite affine-current stages -> ModuleCat colim -> affine Kac--Moody`.

The next genuinely new theorem, if a single coupled representation is desired,
is an intertwiner from the algebraic `Cl11∞` Jordan--Wigner carrier to the
charged-Fock current representation.  No such intertwiner is assumed here.
-/

end InfoGeometry.Canonical.ArtinBraidCurrentAlgebraColimitBridge
