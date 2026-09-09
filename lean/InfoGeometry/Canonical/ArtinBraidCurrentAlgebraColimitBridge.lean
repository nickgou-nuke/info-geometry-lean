import InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
import InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
import InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
import InfoGeometry.Canonical.ArtinBraidFilteredColimit
import InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation
import InfoGeometry.Canonical.Cl11CommonFockCarrier
import InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence
import InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit

/-!
# Canonical current-colimit corridor

The upstream aggregate referred to two absent owners for a braid and affine
lane.  This aligned owner records the representation edge that is actually
present locally: a locally-finite completed current is sent to the same
charged-Fock Heisenberg mode used by the colimit and Sugawara owners.
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

theorem completedCurrent_mode_chargedFock_readout
    (α : 𝕜) (m : ℤ) :
    representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m :=
  representedCompletedCurrentMode_point (𝕜 := 𝕜) α m

theorem completedCurrent_mode_virasoro_shift
    (α : 𝕜) (r m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 r)).commutator
      (representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint m)) =
      -m • representedCompletedCurrentMode (𝕜 := 𝕜) α
        (completedCurrentPoint (r + m)) :=
  virasoro_lgen_acts_on_completedCurrent (𝕜 := 𝕜) α r m

def bInfinityOperatorRepresentation :
    BInfinity →* (Cl11CommonFockCarrier.Operator)ˣ :=
  (Units.map Cl11CommonFockCarrier.limitRepresentation).comp
    bInfinityTensorRepresentation

/-- The infinite braid generator is represented by the canonical left-regular
Majorana unit on the algebraic tensor-tower colimit.  This is the concrete
generator readout of `bInfinityOperatorRepresentation`; it does not identify
the algebraic colimit with the analytic charged-Fock carrier. -/
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

theorem bInfinityOperator_artin (i : ℕ) :
    bInfinityOperatorRepresentation (sigmaInfinity i) *
        bInfinityOperatorRepresentation (sigmaInfinity (i + 1)) *
        bInfinityOperatorRepresentation (sigmaInfinity i) =
      bInfinityOperatorRepresentation (sigmaInfinity (i + 1)) *
        bInfinityOperatorRepresentation (sigmaInfinity i) *
        bInfinityOperatorRepresentation (sigmaInfinity (i + 1)) := by
  simpa only [map_mul] using
    congrArg bInfinityOperatorRepresentation (sigmaInfinity_artin i)

theorem bInfinityOperator_commute {i j : ℕ} (hij : i + 1 < j) :
    bInfinityOperatorRepresentation (sigmaInfinity i) *
        bInfinityOperatorRepresentation (sigmaInfinity j) =
      bInfinityOperatorRepresentation (sigmaInfinity j) *
        bInfinityOperatorRepresentation (sigmaInfinity i) := by
  simpa only [map_mul] using
    congrArg bInfinityOperatorRepresentation (sigmaInfinity_commute hij)

/-! ### Transport to the fermionic Fock-operator limit

The algebraic tensor-colimit representation above has a canonical algebra
equivalence to the fermionic Fock-operator limit.  Transporting units through
that equivalence gives the corresponding representation on the Fock-operator
carrier, without identifying it with the charged Heisenberg Fock module.
-/

def bInfinityFermionicFockOperatorValue (b : BInfinity) :
    InfoGeometry.Canonical.JordanWignerCantorRepresentation.RealCantorOpInf :=
  clLimitFockOpAlgEquiv (bInfinityTensorRepresentation b : Limit)

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

/- The direct-limit carrier is non-unital, so its canonical action is a
non-unital `MulHom`, not a map into units. -/
def bInfinityFermionicFockOperatorMulHom :
    BInfinity →ₙ*
      InfoGeometry.Canonical.JordanWignerCantorRepresentation.RealCantorOpInf where
  toFun := bInfinityFermionicFockOperatorValue
  map_mul' := bInfinityFermionicFockOperatorValue_mul

theorem bInfinityFermionicFockOperatorValue_roundtrip (b : BInfinity) :
    clLimitFockOpAlgEquiv.symm
        (bInfinityFermionicFockOperatorValue b) =
      (bInfinityTensorRepresentation b : Limit) := by
  exact clLimitFockOpAlgEquiv.symm_apply_apply
    (bInfinityTensorRepresentation b : Limit)

theorem bInfinityFermionicFockOperatorMulHom_roundtrip (b : BInfinity) :
    clLimitFockOpAlgEquiv.symm
        (bInfinityFermionicFockOperatorMulHom b) =
      (bInfinityTensorRepresentation b : Limit) := by
  change clLimitFockOpAlgEquiv.symm
      (bInfinityFermionicFockOperatorValue b) = _
  exact bInfinityFermionicFockOperatorValue_roundtrip b

@[simp] theorem bInfinityFermionicFockOperatorValue_sigma (i : ℕ) :
    bInfinityFermionicFockOperatorValue (sigmaInfinity i) =
      clLimitFockOpAlgEquiv (1 + majoranaMode i * majoranaMode (i + 1)) := by
  unfold bInfinityFermionicFockOperatorValue
  rw [bInfinityTensorRepresentation_sigma]
  rfl

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

theorem bInfinityFermionicFockOperatorValue_commute {i j : ℕ} (hij : i + 1 < j) :
    bInfinityFermionicFockOperatorValue (sigmaInfinity i) *
        bInfinityFermionicFockOperatorValue (sigmaInfinity j) =
      bInfinityFermionicFockOperatorValue (sigmaInfinity j) *
        bInfinityFermionicFockOperatorValue (sigmaInfinity i) := by
  have h := congrArg bInfinityTensorRepresentation (sigmaInfinity_commute hij)
  have h' := congrArg (fun x : Limitˣ => (x : Limit)) h
  have h'' := congrArg (fun x : Limit => clLimitFockOpAlgEquiv x) h'
  simpa [bInfinityFermionicFockOperatorValue, map_mul] using h''

@[simp] theorem bInfinityFermionicFockOperatorMulHom_sigma (i : ℕ) :
    bInfinityFermionicFockOperatorMulHom (sigmaInfinity i) =
      clLimitFockOpAlgEquiv (1 + majoranaMode i * majoranaMode (i + 1)) := by
  exact bInfinityFermionicFockOperatorValue_sigma i

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

theorem heisenberg_colimit_current_readout (m : ℤ) :
    heisenbergFiniteModeColimitEquiv
        (heisenbergColimitMode (𝕜 := 𝕜) m) =
      HeisenbergAlgebra.jgen 𝕜 m :=
  heisenbergFiniteModeColimitEquiv_mode (𝕜 := 𝕜) m

theorem completedCurrent_to_same_heisenberg_current
    (α : 𝕜) (m : ℤ) :
    representedCompletedCurrentMode (𝕜 := 𝕜) α (completedCurrentPoint m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m :=
  representedCompletedCurrentMode_eq_chargedFockJ (𝕜 := 𝕜) α m

section Affine
universe u
variable {𝕜a : Type u} [Field 𝕜a] [CharZero 𝕜a] [IsAddTorsionFree 𝕜a]
variable {𝓰 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜a 𝓰]
variable (Φ : LinearMap.BilinForm 𝕜a 𝓰)
variable (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)

theorem affine_current_colimit_readout (n : ℤ) (x : 𝓰) :
    (affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCurrentColimitMode Φ hΦ hΦs n x) =
      VirasoroProject.affineCurrentGen (𝕜 := 𝕜a) (𝓰 := 𝓰) Φ hΦ hΦs n x :=
  affineFiniteModeColimitMap_current Φ hΦ hΦs n x

theorem affine_current_colimit_kacMoody_bracket
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
  exact affineCurrentColimit_bracket_readout Φ hΦ hΦs m n x y

end Affine

end InfoGeometry.Canonical.ArtinBraidCurrentAlgebraColimitBridge
