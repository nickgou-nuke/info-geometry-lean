import InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
import InfoGeometry.Clifford.Cl55ExteriorSpinorCoordinateReadout
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge

/-!
# The finite `Cl(5,5)` spinor inside the Cantor `L²` representation

The exterior-spinor coordinate readout has 32 real coordinates.  At depth
five, the Cantor Cuntz word vectors give 32 vectors in the actual Bernoulli
`L²` space.  This file constructs the coordinate map between those carriers
and proves it injective.  It makes no claim that the chosen `Fin 32`
enumeration agrees with a particular occupation-number bit ordering.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55CantorL2VectorIntertwiner

open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge

/-- A depth-five Cuntz word, indexed by the finite Boolean addresses used by
the existing finite matrix-unit owner. -/
abbrev Address := InfoGeometry.Canonical.UHFInductiveColimitBoundary.BitWord 5

/-- The chosen finite coordinate reindexing from the spinor readout to the
depth-five Cantor addresses. -/
noncomputable def spinorAddressEquiv : Fin 32 ≃ Address :=
  (Fintype.equivFinOfCardEq (by simp [Address])).symm

/-- The Cantor `L²` vector associated with a finite address. -/
def addressVector (w : Address) : L2Boundary :=
  operatorWord (List.ofFn w) vacuumL2

theorem operatorWordDag_addressVector (u v : Address) :
    operatorWordDag (List.ofFn u) (addressVector v) =
      if u = v then vacuumL2 else 0 := by
  by_cases huv : u = v
  · subst v
    rw [if_pos rfl]
    exact ContinuousLinearMap.ext_iff.mp
      (operatorWordDag_comp_operatorWord (List.ofFn u)) vacuumL2
  · have hne : List.ofFn u ≠ List.ofFn v := by
      intro h
      exact huv (List.ofFn_injective h)
    have hzero := operatorWordDag_comp_operatorWord_of_length_eq
      (by simp : (List.ofFn u).length = (List.ofFn v).length) hne
    have hzero' := ContinuousLinearMap.ext_iff.mp hzero vacuumL2
    simpa [addressVector, huv] using hzero'

/-- A finite coordinate vector is sent to its linear combination of the
depth-five Cantor cylinder vectors. -/
def addressCoordinatesToL2 : (Address → ℂ) →ₗ[ℂ] L2Boundary where
  toFun c := ∑ w : Address, c w • addressVector w
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    change (∑ w : Address, (a • c w) • addressVector w) =
      a • ∑ w : Address, c w • addressVector w
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    rw [smul_smul, smul_eq_mul]

theorem operatorWordDag_addressCoordinatesToL2 (c : Address → ℂ) (u : Address) :
    operatorWordDag (List.ofFn u) (addressCoordinatesToL2 c) =
      c u • vacuumL2 := by
  classical
  change operatorWordDag (List.ofFn u)
    (∑ w : Address, c w • addressVector w) = c u • vacuumL2
  simp_rw [map_sum, map_smul, operatorWordDag_addressVector]
  rw [Finset.sum_eq_single u]
  · simp
  · intro v hv hne
    have huv : u ≠ v := fun h => hne h.symm
    simp [huv]
  · simp

theorem addressCoordinatesToL2_injective :
    Function.Injective addressCoordinatesToL2 := by
  intro c d h
  funext u
  have hu := congrArg (operatorWordDag (List.ofFn u)) h
  rw [operatorWordDag_addressCoordinatesToL2,
    operatorWordDag_addressCoordinatesToL2] at hu
  have hsmul : (c u - d u) • vacuumL2 = 0 := by
    rw [sub_smul, hu, sub_self]
  rcases smul_eq_zero.mp hsmul with hcd | hvac
  · exact sub_eq_zero.mp hcd
  · have hnorm : inner ℂ vacuumL2 vacuumL2 = 0 := by
      rw [hvac]
      simp
    rw [vacuumL2_inner_self] at hnorm
    exact (one_ne_zero hnorm).elim

/-- Reindex the real spinor coordinates by finite binary addresses. -/
def reindexRealSpinorCoordinates : (Fin 32 → ℝ) ≃ₗ[ℝ] (Address → ℝ) where
  toFun f w := f (spinorAddressEquiv.symm w)
  invFun f i := f (spinorAddressEquiv i)
  left_inv f := by
    funext i
    simp
  right_inv f := by
    funext w
    simp
  map_add' f g := by
    funext w
    simp
  map_smul' r f := by
    funext w
    simp

/-- Regard real coordinate functions as complex-valued functions, linearly
over `ℝ`. -/
def complexifyAddressCoordinates : (Address → ℝ) →ₗ[ℝ] (Address → ℂ) where
  toFun f w := f w
  map_add' f g := by
    funext w
    simp
  map_smul' r f := by
    funext w
    simp [Algebra.smul_def]

theorem complexifyAddressCoordinates_injective :
    Function.Injective complexifyAddressCoordinates := by
  intro f g h
  funext w
  exact Complex.ofReal_injective (congrFun h w)

/-- The real exterior spinor is read in its established 32-coordinate basis,
reindexed by depth-five binary addresses, then sent to the corresponding
Cantor cylinder vectors. -/
def exterior55ToCantorL2 : Exterior55 →ₗ[ℝ] L2Boundary :=
  (addressCoordinatesToL2.restrictScalars ℝ).comp
    (complexifyAddressCoordinates.comp
      (reindexRealSpinorCoordinates.comp spinorCoordinateEquiv.toLinearMap))

theorem exterior55ToCantorL2_injective :
    Function.Injective exterior55ToCantorL2 := by
  exact addressCoordinatesToL2_injective.comp
    (complexifyAddressCoordinates_injective.comp
      (reindexRealSpinorCoordinates.injective.comp
        spinorCoordinateEquiv.injective))

/-- The positive Grassmannian blade has a concrete vector image in the
depth-five Cantor `L²` carrier. -/
def positiveGrassmannianBladeToCantorL2
    (C : Matrix (Fin 2) (Fin 4) ℝ) : L2Boundary :=
  exterior55ToCantorL2 (positiveGrassmannianBlade C)

theorem positiveGrassmannianBladeToCantorL2_eq_coordinates
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    positiveGrassmannianBladeToCantorL2 C =
      addressCoordinatesToL2 (fun w =>
        (spinorCoordinateEquiv (positiveGrassmannianBlade C)
          (spinorAddressEquiv.symm w) : ℂ)) := rfl

theorem positiveGrassmannianBladeToCantorL2_injective_on_blades
    {C D : Matrix (Fin 2) (Fin 4) ℝ}
    (h : positiveGrassmannianBladeToCantorL2 C =
      positiveGrassmannianBladeToCantorL2 D) :
    positiveGrassmannianBlade C = positiveGrassmannianBlade D :=
  exterior55ToCantorL2_injective h

end InfoGeometry.Clifford.Cl55CantorL2VectorIntertwiner
