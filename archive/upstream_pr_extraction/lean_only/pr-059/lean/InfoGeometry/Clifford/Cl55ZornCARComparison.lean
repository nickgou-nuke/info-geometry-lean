import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
import InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable

/-!
# Relation-level comparison of the circular Zorn channels with Fock CAR

The Zorn carrier is nonassociative, so this file deliberately compares only
the verified generator relations.  It does not construct an algebra
homomorphism from the Zorn carrier into the endomorphism algebra.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55ZornCARComparison

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
open InfoGeometry.Canonical
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

abbrev V5 := InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5
abbrev SpinorEnd := InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.SpinorEnd

def firstThreeIndex (i : Fin 3) : Fin 5 := i.castLE (by omega)

def fockCreation (i : Fin 3) : SpinorEnd :=
  wedge (basisVector (firstThreeIndex i))

def fockAnnihilation (i : Fin 3) : SpinorEnd :=
  contract (dualBasisVector (firstThreeIndex i))

theorem basisVector_ne_zero (i : Fin 5) : basisVector i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [basisVector] at hi

theorem fockCreation_vacuum_ne_zero (i : Fin 3) :
    fockCreation i (1 : Spinor) ≠ 0 := by
  have hι : ExteriorAlgebra.ι ℝ (basisVector (firstThreeIndex i)) ≠ 0 :=
    (ExteriorAlgebra.ι_eq_zero_iff _).not.mpr
      (basisVector_ne_zero (firstThreeIndex i))
  simpa [fockCreation, wedge] using hι

theorem fockAnnihilation_vacuum (i : Fin 3) :
    fockAnnihilation i (1 : Spinor) = 0 := by
  change CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm ℝ V5))
      (dualBasisVector (firstThreeIndex i)) (1 : Spinor) = 0
  exact CliffordAlgebra.contractLeft_one
    (Q := (0 : QuadraticForm ℝ V5))
    (d := dualBasisVector (firstThreeIndex i))

theorem fock_channel_sum_vacuum_eq_creation (i : Fin 3) :
    (fockCreation i + fockAnnihilation i) (1 : Spinor) =
      fockCreation i (1 : Spinor) := by
  change fockCreation i (1 : Spinor) + fockAnnihilation i (1 : Spinor) = _
  rw [fockAnnihilation_vacuum, add_zero]

theorem fock_channel_difference_vacuum_eq_creation (i : Fin 3) :
    (fockCreation i - fockAnnihilation i) (1 : Spinor) =
      fockCreation i (1 : Spinor) := by
  change fockCreation i (1 : Spinor) - fockAnnihilation i (1 : Spinor) = _
  rw [fockAnnihilation_vacuum, sub_zero]

theorem fock_channel_sum_vacuum_ne_zero (i : Fin 3) :
    (fockCreation i + fockAnnihilation i) (1 : Spinor) ≠ 0 := by
  rw [fock_channel_sum_vacuum_eq_creation]
  exact fockCreation_vacuum_ne_zero i

theorem fock_channel_difference_vacuum_ne_zero (i : Fin 3) :
    (fockCreation i - fockAnnihilation i) (1 : Spinor) ≠ 0 := by
  rw [fock_channel_difference_vacuum_eq_creation]
  exact fockCreation_vacuum_ne_zero i

theorem dual_channel_mem_vacuum_neutralAnnihilator (i : Fin 3) :
    (0, dualBasisVector (firstThreeIndex i)) ∈
      neutralAnnihilator (1 : Spinor) := by
  exact dual_mem_vacuum_neutralAnnihilator _

theorem dual_channel_pairing_zero (i j : Fin 3) :
    neutralPairing
        (0, dualBasisVector (firstThreeIndex i))
        (0, dualBasisVector (firstThreeIndex j)) = 0 := by
  exact neutralAnnihilator_totallyNull one_ne_zero _
    (dual_channel_mem_vacuum_neutralAnnihilator i) _
    (dual_channel_mem_vacuum_neutralAnnihilator j)

theorem fock_channel_sum_eq_neutralAction (i : Fin 3) :
    fockCreation i + fockAnnihilation i =
      neutralAction (basisVector (firstThreeIndex i),
        dualBasisVector (firstThreeIndex i)) := by
  rfl

theorem fock_channel_difference_eq_neutralAction (i : Fin 3) :
    fockCreation i - fockAnnihilation i =
      neutralAction (basisVector (firstThreeIndex i),
        -dualBasisVector (firstThreeIndex i)) := by
  change wedge (basisVector (firstThreeIndex i)) -
      contract (dualBasisVector (firstThreeIndex i)) =
    wedge (basisVector (firstThreeIndex i)) +
      contract (-dualBasisVector (firstThreeIndex i))
  have hcontract :
      contract (-dualBasisVector (firstThreeIndex i)) =
        -contract (dualBasisVector (firstThreeIndex i)) := by
    apply LinearMap.ext
    intro ξ
    change CliffordAlgebra.contractLeft
        (Q := (0 : QuadraticForm ℝ V5))
        (-dualBasisVector (firstThreeIndex i)) ξ =
      -CliffordAlgebra.contractLeft
        (Q := (0 : QuadraticForm ℝ V5))
        (dualBasisVector (firstThreeIndex i)) ξ
    rw [show -dualBasisVector (firstThreeIndex i) =
        (-1 : ℝ) • dualBasisVector (firstThreeIndex i) by
          exact (neg_one_smul ℝ (dualBasisVector (firstThreeIndex i))).symm]
    rw [map_smul]
    simp
  rw [hcontract]
  abel

theorem fock_channel_sum_sq (i : Fin 3) :
    (fockCreation i + fockAnnihilation i) *
        (fockCreation i + fockAnnihilation i) =
      (1 : ℝ) • (1 : SpinorEnd) := by
  rw [fock_channel_sum_eq_neutralAction]
  exact neutralAction_basisVector_sq (firstThreeIndex i)

theorem fock_channel_difference_sq (i : Fin 3) :
    (fockCreation i - fockAnnihilation i) *
        (fockCreation i - fockAnnihilation i) =
      (-1 : ℝ) • (1 : SpinorEnd) := by
  rw [fock_channel_difference_eq_neutralAction]
  exact neutralAction_basisVector_opposite_sq (firstThreeIndex i)

theorem firstThreeIndex_injective :
    Function.Injective firstThreeIndex := by
  intro i j h
  apply Fin.ext
  simpa [firstThreeIndex] using congrArg Fin.val h

theorem dual_channel_injective :
    Function.Injective (fun i : Fin 3 =>
      ((0, dualBasisVector (firstThreeIndex i)) : NeutralSpace)) := by
  intro i j h
  have hdual := congrArg Prod.snd h
  have hvalue := congrArg (fun φ : Module.Dual ℝ V5 =>
      φ (basisVector (firstThreeIndex i))) hdual
  have hidx : firstThreeIndex j = firstThreeIndex i := by
    simpa [dualBasisVector_apply] using hvalue
  exact firstThreeIndex_injective hidx.symm

theorem fockCreationAnnihilation_anticommutator (i j : Fin 3) :
    fockAnnihilation i * fockCreation j +
        fockCreation j * fockAnnihilation i =
      (if i = j then (1 : ℝ) else 0) • (1 : SpinorEnd) := by
  change contract (dualBasisVector (firstThreeIndex i)) *
      wedge (basisVector (firstThreeIndex j)) +
      wedge (basisVector (firstThreeIndex j)) *
        contract (dualBasisVector (firstThreeIndex i)) = _
  rw [contract_wedge_add_wedge_contract]
  by_cases h : i = j
  · subst j
    simp [firstThreeIndex]
  · have h' : firstThreeIndex i ≠ firstThreeIndex j := by
      intro hij
      exact h (firstThreeIndex_injective hij)
    simp [dualBasisVector_apply, h, h']

theorem fockCreation_anticommutator (i j : Fin 3) :
    fockCreation i * fockCreation j +
        fockCreation j * fockCreation i = 0 := by
  change wedge (basisVector (firstThreeIndex i)) *
      wedge (basisVector (firstThreeIndex j)) +
      wedge (basisVector (firstThreeIndex j)) *
        wedge (basisVector (firstThreeIndex i)) = 0
  exact wedge_add_swap _ _

theorem fockAnnihilation_anticommutator (i j : Fin 3) :
    fockAnnihilation i * fockAnnihilation j +
        fockAnnihilation j * fockAnnihilation i = 0 := by
  change contract (dualBasisVector (firstThreeIndex i)) *
      contract (dualBasisVector (firstThreeIndex j)) +
      contract (dualBasisVector (firstThreeIndex j)) *
        contract (dualBasisVector (firstThreeIndex i)) = 0
  exact contract_add_swap _ _

theorem fockCreation_sq (i : Fin 3) :
    fockCreation i * fockCreation i = 0 := by
  change wedge (basisVector (firstThreeIndex i)) *
      wedge (basisVector (firstThreeIndex i)) = 0
  exact wedge_sq _

theorem fockAnnihilation_sq (i : Fin 3) :
    fockAnnihilation i * fockAnnihilation i = 0 := by
  change contract (dualBasisVector (firstThreeIndex i)) *
      contract (dualBasisVector (firstThreeIndex i)) = 0
  exact contract_sq _

theorem circularZorn_and_fock_nilpotence (i : Fin 3) :
    (cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootPlus i) = 0) ∧
    (cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootMinus i) = 0) ∧
    fockCreation i * fockCreation i = 0 ∧
    fockAnnihilation i * fockAnnihilation i = 0 := by
  exact ⟨cartesianZorn_rootPlus_sq i,
    cartesianZorn_rootMinus_sq i,
    fockCreation_sq i,
    fockAnnihilation_sq i⟩

theorem circularZorn_and_fock_same_polarity_CAR (i j : Fin 3) :
    (cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootPlus j) +
      cartesianZornLinearEquiv (rootPlus j) *
        cartesianZornLinearEquiv (rootPlus i) = 0) ∧
    (cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootMinus j) +
      cartesianZornLinearEquiv (rootMinus j) *
        cartesianZornLinearEquiv (rootMinus i) = 0) ∧
    fockCreation i * fockCreation j +
        fockCreation j * fockCreation i = 0 ∧
    fockAnnihilation i * fockAnnihilation j +
        fockAnnihilation j * fockAnnihilation i = 0 := by
  exact ⟨cartesianZorn_rootPlus_same_channel_anticommutator i j,
    cartesianZorn_rootMinus_same_channel_anticommutator i j,
    fockCreation_anticommutator i j,
    fockAnnihilation_anticommutator i j⟩

theorem circularZorn_and_fock_CAR (i j : Fin 3) :
    (cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootMinus j) +
      cartesianZornLinearEquiv (rootMinus j) *
        cartesianZornLinearEquiv (rootPlus i) =
      (if i = j then (1 : ℝ) else 0) •
        (1 : InfoGeometry.Canonical.ZornMatrix ℝ)) ∧
    fockAnnihilation i * fockCreation j +
        fockCreation j * fockAnnihilation i =
      (if i = j then (1 : ℝ) else 0) • (1 : SpinorEnd) := by
  constructor
  · exact cartesianZorn_rootPlus_rootMinus_anticommutator_delta i j
  · exact fockCreationAnnihilation_anticommutator i j

end InfoGeometry.Clifford.SplitClifford55ZornCARComparison
