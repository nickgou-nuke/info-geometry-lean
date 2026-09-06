import InfoGeometry.Clifford.Cl55ZornCARComparison

/-!
# Selected three-mode Nambu--Zorn Peirce packet

This file packages the relation-level content of the selected `Fin 3` subsystem.
The Fock/Nambu and circular Zorn carriers are kept separate: no algebra
homomorphism, multiplicative readback, or Clifford/Zorn identification is
introduced here.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55NambuZornPeirceBridge

open InfoGeometry.Clifford.SplitClifford55ZornCARComparison
open InfoGeometry.Canonical
open InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

/-! A relation predicate requiring only the operations used by the finite CAR
packet.  It is intentionally weaker than a ring structure, so it also applies
to the native non-associative Zorn carrier. -/
def ThreeModeCAR {A : Type*} [Zero A] [One A] [Add A] [Mul A]
    (creation annihilation : Fin 3 → A) : Prop :=
  (∀ i, creation i * creation i = 0) ∧
  (∀ i, annihilation i * annihilation i = 0) ∧
  (∀ i j, creation i * creation j + creation j * creation i = 0) ∧
  (∀ i j, annihilation i * annihilation j + annihilation j * annihilation i = 0) ∧
  (∀ i j, annihilation i * creation j + creation j * annihilation i =
    if i = j then (1 : A) else 0)

theorem fock_threeModeCAR :
    ThreeModeCAR fockCreation fockAnnihilation := by
  refine ⟨fockCreation_sq, fockAnnihilation_sq,
    fockCreation_anticommutator, fockAnnihilation_anticommutator, ?_⟩
  intro i j
  simpa using fockCreationAnnihilation_anticommutator i j

theorem zorn_threeModeCAR :
    ThreeModeCAR
      (fun i => cartesianZornLinearEquiv (rootMinus i))
      (fun i => cartesianZornLinearEquiv (rootPlus i)) := by
  refine ⟨cartesianZorn_rootMinus_sq, cartesianZorn_rootPlus_sq,
    cartesianZorn_rootMinus_same_channel_anticommutator,
    cartesianZorn_rootPlus_same_channel_anticommutator, ?_⟩
  intro i j
  simpa using cartesianZorn_rootPlus_rootMinus_anticommutator_delta i j

end InfoGeometry.Clifford.Cl55NambuZornPeirceBridge
