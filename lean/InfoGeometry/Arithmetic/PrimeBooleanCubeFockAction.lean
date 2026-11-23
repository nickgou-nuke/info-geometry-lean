/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Arithmetic.PrimeMajoranaLocalMode
import InfoGeometry.Arithmetic.PrimeMajoranaCAR
import InfoGeometry.Arithmetic.PrimeCARScalarReadoutObstruction
import InfoGeometry.Core.PeirceDecomposition

/-!
# A statewise real Fock action for the finite prime Boolean cube

This owner connects the existing Boolean occupation labels to the actual real
two-state Fock operators. It uses vector eigenvalue equations, not a ring map
from a CAR algebra to `ℤ` (such a unital map is incompatible with CAR).
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeBooleanCubeFockAction

open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Arithmetic.PrimeMajoranaLocalMode
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeMajoranaCAR
open InfoGeometry.Core.PeirceDecomposition

/-- The concrete local real Fock operators form an instance of the generic
exterior CAR structure. -/
def realLocalCARPair : ExteriorCARPair LocalEnd where
  eps := epsilon
  iota := iota
  eps_sq_zero := by
    simpa only [Module.End.mul_eq_comp] using epsilon_sq
  iota_sq_zero := by
    simpa only [Module.End.mul_eq_comp] using iota_sq
  iota_eps_add_eps_iota := by
    simpa only [Module.End.mul_eq_comp] using iota_epsilon_anticomm

/-- The abstract CAR number operator of this concrete representation is the
existing real Fock number projection. -/
theorem realLocalCARPair_numberOp_eq :
    realLocalCARPair.numberOp = PrimeMajoranaLocalMode.numberOp := by
  rfl

/-- The abstract CAR parity operator of this concrete representation is the
existing real Fock parity operator. -/
theorem realLocalCARPair_parityOp_eq :
    realLocalCARPair.parityOp = PrimeMajoranaLocalMode.parityOp := by
  rfl

/-- The local number operator is an idempotent cut in the real endomorphism
algebra. -/
theorem numberOp_idempotent : numberOp * numberOp = numberOp := by
  apply LinearMap.ext
  intro x
  change numberOp (numberOp x) = numberOp x
  rw [numberOp_apply, numberOp_apply]

/-- Creation is the Peirce corner from the unoccupied sector to the occupied
sector for the number projection. -/
theorem epsilon_eq_component10_numberOp :
    epsilon = component10 numberOp epsilon := by
  apply LinearMap.ext
  intro x
  change epsilon x = numberOp (epsilon (x - numberOp x))
  simp [numberOp_apply, epsilon]

/-- Annihilation is the opposite Peirce corner for the same number projection. -/
theorem iota_eq_component01_numberOp :
    iota = component01 numberOp iota := by
  apply LinearMap.ext
  intro x
  change iota x = (1 - numberOp) (iota (numberOp x))
  simp [numberOp_apply, iota]

/-- The number cut acts on creation with commutator weight `+1`. -/
theorem numberOp_commutator_epsilon :
    numberOp * epsilon - epsilon * numberOp = epsilon := by
  apply LinearMap.ext
  intro x
  change numberOp (epsilon x) - epsilon (numberOp x) = epsilon x
  simp [numberOp_apply, epsilon]

/-- The number cut acts on annihilation with the opposite commutator weight. -/
theorem numberOp_commutator_iota :
    numberOp * iota - iota * numberOp = -iota := by
  apply LinearMap.ext
  intro x
  change numberOp (iota x) - iota (numberOp x) = -iota x
  simp [numberOp_apply, iota]

/-- The real one-mode Fock basis vector indexed by Boolean occupation. -/
def primeFockState (p : ℕ) (S : Finset ℕ) : LocalFock :=
  if p ∈ S then occupied else vacuum

/-- The number projection acts on the occupied/vacuum basis by occupation. -/
theorem numberOp_primeFockState (p : ℕ) (S : Finset ℕ) :
    numberOp (primeFockState p S) =
      (occupationInt p S : ℝ) • primeFockState p S := by
  by_cases hp : p ∈ S <;>
    simp [primeFockState, hp, numberOp_apply, occupationInt,
      PrimeMajoranaLocalMode.occupied, vacuum]

/-- The local parity operator acts by the Boolean local parity sign. -/
theorem parityOp_primeFockState (p : ℕ) (S : Finset ℕ) :
    parityOp (primeFockState p S) =
      (localParity p S : ℝ) • primeFockState p S := by
  by_cases hp : p ∈ S <;>
    simp [primeFockState, hp, parityOp_apply, localParity,
      PrimeMajoranaLocalMode.occupied, vacuum]

/-- The real Majorana operator implements the Boolean toggle on the basis. -/
theorem cMajorana_primeFockState (p : ℕ) (S : Finset ℕ) :
    cMajorana (primeFockState p S) =
      primeFockState p (InfoGeometry.Arithmetic.PrimeMajoranaBitFlip.majoranaFlip p S) := by
  by_cases hp : p ∈ S <;>
    simp [primeFockState, hp,
      InfoGeometry.Arithmetic.PrimeMajoranaBitFlip.majoranaFlip,
      cMajorana_occupied, cMajorana_vacuum]

/-- The generic CAR number operator has the Boolean occupation eigenvalue on
the concrete real Fock basis state. -/
theorem realLocalCARPair_numberOp_primeFockState (p : ℕ) (S : Finset ℕ) :
    realLocalCARPair.numberOp (primeFockState p S) =
      (occupationInt p S : ℝ) • primeFockState p S := by
  rw [realLocalCARPair_numberOp_eq]
  exact numberOp_primeFockState p S

/-- The generic CAR parity operator has the Boolean parity eigenvalue on the
concrete real Fock basis state. -/
theorem realLocalCARPair_parityOp_primeFockState (p : ℕ) (S : Finset ℕ) :
    realLocalCARPair.parityOp (primeFockState p S) =
      (localParity p S : ℝ) • primeFockState p S := by
  rw [realLocalCARPair_parityOp_eq]
  exact parityOp_primeFockState p S

/-- The local Fock operator algebra admits no unital multiplicative integer
readout, as required by the CAR relation. -/
theorem no_integer_ring_readout_of_realLocalCARPair :
    ¬ Nonempty (LocalEnd →+* ℤ) := by
  exact
    InfoGeometry.Arithmetic.PrimeCARScalarReadoutObstruction.no_integer_ring_hom_of_exteriorCARPair
      realLocalCARPair

/-- The product of local Fock parity eigenvalues is Boolean global chirality. -/
theorem localFockParity_product_eq_globalChirality
    (P : PrimeRegister) (S : Finset ℕ) :
    (∏ p ∈ P.primes, (localParity p S : ℝ)) =
      (globalChirality P S : ℝ) := by
  simp [globalChirality]

/-- On a certified Boolean vertex, the finite real Fock parity product is
the fermion/Möbius parity already owned by the arithmetic lane. -/
theorem localFockParity_product_eq_fermionParity
    (P : PrimeRegister) (v : Vertex P) :
    (∏ p ∈ P.primes, (localParity p v.val : ℝ)) =
      (fermionParity v : ℝ) := by
  rw [localFockParity_product_eq_globalChirality]
  exact_mod_cast globalChirality_vertex_eq_fermionParity P v

end InfoGeometry.Arithmetic.PrimeBooleanCubeFockAction
