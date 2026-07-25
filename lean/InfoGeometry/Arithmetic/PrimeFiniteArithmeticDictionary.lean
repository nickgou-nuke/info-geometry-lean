import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Arithmetic.PrimeMajoranaCAR
import InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite
import InfoGeometry.Arithmetic.PrimeExteriorRepresentation

/-!
# InfoGeometry.Arithmetic.PrimeFiniteArithmeticDictionary

Native finite dictionary for the prime-indexed Cantor/Fock arithmetic lane.

This module proves only bridge/preservation facts between already-owned finite
surfaces:

* Boolean cube chirality / Möbius readout:
  owned by `PrimeBooleanCube`.
* Local split-Majorana/CAR parity:
  owned by `PrimeMajoranaCAR`.
* Finite sqrt(log p) Dirac Hamiltonian:
  owned by `PrimeMajoranaDiracFinite`.
* Finite exterior square-free readout:
  owned by `PrimeExteriorRepresentation`.

No infinite Euler product.
No analytic continuation.
No Lee--Yang/RH claim.
No Pfaffian alias counted as closure.
-/

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.PrimeFiniteArithmeticDictionary

open InfoGeometry.Arithmetic.PrimeBitWittenIndex (PrimeRegister)
open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Arithmetic.PrimeMajoranaCAR (ExteriorCARPair)
open InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite

/-! ## 1. CAR parity readout preserves Boolean local parity -/

/--
If a ring-valued CAR representation has number-operator readout equal to
Boolean occupation, then its local CAR parity readout is the Boolean local
parity `1 - 2N_p`.

This is the local bridge:

`Π = c*d = 1 - 2N`.
-/
@[bridge_target_tag, rep_depth thermo]
theorem carParity_readout_eq_booleanLocalParity
    {Op : Type*} [Ring Op]
    (E : ExteriorCARPair Op)
    (χ : Op →+* ℤ)
    (p : ℕ)
    (S : Finset ℕ)
    (hN : χ E.numberOp = occupationInt p S) :
    χ E.parityOp = localParity p S := by
  have hpar' : χ E.parityOp = 1 - 2 * χ E.numberOp := by
    rw [E.parityOp_eq_one_sub_two_numberOp]
    rw [map_sub, map_one, map_mul]
    have h2 : χ (2 : Op) = (2 : ℤ) := by
      exact map_natCast χ 2
    rw [h2]
  by_cases hp : p ∈ S
  · have hOcc : χ E.numberOp = 1 := by
      simpa [occupationInt, hp] using hN
    rw [localParity_eq_neg_one_of_mem hp]
    rw [hpar', hOcc]
    norm_num
  · have hOcc : χ E.numberOp = 0 := by
      simpa [occupationInt, hp] using hN
    rw [localParity_eq_one_of_not_mem hp]
    rw [hpar', hOcc]
    norm_num

/-- Occupied local mode: CAR parity readout is `-1`. -/
@[bridge_target_tag, rep_depth thermo]
theorem carParity_readout_eq_neg_one_of_mem
    {Op : Type*} [Ring Op]
    (E : ExteriorCARPair Op)
    (χ : Op →+* ℤ)
    {p : ℕ}
    {S : Finset ℕ}
    (hp : p ∈ S)
    (hN : χ E.numberOp = occupationInt p S) :
    χ E.parityOp = -1 := by
  rw [carParity_readout_eq_booleanLocalParity E χ p S hN]
  exact localParity_eq_neg_one_of_mem hp

/-- Vacant local mode: CAR parity readout is `+1`. -/
@[bridge_target_tag, rep_depth thermo]
theorem carParity_readout_eq_one_of_not_mem
    {Op : Type*} [Ring Op]
    (E : ExteriorCARPair Op)
    (χ : Op →+* ℤ)
    {p : ℕ}
    {S : Finset ℕ}
    (hp : p ∉ S)
    (hN : χ E.numberOp = occupationInt p S) :
    χ E.parityOp = 1 := by
  rw [carParity_readout_eq_booleanLocalParity E χ p S hN]
  exact localParity_eq_one_of_not_mem hp


/-! ## 2. Global CAR readout preserves Boolean chirality and Möbius -/

/-- Global CAR parity readout over a certified finite prime register. -/
@[rep_depth thermo]
def carGlobalChiralityReadout
    {Op : Type*} [Ring Op]
    (P : PrimeRegister)
    (E : ℕ → ExteriorCARPair Op)
    (χ : Op →+* ℤ) : ℤ :=
  ∏ p ∈ P.primes, χ ((E p).parityOp)

/--
If every local CAR number operator reads out as Boolean occupation, then the
global CAR parity readout is exactly Boolean global chirality.
-/
@[bridge_target_tag, rep_depth thermo]
theorem carGlobalChiralityReadout_eq_booleanChirality
    {Op : Type*} [Ring Op]
    (P : PrimeRegister)
    (v : Vertex P)
    (E : ℕ → ExteriorCARPair Op)
    (χ : Op →+* ℤ)
    (hN :
      ∀ p ∈ P.primes,
        χ ((E p).numberOp) = occupationInt p v.val) :
    carGlobalChiralityReadout P E χ =
      globalChirality P v.val := by
  unfold carGlobalChiralityReadout globalChirality
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact carParity_readout_eq_booleanLocalParity
    (E p) χ p v.val (hN p hp)

/-- The global CAR readout equals finite Boolean fermion parity. -/
@[bridge_target_tag, rep_depth thermo]
theorem carGlobalChiralityReadout_eq_fermionParity
    {Op : Type*} [Ring Op]
    (P : PrimeRegister)
    (v : Vertex P)
    (E : ℕ → ExteriorCARPair Op)
    (χ : Op →+* ℤ)
    (hN :
      ∀ p ∈ P.primes,
        χ ((E p).numberOp) = occupationInt p v.val) :
    carGlobalChiralityReadout P E χ =
      fermionParity v := by
  rw [carGlobalChiralityReadout_eq_booleanChirality P v E χ hN]
  exact globalChirality_vertex_eq_fermionParity P v

/--
The global CAR readout equals the Möbius value of the represented square-free
integer.
-/
@[bridge_target_tag, rep_depth thermo]
theorem carGlobalChiralityReadout_eq_mobius
    {Op : Type*} [Ring Op]
    (P : PrimeRegister)
    (v : Vertex P)
    (E : ℕ → ExteriorCARPair Op)
    (χ : Op →+* ℤ)
    (hN :
      ∀ p ∈ P.primes,
        χ ((E p).numberOp) = occupationInt p v.val) :
    carGlobalChiralityReadout P E χ =
      ArithmeticFunction.moebius (representedNat v) := by
  rw [carGlobalChiralityReadout_eq_booleanChirality P v E χ hN]
  exact (mobius_representedNat_eq_globalChirality P v).symm


/-! ## 3. Finite Dirac Hamiltonian dictionary -/

/--
Finite Dirac-square Hamiltonian agrees with the existing finite prime-bit
energy and with the logarithm of the represented prime-bit integer.
-/
@[bridge_target_tag, rep_depth thermo]
theorem finiteDiracHamiltonian_dictionary
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (ψ : InfoGeometry.Arithmetic.PrimeBitState L) :
    finiteDiracHamiltonian L ψ =
      InfoGeometry.Arithmetic.primeBitEnergy L ψ.support
    ∧
    finiteDiracHamiltonian L ψ =
      Real.log (InfoGeometry.Arithmetic.primeBitInteger L ψ : ℝ) := by
  exact
    ⟨ finiteDiracHamiltonian_eq_primeBitEnergy L ψ,
      finiteDiracHamiltonian_eq_log_primeBitInteger L ψ ⟩


/-! ## 4. Exterior readout dictionary -/

/--
The generic exterior state carries exactly the finite square-free fermion
number, chirality, and energy readout supplied by
`PrimeExteriorRepresentation`.

This is a bridge contract, not a new representation.
-/
@[bridge_target_tag, rep_depth thermo]
theorem exteriorSquareFreeState_dictionary
    {PrimeLabel : Type*}
    [DecidableEq PrimeLabel]
    (energy : PrimeLabel → ℝ)
    (S :
      InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState
        PrimeLabel) :
    InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.Gamma S =
      InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.fermionParitySign S
    ∧
    InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.Gamma S =
      (-1 : ℤ) ^
        InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.fermionNumber S
    ∧
    InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.squareFreeEnergy
        energy S =
      ∑ p ∈ S, energy p := by
  exact
    ⟨ rfl,
      InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.Gamma_eq_negOne_pow_fermionNumber S,
      rfl ⟩

/--
Exterior local parity is the same `1 - 2N_p` law as the local CAR/Boolean
parity readout.
-/
@[bridge_target_tag, rep_depth thermo]
theorem exteriorLocalParity_eq_one_sub_two_localOccupation
    {PrimeLabel : Type*}
    [DecidableEq PrimeLabel]
    (p : PrimeLabel)
    (S :
      InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState
        PrimeLabel) :
    InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.localParitySign p S =
      1 -
        2 *
          (InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.localOccupation
            p S : ℤ) :=
  InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.localParitySign_eq_one_sub_two_localOccupation
    p S

/-- The exterior Gamma readout is the Boolean chirality / fermion parity. -/
@[bridge_target_tag, rep_depth thermo]
theorem exteriorGamma_eq_booleanChirality
    {PrimeLabel : Type*}
    [DecidableEq PrimeLabel]
    (S :
      InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState
        PrimeLabel) :
    InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.Gamma S =
      InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.fermionParitySign S :=
  rfl

/-- The exterior Gamma readout also matches the `(-1)^N` Möbius sign law. -/
@[bridge_target_tag, rep_depth thermo]
theorem exteriorMobius_eq_booleanMöbius
    {PrimeLabel : Type*}
    [DecidableEq PrimeLabel]
    (S :
      InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState
        PrimeLabel) :
    InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.Gamma S =
      (-1 : ℤ) ^
        InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.fermionNumber S :=
  InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.Gamma_eq_negOne_pow_fermionNumber
    S

end InfoGeometry.Arithmetic.PrimeFiniteArithmeticDictionary
