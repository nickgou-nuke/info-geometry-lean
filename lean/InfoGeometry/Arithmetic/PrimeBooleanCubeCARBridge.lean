import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Arithmetic.PrimeMajoranaCAR
import InfoGeometry.Arithmetic.PrimeBooleanCube

/-!
# InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge

Native bridge from the local split-Majorana CAR layer to the canonical
finite Boolean-cube owner.

This file proves that any ring-valued CAR representation whose number operator
readout agrees with Boolean occupation automatically preserves:

* local CAR parity `Π = c*d = 1 - 2N`;
* global Boolean chirality;
* finite Möbius parity readout.

It does not construct a concrete Hilbert/Fock representation.
It does not prove a finite Euler product again.
It does not assert an infinite product, analytic continuation, or RH claim.
-/

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge

open InfoGeometry.Arithmetic.PrimeMajoranaCAR
open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-! ## 1. Local CAR parity preserves Boolean local parity -/

/--
Local CAR-to-Boolean readout.

If a ring homomorphism evaluates the CAR number operator as the Boolean
occupation number, then the CAR parity operator evaluates as Boolean local
parity.

This is the exact bridge:
`Π = c*d = 1 - 2N` maps to `1 - 2 occupation`.
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
  have hpar := congrArg χ E.parityOp_eq_one_sub_two_numberOp
  have h2 : χ (2 : Op) = 2 := by
    simpa using (map_natCast χ 2)
  simpa [localParity, occupationInt, hN, h2] using hpar

/--
Membership form: if `p ∈ S`, the CAR parity readout is `-1`.
-/
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

/--
Vacancy form: if `p ∉ S`, the CAR parity readout is `+1`.
-/
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

/-- The evaluated local parity is an involution. -/
theorem carParity_readout_sq
    {Op : Type*} [Ring Op]
    (E : ExteriorCARPair Op)
    (χ : Op →+* ℤ)
    (p : ℕ)
    (S : Finset ℕ)
    (hN : χ E.numberOp = occupationInt p S) :
    χ E.parityOp * χ E.parityOp = 1 := by
  rw [carParity_readout_eq_booleanLocalParity E χ p S hN]
  by_cases hp : p ∈ S <;> simp [localParity, hp]


/-! ## 2. Global CAR chirality readout -/

/--
Global CAR parity readout over a property prime register.

The local CAR pair is indexed by the underlying prime mode.
The readout `χ` is an abstract ring-valued evaluation map into `ℤ`.
-/
@[rep_depth thermo]
def carGlobalChiralityReadout
    {Op : Type*} [Ring Op]
    (P : PrimeRegister)
    (E : ℕ → ExteriorCARPair Op)
    (χ : Op →+* ℤ) : ℤ :=
  Finset.prod P.primes fun p => χ ((E p).parityOp)

/--
If every local CAR number operator evaluates to Boolean occupation, then the
global CAR parity readout equals Boolean global chirality.
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
  simp [carGlobalChiralityReadout, globalChirality]
  refine Finset.prod_congr rfl ?_
  intro p hp
  simpa using carParity_readout_eq_booleanLocalParity (E p) χ p v.val (hN p hp)

/--
Global CAR chirality readout equals finite Boolean fermion parity.
-/
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
Global CAR chirality readout equals the Möbius value of the represented
square-free integer.
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
  rw [carGlobalChiralityReadout_eq_fermionParity P v E χ hN]
  exact (mobius_representedNat_eq_fermionParity P v).symm


/-! ## 3. Bridge theorem packet -/

/--
The finite CAR/Boolean-cube bridge is closed.
-/
theorem primeBooleanCubeCARBridgeOwnerTarget :
    ∀ {Op : Type*} [Ring Op]
      (P : PrimeRegister)
      (v : Vertex P)
      (E : ℕ → ExteriorCARPair Op)
      (χ : Op →+* ℤ)
      (_ :
        ∀ p ∈ P.primes,
          χ ((E p).numberOp) = occupationInt p v.val),
      carGlobalChiralityReadout P E χ = globalChirality P v.val ∧
      carGlobalChiralityReadout P E χ = fermionParity v ∧
      carGlobalChiralityReadout P E χ =
        ArithmeticFunction.moebius (representedNat v) := by
  intro Op inst P v E χ hN
  exact
    ⟨ carGlobalChiralityReadout_eq_booleanChirality P v E χ hN,
      carGlobalChiralityReadout_eq_fermionParity P v E χ hN,
      carGlobalChiralityReadout_eq_mobius P v E χ hN ⟩

@[owner_target_tag, bridge_target_tag, rep_depth thermo]
theorem primeBooleanCubeCARBridge_packet
    {Op : Type*} [Ring Op]
    (P : PrimeRegister)
    (v : Vertex P)
    (E : ℕ → ExteriorCARPair Op)
    (χ : Op →+* ℤ)
    (hN :
      ∀ p ∈ P.primes,
        χ ((E p).numberOp) = occupationInt p v.val) :
    carGlobalChiralityReadout P E χ = globalChirality P v.val ∧
    carGlobalChiralityReadout P E χ = fermionParity v ∧
    carGlobalChiralityReadout P E χ =
      ArithmeticFunction.moebius (representedNat v) :=
  primeBooleanCubeCARBridgeOwnerTarget P v E χ hN

end InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge
