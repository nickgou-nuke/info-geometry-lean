import InfoGeometry.Arithmetic.ChiralPrimonGas
import InfoGeometry.Arithmetic.PrimeBosonFermionGas
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.SUSYCentralChargeBridge
import InfoGeometry.Canonical.WeylNormalizedCARCCRBridge
import InfoGeometry.External.Virasoro.ChiralProduct

/-!
# InfoGeometry.Arithmetic.PrimonSupergradedGasAlgebra

Finite algebraic readout for the primon boson/fermion gas.

This file deliberately separates the layers:

* finite Euler products and Witten parity are arithmetic prime-register facts;
* the fermionic ladder is the existing split-`Cl(1,1)` CAR pair;
* the bosonic unit CCR is witness-gated by `ScaledCCRPair`, because a true
  unit Heisenberg CCR is not a finite-matrix identity;
* the primitive supercharge CAR/CCR channel is the already-owned
  `J/ε/Q = Jε` doubled-Krein spine;
* chiral projectors and central-charge bookkeeping are read from the
  chiral Virasoro product and the SUSY central-charge owner.

No thermodynamic limit, zeta analytic continuation, AQFT cone theorem, or RH
claim is made here.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.Arithmetic.PrimonSupergradedGasAlgebra

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeBosonFermionGas
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical

/-! ## Finite prime-register boson/fermion partition layer -/

variable {ι R : Type*} [Field R]

/-- Bosonic primon Euler factor product, reusing the arithmetic owner. -/
abbrev finiteBosonPrimonPartition (S : Finset ι) (x : ι → R) : R :=
  bosonPartition S x

/-- Signed fermionic primon Euler factor product, reusing the arithmetic owner. -/
abbrev finiteSignedFermionPrimonPartition (S : Finset ι) (x : ι → R) : R :=
  signedFermionPartition S x

/-- Positive fermionic primon Euler factor product, reusing the arithmetic owner. -/
abbrev finitePositiveFermionPrimonPartition (S : Finset ι) (x : ι → R) : R :=
  positiveFermionPartition S x

/--
Finite boson/fermion Euler cancellation.

This is the finite algebraic shadow of `ζ * ζ⁻¹ = 1`; it is not an infinite
Euler-product theorem.
-/
theorem finite_boson_signedFermion_cancel
    (S : Finset ι) (x : ι → R) (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    finiteBosonPrimonPartition S x * finiteSignedFermionPrimonPartition S x = 1 :=
  boson_mul_signedFermion_cancel S x h

/-- Same finite cancellation with the factors reversed. -/
theorem finite_signedFermion_boson_cancel
    (S : Finset ι) (x : ι → R) (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    finiteSignedFermionPrimonPartition S x * finiteBosonPrimonPartition S x = 1 :=
  signedFermion_mul_boson_cancel S x h

/--
The regulated finite bosonic primon partition is nonzero.

This is the finite statement that the inverse Witten/Euler factor exists; it
does not assert analytic continuation or a zeta-zero theorem.
-/
theorem finiteBosonPrimonPartition_ne_zero
    (S : Finset ι) (x : ι → R) (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    finiteBosonPrimonPartition S x ≠ 0 :=
  bosonPartition_ne_zero S x h

/--
The regulated finite signed fermion / Möbius supertrace is nonzero when it is
the inverse Euler factor of the finite bosonic partition.
-/
theorem finiteSignedFermionPrimonPartition_ne_zero
    (S : Finset ι) (x : ι → R) (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    finiteSignedFermionPrimonPartition S x ≠ 0 :=
  signedFermionPartition_ne_zero S x h

/--
Finite positive fermion / boson ratio identity.

This is the finite algebraic shadow of `Z_f^+(s) = ζ(s) / ζ(2s)`.
-/
theorem finite_positiveFermion_mul_squareBoson_eq_boson
    (S : Finset ι)
    (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0)
    (h_sq : ∀ p ∈ S, 1 - x p * x p ≠ 0) :
    finitePositiveFermionPrimonPartition S x *
        finiteBosonPrimonPartition S (fun p => x p * x p) =
      finiteBosonPrimonPartition S x :=
  positiveFermion_mul_squareBoson_eq_boson S x h h_sq

/-- The regulated finite positive fermion primon partition is nonzero. -/
theorem finitePositiveFermionPrimonPartition_ne_zero
    (S : Finset ι)
    (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0)
    (h_sq : ∀ p ∈ S, 1 - x p * x p ≠ 0) :
    finitePositiveFermionPrimonPartition S x ≠ 0 :=
  positiveFermionPartition_ne_zero S x h h_sq

/-! ## Finite Witten-index / Möbius-parity layer -/

/-- Finite Witten index of a prime register as the Boolean supertrace. -/
def finitePrimonWittenIndex (P : PrimeRegister) : ℤ :=
  ∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card

/-- Nonempty finite prime registers have vanishing Boolean Witten supertrace. -/
theorem finitePrimonWittenIndex_cancel
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    finitePrimonWittenIndex P = 0 := by
  simpa [finitePrimonWittenIndex] using finite_witten_supertrace_cancel P hP

/-- Möbius readout equals fermion parity for a finite squarefree prime-bit state. -/
theorem mobius_readout_eq_fermionParity
    (P : PrimeRegister) (ψ : PrimeBitState P) :
    ArithmeticFunction.moebius (representedNatOfState P ψ) = fermionParityOfState P ψ :=
  mobius_representedNatOfState_eq_fermionParity P ψ

/-! ## CAR/CCR and supercharge layer on the doubled Fock carrier -/

section Fock

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The finite primon fermion ladder is the concrete split-`Cl(1,1)` CAR pair. -/
theorem primonFermionCAR :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair (E := E)
      (concreteCARAnnihilation (E := E))
      (concreteCARCreation (E := E)) :=
  concrete_car_pair (E := E)

/-- Same-mode fermion CAR nilpotence for annihilation and creation. -/
theorem primonFermionCAR_nilpotent :
    CARBracket (E := E)
        (concreteCARAnnihilation (E := E))
        (concreteCARAnnihilation (E := E)) = 0
      ∧
      CARBracket (E := E)
        (concreteCARCreation (E := E))
        (concreteCARCreation (E := E)) = 0 :=
  concrete_car_nilpotency (E := E)

/-- Mixed fermion CAR identity `{a, a†} = 1`. -/
theorem primonFermionCAR_mixed :
    CARBracket (E := E)
        (concreteCARAnnihilation (E := E))
        (concreteCARCreation (E := E))
      = ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) :=
  concrete_car_minus_plus (E := E)

/--
Bosonic primon CCR readout.

The unit CCR is obtained from a supplied scaled CCR pair by the existing Weyl
normalization theorem.
-/
theorem primonBosonCCR_of_scaledPair
    (P : ScaledCCRPair E) :
    IsCCRPair (E := E) P.normalizedAnnihilation P.normalizedCreation :=
  P.normalized_isCCRPair

/-- Primitive supercharge CAR channel: `{J, ε} = 0`. -/
theorem primonSuperchargeCAR_zero :
    CARBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E)) = 0 :=
  parity_modular_supercharge_car_zero (E := E)

/-- Primitive supercharge CCR channel: `[J, ε] = 2Q`. -/
theorem primonSuperchargeCCR_eq_two_cpt :
    CCRBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = (2 : ℝ) • cptSuperchargeOp (E := E) :=
  parity_modular_supercharge_ccrBracket_eq_two_cpt (E := E)

/-- The chiral/CPT supercharge squares to `-1` on the doubled real carrier. -/
theorem chiralSupercharge_sq :
    (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E))
      = -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) :=
  cptSuperchargeOp_sq (E := E)

/-- The chiral/CPT supercharge flips the plus sector to the minus sector. -/
theorem chiralSupercharge_maps_plus_to_minus
    {v : InfoGeometry.Krein.DoubledSpace E}
    (hv : InfoGeometry.Krein.inGradePlus (E := E) v) :
    InfoGeometry.Krein.inGradeMinus (E := E) (cptSuperchargeOp (E := E) v) :=
  cptSuperchargeOp_maps_plus_to_minus (E := E) hv

/-- The chiral/CPT supercharge flips the minus sector to the plus sector. -/
theorem chiralSupercharge_maps_minus_to_plus
    {v : InfoGeometry.Krein.DoubledSpace E}
    (hv : InfoGeometry.Krein.inGradeMinus (E := E) v) :
    InfoGeometry.Krein.inGradePlus (E := E) (cptSuperchargeOp (E := E) v) :=
  cptSuperchargeOp_maps_minus_to_plus (E := E) hv

/--
Single packet for the finite doubled-carrier supergraded primon algebra spine.
-/
theorem primonSupergradedFockSpine :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair (E := E)
      (concreteCARAnnihilation (E := E))
      (concreteCARCreation (E := E))
    ∧
    CARBracket (E := E)
      (paritySuperchargeOp (E := E))
      (modularSuperchargeOp (E := E)) = 0
    ∧
    CCRBracket (E := E)
      (paritySuperchargeOp (E := E))
      (modularSuperchargeOp (E := E))
        = (2 : ℝ) • cptSuperchargeOp (E := E)
    ∧
    (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E))
      = -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact primonFermionCAR (E := E)
  · exact primonSuperchargeCAR_zero (E := E)
  · exact primonSuperchargeCCR_eq_two_cpt (E := E)
  · exact chiralSupercharge_sq (E := E)

end Fock

/-! ## Chiral thermodynamic projectors -/

open InfoGeometry.Arithmetic.ChiralPrimonGas

/-- Chiral thermodynamic projectors reconstruct the full two-sector gas readout. -/
theorem chiralPrimonThermo_projectors_resolve
    (T : ChiralThermo) :
    ChiralThermo.reconstruct T = T :=
  ChiralThermo.reconstruct_eq T

/-- The plus projector extracts the plus sector. -/
theorem chiralPrimonThermo_projectLeft_eq
    (T : ChiralThermo) :
    ChiralThermo.projectLeft T = T.plus :=
  ChiralThermo.projectLeft_eq T

/-- The minus projector extracts the minus sector. -/
theorem chiralPrimonThermo_projectRight_eq
    (T : ChiralThermo) :
    ChiralThermo.projectRight T = T.minus :=
  ChiralThermo.projectRight_eq T

/-! ## Chiral Virasoro projectors and central-charge bookkeeping -/

section ChiralVirasoro

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Chiral Virasoro left/right projectors resolve the identity. -/
theorem chiralVirasoro_projectors_resolve
    (X : VirasoroProject.ChiralVirasoro 𝕜) :
    VirasoroProject.ChiralVirasoro.projectLeft (𝕜 := 𝕜) X
      + VirasoroProject.ChiralVirasoro.projectRight (𝕜 := 𝕜) X = X :=
  VirasoroProject.ChiralVirasoro.projectLeft_add_projectRight X

/-- Left and right chiral Virasoro sectors have zero cross bracket. -/
theorem chiralVirasoro_crossBracket_zero
    (X Y : VirasoroProject.VirasoroAlgebra 𝕜) :
    ⁅VirasoroProject.ChiralVirasoro.inLeft X,
      VirasoroProject.ChiralVirasoro.inRight Y⁆ = 0 :=
  VirasoroProject.ChiralVirasoro.inLeft_bracket_inRight X Y

/-- Left central generator commutes with the full chiral Virasoro product. -/
theorem chiralVirasoro_cgenLeft_central
    (X : VirasoroProject.ChiralVirasoro 𝕜) :
    ⁅VirasoroProject.ChiralVirasoro.cgenLeft (𝕜 := 𝕜), X⁆ = 0 :=
  VirasoroProject.ChiralVirasoro.cgenLeft_bracket X

/-- Right central generator commutes with the full chiral Virasoro product. -/
theorem chiralVirasoro_cgenRight_central
    (X : VirasoroProject.ChiralVirasoro 𝕜) :
    ⁅VirasoroProject.ChiralVirasoro.cgenRight (𝕜 := 𝕜), X⁆ = 0 :=
  VirasoroProject.ChiralVirasoro.cgenRight_bracket X

/-- Total central charge of a chiral pair. -/
abbrev chiralCentralChargeTotal
    (c : VirasoroProject.ChiralVirasoro.CentralCharge (𝕜 := 𝕜)) : 𝕜 :=
  VirasoroProject.ChiralVirasoro.CentralCharge.total c

/-- Chiral central-charge imbalance of a chiral pair. -/
abbrev chiralCentralChargeImbalance
    (c : VirasoroProject.ChiralVirasoro.CentralCharge (𝕜 := 𝕜)) : 𝕜 :=
  VirasoroProject.ChiralVirasoro.CentralCharge.imbalance c

omit [CharZero 𝕜] in
@[simp] theorem chiralCentralChargeTotal_mk (cL cR : 𝕜) :
    chiralCentralChargeTotal
        (VirasoroProject.ChiralVirasoro.CentralCharge.mk (𝕜 := 𝕜) cL cR)
      = cL + cR :=
  rfl

omit [CharZero 𝕜] in
@[simp] theorem chiralCentralChargeImbalance_mk (cL cR : 𝕜) :
    chiralCentralChargeImbalance
        (VirasoroProject.ChiralVirasoro.CentralCharge.mk (𝕜 := 𝕜) cL cR)
      = cL - cR :=
  rfl

end ChiralVirasoro

/-! ## Integer central-charge channel counts -/

/-- Eight Majorana channels have `c = 4`, stored as `2c = 8`. -/
theorem eightMajorana_twiceCentralCharge :
    InfoGeometry.Canonical.SUSYCentralChargeBridge.twiceCentralMajorana 8 = 8 :=
  InfoGeometry.Canonical.SUSYCentralChargeBridge.c4_is_eight_majoranas

/-- Eight bosonic current channels have `c = 8`, stored as `2c = 16`. -/
theorem eightBoson_twiceCentralCharge :
    InfoGeometry.Canonical.SUSYCentralChargeBridge.twiceCentralBoson 8 = 16 :=
  InfoGeometry.Canonical.SUSYCentralChargeBridge.c8_is_eight_bosons

/-- Eight free `N = 1` multiplets have `c = 12`, stored as `2c = 24`. -/
theorem eightN1Multiplets_twiceCentralCharge :
    InfoGeometry.Canonical.SUSYCentralChargeBridge.twiceCentralN1Multiplet 8 = 24 :=
  InfoGeometry.Canonical.SUSYCentralChargeBridge.eight_N1_multiplets_have_c12

end InfoGeometry.Arithmetic.PrimonSupergradedGasAlgebra
