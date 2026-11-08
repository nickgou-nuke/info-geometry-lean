import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.FiniteInductiveSUSY
import InfoGeometry.Arithmetic.KudinoorWittenIndexBridge
import InfoGeometry.Canonical.DrazinTripotentTrifactorBridge
import InfoGeometry.Clifford.GullDoranPseudoscalarBridge

/-!
# Virasoro / Drazin / Witten finite unification

This module records the theorem-safe finite corridor behind the requested
Virasoro-Drazin-Witten synthesis.

It does not construct an infinite UHF Hilbert space, a Virasoro representation,
a Sugawara stress tensor, a Seiberg-Witten moduli space, a continuum Maxwell
equation, or any Riemann-zeta consequence.  The Virasoro central charge is kept
as a scalar readout with explicit active/null-sector hypotheses.

#### BUCKET 1: CLOSED FINITE THEOREMS
The closed content is finite algebra:

* nilpotent SUSY charges imply the Dirac-square closure;
* the finite Kudinoor Witten supertrace collapses to the zero-sector index;
* a tripotent operator is its own Drazin inverse and has active/null trifactor
  projectors;
* the finite Gull-Doran Pauli pseudoscalar realification squares to `-1`;
* a central-charge readout with zero null-sector contribution is supported on
  the active Drazin sector.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The central-charge and Witten claims depend on explicit named premises:

* `hCentralSplit : virasoroCentralCharge = activeCentralCharge + nullCentralCharge`;
* `hNullCentral : nullCentralCharge = 0`;
* `hzero` and `hpair` for the finite Witten collapse.

#### BUCKET 3: OPEN CLOSURE DEBT
Categorical direct colimits, UHF completion, genuine Virasoro/Sugawara
construction, continuum STA/Maxwell equations, Seiberg-Witten theory, and
Riemann-zeta/RH interpretations.
-/

noncomputable section

namespace InfoGeometry.GrandUnification.VirasoroDrazinWittenUnification

open scoped BigOperators

/-! ## Finite SUSY owner readout -/

/--
Finite SUSY Dirac-square closure.

This is the local algebraic statement used by the synthesis: if two odd charges
are nilpotent and their anticommutator is `H + Z`, then the combined Dirac
operator squares to `H + Z`.
-/
theorem finite_susy_dirac_square_readout
    {A : Type*} [Ring A]
    (Q R H Z : A)
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hclosure :
      InfoGeometry.Algebra.FiniteInductiveSUSY.anticomm Q R = H + Z) :
    (Q + R) * (Q + R) = H + Z :=
  InfoGeometry.Algebra.FiniteInductiveSUSY.nilpotent_dirac_square_eq_closure
    Q R H Z hQ hR hclosure

/-! ## Drazin active/null central-charge readout -/

/--
The Drazin-filtered central-charge readout.

For a tripotent `O`, the Drazin support is the active trifactor sector
`P_plus O + P_minus O`, while the complementary Drazin projector is `P_zero O`.
If the supplied Virasoro central-charge readout splits into active plus null
sector contributions and the null contribution vanishes, then the readout is
entirely active-sector supported.
-/
theorem drazin_filtered_central_charge_readout
    {R : Type*} [CommRing R] [Invertible (2 : R)]
    (O virasoroCentralCharge activeCentralCharge nullCentralCharge : R)
    (hO : O ^ 3 = O)
    (hCentralSplit :
      virasoroCentralCharge = activeCentralCharge + nullCentralCharge)
    (hNullCentral : nullCentralCharge = 0) :
    virasoroCentralCharge = activeCentralCharge ∧
      InfoGeometry.Singular.Drazin.IsDrazinInverse
        O
        (InfoGeometry.Canonical.DrazinTripotentTrifactorBridge.tripotentDrazinInverse O) 1 ∧
      InfoGeometry.Canonical.DrazinTripotentTrifactorBridge.tripotentDrazinProjector O =
        InfoGeometry.Canonical.TrifactorDecomposition.P_plus O +
          InfoGeometry.Canonical.TrifactorDecomposition.P_minus O ∧
      InfoGeometry.Canonical.DrazinTripotentTrifactorBridge.tripotentDrazinNullProjector O =
        InfoGeometry.Canonical.TrifactorDecomposition.P_zero O ∧
      O *
        InfoGeometry.Canonical.DrazinTripotentTrifactorBridge.tripotentDrazinNullProjector O = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hCentralSplit, hNullCentral, add_zero]
  · exact
      InfoGeometry.Canonical.DrazinTripotentTrifactorBridge.tripotent_is_own_drazin_inverse O hO
  · exact
      InfoGeometry.Canonical.DrazinTripotentTrifactorBridge.tripotent_drazin_projector_eq_active_trifactor O
  · exact
      InfoGeometry.Canonical.DrazinTripotentTrifactorBridge.tripotent_drazin_null_projector_eq_P_zero O
  · exact
      InfoGeometry.Canonical.DrazinTripotentTrifactorBridge.tripotent_annihilates_drazin_null_projector O hO

/-! ## Witten index plus Drazin/Virasoro capstone -/

/--
Finite Witten/Drazin/Virasoro capstone.

This is the combined theorem-safe statement:

* the finite weighted supertrace collapses to the finite Witten index;
* the supplied central-charge readout is active-Drazin supported;
* the Drazin support/null projectors match the trifactor decomposition.
-/
theorem finite_witten_drazin_virasoro_capstone
    {ι R : Type*} [DecidableEq ι] [CommRing R] [Invertible (2 : R)]
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) (weight : ι → Int)
    (O virasoroCentralCharge activeCentralCharge nullCentralCharge : R)
    (hzero : ∀ i ∈ levels, zero i → weight i = 1)
    (hpair : ∀ i ∈ levels, ¬ zero i → boson i = fermion i)
    (hO : O ^ 3 = O)
    (hCentralSplit :
      virasoroCentralCharge = activeCentralCharge + nullCentralCharge)
    (hNullCentral : nullCentralCharge = 0) :
    InfoGeometry.Arithmetic.KudinoorWittenIndexBridge.finiteWeightedSupertrace
          levels boson fermion weight =
        InfoGeometry.Arithmetic.KudinoorWittenIndexBridge.finiteWittenIndex
          levels zero boson fermion ∧
      virasoroCentralCharge = activeCentralCharge ∧
      InfoGeometry.Canonical.DrazinTripotentTrifactorBridge.tripotentDrazinProjector O =
        InfoGeometry.Canonical.TrifactorDecomposition.P_plus O +
          InfoGeometry.Canonical.TrifactorDecomposition.P_minus O ∧
      InfoGeometry.Canonical.DrazinTripotentTrifactorBridge.tripotentDrazinNullProjector O =
        InfoGeometry.Canonical.TrifactorDecomposition.P_zero O ∧
      O *
        InfoGeometry.Canonical.DrazinTripotentTrifactorBridge.tripotentDrazinNullProjector O = 0 := by
  have hWitten :
      InfoGeometry.Arithmetic.KudinoorWittenIndexBridge.finiteWeightedSupertrace
          levels boson fermion weight =
        InfoGeometry.Arithmetic.KudinoorWittenIndexBridge.finiteWittenIndex
          levels zero boson fermion :=
    InfoGeometry.Arithmetic.KudinoorWittenIndexBridge.finiteWeightedSupertrace_eq_finiteWittenIndex
      levels zero boson fermion weight hzero hpair
  have hDrazin :=
    drazin_filtered_central_charge_readout
      O virasoroCentralCharge activeCentralCharge nullCentralCharge
      hO hCentralSplit hNullCentral
  exact ⟨hWitten, hDrazin.1, hDrazin.2.2.1, hDrazin.2.2.2.1,
    hDrazin.2.2.2.2⟩

/-! ## Gull-Doran pseudoscalar readout -/

/--
Finite real geometric-algebra readout.

The realified Pauli volume product is a concrete real phase axis and squares to
`-1`.  This is the theorem-safe finite shadow of the statement that the scalar
imaginary unit is a geometric pseudoscalar/volume-form action.
-/
theorem gull_doran_real_pseudoscalar_phase_readout :
    InfoGeometry.Clifford.GullDoranPseudoscalarBridge.realSigma1 *
        InfoGeometry.Clifford.GullDoranPseudoscalarBridge.realSigma2 *
        InfoGeometry.Clifford.GullDoranPseudoscalarBridge.realSigma3 =
        InfoGeometry.Clifford.GullDoranPseudoscalarBridge.realPhaseAxis ∧
      InfoGeometry.Clifford.GullDoranPseudoscalarBridge.realPhaseAxis *
          InfoGeometry.Clifford.GullDoranPseudoscalarBridge.realPhaseAxis =
        -(1 :
          InfoGeometry.Clifford.GullDoranPseudoscalarBridge.Mat4R) :=
  ⟨InfoGeometry.Clifford.GullDoranPseudoscalarBridge.real_pseudoscalar_eq_phaseAxis,
    InfoGeometry.Clifford.GullDoranPseudoscalarBridge.realPhaseAxis_sq⟩

end InfoGeometry.GrandUnification.VirasoroDrazinWittenUnification
