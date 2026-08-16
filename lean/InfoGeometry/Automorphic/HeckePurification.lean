/-
InfoGeometry/Automorphic/HeckePurification.lean

Hecke spectral purification for Siegel-Langlands resonance.

This module formalizes a proof-carrying Hecke-Sugawara purification property.
It calibrates operator-algebraic Sugawara readouts against arithmetic
automorphic L-functions when the required Hecke compatibility is supplied by a
concrete model.

This module sits above the operator-first Siegel-Eisenstein splitting, the
Roelcke-Selberg spectral interface, and the exceptional Virasoro bridge.

It does not prove Langlands functoriality, S-duality, Hecke diagonalization, or
an unconditional Sugawara/L-function theorem.
-/

import InfoGeometry.Automorphic.RoelckeSelbergSpectral
import InfoGeometry.Automorphic.LFunctionResonance
import InfoGeometry.Automorphic.LanglandsSugawaraBridge
import InfoGeometry.OperatorAlgebra.ExceptionalVirasoroBridge
import InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
import InfoGeometry.OperatorAlgebra.HorizonKMS

noncomputable section

namespace InfoGeometry.Automorphic.HeckePurification

open InfoGeometry.Automorphic.RoelckeSelbergSpectral
open InfoGeometry.Automorphic.SiegelResonance
open InfoGeometry.Automorphic.LFunctionResonance
open InfoGeometry.OperatorAlgebra.ExceptionalVirasoroBridge
open InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge
open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
open InfoGeometry.OperatorAlgebra.HorizonKMS

universe uBulk uBoundary uHecke

/--
Witness that the Sugawara stress-tensor readout on the Siegel boundary
intertwines with the Hecke action on the bulk.

This is the core 'Purification' property. It states that the boundary constant
term (Siegel projection) of a bulk Hecke action is compatible with the
operatorial Sugawara readout.
-/
structure HeckeSugawaraIntertwining
    {Bulk : Type uBulk} {Boundary : Type uBoundary} {HeckeIndex : Type uHecke}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    (R : RoelckeSelbergSpectralDatum W HeckeIndex)
    {J L Obs Memory Finite AffineAlg Vir State Charge : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg] [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Charge] [Module ℝ Charge]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (B : HorizonExceptionalVirasoroBridge J L Obs Memory Finite AffineAlg A)
    (EAV : ExceptionalAffineVirasoroBridge Finite AffineAlg Vir State Charge)
    (charge_eval : Charge → ℂ)
    (L_func : AutomorphicLFunctionDatum HeckeIndex) where

  /--
  Hecke operators on the bulk have corresponding boundary operators that
  intertwine with the Siegel extraction.
  -/
  intertwining : HeckeIndex → AutomorphicOperatorIntertwining W

  /--
  Kernel-level Hecke compatibility derived from the supplied intertwining data.

  Any bulk state already in the Siegel cuspidal kernel stays in that kernel
  after applying a supplied Hecke operator.  This replaces the former generic
  `Prop`/`sorry` placeholder with a concrete theorem-shaped obligation.
  -/
  hecke_preserves_cuspidal_kernel :
    ∀ (i : HeckeIndex) ⦃F : Bulk⦄,
      W.siegel F = 0 → W.siegel ((intertwining i).bulkOp F) = 0

  /--
  Resonance match: the zero-value of a completed L-function matches the
  Euler-product value at s=0 for the corresponding spectral character.
  -/
  completedL_resonance_match :
    ∀ (chi : JointEigenvalue HeckeIndex) (completedL : ℂ → ℂ),
      completedL 0 = L_func.value chi 0

  /-- 
  The spectral L-function value at the resonance point matches the purified 
  Sugawara readout of the corresponding eigenpacket.
  -/
  purification_law :
    ∀ (chi : JointEigenvalue HeckeIndex) (_P : CuspidalEigenpacket R chi) (s : State),
      charge_eval (EAV.centralChargeReadout s) =
        L_func.value chi 0

namespace HeckeSugawaraIntertwining

variable
    {Bulk : Type uBulk} {Boundary : Type uBoundary} {HeckeIndex : Type uHecke}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {R : RoelckeSelbergSpectralDatum W HeckeIndex}
    {J L Obs Memory Finite AffineAlg Vir State Charge : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg] [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Charge] [Module ℝ Charge]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {B : HorizonExceptionalVirasoroBridge J L Obs Memory Finite AffineAlg A}
    {EAV : ExceptionalAffineVirasoroBridge Finite AffineAlg Vir State Charge}
    {charge_eval : Charge → ℂ}
    {L_func : AutomorphicLFunctionDatum HeckeIndex}

variable
    (H : HeckeSugawaraIntertwining R B EAV charge_eval L_func)

/--
Re-export of kernel-level Hecke compatibility on the cuspidal Siegel kernel.
-/
theorem hecke_preserves_cuspidal_kernel_of_intertwining
    (i : HeckeIndex)
    {F : Bulk}
    (hF : W.siegel F = 0) :
    W.siegel ((H.intertwining i).bulkOp F) = 0 :=
  H.hecke_preserves_cuspidal_kernel i hF

/-- The hidden grade-memory readout also matches the Hecke L-value at zero. -/
theorem hiddenGradeMemory_eq_l_value
    (H : HeckeSugawaraIntertwining R B EAV charge_eval L_func)
    (chi : JointEigenvalue HeckeIndex)
    (P : CuspidalEigenpacket R chi)
    (s : State) :
    charge_eval (EAV.calibratedHiddenGradeMemoryReadout s) =
      L_func.value chi 0 := by
  rw [← EAV.centralCharge_eq_hiddenGradeMemory s]
  exact H.purification_law chi P s

end HeckeSugawaraIntertwining

/--
A supplied Langlands/Sugawara bridge and a Hecke purification property together
provide the two certificates needed by the Siegel-Langlands resonance lane:

* the purified Sugawara readout equals the Hecke L-value at zero;
* the Langlands/Sugawara bridge is inhabited.

The bridge itself is not constructed from the Hecke property alone; Euler
products, completed functional equations, and affine/Virasoro calibration remain
separate property data.
-/
theorem langlandsSugawaraBridge_nonempty_of_purification
    {Bulk : Type uBulk} {Boundary : Type uBoundary} {HeckeIndex : Type uHecke}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {R : RoelckeSelbergSpectralDatum W HeckeIndex}
    {J L Obs Memory Finite AffineAlg Vir State Charge : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg] [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Charge] [Module ℝ Charge]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {B : HorizonExceptionalVirasoroBridge J L Obs Memory Finite AffineAlg A}
    {EAV : ExceptionalAffineVirasoroBridge Finite AffineAlg Vir State Charge}
    {charge_eval : Charge → ℂ}
    {L_func : AutomorphicLFunctionDatum HeckeIndex}
    (H : HeckeSugawaraIntertwining R B EAV charge_eval L_func)
    (chi : JointEigenvalue HeckeIndex)
    (P : CuspidalEigenpacket R chi)
    (s : State)
    {W_L : SiegelEisensteinWitness Bulk Boundary}
    (P_L : ProjectedAutomorphicLFunctionWitness W_L)
    {BridgeVir BridgeState : Type*}
    [AddCommGroup BridgeVir] [Module ℝ BridgeVir]
    [LieRing BridgeVir] [LieAlgebra ℝ BridgeVir]
    [AddCommGroup BridgeState] [Module ℝ BridgeState]
    (B_L : LanglandsSugawaraBridge P_L Finite AffineAlg BridgeVir BridgeState) :
    charge_eval (EAV.centralChargeReadout s) = L_func.value chi 0 ∧
      Nonempty (LanglandsSugawaraBridge P_L Finite AffineAlg BridgeVir BridgeState) :=
  ⟨H.purification_law chi P s, ⟨B_L⟩⟩

end InfoGeometry.Automorphic.HeckePurification
