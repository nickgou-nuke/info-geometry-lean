import InfoGeometry.Canonical.TransportLieDerivative
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Volume.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-!
# Constructive Connes/Radon-Nikodym Infinitesimal Layer

This file keeps the infinitesimal modular statements concrete:

* modular time is exponential conjugation by a Hamiltonian/generator;
* its infinitesimal action is the commutator, by the mathlib-rooted
  `NormedSpace.exp` derivative theorem in `TransportLieDerivative`;
* the scalar Radon-Nikodym logarithm is the exact logarithm on real units;
* exponential RN paths have a literal logarithmic derivative;
* the induced logarithmic two-coboundaries vanish by exact additivity.
-/

open scoped InnerProductSpace Topology

namespace InfoGeometry.Volume.ConnesInfinitesimal

open InfoGeometry.Canonical
open InfoGeometry.Volume.ConnesCocycle
open InfoGeometry.Volume.RadonNikodym

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance : NormedRing (AlgebraEnd H) := inferInstance
noncomputable local instance : NormedAlgebra ℝ (AlgebraEnd H) := inferInstance
local instance : IsTopologicalRing (AlgebraEnd H) := inferInstance
local instance : CompleteSpace (AlgebraEnd H) := inferInstance

/-! ## Concrete scalar RN logarithm on real units -/

/-- The constructive scalar RN datum on real units: volume is the identity. -/
noncomputable def unitsRNBridge : HasScalarRNBridge ℝˣ where
  vol := MonoidHom.id ℝˣ
  rn := fun u => Real.log |(u : ℝ)|
  rn_eq_logAbs_vol := by
    intro u
    rfl

@[simp] theorem unitsRNBridge_rn_apply (u : ℝˣ) :
    unitsRNBridge.rn u = Real.log |(u : ℝ)| :=
  rfl

/-- The exact logarithmic RN chain rule on real units. -/
theorem unitsRNBridge_chain_rule (u v : ℝˣ) :
    unitsRNBridge.rn (u * v) = unitsRNBridge.rn u + unitsRNBridge.rn v :=
  rn_chain_rule unitsRNBridge u v

/-- The logarithmic two-coboundary of the concrete RN character. -/
noncomputable def unitsRNTwoCoboundary (u v : ℝˣ) : ℝ :=
  unitsRNBridge.rn (u * v) - unitsRNBridge.rn u - unitsRNBridge.rn v

/-- Exact RN logarithms have zero additive two-coboundary. -/
@[simp] theorem unitsRNTwoCoboundary_eq_zero (u v : ℝˣ) :
    unitsRNTwoCoboundary u v = 0 := by
  unfold unitsRNTwoCoboundary
  rw [unitsRNBridge_chain_rule]
  ring

/-- Positive exponential path in real units with velocity `rate`. -/
noncomputable def expUnitsPath (rate t : ℝ) : ℝˣ :=
  Units.mk0 (Real.exp (rate * t)) (Real.exp_ne_zero _)

@[simp] theorem expUnitsPath_val (rate t : ℝ) :
    ((expUnitsPath rate t : ℝˣ) : ℝ) = Real.exp (rate * t) :=
  rfl

/-- Exponential unit paths are multiplicative for additive time. -/
@[simp] theorem expUnitsPath_add (rate s t : ℝ) :
    expUnitsPath rate (s + t) = expUnitsPath rate s * expUnitsPath rate t := by
  ext
  simp [expUnitsPath, Real.exp_add, mul_add]

/-- The RN logarithm of the exponential unit path is the linear potential. -/
@[simp] theorem unitsRNBridge_rn_expUnitsPath (rate t : ℝ) :
    unitsRNBridge.rn (expUnitsPath rate t) = rate * t := by
  simp [unitsRNBridge, expUnitsPath, Real.log_exp]

/-- The concrete RN logarithmic path has derivative equal to its rate. -/
theorem unitsRNBridge_rn_expUnitsPath_hasDerivAt (rate t : ℝ) :
    HasDerivAt (fun τ : ℝ => unitsRNBridge.rn (expUnitsPath rate τ)) rate t := by
  have hfun :
      (fun τ : ℝ => unitsRNBridge.rn (expUnitsPath rate τ)) =
        fun τ : ℝ => rate * τ := by
    funext τ
    simp
  rw [hfun]
  simpa using ((hasDerivAt_id' t).const_mul rate)

/-! ## Constructive generated Connes cocycle logarithmic two-coboundary -/

/--
The generated unit Connes cocycle log potential for the modular flow generated
by `K`.
-/
noncomputable def generatedUnitConnesLogPotential
    (K : AlgebraEnd H) (t : ℝ) : ℝ :=
  let σ := additiveModularFlowOfGenerator (H := H) K
  cocycleLogPotential (H := H) σ (unitCocycle (H := H))
    (unitScalarBridge (H := H) σ) t

@[simp] theorem generatedUnitConnesLogPotential_eq_zero
    (K : AlgebraEnd H) (t : ℝ) :
    generatedUnitConnesLogPotential (H := H) K t = 0 := by
  simp [generatedUnitConnesLogPotential]

/-- Additive logarithmic two-coboundary for the generated unit Connes cocycle. -/
noncomputable def generatedUnitConnesLogTwoCoboundary
    (K : AlgebraEnd H) (s t : ℝ) : ℝ :=
  generatedUnitConnesLogPotential (H := H) K (s + t)
    - generatedUnitConnesLogPotential (H := H) K s
    - generatedUnitConnesLogPotential (H := H) K t

/-- The generated unit Connes cocycle has zero logarithmic two-coboundary. -/
@[simp] theorem generatedUnitConnesLogTwoCoboundary_eq_zero
    (K : AlgebraEnd H) (s t : ℝ) :
    generatedUnitConnesLogTwoCoboundary (H := H) K s t = 0 := by
  simp [generatedUnitConnesLogTwoCoboundary]

/-! ## Modular Hamiltonian infinitesimal action -/

/--
Modular Hamiltonian action by exponential conjugation.

This is the concrete modular automorphism model used by the derivative
theorems below.
-/
noncomputable def modularHamiltonianAction
    (K A : AlgebraEnd H) (t : ℝ) : AlgebraEnd H :=
  expTransport K A t

@[simp] theorem modularHamiltonianAction_zero
    (K A : AlgebraEnd H) :
    modularHamiltonianAction (H := H) K A 0 = A := by
  unfold modularHamiltonianAction expTransport
  have hK : (0 : ℝ) • K = (0 : AlgebraEnd H) := zero_smul ℝ K
  have hNegK : (0 : ℝ) • (-K) = (0 : AlgebraEnd H) := zero_smul ℝ (-K)
  rw [hK, hNegK, NormedSpace.exp_zero]
  simp

/--
At modular time zero, the infinitesimal modular action is the commutator with
the modular Hamiltonian.
-/
theorem modularHamiltonianAction_hasDerivAt_zero
    (K A : AlgebraEnd H) :
    HasDerivAt (fun t : ℝ => modularHamiltonianAction (H := H) K A t) ⁅K, A⁆ 0 := by
  simpa [modularHamiltonianAction] using
    (hasDerivAt_expTransport_at_zero (A := AlgebraEnd H) K A)

/--
At arbitrary modular time, the derivative is the transported commutator.
-/
theorem modularHamiltonianAction_hasDerivAt
    (K A : AlgebraEnd H) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => modularHamiltonianAction (H := H) K A s)
      (modularHamiltonianAction (H := H) K ⁅K, A⁆ t)
      t := by
  simpa [modularHamiltonianAction] using
    (hasDerivAt_expTransport (A := AlgebraEnd H) K A t)

/--
The generated modular flow acts by the same exponential-conjugation formula as
`modularHamiltonianAction`.
-/
theorem modularHamiltonianAction_eq_generatedFlow
    (K A : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction (H := H) K A t =
      additiveModularFlowOfGenerator (H := H) K t A := by
  simp [modularHamiltonianAction, expTransport, additiveModularFlowOfGenerator_apply,
    InfoGeometry.Krein.modular_shift, InfoGeometry.Krein.krein_modular_shift, smul_neg]

end InfoGeometry.Volume.ConnesInfinitesimal
