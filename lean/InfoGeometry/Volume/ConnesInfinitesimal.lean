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
noncomputable def unitsRNBridge : HasScalarRNBridge ℝˣ := MonoidHom.id ℝˣ

@[simp] theorem unitsRNBridge_rn_apply (u : ℝˣ) :
    HasScalarRNBridge.rn unitsRNBridge u = Real.log |(u : ℝ)| :=
  rfl

/-- The exact logarithmic RN chain rule on real units. -/
theorem unitsRNBridge_chain_rule (u v : ℝˣ) :
    HasScalarRNBridge.rn unitsRNBridge (u * v) =
      HasScalarRNBridge.rn unitsRNBridge u + HasScalarRNBridge.rn unitsRNBridge v :=
  HasScalarRNBridge.rn_chain_rule unitsRNBridge u v

/-- The logarithmic two-coboundary of the concrete RN character. -/
noncomputable def unitsRNTwoCoboundary (u v : ℝˣ) : ℝ :=
  HasScalarRNBridge.rn unitsRNBridge (u * v) -
    HasScalarRNBridge.rn unitsRNBridge u - HasScalarRNBridge.rn unitsRNBridge v

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
  change Real.log |Real.exp (rate * t)| = rate * t
  rw [abs_of_pos (Real.exp_pos _), Real.log_exp]

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
The modular Hamiltonian is fixed by its own exponential-conjugation flow.
-/
@[simp] theorem modularHamiltonianAction_self
    (K : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction (H := H) K K t = K := by
  simpa [modularHamiltonianAction] using
    (expTransport_eq_self_of_commute K K t (Commute.refl K))

/--
At modular time zero, the infinitesimal modular action of the Hamiltonian on
itself vanishes.
-/
@[simp] theorem modularHamiltonianAction_hasDerivAt_zero_self
    (K : AlgebraEnd H) :
    HasDerivAt (fun t : ℝ => modularHamiltonianAction (H := H) K K t) 0 0 := by
  simpa [modularHamiltonianAction] using
    (hasDerivAt_expTransport_at_zero (A := AlgebraEnd H) K K)

/--
At arbitrary modular time, the transported commutator of the Hamiltonian with
itself vanishes.
-/
@[simp] theorem modularHamiltonianAction_hasDerivAt_self
    (K : AlgebraEnd H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => modularHamiltonianAction (H := H) K K s) 0 t := by
  have hfun :
      (fun s : ℝ => modularHamiltonianAction (H := H) K K s) = fun _ : ℝ => K := by
    funext s
    simp
  rw [hfun]
  simpa using (hasDerivAt_const (x := t) (c := K))

/--
At modular time zero, the modular Hamiltonian generates no infinitesimal drift
on itself.
-/
@[simp] theorem deriv_modularHamiltonianAction_self_at_zero
    (K : AlgebraEnd H) :
    deriv (fun t : ℝ => modularHamiltonianAction (H := H) K K t) 0 = 0 := by
  exact (modularHamiltonianAction_hasDerivAt_zero_self (H := H) K).deriv

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
Named Heisenberg equation for the modular orbit generated by `K`.
-/
theorem modularHamiltonianAction_solves_heisenberg_equation
    (K A : AlgebraEnd H) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => modularHamiltonianAction (H := H) K A s)
      (modularHamiltonianAction (H := H) K ⁅K, A⁆ t)
      t :=
  modularHamiltonianAction_hasDerivAt (H := H) K A t

/--
Any operator commuting with the modular Hamiltonian is fixed by the modular
flow.
-/
@[simp] theorem modularHamiltonianAction_eq_self_of_commute
    (K A : AlgebraEnd H) (t : ℝ) (hComm : Commute A K) :
    modularHamiltonianAction (H := H) K A t = A := by
  simpa [modularHamiltonianAction] using
    (expTransport_eq_self_of_commute K A t hComm)

theorem commute_of_modularHamiltonianAction_eq_self
    (K A : AlgebraEnd H)
    (hFixed : ∀ t : ℝ, modularHamiltonianAction (H := H) K A t = A) :
    Commute K A := by
  have hDeriv :
      HasDerivAt (fun t : ℝ => modularHamiltonianAction (H := H) K A t)
        0 0 := by
    have hConst :
        (fun t : ℝ => modularHamiltonianAction (H := H) K A t) =
          (fun _ : ℝ => A) := by
      funext t
      exact hFixed t
    rw [hConst]
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := A))
  have hFlowDeriv :=
    (modularHamiltonianAction_hasDerivAt_zero (H := H) K A).deriv
  have hBracket : ⁅K, A⁆ = 0 := by
    exact hFlowDeriv.symm.trans hDeriv.deriv
  exact sub_eq_zero.mp hBracket

/--
The generated modular flow acts by the same exponential-conjugation formula as
`modularHamiltonianAction`.
-/
theorem modularHamiltonianAction_eq_generatedFlow
    (K A : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction (H := H) K A t =
      additiveModularFlowOfGenerator (H := H) K t A := by
  change expTransport K A t =
    InfoGeometry.Krein.modular_shift (E := H) K t A
  simp [expTransport, InfoGeometry.Krein.krein_modular_shift, smul_neg]

/-! ## Finite additive-time law -/

/-- The finite modular Hamiltonian action is an additive-time flow. -/
theorem modularHamiltonianAction_add
    (K A : AlgebraEnd H) (s t : ℝ) :
    modularHamiltonianAction (H := H) K A (s + t) =
      modularHamiltonianAction (H := H) K
        (modularHamiltonianAction (H := H) K A t) s := by
  have hcomm : Commute (s • K) (t • K) :=
    ((Commute.refl K).smul_left s).smul_right t
  have hcommNeg : Commute (t • (-K)) (s • (-K)) :=
    ((Commute.refl (-K)).smul_left t).smul_right s
  have hneg : (s + t) • (-K) = t • (-K) + s • (-K) := by
    module
  unfold modularHamiltonianAction expTransport
  rw [add_smul, NormedSpace.exp_add_of_commute hcomm, hneg,
    NormedSpace.exp_add_of_commute hcommNeg]
  noncomm_ring

/-- The finite modular Hamiltonian action is multiplicative on observables. -/
theorem modularHamiltonianAction_mul
    (K A B : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction (H := H) K (A * B) t =
      modularHamiltonianAction (H := H) K A t *
        modularHamiltonianAction (H := H) K B t := by
  exact expTransport_mul_seed K A B t

/-- The finite modular Hamiltonian action preserves operator commutators. -/
theorem modularHamiltonianAction_lie
    (K A B : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction (H := H) K ⁅A, B⁆ t =
      ⁅modularHamiltonianAction (H := H) K A t,
        modularHamiltonianAction (H := H) K B t⁆ := by
  exact expTransport_lie K A B t

/-- The finite modular Hamiltonian action fixes the identity operator. -/
@[simp] theorem modularHamiltonianAction_one
    (K : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction (H := H) K 1 t = 1 := by
  exact expTransport_one_seed K t

theorem modularHamiltonianAction_smul
    (K A : AlgebraEnd H) (r t : ℝ) :
    modularHamiltonianAction (H := H) K (r • A) t =
      r • modularHamiltonianAction (H := H) K A t := by
  exact expTransport_smul_seed K A r t

theorem modularHamiltonianAction_pow
    (K A : AlgebraEnd H) (n : ℕ) (t : ℝ) :
    modularHamiltonianAction (H := H) K (A ^ n) t =
      (modularHamiltonianAction (H := H) K A t) ^ n := by
  exact expTransport_pow_seed K A n t

/-- The finite modular flow packaged as an `ℝ`-algebra homomorphism. -/
noncomputable def modularHamiltonianActionAlgHom
    (K : AlgebraEnd H) (t : ℝ) : AlgebraEnd H →ₐ[ℝ] AlgebraEnd H :=
  expTransportAlgHom K t

@[simp] theorem modularHamiltonianActionAlgHom_apply
    (K A : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianActionAlgHom (H := H) K t A =
      modularHamiltonianAction (H := H) K A t := rfl

/-- The finite modular flow packaged as an `ℝ`-algebra equivalence. -/
noncomputable def modularHamiltonianActionAlgEquiv
    (K : AlgebraEnd H) (t : ℝ) : AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H :=
  expTransportAlgEquiv K t

@[simp] theorem modularHamiltonianActionAlgEquiv_apply
    (K A : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianActionAlgEquiv (H := H) K t A =
      modularHamiltonianAction (H := H) K A t := rfl

/-- A finite modular Hamiltonian flow is inverted by reversing its time. -/
theorem modularHamiltonianAction_neg_left
    (K A : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction (H := H) K
        (modularHamiltonianAction (H := H) K A (-t)) t = A := by
  rw [← modularHamiltonianAction_add (H := H) K A t (-t)]
  simp

/-- The opposite composition gives the same finite-time inverse law. -/
theorem modularHamiltonianAction_neg_right
    (K A : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction (H := H) K
        (modularHamiltonianAction (H := H) K A t) (-t) = A := by
  rw [← modularHamiltonianAction_add (H := H) K A (-t) t]
  simp

end InfoGeometry.Volume.ConnesInfinitesimal
