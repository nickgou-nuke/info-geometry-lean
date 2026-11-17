/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.BilinearMetriplecticReduction

/-!
# A pointwise GENERIC reservoir lift

For a real module `V`, an energy covector `h`, and `T > 0`, the map
`A_h v = (v, -h v / T)` takes values in the kernel of the extended energy
covector `(h, T)` on `V × ℝ`. Congruence therefore constructs the dissipative
operator `T⁻¹ • A_h D A_h*` from any symmetric nonnegative mobility `D`.
The reversible lift uses the inclusion `v ↦ (v, 0)`. Both Casimir laws are
derived from these maps, rather than assumed for the extended operators.

The resulting flow is `(L h - T⁻² • D h, T⁻³ * h (D h))`. This construction
never divides by `h` or its norm; it does contain inverses of the positive
parameter `T`. It is a pointwise linear-algebra construction. No Jacobi
identity, manifold, differential equation, trajectory, or physical bath is
constructed here. In particular, the flow is zero when `h = 0`, even though
the dissipative operator need not be zero.
-/

noncomputable section

namespace InfoGeometry.Thermo.GenericReservoirLift

open GenericMetriplecticFlow

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Include mechanical directions in the extended state space. -/
def mechanicalInclusion : V →ₗ[ℝ] V × ℝ :=
  LinearMap.inl ℝ V ℝ

/-- The actual entropy covector on the added real coordinate. -/
def entropyCovector : Covector (V × ℝ) :=
  LinearMap.snd ℝ V ℝ

/-- The extended energy covector is `(v, s) ↦ h v + T * s`. -/
def energyCovector (h : Covector V) (T : ℝ) : Covector (V × ℝ) :=
  h.comp (LinearMap.fst ℝ V ℝ) + T • entropyCovector

/-- Lift a mechanical direction so its extended energy evaluation is zero. -/
def energyTangentLift (h : Covector V) (T : ℝ) : V →ₗ[ℝ] V × ℝ :=
  (LinearMap.id : V →ₗ[ℝ] V).prod ((-T⁻¹) • h)

@[simp] theorem energyTangentLift_apply (h : Covector V) (T : ℝ) (v : V) :
    energyTangentLift h T v = (v, -T⁻¹ * h v) := rfl

theorem entropyCovector_ne_zero : (entropyCovector : Covector (V × ℝ)) ≠ 0 := by
  intro hz
  have hv := congrArg (fun α : Covector (V × ℝ) => α (0, 1)) hz
  change (1 : ℝ) = 0 at hv
  exact one_ne_zero hv

theorem energyCovector_ne_zero (h : Covector V) (T : ℝ) (hT : T ≠ 0) :
    energyCovector h T ≠ 0 := by
  intro hz
  have hv := congrArg (fun α : Covector (V × ℝ) => α (0, 1)) hz
  change h 0 + T * 1 = 0 at hv
  exact hT (by simpa using hv)

@[simp] theorem mechanicalInclusion_dual_energy (h : Covector V) (T : ℝ) :
    (mechanicalInclusion : V →ₗ[ℝ] V × ℝ).dualMap (energyCovector h T) = h := by
  ext v
  change h v + T * 0 = h v
  ring

@[simp] theorem mechanicalInclusion_dual_entropy :
    (mechanicalInclusion : V →ₗ[ℝ] V × ℝ).dualMap entropyCovector = 0 := by
  ext v
  rfl

@[simp] theorem energyTangentLift_dual_entropy (h : Covector V) (T : ℝ) :
    (energyTangentLift h T).dualMap entropyCovector = (-T⁻¹) • h := by
  ext v
  rfl

/-- The key degeneracy is computed on the actual pullback covector. -/
theorem energyTangentLift_dual_energy (h : Covector V) (T : ℝ) (hT : T ≠ 0) :
    (energyTangentLift h T).dualMap (energyCovector h T) = 0 := by
  ext v
  change h v + T * (-T⁻¹ * h v) = 0
  calc
    h v + T * (-T⁻¹ * h v) = (1 - T * T⁻¹) * h v := by ring
    _ = 0 := by rw [mul_inv_cancel₀ hT]; ring

/-- Lift the full reversible operator by the mechanical inclusion. -/
def liftedReversible (L : Covector V →ₗ[ℝ] V) :
    Covector (V × ℝ) →ₗ[ℝ] V × ℝ :=
  mechanicalInclusion.comp (L.comp mechanicalInclusion.dualMap)

/-- Lift the full mobility by congruence and the positive factor `T⁻¹`. -/
def liftedDissipative (h : Covector V) (T : ℝ) (D : Covector V →ₗ[ℝ] V) :
    Covector (V × ℝ) →ₗ[ℝ] V × ℝ :=
  T⁻¹ • ((energyTangentLift h T).comp (D.comp (energyTangentLift h T).dualMap))

theorem liftedReversible_skew (L : Covector V →ₗ[ℝ] V)
    (hL : ∀ α β : Covector V, α (L β) = -β (L α))
    (α β : Covector (V × ℝ)) :
    α (liftedReversible L β) = -β (liftedReversible L α) := by
  exact hL (mechanicalInclusion.dualMap α) (mechanicalInclusion.dualMap β)

@[simp] theorem liftedReversible_entropy (L : Covector V →ₗ[ℝ] V) :
    liftedReversible L entropyCovector = 0 := by
  change mechanicalInclusion (L (mechanicalInclusion.dualMap entropyCovector)) = 0
  rw [mechanicalInclusion_dual_entropy, map_zero, map_zero]

@[simp] theorem liftedReversible_energy (L : Covector V →ₗ[ℝ] V)
    (h : Covector V) (T : ℝ) :
    liftedReversible L (energyCovector h T) = (L h, 0) := by
  change mechanicalInclusion (L (mechanicalInclusion.dualMap (energyCovector h T))) = _
  rw [mechanicalInclusion_dual_energy]
  rfl

/-- Evaluation on arbitrary covectors retains all operator entries. -/
theorem liftedDissipative_pairing (h : Covector V) (T : ℝ)
    (D : Covector V →ₗ[ℝ] V) (α β : Covector (V × ℝ)) :
    α (liftedDissipative h T D β) =
      T⁻¹ * ((energyTangentLift h T).dualMap α)
        (D ((energyTangentLift h T).dualMap β)) := by
  change α (T⁻¹ • energyTangentLift h T (D ((energyTangentLift h T).dualMap β))) = _
  rw [map_smul]
  rfl

theorem liftedDissipative_symmetric (h : Covector V) (T : ℝ)
    (D : Covector V →ₗ[ℝ] V)
    (hD : ∀ α β : Covector V, α (D β) = β (D α))
    (α β : Covector (V × ℝ)) :
    α (liftedDissipative h T D β) = β (liftedDissipative h T D α) := by
  rw [liftedDissipative_pairing, liftedDissipative_pairing, hD]

theorem liftedDissipative_nonneg (h : Covector V) (T : ℝ) (hT : 0 ≤ T)
    (D : Covector V →ₗ[ℝ] V) (hD : ∀ α : Covector V, 0 ≤ α (D α))
    (α : Covector (V × ℝ)) :
    0 ≤ α (liftedDissipative h T D α) := by
  rw [liftedDissipative_pairing]
  exact mul_nonneg (inv_nonneg.mpr hT) (hD _)

theorem liftedDissipative_energy (h : Covector V) (T : ℝ) (hT : T ≠ 0)
    (D : Covector V →ₗ[ℝ] V) :
    liftedDissipative h T D (energyCovector h T) = 0 := by
  change T⁻¹ • energyTangentLift h T
    (D ((energyTangentLift h T).dualMap (energyCovector h T))) = 0
  rw [energyTangentLift_dual_energy h T hT, map_zero, map_zero, smul_zero]

/-- Both output blocks for an arbitrary extended covector. -/
theorem liftedDissipative_apply (h : Covector V) (T : ℝ)
    (D : Covector V →ₗ[ℝ] V) (α : Covector (V × ℝ)) :
    liftedDissipative h T D α =
      (T⁻¹ • D ((energyTangentLift h T).dualMap α),
        -((T⁻¹) ^ 2) * h (D ((energyTangentLift h T).dualMap α))) := by
  apply Prod.ext
  · rfl
  · change T⁻¹ * (-T⁻¹ * h (D ((energyTangentLift h T).dualMap α))) = _
    ring

/-- The kernel is inherited from `D` through the actual pullback map. -/
theorem liftedDissipative_eq_zero_iff (h : Covector V) (T : ℝ) (hT : T ≠ 0)
    (D : Covector V →ₗ[ℝ] V) (α : Covector (V × ℝ)) :
    liftedDissipative h T D α = 0 ↔
      D ((energyTangentLift h T).dualMap α) = 0 := by
  constructor
  · intro hz
    have hf := congrArg Prod.fst hz
    change T⁻¹ • D ((energyTangentLift h T).dualMap α) = 0 at hf
    have hv := congrArg (fun v : V => T • v) hf
    simpa only [smul_smul, mul_inv_cancel₀ hT, one_smul, smul_zero] using hv
  · intro hz
    change T⁻¹ • energyTangentLift h T (D ((energyTangentLift h T).dualMap α)) = 0
    rw [hz, map_zero, smul_zero]

theorem liftedDissipative_entropy (h : Covector V) (T : ℝ)
    (D : Covector V →ₗ[ℝ] V) :
    liftedDissipative h T D entropyCovector =
      (-((T⁻¹) ^ 2) • D h, (T⁻¹) ^ 3 * h (D h)) := by
  change T⁻¹ • energyTangentLift h T
    (D ((energyTangentLift h T).dualMap entropyCovector)) = _
  rw [energyTangentLift_dual_entropy, map_smul, map_smul, smul_smul]
  apply Prod.ext
  · change (T⁻¹ * -T⁻¹) • D h = -((T⁻¹) ^ 2) • D h
    congr 1
    ring
  · change (T⁻¹ * -T⁻¹) * (-T⁻¹ * h (D h)) = (T⁻¹) ^ 3 * h (D h)
    ring

/-- Construct every GENERIC law from the original operators and `T > 0`. -/
def system (h : Covector V) (T : ℝ) (hT : 0 < T)
    (L D : Covector V →ₗ[ℝ] V)
    (hL : ∀ α β : Covector V, α (L β) = -β (L α))
    (hDsymm : ∀ α β : Covector V, α (D β) = β (D α))
    (hDpos : ∀ α : Covector V, 0 ≤ α (D α)) : System (V × ℝ) where
  dH := energyCovector h T
  dS := entropyCovector
  L := liftedReversible L
  M := liftedDissipative h T D
  L_skew := liftedReversible_skew L hL
  L_entropy_casimir := liftedReversible_entropy L
  M_symmetric := liftedDissipative_symmetric h T D hDsymm
  M_hamiltonian_casimir := liftedDissipative_energy h T (ne_of_gt hT) D
  M_nonneg := liftedDissipative_nonneg h T hT.le D hDpos

section Flow

variable (h : Covector V) (T : ℝ) (hT : 0 < T)
  (L D : Covector V →ₗ[ℝ] V)
  (hL : ∀ α β : Covector V, α (L β) = -β (L α))
  (hDsymm : ∀ α β : Covector V, α (D β) = β (D α))
  (hDpos : ∀ α : Covector V, 0 ≤ α (D α))

/-- The two components are computed from the constructed `System.flow`. -/
theorem system_flow :
    (system h T hT L D hL hDsymm hDpos).flow =
      (L h - (T⁻¹) ^ 2 • D h, (T⁻¹) ^ 3 * h (D h)) := by
  change liftedReversible L (energyCovector h T) +
    liftedDissipative h T D entropyCovector = _
  rw [liftedReversible_energy, liftedDissipative_entropy]
  apply Prod.ext
  · change L h + -((T⁻¹) ^ 2) • D h = L h - (T⁻¹) ^ 2 • D h
    rw [neg_smul, sub_eq_add_neg]
  · exact zero_add _

/-- The entropy rate is the base quadratic dissipation scaled by `T⁻³`. -/
theorem system_entropy_rate :
    (system h T hT L D hL hDsymm hDpos).dS
      (system h T hT L D hL hDsymm hDpos).flow =
        (T⁻¹) ^ 3 * h (D h) := by
  change entropyCovector (system h T hT L D hL hDsymm hDpos).flow = _
  rw [system_flow]
  rfl

/-- This is a pointwise evaluation on the mechanical component of the flow. -/
theorem system_mechanical_energy_rate :
    h (system h T hT L D hL hDsymm hDpos).flow.1 =
      -((T⁻¹) ^ 2) * h (D h) := by
  have hdiag : h (L h) = 0 := by
    have hh := hL h h
    linarith
  rw [system_flow]
  change h (L h - (T⁻¹) ^ 2 • D h) = _
  rw [map_sub, map_smul, hdiag]
  change 0 - (T⁻¹) ^ 2 * h (D h) = -((T⁻¹) ^ 2) * h (D h)
  ring

/-- A nonzero entropy covector does not force nonzero flow or production. -/
theorem system_flow_zero_of_energy_zero (hh : h = 0) :
    (system h T hT L D hL hDsymm hDpos).flow = 0 := by
  rw [system_flow, hh]
  simp

end Flow

section BilinearReduction

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- An existing bilinear reduction lifts by composing its original image map
with `energyTangentLift`; no second dual identification is introduced. -/
theorem liftedDissipative_reducedSharp (h : Covector V) (T : ℝ)
    (B : LinearMap.BilinForm ℝ W) (hB : B.Nondegenerate) (C : W →ₗ[ℝ] V) :
    liftedDissipative h T (BilinearMetriplecticReduction.reducedSharp B hB C) =
      T⁻¹ • BilinearMetriplecticReduction.reducedSharp B hB
        ((energyTangentLift h T).comp C) := by
  apply LinearMap.ext
  intro α
  rfl

end BilinearReduction

end InfoGeometry.Thermo.GenericReservoirLift
