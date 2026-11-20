/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.GenericMetriplecticFlow

/-!
# Entropy-coordinate extension of a linear GENERIC system

Let `L : V* → V` be skew and `D : V* → V` symmetric positive semidefinite.
For an energy covector `h` and a positive temperature `T`, adjoin one real
entropy coordinate.  The graph map `C v = (v, -h v / T)` annihilates the total
energy covector `dH (v,s) = h v + T*s`.  Congruence by `C`, rather than division
by the squared energy-gradient norm, constructs the dissipative operator
`M = T⁻¹ C D C*`.  It remains defined at `h = 0`.

The construction uses arbitrary real modules and actual covector-to-vector
operators.  No inner product, finite dimension, invertibility of `D`, or
commutation of `D` and `L` is assumed.  A bilinear Gram form must first be
converted to such an operator using an explicit duality.

These are pointwise linear GENERIC laws in the existing `System` interface.
They do not construct a contact structure, a state-dependent Poisson bracket
with Jacobi identity, or global solutions of an evolution equation.  The
temperature inverses are explicit; only energy-gradient denominators are absent.
-/

noncomputable section

namespace InfoGeometry.Thermo.GenericEntropyExtension

open GenericMetriplecticFlow

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Inclusion of the original state space at zero entropy coordinate. -/
def phaseInclusion : V →ₗ[ℝ] V × ℝ :=
  LinearMap.inl ℝ V ℝ

/-- The differential of the adjoined entropy coordinate. -/
def entropyCovector : Covector (V × ℝ) :=
  LinearMap.snd ℝ V ℝ

/-- Total energy differential for energy `H₀(z) + T*s`. -/
def energyCovector (h : Covector V) (T : ℝ) : Covector (V × ℝ) :=
  h.comp (LinearMap.fst ℝ V ℝ) + T • entropyCovector

/-- Graph inclusion into the kernel of the total energy covector. -/
def energyLift (h : Covector V) (T : ℝ) : V →ₗ[ℝ] V × ℝ :=
  (LinearMap.id : V →ₗ[ℝ] V).prod ((-T⁻¹) • h)

@[simp] theorem phaseInclusion_apply (v : V) :
    phaseInclusion v = (v, 0) := rfl

@[simp] theorem entropyCovector_apply (v : V × ℝ) :
    entropyCovector v = v.2 := rfl

@[simp] theorem energyCovector_apply (h : Covector V) (T : ℝ) (v : V × ℝ) :
    energyCovector h T v = h v.1 + T * v.2 := rfl

@[simp] theorem energyLift_apply (h : Covector V) (T : ℝ) (v : V) :
    energyLift h T v = (v, (-T⁻¹) * h v) := rfl

/-- Covectors on the product split into their horizontal and entropy parts. -/
theorem covector_apply_prod (α : Covector (V × ℝ)) (v : V) (s : ℝ) :
    α (v, s) = α (v, 0) + s * α (0, 1) := by
  have hvs : (v, s) = (v, 0) + s • (0, 1) := by
    apply Prod.ext <;> simp
  simpa only [map_add, map_smul, smul_eq_mul] using congrArg α hvs

/-- The entropy differential is nonzero, including at critical points of `H₀`. -/
theorem entropyCovector_ne_zero : (entropyCovector : Covector (V × ℝ)) ≠ 0 := by
  intro h
  have he := congrArg (fun α : Covector (V × ℝ) => α (0, 1)) h
  norm_num [entropyCovector] at he

@[simp] theorem phaseInclusion_dual_entropy :
    (phaseInclusion : V →ₗ[ℝ] V × ℝ).dualMap entropyCovector = 0 := by
  ext v
  rfl

@[simp] theorem phaseInclusion_dual_energy (h : Covector V) (T : ℝ) :
    phaseInclusion.dualMap (energyCovector h T) = h := by
  ext v
  simp [LinearMap.dualMap_apply]

/-- The pulled-back entropy covector is `-h/T`. -/
@[simp] theorem energyLift_dual_entropy (h : Covector V) (T : ℝ) :
    (energyLift h T).dualMap entropyCovector = (-T⁻¹) • h := by
  ext v
  rfl

/-- The graph map kills the total energy differential, without dividing by `h`. -/
theorem energyLift_dual_energy (h : Covector V) (T : ℝ) (hT : T ≠ 0) :
    (energyLift h T).dualMap (energyCovector h T) = 0 := by
  ext v
  change h v + T * ((-T⁻¹) * h v) = 0
  field_simp [hT]
  <;> ring

/-- The full pullback formula gives the off-diagonal blocks of the friction operator. -/
theorem energyLift_dual_eq (h : Covector V) (T : ℝ)
    (α : Covector (V × ℝ)) :
    (energyLift h T).dualMap α =
      phaseInclusion.dualMap α - (T⁻¹ * α (0, 1)) • h := by
  ext v
  change α (v, (-T⁻¹) * h v) = α (v, 0) - (T⁻¹ * α (0, 1)) * h v
  rw [covector_apply_prod]
  ring

/-- The graph lift has no singularity when the original energy differential is zero. -/
@[simp] theorem energyLift_zero (T : ℝ) :
    energyLift (0 : Covector V) T = phaseInclusion := by
  ext v <;> simp [energyLift, phaseInclusion]

/-- The original reversible operator extended by a zero entropy row and column. -/
def reversible (L : Covector V →ₗ[ℝ] V) : Covector (V × ℝ) →ₗ[ℝ] V × ℝ :=
  phaseInclusion.comp (L.comp phaseInclusion.dualMap)

/-- Energy-conserving congruence of an arbitrary, possibly singular mobility. -/
def dissipative (D : Covector V →ₗ[ℝ] V) (h : Covector V) (T : ℝ) :
    Covector (V × ℝ) →ₗ[ℝ] V × ℝ :=
  T⁻¹ • (energyLift h T).comp (D.comp (energyLift h T).dualMap)

theorem reversible_pairing (L : Covector V →ₗ[ℝ] V)
    (α β : Covector (V × ℝ)) :
    α (reversible L β) =
      phaseInclusion.dualMap α (L (phaseInclusion.dualMap β)) := rfl

theorem reversible_skew (L : Covector V →ₗ[ℝ] V)
    (hL : ∀ α β, α (L β) = -β (L α)) (α β : Covector (V × ℝ)) :
    α (reversible L β) = -β (reversible L α) := by
  rw [reversible_pairing, reversible_pairing, hL]

@[simp] theorem reversible_entropy (L : Covector V →ₗ[ℝ] V) :
    reversible L entropyCovector = 0 := by
  simp [reversible]

@[simp] theorem reversible_energy (L : Covector V →ₗ[ℝ] V)
    (h : Covector V) (T : ℝ) :
    reversible L (energyCovector h T) = (L h, 0) := by
  simp [reversible]

/-- The dissipative quadratic form is the pullback of the original positive form. -/
theorem dissipative_pairing (D : Covector V →ₗ[ℝ] V) (h : Covector V) (T : ℝ)
    (α β : Covector (V × ℝ)) :
    α (dissipative D h T β) =
      T⁻¹ * (energyLift h T).dualMap α (D ((energyLift h T).dualMap β)) := by
  change α (T⁻¹ • energyLift h T (D ((energyLift h T).dualMap β))) = _
  exact map_smul α T⁻¹ (energyLift h T (D ((energyLift h T).dualMap β)))

theorem dissipative_symmetric (D : Covector V →ₗ[ℝ] V)
    (hD : ∀ α β, α (D β) = β (D α)) (h : Covector V) (T : ℝ)
    (α β : Covector (V × ℝ)) :
    α (dissipative D h T β) = β (dissipative D h T α) := by
  rw [dissipative_pairing, dissipative_pairing, hD]

theorem dissipative_nonneg (D : Covector V →ₗ[ℝ] V)
    (hD : ∀ α, 0 ≤ α (D α)) (h : Covector V) (T : ℝ) (hT : 0 ≤ T)
    (α : Covector (V × ℝ)) : 0 ≤ α (dissipative D h T α) := by
  rw [dissipative_pairing]
  exact mul_nonneg (inv_nonneg.mpr hT) (hD _)

theorem dissipative_energy (D : Covector V →ₗ[ℝ] V) (h : Covector V)
    (T : ℝ) (hT : T ≠ 0) : dissipative D h T (energyCovector h T) = 0 := by
  simp [dissipative, energyLift_dual_energy h T hT]

/-- Exact kernel of the friction operator; singular mobility is allowed. -/
theorem dissipative_eq_zero_iff (D : Covector V →ₗ[ℝ] V) (h : Covector V)
    (T : ℝ) (hT : T ≠ 0) (α : Covector (V × ℝ)) :
    dissipative D h T α = 0 ↔ D ((energyLift h T).dualMap α) = 0 := by
  constructor
  · intro hz
    have hf : T⁻¹ • D ((energyLift h T).dualMap α) = 0 :=
      congrArg Prod.fst hz
    exact (smul_eq_zero.mp hf).resolve_left (inv_ne_zero hT)
  · intro hz
    simp [dissipative, hz]

/-- Both components of the entropy-driven dissipative velocity are explicit. -/
theorem dissipative_entropy (D : Covector V →ₗ[ℝ] V) (h : Covector V) (T : ℝ) :
    dissipative D h T entropyCovector =
      (-(T⁻¹ ^ 2) • D h, T⁻¹ ^ 3 * h (D h)) := by
  apply Prod.ext
  · change T⁻¹ • D ((energyLift h T).dualMap entropyCovector) = -(T⁻¹ ^ 2) • D h
    rw [energyLift_dual_entropy, map_smul, smul_smul]
    congr 1
    ring
  · change T⁻¹ * ((-T⁻¹) * h (D ((energyLift h T).dualMap entropyCovector))) = _
    rw [energyLift_dual_entropy, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring

theorem dissipative_entropy_rate (D : Covector V →ₗ[ℝ] V)
    (h : Covector V) (T : ℝ) :
    entropyCovector (dissipative D h T entropyCovector) = T⁻¹ ^ 3 * h (D h) := by
  exact congrArg Prod.snd (dissipative_entropy D h T)

/-- At an energy critical point the operator is still defined on all covectors. -/
theorem dissipative_at_critical (D : Covector V →ₗ[ℝ] V) (T : ℝ)
    (α : Covector (V × ℝ)) :
    dissipative D 0 T α = (T⁻¹ • D (phaseInclusion.dualMap α), 0) := by
  simp [dissipative]

/-- Vanishing horizontal restriction is exactly membership in the entropy line. -/
theorem phaseInclusion_dual_eq_zero_iff (α : Covector (V × ℝ)) :
    phaseInclusion.dualMap α = 0 ↔ α = α (0, 1) • entropyCovector := by
  constructor
  · intro hz
    ext v
    rcases v with ⟨v, s⟩
    have hh : α (v, 0) = 0 := congrArg (fun β : Covector V => β v) hz
    change α (v, s) = α (0, 1) * s
    rw [covector_apply_prod, hh]
    ring
  · intro hα
    rw [hα, map_smul, phaseInclusion_dual_entropy, smul_zero]

/-- An injective original reversible operator acquires exactly one Casimir direction. -/
theorem reversible_eq_zero_iff (L : Covector V →ₗ[ℝ] V)
    (hL : Function.Injective L) (α : Covector (V × ℝ)) :
    reversible L α = 0 ↔ α = α (0, 1) • entropyCovector := by
  rw [← phaseInclusion_dual_eq_zero_iff]
  constructor
  · intro hz
    have hh : L (phaseInclusion.dualMap α) = 0 := congrArg Prod.fst hz
    exact hL (hh.trans (map_zero L).symm)
  · intro hz
    simp [reversible, hz]

/-- Native submodule characterization of the reversible kernel. -/
theorem reversible_kernel (L : Covector V →ₗ[ℝ] V) (hL : Function.Injective L) :
    LinearMap.ker (reversible L) =
      Submodule.span ℝ {(entropyCovector : Covector (V × ℝ))} := by
  ext α
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hα
    exact ⟨α (0, 1), ((reversible_eq_zero_iff L hL α).mp hα).symm⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, reversible_entropy, smul_zero]

/-- A constructed GENERIC system on the entropy-extended carrier. -/
def system (L D : Covector V →ₗ[ℝ] V) (h : Covector V) (T : ℝ)
    (hT : 0 < T) (hL : ∀ α β, α (L β) = -β (L α))
    (hD : ∀ α β, α (D β) = β (D α)) (hpos : ∀ α, 0 ≤ α (D α)) :
    System (V × ℝ) where
  dH := energyCovector h T
  dS := entropyCovector
  L := reversible L
  M := dissipative D h T
  L_skew := reversible_skew L hL
  L_entropy_casimir := reversible_entropy L
  M_symmetric := dissipative_symmetric D hD h T
  M_hamiltonian_casimir := dissipative_energy D h T (ne_of_gt hT)
  M_nonneg := dissipative_nonneg D hpos h T hT.le

variable (L D : Covector V →ₗ[ℝ] V) (h : Covector V) (T : ℝ)
  (hT : 0 < T) (hL : ∀ α β, α (L β) = -β (L α))
  (hD : ∀ α β, α (D β) = β (D α)) (hpos : ∀ α, 0 ≤ α (D α))

/-- The original energy decays while the added entropy coordinate compensates it. -/
theorem system_flow :
    (system L D h T hT hL hD hpos).flow =
      (L h - (T⁻¹ ^ 2) • D h, T⁻¹ ^ 3 * h (D h)) := by
  change reversible L (energyCovector h T) + dissipative D h T entropyCovector = _
  rw [reversible_energy, dissipative_entropy]
  apply Prod.ext <;> simp [sub_eq_add_neg]

/-- Exact decrease of the original energy, before the entropy compensation is added. -/
theorem system_base_energy_rate :
    h (system L D h T hT hL hD hpos).flow.1 = -(T⁻¹ ^ 2 * h (D h)) := by
  have hself : h (L h) = 0 := by
    have hh := hL h h
    linarith
  rw [system_flow]
  simp [hself, smul_eq_mul]

/-- Positivity of the mobility makes the original energy rate nonpositive. -/
theorem system_base_energy_rate_nonpos :
    h (system L D h T hT hL hD hpos).flow.1 ≤ 0 := by
  rw [system_base_energy_rate]
  exact neg_nonpos.mpr (mul_nonneg (sq_nonneg T⁻¹) (hpos h))

/-- Exact entropy production, with the temperature normalization retained. -/
theorem system_entropy_rate :
    (system L D h T hT hL hD hpos).dS
        (system L D h T hT hL hD hpos).flow = T⁻¹ ^ 3 * h (D h) := by
  rw [System.entropy_rate_eq_dissipative]
  exact dissipative_entropy_rate D h T

/-- Strict entropy production occurs precisely when the original quadratic response is positive. -/
theorem system_entropy_rate_pos_iff :
    0 < (system L D h T hT hL hD hpos).dS
        (system L D h T hT hL hD hpos).flow ↔ 0 < h (D h) := by
  rw [system_entropy_rate]
  exact mul_pos_iff_of_pos_left (pow_pos (inv_pos.mpr hT) 3)

/-- Critical points of `H₀` have zero full velocity in this constructed extension. -/
theorem system_flow_at_critical :
    (system L D 0 T hT hL hD hpos).flow = 0 := by
  rw [system_flow]
  simp

end InfoGeometry.Thermo.GenericEntropyExtension
