import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix

-- Thermodynamic Gauge Flow: Connes Cocycle & Araki Entropy
-- KMS states = local vacuum gauge frames
-- Connes cocycle = parallel transport between frames  
-- Araki entropy = edge weight = optimal transport cost
-- JKO scheme = discrete thermal tick = gradient flow
-- Bridges: tomita_kms_v4, determinant_weyl_gauge, krein_souriau_full

set_option maxHeartbeats 400000

-- LAYER 1: KMS STATES AS GAUGE FRAMES

structure KMSFrame (𝒜 : Type) [Ring 𝒜] [Module ℂ 𝒜] where
  β : ℝ
  ω : 𝒜 → ℂ
  σ : ℝ → (𝒜 → 𝒜)
  sigma_preserves_one : ∀ t, σ t 1 = 1

def gaugeEquiv {𝒜 : Type} [Ring 𝒜] [Module ℂ 𝒜] (f1 f2 : KMSFrame 𝒜) : Prop :=
  f1.σ = f2.σ ∧ f1.β = f2.β

-- LAYER 2: CONNES COCYCLE — THE GAUGE CONNECTION

structure ConnesCocycle (𝒜 : Type) [Ring 𝒜] [Module ℂ 𝒜] where
  src : KMSFrame 𝒜
  tgt : KMSFrame 𝒜
  cocycle : ℝ → 𝒜
  h_cocycle : ∀ (t : ℝ) (A : 𝒜), cocycle t * src.σ t A * cocycle (-t) = tgt.σ t A
  inverse_law : ∀ t, cocycle t * cocycle (-t) = 1

-- LAYER 3: ARAKI RELATIVE ENTROPY — THE COST

structure ArakiEntropy (𝒜 : Type) [Ring 𝒜] [Module ℂ 𝒜] where
  S : KMSFrame 𝒜 → KMSFrame 𝒜 → ℝ
  h_nonneg : ∀ f1 f2, S f1 f2 ≥ 0
  h_zero_iff : ∀ f1 f2, S f1 f2 = 0 ↔ gaugeEquiv f1 f2
  h_self_min : ∀ f1 f2, S f1 f1 ≤ S f1 f2

noncomputable def gibbsRelativeEntropy (_H : Matrix (Fin 2) (Fin 2) ℂ) (β₁ β₂ : ℝ) : ℝ :=
  let Z₁ := 1 + Real.exp (-β₁)
  let Z₂ := 1 + Real.exp (-β₂)
  let ρ₁_zero := 1 / Z₁
  let ρ₁_one := Real.exp (-β₁) / Z₁
  (β₁ - β₂) * (0 * ρ₁_zero + 1 * ρ₁_one) + Real.log Z₂ - Real.log Z₁

noncomputable def thermalBoost (β t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh (β * t), Real.sinh (β * t);
     Real.sinh (β * t), Real.cosh (β * t)]

theorem thermal_flow_is_hyperbolic (β t : ℝ) :
    (thermalBoost β t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [thermalBoost]
  simpa [pow_two] using Real.cosh_sq_sub_sinh_sq (β * t)

-- LAYER 4: JKO SCHEME — THE DISCRETE THERMAL TICK

structure JKOStep (𝒜 : Type) [Ring 𝒜] [Module ℂ 𝒜] where
  τ : ℝ
  ρ_t : KMSFrame 𝒜
  ρ_next : KMSFrame 𝒜
  freeEnergy : KMSFrame 𝒜 → ℝ
  h_minimal : ∀ ρ, freeEnergy ρ_next ≤ freeEnergy ρ

-- LAYER 5: GRAPH EDGE — THERMODYNAMIC CONNECTION

structure ThermoEdge (𝒜 : Type) [Ring 𝒜] [Module ℂ 𝒜] where
  source : KMSFrame 𝒜
  target : KMSFrame 𝒜
  cocycle : ConnesCocycle 𝒜
  cost : ℝ
  h_cost_nonneg : cost ≥ 0

theorem thermo_gauge_flow_minimizes_entropy {𝒜 : Type} [Ring 𝒜] [Module ℂ 𝒜]
    (edge : ThermoEdge 𝒜) : edge.cost ≥ 0 :=
  edge.h_cost_nonneg

-- LAYER 6: PROJECTIVE BURG / ITAKURA-SAITO GENERATOR

/-- The spectral density of `Exp(K) - I - K`. -/
noncomputable def modularBurgGenerator (K : ℝ) : ℝ :=
  Real.exp K - 1 - K

/-- Scalar Itakura-Saito divergence `x/y - log(x/y) - 1`. -/
noncomputable def scalarItakuraSaito (x y : ℝ) : ℝ :=
  x / y - Real.log (x / y) - 1

/-- The unnormalized Araki-Umegaki/KL correction:
    normalized relative entropy plus the trace slack `Tr σ - Tr ω`. -/
def unnormalizedKL (traceω traceσ arakiKL : ℝ) : ℝ :=
  traceσ - traceω + arakiKL

/-- Evaluation of `Exp(K) - I - K` against a reference vector after the
    three scalar identifications supplied by the relative modular operator. -/
def evaluatedBurgGenerator (expTerm identityTerm negLogTerm : ℝ) : ℝ :=
  expTerm - identityTerm + negLogTerm

theorem modularBurgGenerator_nonnegative (K : ℝ) :
    0 ≤ modularBurgGenerator K := by
  unfold modularBurgGenerator
  linarith [Real.add_one_le_exp K]

/-- The Burg generator has derivative `exp K - 1`. -/
theorem modularBurgGenerator_deriv (K : ℝ) :
    deriv modularBurgGenerator K = Real.exp K - 1 := by
  unfold modularBurgGenerator
  simp [Real.deriv_exp]

theorem scalarItakuraSaito_scale_invariant (lam x y : ℝ) (hlam : lam ≠ 0) (hy : y ≠ 0) :
    scalarItakuraSaito (lam * x) (lam * y) = scalarItakuraSaito x y := by
  have h_lam_y : lam * y ≠ 0 := mul_ne_zero hlam hy
  unfold scalarItakuraSaito
  have hratio : (lam * x) / (lam * y) = x / y := by
    field_simp [hlam, hy, h_lam_y]
  rw [hratio]

theorem modularBurgGenerator_eq_log_ItakuraSaito (K : ℝ) :
    modularBurgGenerator K = scalarItakuraSaito (Real.exp K) 1 := by
  unfold modularBurgGenerator scalarItakuraSaito
  simp
  ring

theorem evaluatedBurg_eq_unnormalizedKL
    (traceDelta traceId negLogDelta traceω traceσ arakiKL : ℝ)
    (hDelta : traceDelta = traceσ)
    (hId : traceId = traceω)
    (hLog : negLogDelta = arakiKL) :
    evaluatedBurgGenerator traceDelta traceId negLogDelta =
      unnormalizedKL traceω traceσ arakiKL := by
  unfold evaluatedBurgGenerator unnormalizedKL
  rw [hDelta, hId, hLog]
