import InfoGeometry.Canonical.NavierStokesBridge
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Canonical.GrandCanonicalExperts

open scoped BigOperators

namespace InfoGeometry.Canonical.MoE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Arnold-Majorana Network:
A specialized MoE layer where experts operate on the doubled `ArnoldMajoranaCarrier`.
- Experts: `Experts (ArnoldMajoranaCarrier E)`
- Input: `ArnoldMajoranaCarrier E`
- Output: `ArnoldMajoranaCarrier E`
-/
structure ArnoldMajoranaNetwork (n : Nat) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] where
  moe : MoELayer n (ArnoldMajoranaCarrier E)

/--
Canonical Arnold-Majorana routing energy:
The energy depends on the Clifford norm on the doubled space.
-/
def arnoldRoutingEnergy (n : Nat) {Tok : Type*} [Fintype Tok] (x : Tok → ArnoldMajoranaCarrier E) (i : Tok) (e : ExpertIdx n) : ℝ :=
  -- Physics-informed energy: depends on the doubled-space norm
  ‖x i‖ + ((e : ℕ) : ℝ)

/--
Normalized output of an Arnold-Majorana network layer.
This realizes the "context-adaptive" flow in a thermodynamic expert setting.
-/
noncomputable def arnoldNetworkOutput (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ) {Tok : Type*} [Fintype Tok] [DecidableEq Tok] (x : Tok → ArnoldMajoranaCarrier E) (i : Tok) : ArnoldMajoranaCarrier E :=
  let experts := net.moe.experts
  -- We reuse the MoE normalized weight logic
  ∑ e : ExpertIdx n,
    (normalizedWeights n β x i e) • (experts e).apply (x i)

/--
Theorem: The Arnold-Majorana network preserves the subspace of base states
if all experts do.
-/
theorem arnoldNetwork_preserves_base (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ) {Tok : Type*} [Fintype Tok] [DecidableEq Tok] (x : Tok → ArnoldMajoranaCarrier E) (i : Tok)
    (hBase : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E, v.2 = 0 → ((net.moe.experts e).apply v).2 = 0)
    (hx : (x i).2 = 0) :
    (arnoldNetworkOutput n net β x i).2 = 0 := by
  unfold arnoldNetworkOutput
  simp [Prod.snd_sum]
  refine Finset.sum_eq_zero ?_
  intro e _
  simp [hBase e (x i) hx]

end InfoGeometry.Canonical.MoE
