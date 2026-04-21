import Mathlib
import Mathlib



import Mathlib

namespace InfoGeometry.Hypothesis

structure BifurcatingSystem (E : Type u) [AddCommGroup E] [Module ℝ E] where
  dissipation : E → ℝ
  flow : ℝ → E → E
  projection : E →ₗ[ℝ] E
  projection_idem : projection.comp projection = projection
  diss_nonneg : ∀ x, 0 ≤ dissipation x

def memory {E : Type u} [AddCommGroup E] [Module ℝ E]
    (S : BifurcatingSystem E) : Submodule ℝ E :=
  LinearMap.range S.projection

def dissipativeLane {E : Type u} [AddCommGroup E] [Module ℝ E]
    (S : BifurcatingSystem E) : Submodule ℝ E :=
  LinearMap.ker S.projection

structure IsMature {E : Type u} [AddCommGroup E] [Module ℝ E]
    (S : BifurcatingSystem E) : Prop where
  memory_zero :
    ∀ x ∈ memory S, S.dissipation x = 0
  memory_fixed :
    ∀ x ∈ memory S, ∀ t : ℝ, S.flow t x = x
  dissipative_positive :
    ∀ x ∈ dissipativeLane S, x ≠ 0 → 0 < S.dissipation x
  split :
    ∀ x : E, x = S.projection x + (x - S.projection x)

theorem mature_memory_has_zero_dissipation
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    {S : BifurcatingSystem E}
    (hS : IsMature S)
    {x : E}
    (hx : x ∈ memory S) :
    S.dissipation x = 0 :=
  hS.memory_zero x hx

theorem mature_memory_is_flow_fixed
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    {S : BifurcatingSystem E}
    (hS : IsMature S)
    {x : E}
    (hx : x ∈ memory S)
    (t : ℝ) :
    S.flow t x = x :=
  hS.memory_fixed x hx t

theorem mature_dissipative_lane_produces_entropy
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    {S : BifurcatingSystem E}
    (hS : IsMature S)
    {x : E}
    (hx : x ∈ dissipativeLane S)
    (hne : x ≠ 0) :
    0 < S.dissipation x :=
  hS.dissipative_positive x hx hne

end InfoGeometry.Hypothesis
