import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace ConnesTomita

open InfoGeometry.OperatorAlgebra.OperatorThermodynamics

/-- The modular-flow carrier is owned by `OperatorThermodynamics.OperatorFlow`. -/
abbrev ModularAutomorphism (M : Type*) [Monoid M] := OperatorFlow M

namespace ModularAutomorphism

variable {M : Type*} [Monoid M] (mod : ModularAutomorphism M)

theorem modular_flow_comp (t1 t2 : ℝ) (A : M) :
    mod.flow (t1 + t2) A = mod.flow t1 (mod.flow t2 A) :=
  OperatorFlow.flow_add_apply mod t1 t2 A

theorem modular_flow_id (A : M) :
    mod.flow 0 A = A :=
  OperatorFlow.flow_zero_apply mod A

/-- Unit-valued Connes cocycles for an owned modular flow.

The action on units is the canonical `Units.map` lift of the multiplicative
automorphism; the law is the noncommutative cocycle law, not an equality of
scalar readouts. -/
def RadonNikodymCocycle (M : Type*) [Monoid M] :=
  ∀ (mod : ModularAutomorphism M) (t1 t2 : ℝ) (u : ℝ → Mˣ),
    u (t1 + t2) = Units.map (mod.flow t1).toMonoidHom (u t2) * u t1

theorem cocycle_chain_rule
    {M : Type*} [Monoid M]
    (c : RadonNikodymCocycle M) (u : ℝ → Mˣ)
    (mod : ModularAutomorphism M) (t1 t2 : ℝ) :
    u (t1 + t2) = Units.map (mod.flow t1).toMonoidHom (u t2) * u t1 :=
  c mod t1 t2 u

end ModularAutomorphism

end ConnesTomita
