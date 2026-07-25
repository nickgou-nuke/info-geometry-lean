import Mathlib.Tactic
import InfoGeometry.External.Auto.GoutevTonevPrinciple

/-!
# Relative modular state readout and Dikin quadratic germ

This file formalizes the finite algebraic skeleton behind the state-functional
view of Tomita--Takesaki relative modular operators.

The analytic von Neumann data are not asserted here.  The proved content is the
canonical finite algebraic state/readout layer:

* a state is a linear functional `A →ₗ[ℂ] ℂ`;
* gauges are equations on `ω (OP - 1)`;
* the operator Bregman remainder `exp(εK)-1-εK` becomes a scalar only after
  applying `ω`;
* a Taylor split exposes the Dikin quadratic readout `(ε²/2) ω(K²)`.
-/

noncomputable section

namespace RelativeModularStateDikin

open GoutevTonevPrinciple

variable {A : Type*} [Ring A] [Star A] [Algebra ℂ A]

/-- Finite algebraic state data for a complex operator algebra. -/
structure AlgebraicStateData (A : Type*) [Ring A] [Star A] [Algebra ℂ A] where
  omega : OperatorLinearFunctional A
  normalized : omega 1 = 1
  positive : ∀ X : A, 0 ≤ (omega (star X * X)).re

namespace AlgebraicStateData

variable (Ω : AlgebraicStateData A)

/-- Gauge fixing around identity is just a linear-functional equation. -/
theorem gauge_sub_identity_iff (OP : A) (c : ℂ) :
    Ω.omega (OP - 1) = c ↔ Ω.omega OP = c + 1 := by
  rw [map_sub, Ω.normalized]
  constructor
  · intro h
    calc
      Ω.omega OP = (Ω.omega OP - 1) + 1 := by ring
      _ = c + 1 := by rw [h]
  · intro h
    calc
      Ω.omega OP - 1 = (c + 1) - 1 := by rw [h]
      _ = c := by ring

/-- The zero-centered gauge is the usual vacuum fluctuation condition. -/
theorem centered_identity_gauge_iff (OP : A) :
    Ω.omega (OP - 1) = 0 ↔ Ω.omega OP = 1 := by
  simpa using Ω.gauge_sub_identity_iff OP 0

end AlgebraicStateData

/-! ## Operator Bregman and quadratic Dikin readout -/

/-- Complex operator-level Bregman remainder `expOp(εK)-1-εK`.

Here `expOp` is explicit input data for the exponential/functional calculus. -/
def complexOperatorBregman (expOp : A → A) (ε : ℂ) (K : A) : A :=
  expOp (ε • K) - 1 - ε • K

/-- The quadratic Dikin/Taylor germ `(ε²/2)K²`. -/
def quadraticModularUnit (ε : ℂ) (K : A) : A :=
  (ε ^ 2 / 2 : ℂ) • (K * K)

/-- State readout of the operator Bregman remainder. -/
theorem state_readout_bregman
    (Ω : AlgebraicStateData A) (expOp : A → A) (ε : ℂ) (K : A) :
    Ω.omega (complexOperatorBregman (A := A) expOp ε K) =
      Ω.omega (expOp (ε • K)) - 1 - ε * Ω.omega K := by
  simp [complexOperatorBregman, map_sub, Ω.normalized, smul_eq_mul]

/-- If the modular generator is centered, the linear term vanishes after readout. -/
theorem centered_state_readout_bregman
    (Ω : AlgebraicStateData A) (expOp : A → A) (ε : ℂ) (K : A)
    (hK : Ω.omega K = 0) :
    Ω.omega (complexOperatorBregman (A := A) expOp ε K) =
      Ω.omega (expOp (ε • K)) - 1 := by
  rw [state_readout_bregman (Ω := Ω) expOp ε K, hK]
  ring

/-- State readout of the Dikin quadratic germ. -/
theorem quadratic_modular_readout
    (Ω : AlgebraicStateData A) (ε : ℂ) (K : A) :
    Ω.omega (quadraticModularUnit (A := A) ε K) =
      (ε ^ 2 / 2 : ℂ) * Ω.omega (K * K) := by
  simp [quadraticModularUnit, smul_eq_mul]

/-- If the exponential has a Taylor split through second order, the state readout
splits into the Dikin quadratic plus the readout of the higher remainder. -/
theorem taylor_split_readout
    (Ω : AlgebraicStateData A) (expOp : A → A) (ε : ℂ) (K R3 : A)
    (hTaylor :
      expOp (ε • K) = 1 + ε • K + quadraticModularUnit (A := A) ε K + R3) :
    Ω.omega (complexOperatorBregman (A := A) expOp ε K) =
      (ε ^ 2 / 2 : ℂ) * Ω.omega (K * K) + Ω.omega R3 := by
  rw [state_readout_bregman (Ω := Ω) expOp ε K, hTaylor]
  simp [map_add, quadratic_modular_readout (Ω := Ω), Ω.normalized, smul_eq_mul]
  ring

/-! ## Relative modular finite data -/

/-- Finite algebraic data for the relative modular operator `Delta` and
modular Hamiltonian `K`.

The field `taylor_split` is the finite algebraic replacement for analytic
functional calculus: it states exactly the part of the exponential expansion
used by the Dikin readout theorem. -/
structure RelativeModularDikinData (A : Type*) [Ring A] [Star A] [Algebra ℂ A]
    extends AlgebraicStateData A where
  Delta : A
  K : A
  expOp : A → A
  exp_zero : expOp 0 = 1
  Delta_eq_exp_K : Delta = expOp K
  centered_K : omega K = 0
  taylorRemainder : ℂ → A
  taylor_split :
    ∀ ε : ℂ,
      expOp (ε • K) =
        1 + ε • K + quadraticModularUnit (A := A) ε K + taylorRemainder ε

namespace RelativeModularDikinData

variable (S : RelativeModularDikinData A)

/-- The relative modular Taylor/Dikin readout theorem. -/
theorem dikin_readout (ε : ℂ) :
    S.omega (complexOperatorBregman (A := A) S.expOp ε S.K) =
      (ε ^ 2 / 2 : ℂ) * S.omega (S.K * S.K) + S.omega (S.taylorRemainder ε) := by
  exact taylor_split_readout (Ω := S.toAlgebraicStateData)
    S.expOp ε S.K (S.taylorRemainder ε) (S.taylor_split ε)

/-- Centering removes the first-order modular generator from the state readout. -/
theorem centered_readout (ε : ℂ) :
    S.omega (complexOperatorBregman (A := A) S.expOp ε S.K) =
      S.omega (S.expOp (ε • S.K)) - 1 := by
  exact centered_state_readout_bregman
    (Ω := S.toAlgebraicStateData) S.expOp ε S.K S.centered_K

/-- The relative modular operator is the recorded exponential of `K`. -/
theorem delta_is_exp_K : S.Delta = S.expOp S.K := by
  exact S.Delta_eq_exp_K

end RelativeModularDikinData

#check AlgebraicStateData.gauge_sub_identity_iff
#check AlgebraicStateData.centered_identity_gauge_iff
#check state_readout_bregman
#check centered_state_readout_bregman
#check quadratic_modular_readout
#check taylor_split_readout
#check RelativeModularDikinData.dikin_readout
#check RelativeModularDikinData.centered_readout

end RelativeModularStateDikin
