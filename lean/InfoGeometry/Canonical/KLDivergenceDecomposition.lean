import Mathlib
import InfoGeometry.Topology.ThermodynamicGauge

/-!
# KL Symmetric/Antisymmetric Decomposition

Theorem-safe algebraic decomposition of an asymmetric divergence into its
symmetric (Jeffreys/traffic) and antisymmetric (current/affinity) parts.

No analytic KL integrability, Fisher-Hessian theorem, Araki entropy theorem, or
de Rham cohomology identification is asserted here.  Those are represented by
explicit comparison packets.  The closed content is the algebraic even/odd
splitting under state swap.
-/

namespace InfoGeometry.Canonical.KLDivergenceDecomposition

open InfoGeometry.Topology.ThermodynamicGauge

universe u

variable {State : Type u}

/-- Symmetric/Jeffreys half of any asymmetric real divergence. -/
noncomputable def symmetricPart (D : State → State → ℝ) (p q : State) : ℝ :=
  (D p q + D q p) / 2

/-- Antisymmetric/current half of any asymmetric real divergence. -/
noncomputable def antisymmetricPart (D : State → State → ℝ) (p q : State) : ℝ :=
  (D p q - D q p) / 2

/-- The divergence is the sum of its symmetric and antisymmetric halves. -/
theorem divergence_eq_symmetric_add_antisymmetric
    (D : State → State → ℝ) (p q : State) :
    D p q = symmetricPart D p q + antisymmetricPart D p q := by
  unfold symmetricPart antisymmetricPart
  ring

/-- The symmetric half is invariant under swapping arguments. -/
theorem symmetricPart_swap (D : State → State → ℝ) (p q : State) :
    symmetricPart D q p = symmetricPart D p q := by
  unfold symmetricPart
  ring

/-- The antisymmetric half changes sign under swapping arguments. -/
theorem antisymmetricPart_swap (D : State → State → ℝ) (p q : State) :
    antisymmetricPart D q p = - antisymmetricPart D p q := by
  unfold antisymmetricPart
  ring

/-- The reverse divergence uses the same symmetric part and the opposite current. -/
theorem reverse_divergence_eq_symmetric_sub_antisymmetric
    (D : State → State → ℝ) (p q : State) :
    D q p = symmetricPart D p q - antisymmetricPart D p q := by
  unfold symmetricPart antisymmetricPart
  ring

/-- The antisymmetric half vanishes exactly when the divergence is swap-symmetric. -/
theorem antisymmetricPart_eq_zero_iff_symmetric
    (D : State → State → ℝ) (p q : State) :
    antisymmetricPart D p q = 0 ↔ D p q = D q p := by
  unfold antisymmetricPart
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]
    ring

/-- Difference of forward and reverse divergence is twice the antisymmetric part. -/
theorem divergence_sub_reverse_eq_two_mul_antisymmetric
    (D : State → State → ℝ) (p q : State) :
    D p q - D q p = 2 * antisymmetricPart D p q := by
  unfold antisymmetricPart
  ring

/-- Sum of forward and reverse divergence is twice the symmetric part. -/
theorem divergence_add_reverse_eq_two_mul_symmetric
    (D : State → State → ℝ) (p q : State) :
    D p q + D q p = 2 * symmetricPart D p q := by
  unfold symmetricPart
  ring

/-- Nonnegativity of the symmetric half follows from nonnegativity of both directions. -/
theorem symmetricPart_nonneg_of_pair_nonneg
    (D : State → State → ℝ) (p q : State)
    (hpq : 0 ≤ D p q) (hqp : 0 ≤ D q p) :
    0 ≤ symmetricPart D p q := by
  unfold symmetricPart
  nlinarith

/--
A Legendre-dual readout socket for the antisymmetric KL/Bregman component.
The formula is supplied by the dually-flat owner; this file only exposes it.
-/
structure LegendreAntisymmetricReadout (Coord Dual : Type*) where
  pairing : Coord → Dual → ℝ
  psi : Coord → ℝ
  phi : Dual → ℝ
  eta : Coord → Dual
  theta : Dual → Coord
  divergence : Coord → Coord → ℝ
  formula : ∀ θ θ' : Coord,
    antisymmetricPart divergence θ θ' =
      (pairing θ' (eta θ) - pairing θ (eta θ') + psi θ - psi θ' +
        phi (eta θ') - phi (eta θ)) / 2

namespace LegendreAntisymmetricReadout

variable {Coord Dual : Type*} (L : LegendreAntisymmetricReadout Coord Dual)

/-- Readback of the supplied Legendre-dual antisymmetric formula. -/
theorem antisymmetric_eq_legendre_formula (θ θ' : Coord) :
    antisymmetricPart L.divergence θ θ' =
      (L.pairing θ' (L.eta θ) - L.pairing θ (L.eta θ') + L.psi θ - L.psi θ' +
        L.phi (L.eta θ') - L.phi (L.eta θ)) / 2 :=
  L.formula θ θ'

end LegendreAntisymmetricReadout

/--
Thermodynamic identification socket: the antisymmetric divergence between two
states is calibrated to entropy production of a finite thermodynamic-gauge flow.
-/
structure AntisymmetricThermodynamicBridge
    {Op : Type*} [Ring Op]
    (D : State → State → ℝ) (eval : Op → ℝ)
    (flow : CausalNonequilibriumFlow Op) where
  left : State
  right : State
  antisym_eq_eval_entropy : antisymmetricPart D left right = eval (entropy_production flow)
  eval_dlnQ_eq : eval flow.d_ln_Q = eval (entropy_production flow)

namespace AntisymmetricThermodynamicBridge

variable {Op : Type*} [Ring Op]
variable {D : State → State → ℝ} {eval : Op → ℝ}
variable {flow : CausalNonequilibriumFlow Op}
variable (B : AntisymmetricThermodynamicBridge D eval flow)

/-- Readback: the antisymmetric KL component is the evaluated entropy production. -/
theorem antisymmetric_eq_entropy_eval :
    antisymmetricPart D B.left B.right = eval (entropy_production flow) :=
  B.antisym_eq_eval_entropy

/-- Readback: after calibration, the antisymmetric component is the evaluated `d_ln_Q`. -/
theorem antisymmetric_eq_dlnQ_eval :
    antisymmetricPart D B.left B.right = eval flow.d_ln_Q := by
  rw [B.antisym_eq_eval_entropy, B.eval_dlnQ_eq]

end AntisymmetricThermodynamicBridge

end InfoGeometry.Canonical.KLDivergenceDecomposition
