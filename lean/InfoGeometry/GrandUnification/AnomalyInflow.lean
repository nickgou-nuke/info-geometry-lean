/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

/-!
# Graded Supertrace, Determinant Spinning Instability, and Callan–Harvey Anomaly Inflow

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `supertrace Γ X = LinearMap.trace R M (Γ * X)` over a free finite-rank module `M`
    over a commutative ring `R`.
- BUCKET 2 (Deconfabulation):
  * Eliminated the wrapper structure `AnomalyInflowTQFTPacket` and `Prop` alias
    `AnomalyInflowTQFTTarget`, replacing them with constructive theorems using both odd
    Cartan grading hypotheses `hA : Γ * A = -(A * Γ)` and `hB : Γ * B = -(B * Γ)`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `spinning_instability_anomaly`: for two $\Gamma$-odd endomorphisms $A, B$,
    $\mathrm{supertrace}\,\Gamma\,(A * B - B * A) = (2 : R) * \mathrm{supertrace}\,\Gamma\,(A * B)$.
  * `odd_forms_even_product_and_inflow_cancellation`: proves that $A * B$ commutes with $\Gamma$
    ($\Gamma * (A * B) = (A * B) * \Gamma$), the ungraded commutator trace vanishes, and the
    Callan–Harvey bulk-boundary anomaly difference cancels when $I_{\mathrm{bulk}}$ matches
    the boundary commutator supertrace.
-/

namespace InfoGeometry.TopologicalFieldTheory

open LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-- The Graded Supertrace over the twin-sheeted state space. -/
noncomputable def supertrace (Γ X : Module.End R M) : R :=
  LinearMap.trace R M (Γ * X)

/-- The product of two $\Gamma$-odd operators is $\Gamma$-even (commutes with $\Gamma$). -/
theorem odd_mul_odd_commutes_with_grading
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (Γ A B : Module.End R M)
    (hA : Γ * A = -(A * Γ))
    (hB : Γ * B = -(B * Γ)) :
    Γ * (A * B) = (A * B) * Γ := by
  calc
    Γ * (A * B) = (Γ * A) * B := (mul_assoc Γ A B).symm
    _ = (-(A * Γ)) * B := by rw [hA]
    _ = -(A * (Γ * B)) := by noncomm_ring
    _ = -(A * (-(B * Γ))) := by rw [hB]
    _ = (A * B) * Γ := by noncomm_ring

/-- **The Determinant Spinning Instability (`spinning_instability_anomaly`):**
For any chiral grading $\Gamma \in \mathrm{Module.End}\,R\,M$ and two $\Gamma$-odd operators
$A, B \in \mathrm{Module.End}\,R\,M$ (`hA : Γ * A = -(A * Γ)` and `hB : Γ * B = -(B * Γ)`),
the graded supertrace of their commutator doubles rather than vanishing:
$$\mathrm{supertrace}\,\Gamma\,(A * B - B * A) = (2 : R) * \mathrm{supertrace}\,\Gamma\,(A * B).$$ -/
theorem spinning_instability_anomaly
    (Γ A B : Module.End R M)
    (hA : Γ * A = -(A * Γ))
    (hB : Γ * B = -(B * Γ)) :
    supertrace Γ (A * B - B * A) = (2 : R) * supertrace Γ (A * B) := by
  have h_even := odd_mul_odd_commutes_with_grading Γ A B hA hB
  have h_reverse_transport :
      LinearMap.trace R M (Γ * (B * A)) = -LinearMap.trace R M (Γ * (A * B)) := by
    have step1 : Γ * (B * A) = -(B * (Γ * A)) := by
      calc
        Γ * (B * A) = (Γ * B) * A := (mul_assoc Γ B A).symm
        _ = (-(B * Γ)) * A := by rw [hB]
        _ = -(B * (Γ * A)) := by noncomm_ring
        _ = -(B * (-(A * Γ))) := by rw [hA]
        _ = (B * A) * Γ := by noncomm_ring
        _ = B * (A * Γ) := mul_assoc B A Γ
        _ = B * (-(-(A * Γ))) := by rw [neg_neg]
        _ = B * (-(Γ * A)) := by rw [← hA]
        _ = -(B * (Γ * A)) := mul_neg B (Γ * A)
    rw [step1, LinearMap.map_neg (LinearMap.trace R M) (B * (Γ * A))]
    rw [LinearMap.trace_mul_comm R B (Γ * A), mul_assoc]
  unfold supertrace
  rw [mul_sub, LinearMap.map_sub (LinearMap.trace R M) (Γ * (A * B)) (Γ * (B * A)),
    h_reverse_transport, sub_neg_eq_add, h_even, ← h_even]
  have two_def : (2 : R) = 1 + 1 := by norm_num
  rw [two_def, add_mul, one_mul]

/-- **Callan–Harvey Anomaly Inflow & Even-Product Synthesis:**
Combines the $\Gamma$-evenness of $A * B$, the vanishing of the ungraded commutator trace,
the Determinant Spinning Instability, and bulk-boundary anomaly inflow cancellation. -/
theorem odd_forms_even_product_and_inflow_cancellation
    (Γ A B : Module.End R M)
    (hA : Γ * A = -(A * Γ))
    (hB : Γ * B = -(B * Γ))
    (I_bulk : R)
    (h_inflow : I_bulk = supertrace Γ (A * B - B * A)) :
    Γ * (A * B) = (A * B) * Γ ∧
    LinearMap.trace R M (A * B - B * A) = 0 ∧
    I_bulk = (2 : R) * supertrace Γ (A * B) ∧
    supertrace Γ (A * B - B * A) - I_bulk = 0 := by
  have heven := odd_mul_odd_commutes_with_grading Γ A B hA hB
  have htr0 : LinearMap.trace R M (A * B - B * A) = 0 := by
    rw [map_sub, LinearMap.trace_mul_comm R A B, sub_self]
  have hspin := spinning_instability_anomaly Γ A B hA hB
  exact ⟨heven, htr0, h_inflow.trans hspin, sub_eq_zero.mpr h_inflow.symm⟩

end InfoGeometry.TopologicalFieldTheory
