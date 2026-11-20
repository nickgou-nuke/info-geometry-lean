/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorContentNetwork.PathTransport
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Finite ordered path amplitudes and gauge-invariant loop readouts

Reuse the existing real matrix transport on native `Quiver.Path`. Weighted
sums transform by their endpoints; loop traces are invariant by Mathlib's
cyclic matrix trace theorem. Products concatenate paths in order. A nontrivial
loop obstructs a potential depending only on vertices.

The finite-history cardinality makes both the edge set and time horizon
explicit. None of these statements constructs an infinite or continuum path
integral. Source: holographic white paper v6.1, sections 5.2, 5.3, and 5.11.
-/

noncomputable section

namespace InfoGeometry.Holographic.PathAmplitudes

open InfoGeometry.Canonical.OperatorContentNetwork

variable {V n I J : Type*} [Quiver V] [Fintype n] [DecidableEq n]

/-- A finite sum of ordered matrix transports between fixed endpoints. -/
def pathAmplitude (L : EdgeLabelling V n) {a b : V} (s : Finset I)
    (weight : I → ℝ) (paths : I → Quiver.Path a b) : Operator n :=
  ∑ i ∈ s, weight i • pathTransport L (paths i)

/-- Internal frame changes cancel in every summand. -/
theorem pathAmplitude_gauge (G : V → (Operator n)ˣ) (L : EdgeLabelling V n)
    {a b : V} (s : Finset I) (weight : I → ℝ) (paths : I → Quiver.Path a b) :
    pathAmplitude (gaugeLabel G L) s weight paths =
      (G a : Operator n) * pathAmplitude L s weight paths * ↑((G b)⁻¹) := by
  simp only [pathAmplitude, pathTransport_gaugeLabel, Finset.mul_sum, Finset.sum_mul,
    smul_mul_assoc, mul_smul_comm]

/-- A loop amplitude has gauge-invariant trace; its matrix need not be invariant. -/
theorem loop_amplitude_trace_gauge (G : V → (Operator n)ˣ) (L : EdgeLabelling V n)
    {a : V} (s : Finset I) (weight : I → ℝ) (paths : I → Quiver.Path a a) :
    Matrix.trace (pathAmplitude (gaugeLabel G L) s weight paths) =
      Matrix.trace (pathAmplitude L s weight paths) := by
  rw [pathAmplitude_gauge, Matrix.trace_units_conj]

/-- The finite composition law is an ordered sum over pairs of histories. -/
theorem pathAmplitude_mul (L : EdgeLabelling V n) {a b c : V}
    (s : Finset I) (t : Finset J) (w : I → ℝ) (v : J → ℝ)
    (p : I → Quiver.Path a b) (q : J → Quiver.Path b c) :
    pathAmplitude L s w p * pathAmplitude L t v q =
      ∑ i ∈ s, ∑ j ∈ t, (w i * v j) • pathTransport L ((p i).comp (q j)) := by
  unfold pathAmplitude
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [pathTransport_comp, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm (v j) (w i)]

/-- For potential-induced labels all path dependence reduces to the total weight. -/
theorem pathAmplitude_potential (G : V → (Operator n)ˣ) {a b : V}
    (s : Finset I) (weight : I → ℝ) (paths : I → Quiver.Path a b) :
    pathAmplitude (potentialLabel G) s weight paths =
      (∑ i ∈ s, weight i) • ((↑((G a)⁻¹) : Operator n) * G b) := by
  simp only [pathAmplitude, pathTransport_potentialLabel, Finset.sum_smul]

/-- A nontrivial loop supplies two paths with the same endpoints and distinct transports. -/
theorem nontrivial_loop_obstructs_path_independence (L : EdgeLabelling V n)
    {a : V} (p : Quiver.Path a a) (hp : pathTransport L p ≠ 1) :
    ¬∀ q r : Quiver.Path a a, pathTransport L q = pathTransport L r := by
  intro h
  exact hp (by simpa using h p .nil)

/-- In particular, nontrivial holonomy excludes a global vertex potential. -/
theorem nontrivial_loop_not_potential (L : EdgeLabelling V n)
    {a : V} (p : Quiver.Path a a) (hp : pathTransport L p ≠ 1) :
    ¬∃ G : V → (Operator n)ˣ,
      (L : EdgeLabelling V n) = (potentialLabel G : EdgeLabelling V n) := by
  rintro ⟨G, hG⟩
  apply hp
  calc
    pathTransport L p = pathTransport (potentialLabel G) p :=
      congrArg (fun K : EdgeLabelling V n => pathTransport K p) hG
    _ = 1 := potentialLabel_loop G p

end InfoGeometry.Holographic.PathAmplitudes

namespace InfoGeometry.Holographic.FiniteHistories

/-- Both a finite edge set and a finite time horizon are needed for this count. -/
theorem quarter_phase_history_card (Edge : Type*) [Fintype Edge] [DecidableEq Edge]
    (steps : ℕ) :
    Fintype.card (Edge × Fin steps → ZMod 4) = 4 ^ (Fintype.card Edge * steps) := by
  simp

end InfoGeometry.Holographic.FiniteHistories
