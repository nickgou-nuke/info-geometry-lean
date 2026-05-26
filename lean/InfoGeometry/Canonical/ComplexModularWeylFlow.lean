import Mathlib

/-!
# InfoGeometry.Canonical.ComplexModularWeylFlow

Finite complex-time modular/Weyl readout on a 2D real carrier:

* real time drives unitary phase (`cos/sin`),
* imaginary-time (`β`) drives Weyl damping (`exp (-scale * β)`).

This is a concrete owner-side packet (no Type III/KMS existence claim).
-/

namespace InfoGeometry.Canonical.ComplexModularWeylFlow

noncomputable section

structure ComplexModularGenerator where
  unitaryK : ℝ
  weylScale : ℝ

structure ComplexParameter where
  time : ℝ
  beta : ℝ

/-- Finite modular/Weyl flow readout `(x,y)` with common damping factor. -/
def modularScale (G : ComplexModularGenerator) (p : ComplexParameter) : ℝ × ℝ :=
  let a := Real.exp (-G.weylScale * p.beta)
  let θ := G.unitaryK * p.time
  (a * Real.cos θ, a * Real.sin θ)

@[simp] theorem modularScale_fst (G : ComplexModularGenerator) (p : ComplexParameter) :
    (modularScale G p).1 = Real.exp (-G.weylScale * p.beta) * Real.cos (G.unitaryK * p.time) := by
  rfl

@[simp] theorem modularScale_snd (G : ComplexModularGenerator) (p : ComplexParameter) :
    (modularScale G p).2 = Real.exp (-G.weylScale * p.beta) * Real.sin (G.unitaryK * p.time) := by
  rfl

/-- `β = 0` gives pure unitary circle coordinates. -/
theorem zero_beta_is_unitary (G : ComplexModularGenerator) (t : ℝ) :
    modularScale G ⟨t, 0⟩
      = (Real.cos (G.unitaryK * t), Real.sin (G.unitaryK * t)) := by
  ext <;> simp [modularScale]

/-- `t = 0` gives pure Weyl scaling on the horizontal axis. -/
theorem zero_time_is_pure_weyl (G : ComplexModularGenerator) (β : ℝ) :
    modularScale G ⟨0, β⟩ = (Real.exp (-G.weylScale * β), 0) := by
  ext <;> simp [modularScale]

/-- Squared norm is exactly the Weyl damping square, phase-independent. -/
theorem modularScale_normSq (G : ComplexModularGenerator) (p : ComplexParameter) :
    (modularScale G p).1 ^ 2 + (modularScale G p).2 ^ 2
      = Real.exp (-2 * G.weylScale * p.beta) := by
  rcases p with ⟨t, β⟩
  calc
    (modularScale G ⟨t, β⟩).1 ^ 2 + (modularScale G ⟨t, β⟩).2 ^ 2
        = (Real.exp (-(G.weylScale * β)) * Real.cos (G.unitaryK * t)) ^ 2
          + (Real.exp (-(G.weylScale * β)) * Real.sin (G.unitaryK * t)) ^ 2 := by
            simp [modularScale]
    _ = Real.exp (-(G.weylScale * β)) ^ 2 *
          (Real.cos (G.unitaryK * t) ^ 2 + Real.sin (G.unitaryK * t) ^ 2) := by
            ring
    _ = Real.exp (-(G.weylScale * β)) ^ 2 := by
            rw [Real.cos_sq_add_sin_sq]
            ring
    _ = Real.exp (-2 * G.weylScale * β) := by
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring

/--
Complex-parameter composition at fixed generator:

adding `(t,β)` parameters multiplies amplitudes as expected:
* phase adds (`θ₁+θ₂`),
* damping multiplies (`exp` add law).
-/
theorem modularScale_compose
    (G : ComplexModularGenerator)
    (p q : ComplexParameter) :
    modularScale G ⟨p.time + q.time, p.beta + q.beta⟩
      =
      let u := modularScale G p
      let v := modularScale G q
      (u.1 * v.1 - u.2 * v.2, u.1 * v.2 + u.2 * v.1) := by
  rcases p with ⟨tp, βp⟩
  rcases q with ⟨tq, βq⟩
  ext <;> simp [modularScale, Real.exp_add, mul_add, Real.cos_add, Real.sin_add]
  · ring
  · ring

end

end InfoGeometry.Canonical.ComplexModularWeylFlow
