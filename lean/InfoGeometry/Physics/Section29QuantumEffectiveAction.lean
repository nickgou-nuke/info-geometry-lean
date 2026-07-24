import Mathlib

/-!
# Section 29 repaired: finite quantum-effective-action algebra

The source `section29.txt` sketches a quantum effective action, loop expansion,
renormalization flow, quaternionic fluctuations, and black-hole evaporation
claims.  Most of that requires analytic path-integral, regularization, and
geometric hypotheses not supplied by the text.

This file extracts theorem-safe finite algebra only:

* a formal two-loop effective action polynomial in `ℏ`;
* exact identities for the classical limit and loop remainder;
* linear running couplings and their additive flow law;
* a finite self-consistency residual for a quartic condensate potential;
* integer superficial-divergence bookkeeping.

No path-integral construction, `Tr log` determinant theorem, renormalizability
theorem, exact RG theorem, Hawking-radiation theorem, or information-paradox
resolution is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.Section29QuantumEffectiveAction

/-- Finite scalar coefficients for a formal two-loop effective action. -/
structure LoopActionDatum where
  classical : ℝ
  oneLoop : ℝ
  twoLoop : ℝ

/-- Formal two-loop effective action `Γ₂(ℏ) = S + ℏ Γ₁ + ℏ² Γ₂`. -/
def effectiveActionTwoLoop (D : LoopActionDatum) (hbar : ℝ) : ℝ :=
  D.classical + hbar * D.oneLoop + hbar ^ 2 * D.twoLoop

/-- Classical limit of the formal loop expansion. -/
theorem effectiveActionTwoLoop_zero (D : LoopActionDatum) :
    effectiveActionTwoLoop D 0 = D.classical := by
  simp [effectiveActionTwoLoop]

/-- The loop remainder is exactly the `ℏ`-weighted correction polynomial. -/
theorem effectiveActionTwoLoop_sub_classical (D : LoopActionDatum) (hbar : ℝ) :
    effectiveActionTwoLoop D hbar - D.classical = hbar * D.oneLoop + hbar ^ 2 * D.twoLoop := by
  unfold effectiveActionTwoLoop
  ring

/-- If loop corrections vanish, the formal effective action is classical for all `ℏ`. -/
theorem effectiveActionTwoLoop_eq_classical_of_zero_loops
    (D : LoopActionDatum) (hbar : ℝ) (h1 : D.oneLoop = 0) (h2 : D.twoLoop = 0) :
    effectiveActionTwoLoop D hbar = D.classical := by
  simp [effectiveActionTwoLoop, h1, h2]

/-- A finite linear RG running datum for a coupling. -/
structure LinearRunningCoupling where
  initial : ℝ
  slope : ℝ

/-- Linear running `g(t) = g₀ - slope * t`, where `t = log μ` is a formal parameter. -/
def runningCoupling (C : LinearRunningCoupling) (t : ℝ) : ℝ :=
  C.initial - C.slope * t

/-- Additive flow law for the finite linear running coupling. -/
theorem runningCoupling_add (C : LinearRunningCoupling) (t s : ℝ) :
    runningCoupling C (t + s) = runningCoupling C t - C.slope * s := by
  unfold runningCoupling
  ring

/-- Zero slope means no running. -/
theorem runningCoupling_eq_initial_of_zero_slope
    (C : LinearRunningCoupling) (hC : C.slope = 0) (t : ℝ) :
    runningCoupling C t = C.initial := by
  simp [runningCoupling, hC]

/-- Beta function for the finite linear running model. -/
def linearBeta (C : LinearRunningCoupling) : ℝ :=
  -C.slope

/-- A fixed point of the finite linear model is exactly zero slope. -/
theorem linearBeta_eq_zero_iff (C : LinearRunningCoupling) :
    linearBeta C = 0 ↔ C.slope = 0 := by
  unfold linearBeta
  constructor <;> intro h
  · linarith
  · linarith

/-- Quartic condensate potential `V(φ) = a φ² + b φ⁴`. -/
def condensatePotential (a b phi : ℝ) : ℝ :=
  a * phi ^ 2 + b * phi ^ 4

/-- Algebraic self-consistency residual `dV/dφ` for the quartic potential. -/
def condensateResidual (a b phi : ℝ) : ℝ :=
  2 * a * phi + 4 * b * phi ^ 3

/-- Zero condensate always solves the finite quartic residual equation. -/
theorem condensateResidual_zero (a b : ℝ) :
    condensateResidual a b 0 = 0 := by
  simp [condensateResidual]

/-- A nonzero critical point satisfies the reduced quadratic equation. -/
theorem condensateResidual_eq_zero_of_square_condition
    {a b phi : ℝ} (h : a + 2 * b * phi ^ 2 = 0) :
    condensateResidual a b phi = 0 := by
  have hmul : phi * (a + 2 * b * phi ^ 2) = 0 := by rw [h, mul_zero]
  unfold condensateResidual
  nlinarith [hmul]

/-- Superficial degree of divergence bookkeeping from the source text. -/
def superficialDegree (E_q E_g E_psi V_int : ℤ) : ℤ :=
  4 - E_q - 2 * E_g - E_psi + V_int

/-- Adding one quaternionic external leg lowers the superficial degree by one. -/
theorem superficialDegree_add_quaternion_external
    (E_q E_g E_psi V_int : ℤ) :
    superficialDegree (E_q + 1) E_g E_psi V_int =
      superficialDegree E_q E_g E_psi V_int - 1 := by
  unfold superficialDegree
  ring

/-- Adding one graviton external leg lowers the superficial degree by two. -/
theorem superficialDegree_add_graviton_external
    (E_q E_g E_psi V_int : ℤ) :
    superficialDegree E_q (E_g + 1) E_psi V_int =
      superficialDegree E_q E_g E_psi V_int - 2 := by
  unfold superficialDegree
  ring

/-- Adding one interaction vertex raises the superficial degree by one. -/
theorem superficialDegree_add_vertex
    (E_q E_g E_psi V_int : ℤ) :
    superficialDegree E_q E_g E_psi (V_int + 1) =
      superficialDegree E_q E_g E_psi V_int + 1 := by
  unfold superficialDegree
  ring

/-- Finite repaired Section 29 packet: loop remainder and linear RG flow law. -/
theorem repaired_section29_loop_rg_packet
    (D : LoopActionDatum) (C : LinearRunningCoupling) (hbar t s : ℝ) :
    effectiveActionTwoLoop D hbar - D.classical = hbar * D.oneLoop + hbar ^ 2 * D.twoLoop ∧
      runningCoupling C (t + s) = runningCoupling C t - C.slope * s := by
  exact ⟨effectiveActionTwoLoop_sub_classical D hbar, runningCoupling_add C t s⟩

end InfoGeometry.Physics.Section29QuantumEffectiveAction

end noncomputable section
