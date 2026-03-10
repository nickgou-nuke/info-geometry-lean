import InfoGeometry.MaxEnt.Optimality

open scoped BigOperators

/-!
# Finite MaxEnt Dual Bridge

Adds the standard Jaynes dual/free-energy packaging on top of
`InfoGeometry.MaxEnt.Optimality`:

- dual objective `Φ(lam) = lam E + log Z(lam)`
- moment residual `gibbsExpectation - E`
- Gibbs feasibility ↔ residual vanishes
- entropy upper bound by the dual objective on the constraint set
- Gibbs achieves the bound when feasible
- packaged argmax theorem
-/

namespace InfoGeometry.MaxEnt

section DualBridge

variable {n : ℕ} [Nonempty (Fin n)]

/-- Jaynes dual/free-energy objective (for one moment constraint). -/
noncomputable def dualObjective
    (f : Fin n → ℝ) (E lam : ℝ) : ℝ :=
  lam * E + logPartition f lam

/-- Moment residual of the Gibbs family at multiplier `lam`. -/
noncomputable def momentResidual
    (f : Fin n → ℝ) (E lam : ℝ) : ℝ :=
  gibbsExpectation f lam - E

omit [Nonempty (Fin n)] in
@[simp] lemma momentResidual_eq_zero_iff
    (f : Fin n → ℝ) (E lam : ℝ) :
    momentResidual (n := n) f E lam = 0 ↔ gibbsExpectation f lam = E := by
  unfold momentResidual
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Gibbs is feasible for the one-moment MaxEnt constraint exactly when its moment matches `E`. -/
lemma gibbs_mem_maxEntConstraint_iff
    (f : Fin n → ℝ) (E lam : ℝ) :
    gibbs f lam ∈ MaxEntConstraint (n := n) f E ↔ gibbsExpectation f lam = E := by
  constructor
  · intro h
    simpa [gibbsExpectation] using h.2
  · intro hE
    refine ⟨?_, ?_⟩
    · exact ⟨(fun i => gibbs_nonneg f lam i), gibbs_sum_one f lam⟩
    · simpa [gibbsExpectation] using hE

/-- On the constraint set, the Gibbs cross-entropy equals the dual objective. -/
lemma crossEntropyToGibbs_eq_dualObjective
    (f : Fin n → ℝ) (E lam : ℝ)
    {q : Fin n → ℝ}
    (hq : q ∈ MaxEntConstraint (n := n) f E) :
    -∑ i, q i * Real.log (gibbs f lam i) = dualObjective (n := n) f E lam := by
  simpa [dualObjective] using
    crossEntropyToGibbs_eq (n := n) (f := f) (E := E) (lam := lam) hq

/-- If the Gibbs family hits the target moment, its entropy equals the dual objective. -/
lemma entropy_gibbs_eq_dualObjective
    (f : Fin n → ℝ) (E lam : ℝ)
    (hE : gibbsExpectation f lam = E) :
    entropy (gibbs f lam) 1 = dualObjective (n := n) f E lam := by
  simpa [dualObjective] using
    entropy_gibbs_eq (n := n) (f := f) (E := E) (lam := lam) hE

/-- Weak dual bound on the feasible set: any feasible entropy is bounded by `lamE + log Z(lam)`. -/
theorem entropy_le_dualObjective_on_constraint
    (f : Fin n → ℝ) (E lam : ℝ)
    (q : Fin n → ℝ)
    (hq : q ∈ MaxEntConstraint (n := n) f E) :
    entropy q 1 ≤ dualObjective (n := n) f E lam := by
  have hKLnonneg :
      0 ≤ InfoGeometry.kl_div
        (probDistOfSimplex (n := n) q hq.1)
        (gibbsDist (n := n) f lam) := by
    apply InfoGeometry.KL.klDiv_nonneg_of_fullSupport
    intro i
    show 0 < (gibbsDist (n := n) f lam).prob i
    simpa [gibbsDist] using gibbs_pos (f := f) (lam := lam) i
  have hKLexpand :
      InfoGeometry.kl_div
        (probDistOfSimplex (n := n) q hq.1)
        (gibbsDist (n := n) f lam)
        = ∑ i, q i * (Real.log (q i) - Real.log (gibbs f lam i)) := by
    unfold InfoGeometry.kl_div InfoGeometry.expectation InfoGeometry.logDensity
    simp [probDistOfSimplex, gibbsDist]
  have hkl :
      0 ≤ (∑ i, q i * Real.log (q i)) - (∑ i, q i * Real.log (gibbs f lam i)) := by
    have htmp := hKLnonneg
    rw [hKLexpand] at htmp
    have hsum :
        ∑ i, q i * (Real.log (q i) - Real.log (gibbs f lam i))
          = (∑ i, q i * Real.log (q i)) - (∑ i, q i * Real.log (gibbs f lam i)) := by
      calc
        ∑ i, q i * (Real.log (q i) - Real.log (gibbs f lam i))
            = ∑ i, (q i * Real.log (q i) - q i * Real.log (gibbs f lam i)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
        _ = (∑ i, q i * Real.log (q i)) - (∑ i, q i * Real.log (gibbs f lam i)) := by
              rw [Finset.sum_sub_distrib]
    exact hsum ▸ htmp
  have hq_le_cross :
      entropy q 1 ≤ -∑ i, q i * Real.log (gibbs f lam i) := by
    have hq_form : entropy q 1 = -∑ i, q i * Real.log (q i) := by
      simp [entropy]
    linarith [hkl, hq_form]
  calc
    entropy q 1 ≤ -∑ i, q i * Real.log (gibbs f lam i) := hq_le_cross
    _ = dualObjective (n := n) f E lam :=
      crossEntropyToGibbs_eq_dualObjective (n := n) (f := f) (E := E) (lam := lam) hq

/-- Strong dual attainment: if Gibbs matches the moment, it attains the dual bound. -/
theorem gibbs_attains_dualObjective
    (f : Fin n → ℝ) (E lam : ℝ)
    (hE : gibbsExpectation f lam = E) :
    entropy (gibbs f lam) 1 = dualObjective (n := n) f E lam :=
  entropy_gibbs_eq_dualObjective (n := n) (f := f) (E := E) (lam := lam) hE

/--
Packaged Jaynes optimality: feasible Gibbs maximizes entropy on the one-moment
constraint set.
-/
theorem gibbs_maximizes_entropy_on_constraint
    (f : Fin n → ℝ) (E lam : ℝ)
    (hE : gibbsExpectation f lam = E) :
    ∀ q, q ∈ MaxEntConstraint (n := n) f E →
      entropy q 1 ≤ entropy (gibbs f lam) 1 := by
  intro q hq
  have h1 :
      entropy q 1 ≤ dualObjective (n := n) f E lam :=
    entropy_le_dualObjective_on_constraint (n := n) (f := f) (E := E) (lam := lam) q hq
  have h2 :
      entropy (gibbs f lam) 1 = dualObjective (n := n) f E lam :=
    gibbs_attains_dualObjective (n := n) (f := f) (E := E) (lam := lam) hE
  calc
    entropy q 1 ≤ dualObjective (n := n) f E lam := h1
    _ = entropy (gibbs f lam) 1 := h2.symm

/-- Same theorem, but for a candidate `p` identified pointwise with the Gibbs law. -/
theorem gibbs_form_candidate_maximizes_entropy
    (f : Fin n → ℝ) (E lam : ℝ)
    (p : Fin n → ℝ)
    (hp : p ∈ MaxEntConstraint (n := n) f E)
    (h_dist : ∀ i, p i = gibbs f lam i) :
    ∀ q, q ∈ MaxEntConstraint (n := n) f E →
      entropy q 1 ≤ entropy p 1 :=
  max_ent_lagrange_multiplier_gibbs (n := n) (f := f) (E := E) (lam := lam) (p := p) hp h_dist

end DualBridge

end InfoGeometry.MaxEnt
