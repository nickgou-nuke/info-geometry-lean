import InfoGeometry.Algebra.JordanInnerDerivations

/-!
# Trace-zero on the inner split-Albert derivation span

The native Jordan owner proves trace-zero pointwise for each inner derivation.
This file closes the linear-span consequence without claiming that every
Jordan derivation is inner or that the span has already been identified with
the full `F₄` carrier.
-/

namespace InfoGeometry.Algebra

open Set
open H3Zorn

def h3ZornInnerDerivationGenerators : Set
    (Module.End ℝ (H3Zorn ℝ)) :=
  {D | ∃ a b : H3Zorn ℝ,
    D = h3ZornJordanInnerDerivation a b}

def h3ZornInnerDerivationSpan :
    Submodule ℝ (Module.End ℝ (H3Zorn ℝ)) :=
  Submodule.span ℝ h3ZornInnerDerivationGenerators

/-- The trace-zero endomorphism carrier for the split-Albert Jordan space. -/
def h3ZornTraceZeroEndomorphisms :
    Submodule ℝ (Module.End ℝ (H3Zorn ℝ)) where
  carrier := {D | ∀ x : H3Zorn ℝ, linearTrace (D x) = 0}
  zero_mem' := by
    intro x
    simp [linearTrace]
  add_mem' := by
    intro D E hD hE x
    rw [show (D + E) x = D x + E x by rfl, linearTrace_add, hD x, hE x,
      add_zero]
  smul_mem' := by
    intro r D hD x
    rw [show (r • D) x = r • D x by rfl, linearTrace_smul, hD x, mul_zero]

/-- Trace-zero endomorphisms are closed under the endomorphism Lie bracket.
This is a statement about the scalar `linearTrace` readout only; it does not
assert that every Jordan derivation is inner. -/
def h3ZornTraceZeroLieSubalgebra :
    LieSubalgebra ℝ (Module.End ℝ (H3Zorn ℝ)) where
  carrier := {D | ∀ x : H3Zorn ℝ, linearTrace (D x) = 0}
  zero_mem' := by
    intro x
    simp [linearTrace]
  add_mem' := by
    intro D E hD hE x
    rw [show (D + E) x = D x + E x by rfl, linearTrace_add, hD x, hE x,
      add_zero]
  smul_mem' := by
    intro r D hD x
    rw [show (r • D) x = r • D x by rfl, linearTrace_smul, hD x, mul_zero]
  lie_mem' := by
    intro D E hD hE x
    change linearTrace (D (E x) - E (D x)) = 0
    rw [sub_eq_add_neg, linearTrace_add]
    rw [show -E (D x) = (-1 : ℝ) • E (D x) by module,
      linearTrace_smul, hD (E x), hE (D x)]
    ring

theorem h3ZornInnerDerivationSpan_trace_zero
    {D : Module.End ℝ (H3Zorn ℝ)}
    (hD : D ∈ h3ZornInnerDerivationSpan)
    (x : H3Zorn ℝ) :
    linearTrace (D x) = 0 := by
  have hspan : ∀ y : H3Zorn ℝ, linearTrace (D y) = 0 := by
    refine Submodule.span_induction
      (p := fun D _ => ∀ y : H3Zorn ℝ, linearTrace (D y) = 0)
      ?_ ?_ ?_ ?_ hD
    · rintro D ⟨a, b, rfl⟩ y
      exact h3ZornJordanInnerDerivation_linearTrace_zero a b y
    · intro y
      simp [linearTrace]
    · intro D E _ _ hD hE y
      rw [show (D + E) y = D y + E y by rfl, linearTrace_add, hD y,
        hE y, add_zero]
    · intro r D _ hD y
      simp [show (r • D) y = r • D y by rfl, linearTrace_smul, hD y]
  exact hspan x

theorem h3ZornInnerDerivationSpan_le_traceZero :
    h3ZornInnerDerivationSpan ≤ h3ZornTraceZeroEndomorphisms := by
  intro D hD
  exact h3ZornInnerDerivationSpan_trace_zero hD

/-- The inner-derivation span lands in the trace-zero Lie carrier as well as
the underlying trace-zero submodule.  The two carriers have the same
pointwise predicate; this theorem exposes the Lie-compatible edge explicitly.
It makes no claim that this span exhausts all Jordan derivations. -/
theorem h3ZornInnerDerivationSpan_le_traceZeroLie :
    h3ZornInnerDerivationSpan ≤ h3ZornTraceZeroLieSubalgebra := by
  intro D hD
  exact h3ZornInnerDerivationSpan_trace_zero hD

end InfoGeometry.Algebra
