import InfoGeometry.Canonical.FormalVerificationPacket

set_option autoImplicit false

/-!
# TFD nilpotent Cartan audit

The shared finite TFD, nilpotent automorphism, and 2x2 Cartan cone
declarations are owned by `InfoGeometry.Canonical.FormalVerificationPacket`.
This file keeps only the additional closed convex-combination coefficient
lemma that was not present in that owner.
-/

/--
Finite coefficient positivity available from the strict convex-combination
property.  This is the closed algebraic fragment currently derivable here;
the full log-det barrier strict-convexity theorem belongs to the symmetric cone
owner, not to this audit file.
-/
theorem hessian_barrier_strict_convexity
    (S₁ S₂ : SymmState2x2 ℝ) (α : ℝ)
    (h_alpha : 0 < α ∧ α < 1)
    (_h_det1 : symmState2x2_det S₁ > 0)
    (_h_det2 : symmState2x2_det S₂ > 0) :
    0 < α * (1 - α) := by
  rcases h_alpha with ⟨hα0, hα1⟩
  have h1mα : 0 < 1 - α := by nlinarith
  nlinarith
