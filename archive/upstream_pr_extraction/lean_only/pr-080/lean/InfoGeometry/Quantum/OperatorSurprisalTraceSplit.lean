import Mathlib.LinearAlgebra.Trace

/-!
# Scalar and traceless operator parts

This is the algebraic part of the Weyl/shape separation.  It does not assume
that an operator logarithm or modulus exists: those analytic constructions are
provided by separate finite-dimensional spectral owners.
-/

namespace InfoGeometry.Quantum.OperatorSurprisalTraceSplit

noncomputable section

variable {𝕜 H : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H]
  [Module.Free 𝕜 H] [Module.Finite 𝕜 H]

local notation "EndH" => Module.End 𝕜 H

def traceScalarPart (A : EndH) : EndH :=
  ((Module.finrank 𝕜 H : 𝕜)⁻¹ * LinearMap.trace 𝕜 H A) • LinearMap.id

def traceFreePart (A : EndH) : EndH :=
  A - traceScalarPart A

theorem traceScalarPart_trace (A : EndH)
    (hn : (Module.finrank 𝕜 H : 𝕜) ≠ 0) :
    LinearMap.trace 𝕜 H (traceScalarPart A) =
      LinearMap.trace 𝕜 H A := by
  rw [traceScalarPart, map_smul, LinearMap.trace_id]
  field_simp [hn]
  simp [smul_eq_mul, mul_assoc, hn]

theorem traceFreePart_trace (A : EndH)
    (hn : (Module.finrank 𝕜 H : 𝕜) ≠ 0) :
    LinearMap.trace 𝕜 H (traceFreePart A) = 0 := by
  rw [traceFreePart, map_sub, traceScalarPart_trace A hn, sub_self]

theorem trace_decomposition (A : EndH) :
    A = traceScalarPart A + traceFreePart A := by
  simp [traceFreePart]

theorem traceFreePart_eq_self_iff (A : EndH) (hn : (Module.finrank 𝕜 H : 𝕜) ≠ 0) :
    traceFreePart A = A ↔ LinearMap.trace 𝕜 H A = 0 := by
  constructor
  · intro h
    have htrace := congrArg (LinearMap.trace 𝕜 H) h
    rw [traceFreePart_trace A hn] at htrace
    exact htrace.symm
  · intro h
    simp [traceFreePart, traceScalarPart, h]

end
end InfoGeometry.Quantum.OperatorSurprisalTraceSplit
