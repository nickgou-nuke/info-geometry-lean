import InfoGeometry.Canonical.ModularSL2R
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Routing marker: canonical `sl(2, ℝ)` modular carrier

The former file duplicated a finite `M₂(ℝ)` presentation of the three
commutator generators `L₀`, `L₁`, and `L₋₁` without any maintained consumers.
The authoritative noncommutative owner is
`InfoGeometry.Canonical.ModularSL2R`, which already provides the same matrix
carrier, the nilpotent transpose pair, their commutator, and the trace form.

This module remains as a compatibility import point only; it does not expose a
second scalar or matrix-level implementation.
-/
