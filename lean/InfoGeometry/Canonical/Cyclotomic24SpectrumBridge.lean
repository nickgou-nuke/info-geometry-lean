import Mathlib
import InfoGeometry.Canonical.Cyclotomic24PolynomialBridge
import InfoGeometry.Physics.Algebra.NPotentCyclotomicSpinHullBridge

/-!
# Finite spectrum consequence of the 24-fold master annihilator

This owner proves the precise spectral consequence of the master equation

`T * (T^24 - 1) = 0`.

For a finite-dimensional complex endomorphism this equation is equivalent to
`T^25 = T`.  The existing generic `n`-potent spectrum theorem can therefore be
reused at `n = 25`, giving

`spectrum ℂ T ⊆ {0} ∪ {z | z^24 = 1}`.

The inclusion is deliberately not strengthened to equality.  Equality would
require a separate theorem that every listed 24th root actually occurs as an
eigenvalue of the supplied operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cyclotomic24SpectrumBridge

open InfoGeometry.Physics.Algebra.NPotentCyclotomicSpinHullBridge

/-- The master annihilator equation is exactly 25-potency. -/
theorem master24_eq_zero_iff_pow25_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) :
    T * (T ^ 24 - 1) = 0 ↔ T ^ 25 = T := by
  constructor
  · intro h
    have hzero : T ^ 25 - T = 0 := by
      calc
        T ^ 25 - T = T * (T ^ 24 - 1) := by noncomm_ring
        _ = 0 := h
    exact sub_eq_zero.mp hzero
  · intro h
    calc
      T * (T ^ 24 - 1) = T ^ 25 - T := by noncomm_ring
      _ = 0 := sub_eq_zero.mpr h

/-- Any eigenvalue of a finite-dimensional complex operator satisfying the
master equation is either zero or a 24th root of unity. -/
theorem spectrum_subset_zero_union_roots24
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V]
    (T : Module.End ℂ V)
    (hmaster : T * (T ^ 24 - 1) = 0) :
    spectrum ℂ T ⊆ {0} ∪ {z : ℂ | z ^ 24 = 1} := by
  have h25 : T ^ 25 = T :=
    (master24_eq_zero_iff_pow25_eq T).mp hmaster
  simpa using
    (operator_spectrum_subset_npotent_hull T 25 (by norm_num) h25)

/-- The same spectral containment from the equivalent 25-potency equation. -/
theorem spectrum_subset_zero_union_roots24_of_pow25
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V]
    (T : Module.End ℂ V)
    (h25 : T ^ 25 = T) :
    spectrum ℂ T ⊆ {0} ∪ {z : ℂ | z ^ 24 = 1} := by
  simpa using
    (operator_spectrum_subset_npotent_hull T 25 (by norm_num) h25)

/-- Pointwise eigenvalue form of the master spectral restriction. -/
theorem eigenvalue_zero_or_pow24_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V]
    (T : Module.End ℂ V)
    (hmaster : T * (T ^ 24 - 1) = 0)
    {z : ℂ} (hz : T.HasEigenvalue z) :
    z = 0 ∨ z ^ 24 = 1 := by
  have hmem : z ∈ spectrum ℂ T :=
    (Module.End.hasEigenvalue_iff_mem_spectrum).mp hz
  have hsubset := spectrum_subset_zero_union_roots24 T hmaster hmem
  simpa [Set.mem_union] using hsubset

/-- Compact theorem packet: the master equation is 25-potency and implies the
finite spectral containment. -/
theorem master24_spectrum_packet
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V]
    (T : Module.End ℂ V)
    (hmaster : T * (T ^ 24 - 1) = 0) :
    T ^ 25 = T ∧
      spectrum ℂ T ⊆ {0} ∪ {z : ℂ | z ^ 24 = 1} := by
  exact ⟨(master24_eq_zero_iff_pow25_eq T).mp hmaster,
    spectrum_subset_zero_union_roots24 T hmaster⟩

end InfoGeometry.Canonical.Cyclotomic24SpectrumBridge

