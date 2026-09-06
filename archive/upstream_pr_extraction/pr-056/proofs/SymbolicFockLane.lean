import Mathlib

/-!
# Symbolic Fock Lane

This file records the CAS-style symbolic lane for occupation variables.

Instead of enumerating concrete words immediately, introduce symbolic
idempotents `eᵢ` with `eᵢ^2 = eᵢ`.  The local symbolic lane is

`(1 - e) + e*x`.

The parity lane is

`1 - 2*e`.

Under the idempotent law, their product collapses locally to `1 - e - e*x`.
Boolean trace projection over `e ∈ {0,1}` gives the graded local factor
`1 - x`, while tracing without parity gives the ordinary fermion factor
`1 + x`.
-/

noncomputable section

namespace SymbolicFockLane

/-- Symbolic local occupation lane. -/
def occupationLane (e x : ℂ) : ℂ :=
  (1 - e) + e * x

/-- Symbolic local parity lane. -/
def parityLane (e : ℂ) : ℂ :=
  1 - 2 * e

/-- Symbolic local graded lane before projection. -/
def gradedLane (e x : ℂ) : ℂ :=
  parityLane e * occupationLane e x

/-- Idempotent occupation markers satisfy `e^2=e`. -/
def Idempotent (e : ℂ) : Prop :=
  e * e = e

theorem occupationLane_empty (x : ℂ) :
    occupationLane 0 x = 1 := by
  simp [occupationLane]

theorem occupationLane_occupied (x : ℂ) :
    occupationLane 1 x = x := by
  simp [occupationLane]

theorem parityLane_empty :
    parityLane 0 = 1 := by
  simp [parityLane]

theorem parityLane_occupied :
    parityLane 1 = -1 := by
  norm_num [parityLane]

/--
Local symbolic supertrace collapse:
with `e²=e`, parity times occupation is the selector `1 - e - e*x`.
-/
theorem gradedLane_idempotent {e x : ℂ} (he : Idempotent e) :
    gradedLane e x = 1 - e - e * x := by
  unfold gradedLane parityLane occupationLane Idempotent at *
  calc
    (1 - 2 * e) * ((1 - e) + e * x)
        = 1 - 3 * e + e * x + 2 * (e * e) - 2 * (e * e) * x := by ring
    _ = 1 - e - e * x := by
        rw [he]
        ring_nf

/-- Projecting the symbolic occupation lane by `e=1` gives `x`. -/
theorem occupationLane_project_occupied (x : ℂ) :
    occupationLane 1 x = x := by
  exact occupationLane_occupied x

/-- Projecting the symbolic graded lane by `e=1` gives the local factor `-x`. -/
theorem gradedLane_project_occupied (x : ℂ) :
    gradedLane 1 x = -x := by
  norm_num [gradedLane, parityLane, occupationLane]

/-- Summing empty and occupied lanes gives the ordinary local fermion factor. -/
theorem ordinary_projected_local_factor (x : ℂ) :
    occupationLane 0 x + occupationLane 1 x = 1 + x := by
  simp [occupationLane]

/-- Summing parity-weighted empty and occupied lanes gives the graded local factor. -/
theorem graded_projected_local_factor (x : ℂ) :
    parityLane 0 * occupationLane 0 x +
      parityLane 1 * occupationLane 1 x = 1 - x := by
  norm_num [parityLane, occupationLane]
  ring_nf

/-- Two independent symbolic lanes factor before projection. -/
theorem two_lane_ordinary_projection (x y : ℂ) :
    (occupationLane 0 x + occupationLane 1 x) *
      (occupationLane 0 y + occupationLane 1 y)
      =
    (1 + x) * (1 + y) := by
  simp [occupationLane]

/-- Two independent parity lanes factor to the finite graded determinant. -/
theorem two_lane_graded_projection (x y : ℂ) :
    (parityLane 0 * occupationLane 0 x +
        parityLane 1 * occupationLane 1 x) *
      (parityLane 0 * occupationLane 0 y +
        parityLane 1 * occupationLane 1 y)
      =
    (1 - x) * (1 - y) := by
  norm_num [parityLane, occupationLane]
  ring_nf

/-- Three independent parity lanes produce the usual three-prime supertrace. -/
theorem three_lane_graded_projection (x y z : ℂ) :
    (1 - x) * (1 - y) * (1 - z)
      =
    1 - (x + y + z) + (x * y + x * z + y * z) - x * y * z := by
  ring

/--
Consolidated symbolic lane package:
idempotent occupation variables allow CAS-style symbolic manipulation before
projecting back to ordinary or graded finite Fock factors.
-/
theorem symbolic_fock_lane_synthesis :
    (∀ x : ℂ, occupationLane 0 x = 1) ∧
    (∀ x : ℂ, occupationLane 1 x = x) ∧
    parityLane 0 = 1 ∧
    parityLane 1 = -1 ∧
    (∀ e x : ℂ, Idempotent e → gradedLane e x = 1 - e - e * x) ∧
    (∀ x : ℂ, occupationLane 0 x + occupationLane 1 x = 1 + x) ∧
    (∀ x : ℂ,
      parityLane 0 * occupationLane 0 x +
        parityLane 1 * occupationLane 1 x = 1 - x) ∧
    (∀ x y : ℂ,
      (parityLane 0 * occupationLane 0 x +
          parityLane 1 * occupationLane 1 x) *
        (parityLane 0 * occupationLane 0 y +
          parityLane 1 * occupationLane 1 y)
        =
      (1 - x) * (1 - y)) := by
  exact ⟨occupationLane_empty,
    occupationLane_occupied,
    parityLane_empty,
    parityLane_occupied,
    fun e x he => gradedLane_idempotent he,
    ordinary_projected_local_factor,
    graded_projected_local_factor,
    two_lane_graded_projection⟩

end SymbolicFockLane

end noncomputable section
