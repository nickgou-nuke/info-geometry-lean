import Mathlib.Tactic
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport
import InfoGeometry.Thermodynamics.TomitaModularDeviance

/-!
# Scalar modular deviance on the Hestenes--Krein colimit

The operator expression

`exp (-β K) - 1 + β K`

is represented here by the native real scalar functional-calculus owner.  A
stage Hamiltonian is a real-valued readout on a doubled Hestenes carrier; the
colimit theorem is only the compatibility of that readout with the canonical
maps.  No operator exponential, logarithm, trace, or spectral theorem is
introduced by this file.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinModularDevianceColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Krein
open InfoGeometry.Thermodynamics.TomitaModularDeviance

variable {C : HestenesKreinCone}

def stageDeviance
    (β : ℝ) (K : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  scalar (β * K n x)

def limitDeviance
    (β : ℝ) (K : DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  scalar (β * K x)

theorem stageDeviance_nonneg
    (β : ℝ) (K : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 ≤ stageDeviance β K n x := by
  exact scalar_nonneg _

theorem limitDeviance_nonneg
    (β : ℝ) (K : DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) :
    0 ≤ limitDeviance β K x := by
  exact scalar_nonneg _

theorem stageDeviance_pos_iff
    (β : ℝ) (K : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 < stageDeviance β K n x ↔ β * K n x ≠ 0 := by
  exact scalar_pos_iff _

theorem limitDeviance_pos_iff
    (β : ℝ) (K : DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) :
    0 < limitDeviance β K x ↔ β * K x ≠ 0 := by
  exact scalar_pos_iff _

theorem stageDeviance_eq_limitDeviance
    (β : ℝ) (Kstage : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (Klimit : DoubledSpace C.LimitBase → ℝ)
    (hK : ∀ n x, Kstage n x = Klimit (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageDeviance β Kstage n x = limitDeviance β Klimit (C.ι n x) := by
  rw [stageDeviance, limitDeviance, hK n x]

theorem stageDeviance_bond
    (β : ℝ) (Kstage : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (Klimit : DoubledSpace C.LimitBase → ℝ)
    (hK : ∀ n x, Kstage n x = Klimit (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageDeviance β Kstage (n + 1) (C.bond n x) =
      stageDeviance β Kstage n x := by
  rw [stageDeviance_eq_limitDeviance β Kstage Klimit hK (n + 1) (C.bond n x),
    stageDeviance_eq_limitDeviance β Kstage Klimit hK n x]
  have hι : C.ι (n + 1) (C.bond n x) = C.ι n x :=
    congrArg (fun f => f x) (C.ι_bond n)
  exact congrArg (limitDeviance β Klimit) hι

theorem stageDeviance_bondIterate
    (β : ℝ) (Kstage : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (Klimit : DoubledSpace C.LimitBase → ℝ)
    (hK : ∀ n x, Kstage n x = Klimit (C.ι n x))
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageDeviance β Kstage (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) =
      stageDeviance β Kstage n x := by
  rw [stageDeviance_eq_limitDeviance β Kstage Klimit hK (n + m),
    stageDeviance_eq_limitDeviance β Kstage Klimit hK n]
  exact congrArg (limitDeviance β Klimit)
    (C.toFilteredPhaseCone.ι_bondIterate_apply n m x)

end InfoGeometry.Canonical.HestenesKreinModularDevianceColimit

end noncomputable section
