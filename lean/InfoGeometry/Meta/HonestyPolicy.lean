import InfoGeometry.Meta.Admission
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Meta.Trust

/-!
# InfoGeometry.Meta.HonestyPolicy

Repository honesty policy.

The rule is simple:

- if a Mathlib-rooted derivation chain exists, state it as a proof;
- if it does not exist yet, expose the gap explicitly as `sorry` or an
  explicit zero-datum;
- do not hide missing debt behind fake witnesses, empty shells, or banners
  that claim certified readback when the file still contains debt markers.

This module is descriptive. Enforcement lives in the existing policy and lint
layers:

- `InfoGeometry.Meta.OwnerTarget`
- `InfoGeometry.Meta.SocketTarget`
- `InfoGeometry.Meta.Trust`
- `InfoGeometry.Meta.Admission`
- `InfoGeometry.Meta.Vacuity`

The policy here is the baseline mandate that those layers are meant to enforce.
-/

noncomputable section

namespace InfoGeometry.Meta

/--
Repository policy snapshot for honesty about proof debt.

This is a lightweight, importable policy record. It is not a theorem and it is
not a lint engine; it is the canonical textual mandate for the repo.
-/
structure HonestyPolicy where
  /-- Explicit `sorry` is acceptable only as visible debt. -/
  explicitSorryVisible : Bool
  /-- Fake witnesses and empty closure shells are forbidden. -/
  fakeWitnessesForbidden : Bool
  /-- Banner text must not claim certified readback when `sorry` remains. -/
  bannerClaimsMustMatchBody : Bool
  /-- Explicit zero-datum objects are allowed when they are declared as such. -/
  explicitZeroDatumAllowed : Bool
  /-- Zero-datum surfaces must be named and documented as debt, not proof. -/
  explicitZeroDatumMustBeNamed : Bool
  /-- Socket-level debt must be machine-visible. -/
  socketDebtMustBeTagged : Bool
  /-- Owner-target debt must be machine-visible. -/
  ownerDebtMustBeMachineVisible : Bool
  /-- Textual mandate for future maintainers. -/
  mandateText : String

/-- The repository-default honesty policy. -/
def defaultHonestyPolicy : HonestyPolicy :=
  { explicitSorryVisible := true
    fakeWitnessesForbidden := true
    bannerClaimsMustMatchBody := true
    explicitZeroDatumAllowed := true
    explicitZeroDatumMustBeNamed := true
    socketDebtMustBeTagged := true
    ownerDebtMustBeMachineVisible := true
    mandateText :=
      "If a Mathlib-rooted derivation chain is missing, expose the gap explicitly as sorry or an explicit zero-datum. Do not hide debt behind fake witnesses, empty shells, or misleading certification banners." }

/--
Human-readable summary of the repository honesty policy.

This is intended for audit output and documentation, not as a proof object.
-/
def honestyPolicySummary : String :=
  defaultHonestyPolicy.mandateText

end InfoGeometry.Meta
