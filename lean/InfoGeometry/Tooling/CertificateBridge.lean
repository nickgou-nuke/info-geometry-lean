import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry/Tooling/CertificateBridge.lean

The former external-certificate API has intentionally been removed.  Strings,
optional rationals, and identity forwarding theorems are not proof owners.
Actual computational claims must now be represented by native Lean
propositions and proved in their mathematical owner modules.
-/
