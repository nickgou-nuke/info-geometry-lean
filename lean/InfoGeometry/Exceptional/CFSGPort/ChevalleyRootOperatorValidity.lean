module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorTables

/-!
# Kernel checks for decoded exceptional root-operator indices

These checks establish the input/output index bounds for every stored
coefficient of degrees 1, 2, and 3. They do not assert agreement with the
pinned generators or the commutator relations.
-/

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem allValid_G2 : allValid .G2 = true := by decide +kernel
theorem allValid_F4 : allValid .F4 = true := by decide +kernel
theorem allValid_D4 : allValid .D4 = true := by decide +kernel
theorem allValid_E6 : allValid .E6 = true := by decide +kernel
theorem allValid_E7 : allValid .E7 = true := by decide +kernel
theorem allValid_E8 : allValid .E8 = true := by decide +kernel

theorem allValid_tag : ∀ τ : Tag, allValid τ = true
  | .G2 => allValid_G2
  | .F4 => allValid_F4
  | .D4 => allValid_D4
  | .E6 => allValid_E6
  | .E7 => allValid_E7
  | .E8 => allValid_E8

/-- Every stored sparse coefficient is an endomorphism on the valid
root-module indices. -/
theorem entries_valid (τ : Tag) {a k : ℕ}
    (ha : a < τ.rootCertificate.roots.length) (hk : k ∈ [1, 2, 3]) :
    ValidEntries τ (entries τ a k) :=
  validEntries_of_validB (validB_of_allValid (allValid_tag τ) ha hk)

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
