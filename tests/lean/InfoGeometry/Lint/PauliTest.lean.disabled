import InfoGeometry.Lint.Pauli

namespace InfoGeometry.Canonical

/--
This theorem uses sorry and should be caught by the Pauli linter.
-/
theorem sorry_test : 1 + 1 = 3 := by
  sorry

/--
This theorem is proved via rfl and should be caught by the Pauli grandUnity linter
if it's in the Canonical namespace.
-/
theorem rfl_test : 1 + 1 = 2 := rfl

/--
This theorem uses a physical keyword 'Einstein' but has no foundation.
Should be caught by the No-Mask Mandate.
-/
theorem Einstein_test : 1 + 1 = 2 := rfl

end InfoGeometry.Canonical

namespace InfoGeometry.Exploratory

/--
This is NOT in the Canonical namespace, so the linter should ignore it.
-/
theorem sorry_ignore_test : 1 + 1 = 4 := by
  sorry

end InfoGeometry.Exploratory
