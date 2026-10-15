import InfoGeometry.Lint.Pauli

namespace InfoGeometry.Canonical

/--
warning: declaration uses `sorry`
---
info: [Pauli/Closure Debt] InfoGeometry.Canonical.sorry_test explicitly depends on `sorryAx`; permitted as honest closure debt, not eligible for contraction/deletion.
---
error: [Pauli/Identity-via-Reflexivity] InfoGeometry.Canonical.sorry_test recursively evaluates to a trivial/tautological proof. Metric: { termNodeCount := 1,
  utilizesMathlibAxioms := false,
  containsVacuousSockets := false,
  unfoldedLocalWrapperCount := 0,
  hitUnfoldLimit := false,
  containsSorry := true }
-/
#guard_msgs in
theorem sorry_test : 1 + 1 = 3 := by
  sorry

/--
error: [Pauli/Identity-via-Reflexivity] InfoGeometry.Canonical.rfl_test is proved via trivial `rfl`.
-/
#guard_msgs in
theorem rfl_test : 1 + 1 = 2 := rfl

/--
error: [Pauli/Identity-via-Reflexivity] InfoGeometry.Canonical.Einstein_test is proved via trivial `rfl`.
---
warning: [Pauli/No-Mask Mandate] InfoGeometry.Canonical.Einstein_test uses a physically-loaded name but does not transitively depend on foundational Core or Algebra transformations. Ensure this is not symbolic inflation.
-/
#guard_msgs in
theorem Einstein_test : 1 + 1 = 2 := rfl

end InfoGeometry.Canonical

namespace InfoGeometry.Exploratory

/--
warning: declaration uses `sorry`
-/
#guard_msgs in
theorem sorry_ignore_test : 1 + 1 = 4 := by
  sorry

end InfoGeometry.Exploratory
