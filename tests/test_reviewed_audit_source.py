"""Python fixtures only: these tests do not elaborate or execute generated Lean."""
from pathlib import Path
import sys
import unittest
from tempfile import TemporaryDirectory

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tools.quality.reviewed_audit_source import (audit_source, validate_targets, validate_roles,
    may_reuse_cache, check_command_sources, COMMAND_ONLY_OWNERS, parse_audit_output)


class TargetValidationTests(unittest.TestCase):
    def test_order_and_input_are_preserved(self):
        source = ["InfoGeometry.Zeta", "InfoGeometry.Alpha"]
        result = validate_targets(source)
        self.assertEqual(result, source)
        self.assertIsNot(result, source)
        result.append("Other")
        self.assertEqual(source, ["InfoGeometry.Zeta", "InfoGeometry.Alpha"])

    def test_nonempty_tuple_and_identifier_components(self):
        self.assertEqual(validate_targets(("A._aux2", "A.foo'")), ["A._aux2", "A.foo'"])

    def test_wrong_container_and_empty_input_rejected(self):
        for value in (None, False, 4, "A.B", {"A.B": 1}, {"A.B"}, [], (), iter(["A.B"])):
            with self.subTest(value=value), self.assertRaises(ValueError):
                validate_targets(value)

    def test_nonstrings_rejected(self):
        for value in (None, 1, False, [], {}, b"A.B"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                validate_targets(["A.B", value])

    def test_duplicate_targets_rejected(self):
        with self.assertRaisesRegex(ValueError, "Duplicate reviewed module"):
            validate_targets(["A.B", "C.D", "A.B"])

    def test_malformed_or_unsupported_names_rejected(self):
        for name in ("", ".A", "A.", "A..B", "9A.B", "A.2B", " A.B", "A.B ",
                     "A/B", "../A", "A\\B", "A-B", "A:B", "A.β", "«A»", "A\x00B"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                validate_targets([name])

    def test_interpolation_payloads_rejected_by_generator(self):
        for name in ("A\nimport Evil", "A\nrun_cmd do pure ()", "A\n", "A\rB",
                     "A\tB", "A -- comment", "A/-comment-/", "A`B", 'A"B', "A»B"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                audit_source([name])


class GeneratedAuditFixtures(unittest.TestCase):
    def test_each_target_is_imported_and_quoted_in_name_array(self):
        generated = audit_source(["InfoGeometry.A", "InfoGeometry.B"])
        self.assertTrue(generated.startswith("import «InfoGeometry».«A»\nimport «InfoGeometry».«B»\n"))
        self.assertIn("let targets : Array Name := #[`«InfoGeometry».«A», `«InfoGeometry».«B»]", generated)

    def test_keyword_components_are_quoted(self):
        generated = audit_source(["namespace.end"])
        self.assertIn("import «namespace».«end»\n", generated)
        self.assertIn("#[`«namespace».«end»]", generated)

    def test_generator_validates_independently(self):
        for targets in ([], ["A", "A"], "A", ["A;B"]):
            with self.subTest(targets=targets), self.assertRaises(ValueError):
                audit_source(targets)

    def test_coverage_comes_from_actual_environment_owners(self):
        generated = audit_source(["Fixture.Nonempty", "Fixture.ImportOnly"])
        self.assertIn("for (name, info) in env.constants do", generated)
        self.assertIn("env.getModuleIdxFor? name", generated)
        self.assertIn("let owner := env.header.moduleNames[idx.toNat]!", generated)
        self.assertIn("if !targets.contains owner then continue", generated)
        self.assertEqual(generated.count("ownerCounts := ownerCounts.insert owner"), 1)
        self.assertNotIn("ownerCounts := ownerCounts.insert target", generated)

    def test_every_selected_owner_is_checked_before_completion(self):
        generated = audit_source(["Fixture.A", "Fixture.Empty"])
        expected = 'throwError "No declarations audited in reviewed module: {target}"'
        self.assertIn(expected, generated)
        self.assertIn("unless env.header.moduleNames.contains target do", generated)
        self.assertLess(generated.index("ownerCounts := ownerCounts.insert owner"), generated.index(expected))
        self.assertLess(generated.index(expected), generated.index('logInfo m!"AUDIT_COUNT:'))

    def test_public_collector_and_safety_checks_retained(self):
        generated = audit_source(["Fixture.A", "Fixture.B"])
        self.assertNotIn("Lean.CollectAxioms.", generated)
        self.assertEqual(generated.count("let axioms ← Lean.collectAxioms name"), 1)
        self.assertIn("for ax in axioms do", generated)
        self.assertIn("if !allAxioms.contains ax then", generated)
        self.assertIn("allAxioms := allAxioms.push ax", generated)
        self.assertIn('AUDIT_AXIOMS: {allAxioms.qsort Name.lt}', generated)
        self.assertIn("if info.isUnsafe || info.isPartial then", generated)
        self.assertIn("#[`propext, `Classical.choice, `Quot.sound]", generated)
        self.assertLess(generated.index("unless allowed.contains ax do"),
                        generated.index("ownerCounts := ownerCounts.insert owner"))

    def test_numeric_counts_are_accumulated_and_emitted_for_each_target(self):
        generated = audit_source(["Fixture.A", "Fixture.B"])
        self.assertIn("let mut ownerCounts : NameMap Nat := {}", generated)
        self.assertIn("ownerCounts.insert owner ((ownerCounts.find? owner).getD 0 + 1)", generated)
        self.assertIn("let moduleCount := (ownerCounts.find? target).getD 0", generated)
        self.assertIn('AUDIT_MODULE_COUNT: {target}: {moduleCount}', generated)
        self.assertIn("if moduleCount == 0 then", generated)
        self.assertIn("if moduleCount != 0 then", generated)
        self.assertLess(generated.index('AUDIT_MODULE_COUNT:'), generated.index('AUDIT_COUNT:'))

    def test_existing_completion_and_declaration_markers_retained(self):
        generated = audit_source(["Fixture.A"])
        self.assertIn('if count == 0 then throwError "No declarations audited"', generated)
        for marker in ("AUDIT_DECL:", "AUDIT_AXIOMS:", "AUDIT_COUNT:"):
            self.assertEqual(generated.count(marker), 1)


class CommandRoleFixtures(unittest.TestCase):
    def setUp(self):
        self.roles = list(COMMAND_ONLY_OWNERS)
        self.targets = list(self.roles)
        for owners in COMMAND_ONLY_OWNERS.values():
            self.targets.extend(owners)

    def test_exact_roles_and_owners_retained(self):
        self.assertEqual(validate_roles(self.targets), tuple(self.roles))
        self.assertEqual(validate_roles(self.targets, self.roles), tuple(self.roles))
        for owner in self.targets[len(self.roles):]:
            self.assertTrue(may_reuse_cache(owner, self.targets))
        for module in self.roles:
            self.assertFalse(may_reuse_cache(module, self.targets))
        self.assertTrue(may_reuse_cache("Other.Audit", ["Other.Audit"]))

    def test_bad_role_mappings_rejected(self):
        cases = [[], [self.roles[0]], self.roles + [self.roles[0]],
                 self.roles + ["Unknown.Audit"], self.roles + [self.targets[len(self.roles)]],
                 "bad", {self.roles[0]: "command-only"}]
        for roles in cases:
            with self.subTest(roles=roles), self.assertRaises(ValueError):
                validate_roles(self.targets, roles)
        with self.assertRaisesRegex(ValueError, "Nonselected"):
            validate_roles(["Other.Owner"], self.roles)

    def test_missing_required_owner_rejected(self):
        for owner in self.targets[len(self.roles):]:
            with self.subTest(owner=owner), self.assertRaisesRegex(ValueError, "selected owner"):
                audit_source([m for m in self.targets if m != owner])

    def test_unknown_audit_suffix_still_requires_positive_coverage(self):
        generated = audit_source(["Other.Audit"])
        self.assertIn("let commandOnly : Array Name := #[]", generated)
        self.assertIn('No declarations audited in reviewed module', generated)

    def test_reconstruction_examples_require_fresh_source_and_all_four_owners(self):
        module = 'InfoGeometry.Canonical.WeakValueReconstructionChecks'
        self.assertEqual(COMMAND_ONLY_OWNERS[module], (
            'InfoGeometry.Canonical.WeakValueEnstrophy',
            'InfoGeometry.Canonical.KreinSeamEvolution',
            'InfoGeometry.Canonical.WeakValueCylinderTransport',
            'InfoGeometry.Canonical.WeakValueForcedShear'))
        self.assertFalse(may_reuse_cache(module, self.targets))
        self.assertEqual(len(self.roles), 3)

    def test_zero_owned_and_presence_checks_without_skipping_declarations(self):
        generated = audit_source(self.targets)
        self.assertIn('unless env.header.moduleNames.contains target do', generated)
        self.assertIn('if commandOnly.contains target then\n      if moduleCount != 0 then', generated)
        self.assertIn('Command-only module owns declarations:', generated)
        loop = generated.split('for (name, info) in env.constants do', 1)[1].split('  for target in targets do', 1)[0]
        self.assertNotIn('commandOnly', loop)
        self.assertIn('Lean.collectAxioms name', loop)
        for module in self.targets:
            self.assertIn('import ' + '.'.join('«' + p + '»' for p in module.split('.')), generated)

    def test_allowlist_is_immutable(self):
        with self.assertRaises(TypeError):
            COMMAND_ONLY_OWNERS['Other.Audit'] = ()

    def test_changed_command_source_rejected(self):
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            for module in self.roles:
                path = root / (module.replace('.', '/') + '.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('-- changed or emptied command source\n')
            with self.assertRaisesRegex(ValueError, 'role review required'):
                check_command_sources(root, self.targets)

    def test_missing_command_source_rejected(self):
        with TemporaryDirectory() as temporary:
            with self.assertRaises(FileNotFoundError):
                check_command_sources(Path(temporary), self.targets)



class AuditReceiptTests(unittest.TestCase):
    targets = ["Fixture.A", "Fixture.B"]
    good = ("AUDIT_MODULE_COUNT: Fixture.A: 2\nAUDIT_MODULE: Fixture.A\n"
            "AUDIT_MODULE_COUNT: Fixture.B: 1\nAUDIT_MODULE: Fixture.B\nAUDIT_COUNT: 3\n")

    def test_exact_counts(self):
        self.assertEqual(parse_audit_output(self.good, self.targets),
                         {"Fixture.A": 2, "Fixture.B": 1})

    def test_partial_duplicate_wrong_role_and_total_rejected(self):
        bad = [self.good.replace("AUDIT_MODULE: Fixture.B\n", ""),
               self.good + "AUDIT_MODULE_COUNT: Fixture.A: 2\n",
               self.good + "AUDIT_MODULE: Fixture.A\n",
               self.good + "AUDIT_COUNT: 3\n",
               self.good.replace("AUDIT_COUNT: 3", "AUDIT_COUNT: 4"),
               self.good.replace("Fixture.B: 1", "Fixture.B: 0"),
               self.good.replace("AUDIT_MODULE: Fixture.B", "AUDIT_COMMAND_MODULE: Fixture.B"),
               self.good.replace("AUDIT_MODULE_COUNT: Fixture.B", "AUDIT_MODULE_COUNT: Fixture.C")]
        for text in bad:
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_audit_output(text, self.targets)

    def test_explicit_command_zero_with_audited_owners(self):
        command = "InfoGeometry.Algebra.CuntzClifford22Audit"
        owners = list(COMMAND_ONLY_OWNERS[command])
        targets = [command, *owners]
        text = f"AUDIT_MODULE_COUNT: {command}: 0\nAUDIT_COMMAND_MODULE: {command}\n"
        for owner in owners:
            text += f"AUDIT_MODULE_COUNT: {owner}: 1\nAUDIT_MODULE: {owner}\n"
        text += f"AUDIT_COUNT: {len(owners)}\n"
        self.assertEqual(parse_audit_output(text, targets)[command], 0)
        with self.assertRaises(ValueError):
            parse_audit_output(text.replace(f"{command}: 0", f"{command}: 1"), targets)

if __name__ == "__main__":
    unittest.main()
