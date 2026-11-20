"""Filesystem and cache-identity tests only; no Lean, Lake, or build lock is used."""
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tools.quality.check_reviewed_prs import (
    SOURCE_FINGERPRINT_VERSION,
    closure,
    repository_source_fingerprint,
    repository_source_path,
)


class RepositorySourceTests(unittest.TestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.parent = Path(temporary.name)
        self.repo = self.parent / 'repo'
        self.repo.mkdir()

    def write(self, relative, text=''):
        path = self.repo / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def test_default_ordinary_module_stays_under_lean(self):
        expected = self.write('lean/InfoGeometry/Owner.lean')
        self.write('InfoGeometry/Owner.lean', 'import Missing.RootShadow\n')
        self.assertEqual(repository_source_path(self.repo, 'InfoGeometry.Owner'), expected)
        self.assertEqual(closure(self.repo, ['InfoGeometry.Owner']),
                         (['InfoGeometry.Owner'], {'InfoGeometry.Owner': []}, set()))

    def test_opt_in_does_not_change_ordinary_module_lookup(self):
        expected = self.write('lean/InfoGeometry/Owner.lean')
        self.assertEqual(repository_source_path(
            self.repo, 'InfoGeometry.Owner', allow_root_proofs=True), expected)

    def test_root_proofs_module_requires_opt_in(self):
        expected = self.write('proofs/Native.lean')
        self.assertEqual(repository_source_path(
            self.repo, 'proofs.Native', allow_root_proofs=True), expected)
        self.assertEqual(repository_source_path(self.repo, 'proofs.Native'),
                         self.repo / 'lean/proofs/Native.lean')
        with self.assertRaises(FileNotFoundError):
            closure(self.repo, ['proofs.Native'])
        self.assertEqual(closure(self.repo, ['proofs.Native'], allow_root_proofs=True),
                         (['proofs.Native'], {'proofs.Native': []}, set()))

    def test_default_preserves_existing_lean_proofs_namespace(self):
        expected = self.write('lean/proofs/Legacy.lean')
        self.write('proofs/Legacy.lean', 'import Missing.RootDependency\n')
        self.assertEqual(repository_source_path(self.repo, 'proofs.Legacy'), expected)
        self.assertEqual(closure(self.repo, ['proofs.Legacy'])[0], ['proofs.Legacy'])

    def test_opt_in_selects_root_proofs_without_lean_fallback(self):
        self.write('lean/proofs/Native.lean', 'import Missing.LeanShadow\n')
        expected = self.write('proofs/Native.lean')
        self.assertEqual(repository_source_path(
            self.repo, 'proofs.Native', allow_root_proofs=True), expected)
        self.assertEqual(closure(self.repo, ['proofs.Native'], allow_root_proofs=True)[0],
                         ['proofs.Native'])
        self.write('lean/proofs/OnlyInLean.lean')
        with self.assertRaises(FileNotFoundError):
            closure(self.repo, ['proofs.OnlyInLean'], allow_root_proofs=True)

    def test_mixed_closure_keeps_dependency_order_and_three_item_return(self):
        self.write('lean/InfoGeometry/Leaf.lean')
        self.write('proofs/Helper.lean', 'import InfoGeometry.Leaf\n')
        self.write('lean/InfoGeometry/Main.lean',
                   'import InfoGeometry.Leaf proofs.Helper Mathlib.Data.Real.Basic -- comment\n')
        result = closure(self.repo, ['InfoGeometry.Main'], allow_root_proofs=True)
        self.assertEqual(len(result), 3)
        self.assertEqual(result[0], ['InfoGeometry.Leaf', 'proofs.Helper', 'InfoGeometry.Main'])
        self.assertEqual(result[1], {
            'InfoGeometry.Leaf': [], 'proofs.Helper': ['InfoGeometry.Leaf'],
            'InfoGeometry.Main': ['InfoGeometry.Leaf', 'proofs.Helper']})
        self.assertEqual(result[2], {'Mathlib/Data/Real/Basic.lean'})

    def test_target_order_and_repeated_dependencies_keep_existing_behavior(self):
        self.write('lean/Shared.lean')
        self.write('lean/First.lean', 'import Shared\n')
        self.write('lean/Second.lean', 'import Shared\n')
        self.assertEqual(closure(self.repo, ['Second', 'First', 'Second'])[0],
                         ['Shared', 'Second', 'First'])
        self.assertEqual(closure(self.repo, []), ([], {}, set()))

    def test_missing_ordinary_import_fails(self):
        self.write('lean/Owner.lean', 'import InfoGeometry.Missing\n')
        with self.assertRaisesRegex(RuntimeError, 'Owner -> InfoGeometry.Missing'):
            closure(self.repo, ['Owner'], allow_root_proofs=True)

    def test_missing_proofs_import_fails(self):
        self.write('lean/Owner.lean', 'import proofs.Missing\n')
        with self.assertRaisesRegex(RuntimeError, 'Owner -> proofs.Missing'):
            closure(self.repo, ['Owner'], allow_root_proofs=True)

    def test_root_proofs_import_is_unresolved_by_default(self):
        self.write('lean/Owner.lean', 'import proofs.Native\n')
        self.write('proofs/Native.lean')
        with self.assertRaisesRegex(RuntimeError, 'Owner -> proofs.Native'):
            closure(self.repo, ['Owner'])

    def test_missing_target_fails(self):
        with self.assertRaises(FileNotFoundError):
            closure(self.repo, ['InfoGeometry.Missing'], allow_root_proofs=True)

    def test_arbitrary_repository_root_is_never_a_source_fallback(self):
        self.write('Extra/Owner.lean')
        self.write('src/Extra/Owner.lean')
        self.write('lean/Main.lean', 'import Extra.Owner\n')
        for opt_in in (False, True):
            with self.subTest(opt_in=opt_in):
                self.assertEqual(repository_source_path(
                    self.repo, 'Extra.Owner', allow_root_proofs=opt_in),
                    self.repo / 'lean/Extra/Owner.lean')
                with self.assertRaisesRegex(RuntimeError, 'Main -> Extra.Owner'):
                    closure(self.repo, ['Main'], allow_root_proofs=opt_in)

    def test_malformed_and_path_escaping_names_fail_before_lookup(self):
        invalid = ('', '.', '..', '../Outside', '/absolute', 'A/B', 'A\\B',
                   'A..B', '.A', 'A.', 'proofs..Escape', 'proofs/Native',
                   'Mathlib../Escape', ' A', 'A\nimport Evil', 'A;B', 'A.β',
                   None, 3)
        for name in invalid:
            for opt_in in (False, True):
                with self.subTest(name=name, opt_in=opt_in), self.assertRaises(ValueError):
                    repository_source_path(self.repo, name, allow_root_proofs=opt_in)

    def test_malformed_native_looking_import_is_not_silently_classified(self):
        self.write('lean/Owner.lean', 'import Mathlib../Escape\n')
        with self.assertRaises(ValueError):
            closure(self.repo, ['Owner'], allow_root_proofs=True)

    def test_valid_identifier_conventions_are_preserved(self):
        expected = self.write("lean/namespace/_helper2'.lean")
        self.assertEqual(repository_source_path(self.repo, "namespace._helper2'"), expected)

    def test_file_symlink_cannot_escape_selected_source_root(self):
        outside = self.parent / 'Outside.lean'
        outside.write_text('')
        for relative, module, opt_in in (
                ('lean/Owner.lean', 'Owner', False),
                ('proofs/Owner.lean', 'proofs.Owner', True)):
            link = self.repo / relative
            link.parent.mkdir(parents=True, exist_ok=True)
            link.symlink_to(outside)
            with self.subTest(module=module), self.assertRaisesRegex(ValueError, 'escapes'):
                repository_source_path(self.repo, module, allow_root_proofs=opt_in)

    def test_directory_symlink_cannot_cross_from_lean_into_root_proofs(self):
        self.write('proofs/Owner.lean')
        (self.repo / 'lean').mkdir()
        (self.repo / 'lean/Alias').symlink_to(self.repo / 'proofs', target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'escapes'):
            repository_source_path(self.repo, 'Alias.Owner', allow_root_proofs=True)

    def test_in_root_symlink_reports_actual_resolved_source(self):
        actual = self.write('lean/Actual.lean')
        (self.repo / 'lean/Alias.lean').symlink_to(actual)
        self.assertEqual(repository_source_path(self.repo, 'Alias'), actual)

    def test_ordinary_cycle_fails(self):
        self.write('lean/First.lean', 'import Second\n')
        self.write('lean/Second.lean', 'import First\n')
        with self.assertRaisesRegex(RuntimeError, 'Import cycle at First'):
            closure(self.repo, ['First'])

    def test_mixed_source_cycle_fails(self):
        self.write('lean/Owner.lean', 'import proofs.Helper\n')
        self.write('proofs/Helper.lean', 'import Owner\n')
        with self.assertRaisesRegex(RuntimeError, 'Import cycle at Owner'):
            closure(self.repo, ['Owner'], allow_root_proofs=True)

    def test_native_import_classification_is_unchanged(self):
        self.write('lean/Owner.lean',
                   'import Mathlib Mathlib.Data.Real.Basic Lean Lean.Meta Std Std.Data.Init Init\n')
        ordered, dependencies, native = closure(self.repo, ['Owner'], allow_root_proofs=True)
        self.assertEqual(ordered, ['Owner'])
        self.assertEqual(dependencies, {'Owner': []})
        self.assertEqual(native, {'Mathlib.lean', 'Mathlib/Data/Real/Basic.lean'})

    def test_native_prefix_lookalike_remains_unresolved(self):
        self.write('lean/Owner.lean', 'import MathlibExtra.Algebra\n')
        with self.assertRaisesRegex(RuntimeError, 'Owner -> MathlibExtra.Algebra'):
            closure(self.repo, ['Owner'], allow_root_proofs=True)

    def test_local_native_named_source_keeps_existing_precedence(self):
        self.write('lean/Mathlib/Local.lean')
        self.write('lean/Owner.lean', 'import Mathlib.Local\n')
        ordered, dependencies, native = closure(self.repo, ['Owner'])
        self.assertEqual(ordered, ['Mathlib.Local', 'Owner'])
        self.assertEqual(dependencies['Owner'], ['Mathlib.Local'])
        self.assertEqual(native, set())


class SourceFingerprintTests(unittest.TestCase):
    def fingerprint(self, **changes):
        values = dict(module='proofs.Owner', source_path='proofs/Owner.lean',
                      source_sha256='source-bytes', toolchain='leanprover/lean4:v4.34.1',
                      mathlib_revision='pinned-revision', dependency_fingerprints=['dependency'])
        values.update(changes)
        return repository_source_fingerprint(**values)

    def test_fingerprint_format_is_versioned_and_deterministic(self):
        self.assertEqual(SOURCE_FINGERPRINT_VERSION, 2)
        self.assertEqual(self.fingerprint(), self.fingerprint())
        self.assertEqual(len(self.fingerprint()), 64)

    def test_identical_module_and_bytes_from_different_roots_do_not_share_cache(self):
        self.assertNotEqual(self.fingerprint(),
                            self.fingerprint(source_path='lean/proofs/Owner.lean'))

    def test_all_existing_cache_inputs_remain_bound(self):
        for changes in (dict(module='proofs.Other'), dict(source_sha256='changed-bytes'),
                        dict(toolchain='changed-toolchain'), dict(mathlib_revision='changed-pin'),
                        dict(dependency_fingerprints=['changed-dependency'])):
            with self.subTest(changes=changes):
                self.assertNotEqual(self.fingerprint(), self.fingerprint(**changes))


if __name__ == '__main__':
    unittest.main()
