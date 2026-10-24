"""UNEXECUTED until A-A clearance; narrow source scanner regression fixtures.

Temporary directories only. No native build, checkout repair, or source edits.
Run serially under the shared verification lock after parent authorization.
"""
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality.reviewed_native import source_files


class KiloWorktreeBoundaryFixtures(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='qa-kilo-scan-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def broken_link(self, relative):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.symlink_to('lib/scripts')
        self.assertTrue(path.is_symlink())
        self.assertFalse(path.exists())
        return path

    def test_nested_worktree_broken_symlink_excluded(self):
        self.write('Owner.lean', '-- native owner\n')
        link = self.broken_link('.kilo/worktrees/muddy-onion/.agents/workflows/lean4/scripts')
        self.write('.kilo/worktrees/muddy-onion/Foreign.lean', '-- independent checkout\n')
        scanned = source_files(self.root, excluded_directories=frozenset({'.kilo/worktrees'}))
        self.assertIn('Owner.lean', scanned)
        self.assertFalse(any(p.startswith('.kilo/worktrees/') for p in scanned))
        self.assertTrue(link.is_symlink(), 'Scanner must not delete or repair excluded sources')

    def test_default_scan_does_not_exclude_nested_worktrees(self):
        self.broken_link('.kilo/worktrees/foreign/broken')
        with self.assertRaisesRegex(RuntimeError, 'Unreadable/special source'):
            source_files(self.root)

    def test_explicit_empty_exclusions_preserve_dependency_scan(self):
        self.broken_link('.kilo/worktrees/dependency/broken')
        with self.assertRaisesRegex(RuntimeError, 'Unreadable/special source'):
            source_files(self.root, excluded_directories=frozenset())

    def test_exclusion_is_relative_not_any_nested_kilo_match(self):
        self.broken_link('nested/.kilo/worktrees/foreign/broken')
        with self.assertRaisesRegex(RuntimeError, 'Unreadable/special source'):
            source_files(self.root, excluded_directories=frozenset({'.kilo/worktrees'}))

    def test_ordinary_kilo_siblings_are_hashed_and_changes_detected(self):
        self.broken_link('.kilo/worktrees/nested/broken')
        direct = self.write('.kilo/sibling.lean', '-- first\n')
        self.write('.kilo/sources/Kept.lean', '-- kept nested sibling\n')
        before = source_files(self.root, excluded_directories=frozenset({'.kilo/worktrees'}))
        self.assertIn('.kilo/sibling.lean', before)
        self.assertIn('.kilo/sources/Kept.lean', before)
        self.assertEqual(before['.kilo/sibling.lean']['sha256'], hashlib.sha256(direct.read_bytes()).hexdigest())
        direct.write_text('-- second\n')
        self.assertNotEqual(before['.kilo/sibling.lean'], source_files(self.root, excluded_directories=frozenset({'.kilo/worktrees'}))['.kilo/sibling.lean'])

    def test_ordinary_ignored_lean_sources_still_hashed(self):
        self.write('.gitignore', 'ignored/\nHidden.lean\n.kilo/\n')
        hidden = self.write('Hidden.lean', '-- ignored direct source\n')
        self.write('ignored/Owner.lean', '-- ignored nested source\n')
        self.write('.kilo/Kept.lean', '-- ignored editor sibling\n')
        before = source_files(self.root, excluded_directories=frozenset({'.kilo/worktrees'}))
        for name in ('Hidden.lean', 'ignored/Owner.lean', '.kilo/Kept.lean'):
            self.assertIn(name, before)
        hidden.write_text('-- changed ignored direct source\n')
        self.assertNotEqual(before['Hidden.lean'], source_files(self.root, excluded_directories=frozenset({'.kilo/worktrees'}))['Hidden.lean'])

    def test_worktrees_name_outside_kilo_is_not_excluded(self):
        for relative in ('worktrees/Owner.lean', '.other/worktrees/Owner.lean', '.kilo/worktreesSibling/Owner.lean'):
            self.write(relative, '-- retained\n')
        scanned = source_files(self.root, excluded_directories=frozenset({'.kilo/worktrees'}))
        for relative in ('worktrees/Owner.lean', '.other/worktrees/Owner.lean', '.kilo/worktreesSibling/Owner.lean'):
            self.assertIn(relative, scanned)

    def test_broken_symlink_in_kilo_sibling_still_rejected(self):
        self.broken_link('.kilo/sources/broken')
        with self.assertRaisesRegex(RuntimeError, 'Unreadable/special source'):
            source_files(self.root, excluded_directories=frozenset({'.kilo/worktrees'}))

    def test_broken_symlink_in_unrelated_worktrees_still_rejected(self):
        self.broken_link('worktrees/ordinary/broken')
        with self.assertRaisesRegex(RuntimeError, 'Unreadable/special source'):
            source_files(self.root, excluded_directories=frozenset({'.kilo/worktrees'}))


if __name__ == '__main__':
    unittest.main()
