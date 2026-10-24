"""UNEXECUTED QA draft. Run only after final freeze/A-A, under shared BuildLock.

Mocks establish control flow, not provenance or kernel acceptance. This module
never edits or compiles repository owners and never runs the reviewed65 build.
"""
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch, MagicMock

ROOT = Path(__file__).resolve().parents[2]
CANDIDATE = ROOT / 'scratch/reviewed_native65_20261023/native_reviewed.py'


def load_candidate():
    spec = importlib.util.spec_from_file_location('native65_qa_candidate', CANDIDATE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class ProvenanceFixtures(unittest.TestCase):
    def setUp(self):
        self.m = load_candidate()
        self.tmp = tempfile.TemporaryDirectory(prefix='native65-provenance-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.pkg = self.root / '.lake/packages/Pkg'
        self.pkg.mkdir(parents=True)
        (self.pkg / '.git').mkdir()
        (self.pkg / 'lakefile.lean').write_text('-- fixture only\n')
        (self.root / 'owner.lean').write_text('-- fixture only\n')
        self.entry = {'name': 'Pkg', 'type': 'git', 'rev': 'fixture-pin'}
        self.manifest([self.entry])
        self.dirty_package = self.dirty_root = ''
        self.installed_revision = 'fixture-pin'
        self.package_top = str(self.pkg)
        self.package_index = ''

    def manifest(self, entries):
        (self.root / 'lake-manifest.json').write_text(json.dumps({
            'packagesDir': '.lake/packages', 'packages': entries}))

    def git(self, directory, *args):
        directory = Path(directory)
        if args == ('rev-parse', '--show-toplevel'):
            return self.package_top
        if args == ('rev-parse', 'HEAD'):
            return self.installed_revision if directory == self.pkg else 'fixture-root'
        if args[0] == 'status':
            return self.dirty_package if directory == self.pkg else self.dirty_root
        if args == ('ls-files', '--stage'):
            return self.package_index
        if args == ('ls-files', '-z'):
            return 'owner.lean\0lake-manifest.json\0'
        raise AssertionError((directory, args))

    def identity(self, ok=True):
        with patch.object(self.m, 'path_package_report', return_value={'ok': ok}), \
             patch.object(self.m, 'git', side_effect=self.git):
            return self.m.source_identity(self.root)

    def test_mock_clean_exact_pin_is_recorded(self):
        result = self.identity()
        self.assertEqual(result['revision'], 'fixture-root')
        self.assertEqual(result['packages'][0]['entry']['rev'], 'fixture-pin')
        self.assertIn('owner.lean', result['source_sha256'])

    def test_bootstrap_rejection_is_not_overridden(self):
        with self.assertRaisesRegex(RuntimeError, 'path provenance'):
            self.identity(ok=False)

    def test_wrong_package_revision_rejected(self):
        self.installed_revision = 'different'
        with self.assertRaisesRegex(RuntimeError, 'revision differs'):
            self.identity()

    def test_dirty_package_rejected(self):
        for dirty in (' M tracked.lean', '?? untracked.lean', 'M  staged.lean'):
            self.dirty_package = dirty
            with self.subTest(dirty=dirty), self.assertRaisesRegex(RuntimeError, 'Dirty package'):
                self.identity()

    def test_dirty_root_rejected(self):
        self.dirty_root = '?? draft.lean'
        with self.assertRaisesRegex(RuntimeError, 'clean committed checkout'):
            self.identity()

    def test_package_not_own_repository_rejected(self):
        self.package_top = str(self.root)
        with self.assertRaisesRegex(RuntimeError, 'own repository'):
            self.identity()

    def test_nested_gitlinks_rejected(self):
        self.package_index = '160000 deadbeef 0\tnested\n'
        with self.assertRaisesRegex(RuntimeError, 'Nested gitlinks'):
            self.identity()

    def test_duplicate_package_rejected(self):
        self.manifest([self.entry, self.entry])
        with self.assertRaisesRegex(RuntimeError, 'duplicate'):
            self.identity()

    def test_subdir_rejected(self):
        self.manifest([{**self.entry, 'subDir': 'nested'}])
        with self.assertRaisesRegex(RuntimeError, 'subDir'):
            self.identity()

    def test_escaping_provider_rejected(self):
        self.manifest([{**self.entry, 'name': '../outside'}])
        with self.assertRaisesRegex(RuntimeError, 'Invalid/duplicate'):
            self.identity()

    def test_warm_build_rejected_without_deletion(self):
        build = self.pkg / '.lake/build'; build.mkdir(parents=True)
        artifact = build / 'fixture.olean'; artifact.write_bytes(b'keep me')
        with self.assertRaisesRegex(RuntimeError, 'preexisting build'):
            self.m.require_cold_builds(self.root, {'packages': [{'directory': str(self.pkg)}]})
        self.assertEqual(artifact.read_bytes(), b'keep me')

    def test_cached_lake_config_rejected(self):
        lake = self.pkg / '.lake'; lake.mkdir()
        artifact = lake / 'lakefile.olean'; artifact.write_bytes(b'keep config')
        with self.assertRaisesRegex(RuntimeError, 'cached Lake configuration'):
            self.m.require_cold_builds(self.root, {'packages': [{'directory': str(self.pkg)}]})
        self.assertTrue(artifact.exists())


class NativeEntryPreflightFixtures(unittest.TestCase):
    def setUp(self):
        self.m = load_candidate()
        self.tmp = tempfile.TemporaryDirectory(prefix='native65-entry-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        spec = self.root / 'tools/quality/reviewed_prs_20260921.json'
        spec.parent.mkdir(parents=True)
        # Exact live target order, not a reduced or fabricated 65-owner set.
        self.targets = json.loads((ROOT / 'tools/quality/reviewed_prs_20260921.json').read_text())['targets']
        spec.write_text(json.dumps({'targets': self.targets}))
        self.output = self.root / '.artifacts/fresh'

    def test_wrong_cwd_stops_before_lock_and_children(self):
        with patch.object(self.m, 'BuildLock') as lock, patch.object(self.m.subprocess, 'Popen') as popen:
            with self.assertRaisesRegex(RuntimeError, 'native repository root'):
                self.m.run_native(self.root, self.output)
            lock.assert_not_called(); popen.assert_not_called()

    def test_existing_output_rejected(self):
        self.output.mkdir(parents=True)
        with patch.object(Path, 'cwd', return_value=self.root), patch.object(self.m, 'BuildLock') as lock:
            with self.assertRaises(FileExistsError):
                self.m.run_native(self.root, self.output)
            lock.assert_not_called()

    def test_provenance_failure_preserves_exact_targets_and_report(self):
        fake_lock = MagicMock()
        with patch.object(Path, 'cwd', return_value=self.root), \
             patch.object(self.m, 'BuildLock', return_value=fake_lock), \
             patch.object(self.m, 'idle'), \
             patch.dict(os.environ, {}, clear=True), \
             patch.object(self.m, 'source_identity', side_effect=RuntimeError('fixture provenance failure')), \
             patch.object(self.m.subprocess, 'Popen') as popen:
            with self.assertRaisesRegex(RuntimeError, 'fixture provenance failure'):
                self.m.run_native(self.root, self.output)
            popen.assert_not_called()
        report = json.loads((self.output / 'report.json').read_text())
        self.assertEqual(report['targets'], self.targets)
        self.assertEqual(report['status'], 'failed')
        self.assertEqual(report['commands'], [])
        self.assertIn('fixture provenance failure', report['error'])


if __name__ == '__main__':
    unittest.main()
