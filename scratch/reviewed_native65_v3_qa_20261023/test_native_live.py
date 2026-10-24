"""Bounded independent QA; run only under shared lock after aggregate lane ends.

All run_native success scenarios below MOCK compilers/provenance and are not
native acceptance. No owner edits, package fetches, cache deletion or builds.
"""
from contextlib import ExitStack
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch, MagicMock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import reviewed_native as native
from tools.quality import check_reviewed_prs as cli
from tools.quality.reviewed_audit_source import validate_roles


class SourceFixtures(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='native-v3-source-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()

    def test_ignored_source_included_and_cache_unchanged(self):
        (self.root / '.gitignore').write_text('ignored.lean\n')
        (self.root / 'ignored.lean').write_text('first')
        cache = self.root / '.lake/config'; cache.mkdir(parents=True)
        (cache / 'lakefile.olean').write_bytes(b'preserve')
        before = native.source_files(self.root)
        self.assertIn('ignored.lean', before)
        self.assertFalse(any(p.startswith('.lake/') for p in before))
        (self.root / 'ignored.lean').write_text('second')
        self.assertNotEqual(before, native.source_files(self.root))
        self.assertEqual((cache / 'lakefile.olean').read_bytes(), b'preserve')

    def test_symlink_file_binds_target_bytes_and_link(self):
        target = self.root / 'real.lean'; target.write_text('first')
        link = self.root / 'link.lean'; link.symlink_to('real.lean')
        before = native.source_files(self.root)
        self.assertEqual(before['link.lean']['link'], 'real.lean')
        self.assertEqual(before['link.lean']['resolved'], str(target))
        target.write_text('second')
        self.assertNotEqual(before['link.lean'], native.source_files(self.root)['link.lean'])

    def test_source_directory_symlink_rejected(self):
        (self.root / 'real').mkdir(); (self.root / 'alias').symlink_to('real', target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, 'directory symlink'):
            native.source_files(self.root)

    def package(self):
        package = self.root / 'Paperproof/lean'; package.mkdir(parents=True)
        (package / 'lakefile.lean').write_text('-- fixture')
        return {'name': 'Paperproof', 'package': str(package),
                'entry': {'type': 'git', 'rev': 'pin', 'subDir': 'lean'},
                'identity': {'head': 'pin', 'clean': False, 'status': ' M source.lean'}}

    def test_materialized_dirty_pinned_subdir_allowed_locally(self):
        native.require_materialized_dependencies({'packages': [self.package()]})

    def test_wrong_revision_rejected(self):
        p = self.package(); p['identity']['head'] = 'wrong'
        with self.assertRaisesRegex(RuntimeError, 'wrong-revision'):
            native.require_materialized_dependencies({'packages': [p]})

    def test_missing_config_rejected(self):
        p = self.package(); p['entry']['configFile'] = 'absent.lean'
        with self.assertRaisesRegex(RuntimeError, 'Missing package configuration'):
            native.require_materialized_dependencies({'packages': [p]})

    def test_missing_package_rejected(self):
        p = self.package(); p['package'] += '/missing'
        with self.assertRaisesRegex(RuntimeError, 'Missing package directory'):
            native.require_materialized_dependencies({'packages': [p]})

    def test_exact_specification_matches_65(self):
        actual = json.loads((ROOT / 'tools/quality/reviewed_prs_20260921.json').read_text())['targets']
        self.assertEqual(tuple(actual), native.EXPECTED_TARGETS)
        self.assertEqual(len(actual), 65)
        self.assertEqual(len(set(actual)), 65)

    def test_safe_output_guards(self):
        (self.root / 'lake-manifest.json').write_text(json.dumps({'packagesDir': '.lake/packages', 'packages': []}))
        good = self.root / 'scratch/native_reviewed_runs/fresh'
        with patch.object(native.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0)):
            self.assertEqual(native.safe_output(self.root, good), good)
            for bad in (self.root, self.root / 'lean/run', self.root / 'scratch/native_reviewed_runs/../escape'):
                with self.subTest(path=bad), self.assertRaises((ValueError, RuntimeError)):
                    native.safe_output(self.root, bad)
            good.mkdir(parents=True)
            with self.assertRaisesRegex(RuntimeError, 'already exists'):
                native.safe_output(self.root, good)

    def test_nonignored_output_rejected(self):
        with patch.object(native.subprocess, 'run', return_value=subprocess.CompletedProcess([], 1)):
            with self.assertRaisesRegex(RuntimeError, 'must be ignored'):
                native.safe_output(self.root, self.root / 'scratch/native_reviewed_runs/fresh')


class NativeControlFlowFixtures(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='native-v3-flow-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve(); self.output = self.root / 'new-output'
        spec = self.root / 'tools/quality/reviewed_prs_20260921.json'; spec.parent.mkdir(parents=True)
        self.targets = list(native.EXPECTED_TARGETS)
        spec.write_text(json.dumps({'targets': self.targets}))
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
        self.roles = validate_roles(self.targets)
        self.identity = {'clean_release_eligible': False, 'packages': []}
        self.calls = []; self.fail = None; self.spawn_fail = False; self.context_kwargs = None
        self.stack = ExitStack(); self.addCleanup(self.stack.close)
        self.lock = MagicMock(); self.lock.__enter__.return_value = self.lock; self.lock.fileno.return_value = 191
        for obj, name, kwargs in [
            (Path, 'cwd', {'return_value': self.root}),
            (native, 'safe_output', {'side_effect': lambda root, output: output}),
            (native, 'BuildLock', {'return_value': self.lock}),
            (native, 'idle', {}),
            (native, 'snapshot', {'side_effect': lambda root: copy.deepcopy(self.identity)}),
            (native, 'require_materialized_dependencies', {}),
            (native, 'check_command_sources', {}),
            (native, 'build_lean_context_manifest', {'side_effect': self.context}),
            (native.subprocess, 'Popen', {'side_effect': self.popen}),
        ]:
            self.stack.enter_context(patch.object(obj, name, **kwargs))

    def markers(self):
        return ''.join(f'AUDIT_MODULE_COUNT: {m}: {0 if m in self.roles else 1}\n'
            f'{"AUDIT_COMMAND_MODULE" if m in self.roles else "AUDIT_MODULE"}: {m}\n' for m in self.targets) + f'AUDIT_COUNT: {len(self.targets)-len(self.roles)}\n'

    def popen(self, argv, **kwargs):
        self.calls.append((list(argv), kwargs))
        self.assertEqual(kwargs['pass_fds'], (191,)); self.assertTrue(kwargs['start_new_session'])
        if self.spawn_fail: raise OSError('fixture launch failure')
        text = ''
        if argv[-1] == '--version': text = 'Lean (version 4.34.1)' if 'lean' in argv else 'Lake fixture'
        if str(argv[-1]).endswith('ReviewedPRsAudit.lean'): text = self.markers()
        process = MagicMock(); process.returncode = 7 if self.fail and self.fail in argv else 0
        process.communicate.return_value = (text, 'fixture stderr retained\n')
        return process

    def context(self, root, source, runner):
        if self.context_kwargs is not None:
            runner(['fixture-context-command'], **self.context_kwargs)
        return {'fixture-context': str(source)}

    def report(self):
        return json.loads((self.output / 'report.json').read_text())

    def test_dirty_local_pass_is_not_clean_release(self):
        result = native.run_native(self.root, self.output)
        self.assertEqual(result['local_kernel_status'], 'passed')
        self.assertEqual(result['clean_release_status'], 'failed')
        build = [argv for argv, _ in self.calls if argv[:2] == ['lake', 'build']]
        self.assertEqual(build, [['lake', 'build', *self.targets]])
        for role in self.roles:
            path = str(self.root / 'lean' / (role.replace('.', '/') + '.lean'))
            self.assertEqual(sum(path in argv for argv, _ in self.calls), 1)
        self.assertNotIn('--offline', sum((argv for argv, _ in self.calls), []))
        self.assertNotIn('--no-cache', sum((argv for argv, _ in self.calls), []))

    def test_clean_release_request_fails_but_records_local_pass(self):
        with self.assertRaisesRegex(RuntimeError, 'clean release failed'):
            native.run_native(self.root, self.output, clean_release=True)
        self.assertEqual(self.report()['local_kernel_status'], 'passed')
        self.assertEqual(self.report()['clean_release_status'], 'failed')

    def test_mock_clean_release_classification(self):
        self.identity['clean_release_eligible'] = True
        self.assertEqual(native.run_native(self.root, self.output, clean_release=True)['clean_release_status'], 'passed')

    def test_same_count_target_reorder_rejected_before_lock(self):
        self.targets[0], self.targets[1] = self.targets[1], self.targets[0]
        (self.root / 'tools/quality/reviewed_prs_20260921.json').write_text(json.dumps({'targets': self.targets}))
        with self.assertRaisesRegex(RuntimeError, 'Exact ordered65'):
            native.run_native(self.root, self.output)
        self.lock.__enter__.assert_not_called(); self.assertEqual(self.calls, [])

    def test_build_failure_is_logged_and_not_passed(self):
        self.fail = 'build'
        with self.assertRaisesRegex(RuntimeError, 'Command failed'):
            native.run_native(self.root, self.output)
        report = self.report(); self.assertEqual(report['local_kernel_status'], 'failed')
        last = report['commands'][-1]; self.assertEqual(last['exit_code'], 7)
        self.assertIn('fixture stderr', (self.output / (last['log_prefix']+'.stderr.log')).read_text())

    def test_spawn_failure_retains_row_and_traceback(self):
        self.spawn_fail = True
        with self.assertRaisesRegex(OSError, 'launch failure'):
            native.run_native(self.root, self.output)
        row = self.report()['commands'][0]; self.assertEqual(row['status'], 'launch_failed')
        self.assertIn('launch failure', (self.output / (row['log_prefix']+'.stderr.log')).read_text())

    def test_context_supported_kwargs(self):
        self.context_kwargs = {'check': False, 'capture_output': True, 'text': True, 'input': 'import Init\n'}
        self.assertEqual(native.run_native(self.root, self.output)['local_kernel_status'], 'passed')
        self.assertTrue(any(kw['stdin'] == subprocess.PIPE for _, kw in self.calls))

    def test_context_unknown_kwargs_fail_closed(self):
        self.context_kwargs = {'env': {}}
        with self.assertRaisesRegex(RuntimeError, 'Unsupported runner kwargs'):
            native.run_native(self.root, self.output)


class CLIIntegrationFixtures(unittest.TestCase):
    def test_native_dispatch_preserves_flags(self):
        with patch.object(sys, 'argv', ['checker', '--mode', 'native', '--output', 'scratch/native_reviewed_runs/test', '--wait-for-build-lock', '--clean-release']), \
             patch.object(native, 'run_native', return_value={}) as call:
            cli.main()
        args, kwargs = call.call_args
        self.assertEqual(args[0], ROOT)
        self.assertEqual(kwargs, {'wait': True, 'clean_release': True})

    def test_native_failure_propagates(self):
        with patch.object(sys, 'argv', ['checker', '--mode', 'native', '--output', 'unused']), \
             patch.object(native, 'run_native', side_effect=RuntimeError('fixture native failure')):
            with self.assertRaisesRegex(RuntimeError, 'fixture native failure'): cli.main()

    def test_native_rejects_alternate_dependencies_and_cache(self):
        for flag in ('--mathlib-root', '--cache-dir'):
            with self.subTest(flag=flag), patch.object(sys, 'argv', ['checker', '--mode', 'native', '--output', 'unused', flag, 'elsewhere']), patch.object(native, 'run_native') as call:
                with self.assertRaises(SystemExit): cli.main()
                call.assert_not_called()

    def test_default_copied_mode_still_requires_mathlib(self):
        with patch.object(sys, 'argv', ['checker', '--output', 'unused']), patch.object(native, 'run_native') as call:
            with self.assertRaises(SystemExit): cli.main()
            call.assert_not_called()


if __name__ == '__main__':
    unittest.main()
