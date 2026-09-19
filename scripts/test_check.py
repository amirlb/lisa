"""Offline tests for the check CLI; no JVM or network required."""
import base64
import contextlib
import importlib.machinery
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

loader = importlib.machinery.SourceFileLoader('proof_check', str(Path(__file__).resolve().parents[1] / 'check'))
spec = importlib.util.spec_from_loader(loader.name, loader)
check = importlib.util.module_from_spec(spec)
loader.exec_module(check)


class CheckTests(unittest.TestCase):
    def record(self, status, statement='⊢ x = x'):
        encode = lambda s: base64.b64encode(s.encode()).decode()
        return '\t'.join(['PROOF_RECORD', encode('test.Theory.identity'), encode(statement), encode('test.Theory.definition'), status, 'theorem'])

    def test_inventory_preserves_checked_status_and_unicode(self):
        items = check.records('\n'.join([self.record('checked'), self.record('dependency')]))
        self.assertEqual(items['test.Theory.identity']['status'], 'checked')
        self.assertEqual(items['test.Theory.identity']['statement'], '⊢ x = x')

    def test_inventory_rejects_conflicting_statements(self):
        with self.assertRaises(ValueError):
            check.records(self.record('checked') + '\n' + self.record('dependency', '⊢ false'))

    def test_inventory_rejects_conflicting_admission_status(self):
        with self.assertRaises(ValueError):
            check.records(self.record('checked') + '\n' + self.record('admitted'))

    def fake_run(self, output, code=0, fingerprints=None):
        class Process:
            returncode = code
            def poll(self):
                return code
        def spawn(*args, **kwargs):
            kwargs['stdout'].write(output.encode())
            return Process()
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(check, 'OUTPUT', Path(directory)), patch.object(check, 'fingerprint', side_effect=fingerprints, return_value='stable'), patch.object(check.subprocess, 'Popen', side_effect=spawn), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                return check.run('algebra')

    def test_zero_exit_without_verification_markers_fails(self):
        self.assertNotEqual(self.fake_run('[success] No tests run\n'), 0)

    def test_nonzero_exit_with_success_markers_fails(self):
        self.assertEqual(self.fake_run('PROOF_CHECK GROUP_CHECK PASSED (1)\nPROOF_CHECK LAGRANGE_CHECK PASSED (1)\n', 7), 7)

    def test_success_requires_both_checks(self):
        self.assertEqual(self.fake_run('PROOF_CHECK GROUP_CHECK PASSED (1)\nPROOF_CHECK LAGRANGE_CHECK PASSED (1)\n'), 0)

    def test_source_changes_during_check_fail(self):
        self.assertNotEqual(self.fake_run('PROOF_CHECK GROUP_CHECK PASSED (1)\nPROOF_CHECK LAGRANGE_CHECK PASSED (1)\n', fingerprints=['before', 'after', 'after']), 0)

    def test_search_rejects_stale_index(self):
        with tempfile.TemporaryDirectory() as directory:
            index = Path(directory) / 'index.json'
            index.write_text(json.dumps(dict(fingerprint='old', theorems=[])))
            with patch.object(check, 'INDEX', index), patch.object(check, 'fingerprint', return_value='new'), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(check.search('identity'), 2)


if __name__ == '__main__':
    unittest.main()
