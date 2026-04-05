import json
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="strict-def-test-") as td:
        path = Path(td) / "StrictSmoke.lean"
        path.write_text(
            textwrap.dedent(
                f"""\
                import InfoGeometry.Meta.StrictDef

                {body}
                """
            ),
            encoding="utf-8",
        )
        return subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
        )


def _combined_output(proc: subprocess.CompletedProcess[str]) -> str:
    return f"{proc.stdout}\n{proc.stderr}"


def _extract_gap_json(output: str) -> dict:
    for line in output.splitlines():
        if line.startswith("[strict-gap-json] "):
            return json.loads(line.removeprefix("[strict-gap-json] "))
    raise AssertionError(f"missing strict-gap-json in output:\n{output}")


class StrictDefTests(unittest.TestCase):
    def test_strict_def_accepts_term_mode_definition(self):
        proc = _run_snippet(
            """
            #strict_def strictId : Nat → Nat := fun x => x
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)

    def test_strict_theorem_accepts_term_mode_proof(self):
        proc = _run_snippet(
            """
            #strict_theorem reflNat : 1 = 1 := rfl
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)

    def test_strict_def_rejects_tactic_mode(self):
        proc = _run_snippet(
            """
            #strict_def badStrict : True := by trivial
            """
        )
        output = _combined_output(proc)
        self.assertNotEqual(proc.returncode, 0, msg=output)
        self.assertIn("uses forbidden term syntax", output)

    def test_strict_theorem_hole_emits_gap_json(self):
        proc = _run_snippet(
            """
            #strict_theorem holeNat : 1 = 1 := _
            """
        )
        output = _combined_output(proc)
        self.assertNotEqual(proc.returncode, 0, msg=output)
        self.assertIn("strict theorem `holeNat` elaborated to an expression with unresolved metavariables.", output)
        payload = _extract_gap_json(output)
        self.assertEqual(payload["declKind"], "theorem")
        self.assertEqual(payload["declName"], "holeNat")
        self.assertEqual(payload["failureKind"], "unresolvedMetavariables")
        self.assertEqual(payload["expectedType"], "1 = 1")
        self.assertTrue(payload["hasExprMVar"])
        self.assertFalse(payload["hasSorry"])
        self.assertEqual(len(payload["holes"]), 1)
        self.assertEqual(payload["holes"][0]["expectedType"], "1 = 1")
        self.assertEqual(payload["holes"][0]["localContext"], [])

    def test_strict_def_type_mismatch_emits_raw_boundary_json(self):
        proc = _run_snippet(
            """
            #strict_def strictGap : Nat := id
            """
        )
        output = _combined_output(proc)
        self.assertNotEqual(proc.returncode, 0, msg=output)
        self.assertNotIn("Type mismatch", output)
        self.assertIn(
            "strict definition `strictGap` failed to elaborate against its declared type.",
            output,
        )
        payload = _extract_gap_json(output)
        self.assertEqual(payload["declKind"], "definition")
        self.assertEqual(payload["declName"], "strictGap")
        self.assertEqual(payload["failureKind"], "typeMismatch")
        self.assertEqual(payload["expectedType"], "Nat")
        self.assertIn("inferredType", payload)
        self.assertFalse(payload["hasSorry"])
        self.assertTrue(payload["hasExprMVar"])
        self.assertGreaterEqual(len(payload["holes"]), 1)

    def test_strict_theorem_blocks_thin_wrapper_in_protected_region(self):
        proc = _run_snippet(
            """
            namespace InfoGeometry.Meta.Test

            #strict_theorem trivialCarrier : True := True.intro

            end InfoGeometry.Meta.Test
            """
        )
        output = _combined_output(proc)
        self.assertNotEqual(proc.returncode, 0, msg=output)
        self.assertIn(
            "strict theorem `InfoGeometry.Meta.Test.trivialCarrier` is blocked in protected region",
            output,
        )
        payload = _extract_gap_json(output)
        self.assertEqual(payload["declKind"], "theorem")
        self.assertEqual(payload["declName"], "InfoGeometry.Meta.Test.trivialCarrier")
        self.assertEqual(payload["failureKind"], "blockedProofShape")
        self.assertEqual(payload["region"], "protected")
        self.assertEqual(payload["thinSurface"], "wrapper")
        self.assertEqual(payload["statementShape"], "prop")


if __name__ == "__main__":
    unittest.main()
