import json
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_snippet(body: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="strict-surface-test-") as td:
      path = Path(td) / "StrictSurfaceSmoke.lean"
      path.write_text(
          textwrap.dedent(
              f"""\
              import InfoGeometry.Meta.StrictSurface

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


def _extract_prefixed_json(output: str, prefix: str) -> dict:
    for line in output.splitlines():
        if line.startswith(prefix):
            return json.loads(line.removeprefix(prefix))
    raise AssertionError(f"missing {prefix!r} in output:\n{output}")


class StrictSurfaceTests(unittest.TestCase):
    def test_strict_def_admits_ordinary_definition(self):
        proc = _run_snippet(
            """
            namespace Scratch.StrictSurface

            strict_def strictId : Nat → Nat := fun x => x

            end Scratch.StrictSurface
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)
        payload = _extract_prefixed_json(output, "[strict-admission-json] ")
        self.assertEqual(payload["name"], "Scratch.StrictSurface.strictId")
        self.assertEqual(payload["declKind"], "definition")
        self.assertEqual(payload["role"], "constructor")
        self.assertEqual(payload["region"], "ordinary")
        self.assertEqual(payload["decision"], "admitted")

    def test_strict_theorem_marks_wrapper_as_needs_review(self):
        proc = _run_snippet(
            """
            namespace Scratch.StrictSurface

            strict_theorem trivialCarrier : True := True.intro

            end Scratch.StrictSurface
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)
        payload = _extract_prefixed_json(output, "[strict-admission-json] ")
        self.assertEqual(payload["declKind"], "theorem")
        self.assertEqual(payload["role"], "owner")
        self.assertEqual(payload["region"], "ordinary")
        self.assertEqual(payload["decision"], "needs_review")
        self.assertEqual(payload["thinSurface"], "wrapper")

    def test_strict_bridge_is_not_promotable_in_bridge_region(self):
        proc = _run_snippet(
            """
            namespace InfoGeometry.LLM.StrictSurface

            strict_bridge bridgeId : Nat → Nat := fun x => x

            end InfoGeometry.LLM.StrictSurface
            """
        )
        output = _combined_output(proc)
        self.assertEqual(proc.returncode, 0, msg=output)
        payload = _extract_prefixed_json(output, "[strict-admission-json] ")
        self.assertEqual(payload["declKind"], "bridge")
        self.assertEqual(payload["role"], "bridge")
        self.assertEqual(payload["region"], "bridge")
        self.assertEqual(payload["decision"], "not_promotable")

    def test_strict_theorem_blocks_protected_region_without_metadata(self):
        proc = _run_snippet(
            """
            namespace InfoGeometry.Meta.StrictSurface

            strict_theorem protectedRefl : 1 = 1 := rfl

            end InfoGeometry.Meta.StrictSurface
            """
        )
        output = _combined_output(proc)
        self.assertNotEqual(proc.returncode, 0, msg=output)
        payload = _extract_prefixed_json(output, "[strict-admission-json] ")
        self.assertEqual(payload["declKind"], "theorem")
        self.assertEqual(payload["region"], "protected")
        self.assertEqual(payload["decision"], "blocked")
        self.assertIn("rep_depth", payload["hard"]["missingRequiredAttrs"])


if __name__ == "__main__":
    unittest.main()
