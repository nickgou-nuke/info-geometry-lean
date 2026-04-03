import tempfile
import unittest
from contextlib import contextmanager
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.frontier import compiler_bridge_client as bridge_client


class CompilerBridgeRpcTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls._tmp = tempfile.TemporaryDirectory()
        cls.tmp_dir = Path(cls._tmp.name)

        cls.clean_file = cls.tmp_dir / "bridge_clean.lean"
        cls.clean_file.write_text(
            "\n".join(
                [
                    "theorem bridge_ok (p : Prop) (hp : p) : p := by",
                    "  exact hp",
                    "",
                ]
            ),
            encoding="utf-8",
        )

        cls.sorry_file = cls.tmp_dir / "bridge_sorry.lean"
        cls.sorry_file.write_text(
            "\n".join(
                [
                    "theorem bridge_sorry (p : Prop) : p := by",
                    "  sorry",
                    "",
                ]
            ),
            encoding="utf-8",
        )

    @classmethod
    def tearDownClass(cls):
        cls._tmp.cleanup()

    def _call(
        self,
        input_path: Path,
        rpc_method: str,
        *,
        line: int = 0,
        character: int = 0,
        decl_name: str | None = None,
    ) -> dict:
        return bridge_client.call_bridge_method(
            input_path=input_path,
            line=line,
            character=character,
            timeout_s=120.0,
            server_mode="custom",
            inject_rpc_import_flag=False,
            wait_for_diagnostics=True,
            rpc_method=rpc_method,
            decl_name=decl_name,
        )

    @contextmanager
    def _bridge_version(self, schema: int, protocol: str):
        old = bridge_client.BRIDGE_VERSION
        bridge_client.BRIDGE_VERSION = {"schema": schema, "protocol": protocol}
        try:
            yield
        finally:
            bridge_client.BRIDGE_VERSION = old

    def test_get_env_fingerprint_returns_stable_envelope(self):
        result = self._call(self.clean_file, "getEnvFingerprint")
        self.assertTrue(result["ok"])

        response_meta = result["responseMeta"]
        self.assertEqual(response_meta["version"]["schema"], 1)
        self.assertEqual(response_meta["version"]["protocol"], "ig.compiler/v1")

        env = response_meta["env"]
        self.assertIsInstance(env["leanToolchain"], str)
        self.assertIsInstance(env["importRoot"], str)
        self.assertIsInstance(env["namespaceHint"], str)
        self.assertIsInstance(env["oleanHash"], str)
        self.assertIsInstance(env["artifactSchema"], int)

    def test_check_snippet_returns_typed_goals_and_count(self):
        result = self._call(
            self.clean_file,
            "checkSnippet",
            line=1,
            character=2,
        )
        self.assertTrue(result["ok"])
        self.assertIn("goals", result)
        self.assertIn("goalCount", result)
        self.assertEqual(result["goalCount"], len(result["goals"]))
        self.assertGreaterEqual(result["goalCount"], 1)

        first_goal = result["goals"][0]
        self.assertIn("targetHead", first_goal)
        self.assertIn("targetHeadSource", first_goal)
        self.assertEqual(first_goal["targetHead"], "p")
        self.assertEqual(first_goal["targetHeadSource"], "textHeuristic")

        first_local = first_goal["locals"][0]
        self.assertIn("typeHead", first_local)
        self.assertIn("typeHeadSource", first_local)
        self.assertEqual(first_local["typeHead"], "Prop")
        self.assertEqual(first_local["typeHeadSource"], "textHeuristic")

    def test_validate_decl_happy_path(self):
        result = self._call(
            self.clean_file,
            "validateDecl",
            decl_name="bridge_ok",
        )
        self.assertTrue(result["ok"])
        self.assertTrue(result["declFound"])
        self.assertFalse(result["hasSorry"])
        self.assertTrue(result["theoremType"])
        self.assertEqual(result["theoremTypeHead"], "∀")
        self.assertEqual(result["theoremTypeHeadSource"], "textHeuristic")

    def test_validate_decl_detects_sorry(self):
        result = self._call(
            self.sorry_file,
            "validateDecl",
            decl_name="bridge_sorry",
        )
        self.assertFalse(result["ok"])
        self.assertTrue(result["declFound"])
        self.assertTrue(result["hasSorry"])
        codes = [diag.get("code") for diag in result.get("diagnostics", [])]
        self.assertIn("containsSorry", codes)

    def test_protocol_mismatch_short_circuits_without_semantic_work(self):
        with self._bridge_version(schema=999, protocol="ig.compiler/v999"):
            result = self._call(
                self.clean_file,
                "checkSnippet",
                line=0,
                character=2,
            )

        self.assertFalse(result["ok"])
        self.assertEqual(result["goals"], [])
        self.assertEqual(result["goalCount"], 0)

        diagnostics = result.get("diagnostics", [])
        self.assertEqual(len(diagnostics), 1)
        self.assertEqual(diagnostics[0].get("code"), "unsupportedProtocolVersion")
        self.assertEqual(diagnostics[0].get("phase"), "protocol")
        self.assertEqual(diagnostics[0].get("classificationProvenance"), "bridgeRule")


if __name__ == "__main__":
    unittest.main()