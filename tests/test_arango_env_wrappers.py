import os
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
WITH_ENV = REPO_ROOT / "tools/infra/with_arango_env.sh"


class TestArangoEnvWrappers(unittest.TestCase):
    def _run_with_env(self, env_body: str, cmd):
        with tempfile.NamedTemporaryFile("w", delete=False) as f:
            f.write(textwrap.dedent(env_body).strip() + "\n")
            env_file = f.name
        try:
            env = os.environ.copy()
            env["HIVE_ARANGO_ENV_FILE"] = env_file
            return subprocess.run(
                [str(WITH_ENV), "--", *cmd],
                cwd=REPO_ROOT,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
        finally:
            os.unlink(env_file)

    def test_exports_alias_pairs_from_primary_names(self):
        result = self._run_with_env(
            """
            ARANGO_ENDPOINT=http://127.0.0.1:8530
            ARANGO_DATABASE=infogeometry
            ARANGO_USER=root
            ARANGO_PASS=secret123
            """,
            [
                "python3",
                "-c",
                "import os; print(os.getenv('ARANGO_USER')); print(os.getenv('ARANGO_USERNAME')); print(os.getenv('ARANGO_PASS')); print(os.getenv('ARANGO_PASSWORD'))",
            ],
        )
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        lines = result.stdout.strip().splitlines()
        self.assertEqual(lines, ["root", "root", "secret123", "secret123"])

    def test_supports_legacy_alias_inputs(self):
        result = self._run_with_env(
            """
            ARANGO_ENDPOINT=http://127.0.0.1:8530
            ARANGO_DATABASE=infogeometry
            ARANGO_USERNAME=legacy_user
            ARANGO_PASSWORD=legacy_pass
            """,
            [
                "python3",
                "-c",
                "import os; print(os.getenv('ARANGO_USER')); print(os.getenv('ARANGO_PASS'))",
            ],
        )
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertEqual(result.stdout.strip().splitlines(), ["legacy_user", "legacy_pass"])

    def test_missing_env_file_returns_actionable_error(self):
        env = os.environ.copy()
        env["HIVE_ARANGO_ENV_FILE"] = str(REPO_ROOT / "configs/local/DOES_NOT_EXIST.env")
        result = subprocess.run(
            [str(WITH_ENV), "--", "python3", "-c", "print('x')"],
            cwd=REPO_ROOT,
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(result.returncode, 2)
        self.assertIn("Missing env file", result.stderr)
        self.assertIn("arango_access_setup.sh", result.stderr)


if __name__ == "__main__":
    unittest.main()
