from pathlib import Path
import subprocess
import unittest
import os


REPO = Path(__file__).resolve().parents[1]


class SuperMetriplecticBPSBuildTests(unittest.TestCase):
    def test_bps_locked_build(self) -> None:
        env = os.environ.copy()
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env['PATH']}"
        cmd = [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.SuperMetriplectic.BPS",
        ]
        subprocess.run(cmd, cwd=REPO, env=env, check=True)


if __name__ == "__main__":
    unittest.main()
